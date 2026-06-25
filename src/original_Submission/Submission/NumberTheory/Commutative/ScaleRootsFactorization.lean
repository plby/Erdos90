import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Factorization after scaling polynomial roots

Scaling every root by a unit preserves polynomial units, irreducibility, and
the multiset of degrees of normalized irreducible factors.  This supplies the
local algebra needed to compare different integral models of a rational
polynomial away from their denominator primes.
-/

namespace Submission.NumberTheory.Milne

open Polynomial UniqueFactorizationMonoid

noncomputable section

variable {k : Type*} [Field k]

noncomputable local instance scaleRootsFactorizationDecidableEq : DecidableEq k :=
  Classical.decEq k

/-- Scaling roots by a unit preserves and reflects polynomial units. -/
theorem unit_scale_roots (p : k[X]) {u : k} (_hu : IsUnit u) :
    IsUnit (p.scaleRoots u) ↔ IsUnit p := by
  rw [Polynomial.isUnit_iff_degree_eq_zero,
    Polynomial.isUnit_iff_degree_eq_zero, degree_scaleRoots]

private theorem irreducible_scale_unit
    (p : k[X]) (u : kˣ) (hp : Irreducible p) :
    Irreducible (p.scaleRoots (u : k)) := by
  refine ⟨?_, ?_⟩
  · exact fun hunit => hp.not_isUnit
      ((unit_scale_roots p u.isUnit).mp hunit)
  · intro a b hab
    have hback := congrArg
      (fun q : k[X] => q.scaleRoots ((u⁻¹ : kˣ) : k)) hab
    have hfactor :
        p = a.scaleRoots ((u⁻¹ : kˣ) : k) *
          b.scaleRoots ((u⁻¹ : kˣ) : k) := by
      simpa [← scaleRoots_mul, mul_scaleRoots_of_noZeroDivisors] using hback
    rcases hp.isUnit_or_isUnit hfactor with ha | hb
    · exact Or.inl
        ((unit_scale_roots a (u⁻¹).isUnit).mp ha)
    · exact Or.inr
        ((unit_scale_roots b (u⁻¹).isUnit).mp hb)

/-- Scaling roots by a unit preserves and reflects irreducibility. -/
theorem irreducible_scale_roots
    (p : k[X]) {u : k} (hu : IsUnit u) :
    Irreducible (p.scaleRoots u) ↔ Irreducible p := by
  obtain ⟨u, rfl⟩ := hu
  constructor
  · intro hp
    have h := irreducible_scale_unit
      (p.scaleRoots (u : k)) u⁻¹ hp
    simpa [← scaleRoots_mul] using h
  · exact irreducible_scale_unit p u

/-- The normalized factorization of a root-scaled polynomial is obtained by
root-scaling every normalized factor. -/
theorem normalized_scale_roots
    (p : k[X]) (hp : p ≠ 0) {u : k} (hu : IsUnit u) :
    normalizedFactors (p.scaleRoots u) =
      (normalizedFactors p).map (fun q => q.scaleRoots u) := by
  classical
  obtain ⟨u, rfl⟩ := hu
  let s : Multiset k[X] := normalizedFactors p
  let t : Multiset k[X] := s.map (fun q => q.scaleRoots (u : k))
  have hprod (m : Multiset k[X]) :
      (m.map (fun q => q.scaleRoots (u : k))).prod =
        m.prod.scaleRoots (u : k) := by
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons q m ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons]
        rw [ih, mul_scaleRoots_of_noZeroDivisors]
  have htIrreducible : ∀ q ∈ t, Irreducible q := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hq
    exact (irreducible_scale_roots a u.isUnit).2
      (irreducible_of_normalized_factor a ha)
  have htMonic : ∀ q ∈ t, q.Monic := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hq
    have ha' : a ∈ normalizedFactors p := by simpa only [s] using ha
    exact (monic_scaleRoots_iff _).2
      ((Polynomial.mem_normalizedFactors_iff hp).mp ha').2.1
  have htAssociated : Associated t.prod (p.scaleRoots (u : k)) := by
    obtain ⟨v, hv⟩ := prod_normalizedFactors hp
    have hvUnit : IsUnit (((v : k[X]).scaleRoots (u : k))) :=
      (unit_scale_roots (v : k[X]) u.isUnit).2 v.isUnit
    obtain ⟨w, hw⟩ := hvUnit
    refine ⟨w, ?_⟩
    change t.prod * (w : k[X]) = p.scaleRoots (u : k)
    rw [hw, show t.prod = s.prod.scaleRoots (u : k) from hprod s]
    rw [← mul_scaleRoots_of_noZeroDivisors, hv]
  calc
    normalizedFactors (p.scaleRoots (u : k)) = normalizedFactors t.prod :=
      htAssociated.symm.normalizedFactors_eq
    _ = t.map normalize := normalizedFactors_prod_eq t htIrreducible
    _ = t.map id := by
      apply Multiset.map_congr rfl
      intro q hq
      exact (htMonic q hq).normalize_eq_self
    _ = t := Multiset.map_id t

/-- In particular, unit root-scaling preserves the multiset of degrees of
the normalized irreducible factors. -/
theorem degrees_scale_roots
    (p : k[X]) (hp : p ≠ 0) {u : k} (hu : IsUnit u) :
    (normalizedFactors (p.scaleRoots u)).map natDegree =
      (normalizedFactors p).map natDegree := by
  rw [normalized_scale_roots p hp hu, Multiset.map_map]
  exact Multiset.map_congr rfl fun q _ => natDegree_scaleRoots q u

end

end Submission.NumberTheory.Milne
