import Submission.NumberTheory.Galois.GaloisOrbitFactorization
import Submission.NumberTheory.Galois.PermutationCycleTransport

/-!
# Frobenius cycles as permutation cycles

The finite-field Frobenius automorphism induces a permutation of the roots of
every polynomial.  Each `frobeniusCycle` is a cyclic subset for that
permutation.
-/

namespace Submission.NumberTheory.Milne

open Equiv Finset Polynomial Set

noncomputable section

variable (k l : Type*) [Field k] [Field l] [Fintype k] [Finite l]
  [Algebra k l]

/-- Finite-field Frobenius, restricted to the root set of a polynomial. -/
def frobeniusRootPerm (f : k[X]) : Equiv.Perm (f.rootSet l) :=
  MulAction.toPermHom Gal(l/k) (f.rootSet l)
    (FiniteField.frobeniusAlgEquivOfAlgebraic k l)

/-- The roots in the Frobenius cycle through `x`, as a finset of roots. -/
noncomputable def frobeniusRootCycle
    (f : k[X]) (x : f.rootSet l) : Finset (f.rootSet l) := by
  classical
  exact Finset.univ.filter fun y => (y : l) ∈ frobeniusCycle k l x

@[simp]
theorem frobenius_root_cycle (f : k[X]) (x y : f.rootSet l) :
    y ∈ frobeniusRootCycle k l f x ↔
      (y : l) ∈ frobeniusCycle k l x := by
  simp [frobeniusRootCycle]

/-- A finite-field Frobenius orbit is a cyclic subset of its permutation on
the roots. -/
theorem frobenius_perm_cycle
    (f : k[X]) (x : f.rootSet l) :
    (frobeniusRootPerm k l f).IsCycleOn
      (frobeniusRootCycle k l f x : Set (f.rootSet l)) := by
  let F : Gal(l/k) := FiniteField.frobeniusAlgEquivOfAlgebraic k l
  let tau : Equiv.Perm (f.rootSet l) := frobeniusRootPerm k l f
  let s : Finset (f.rootSet l) := frobeniusRootCycle k l f x
  change tau.IsCycleOn (s : Set (f.rootSet l))
  constructor
  · refine ⟨?_, tau.injective.injOn, ?_⟩
    · intro y hy
      change y ∈ s at hy
      change tau y ∈ s
      rw [show y ∈ s ↔ (y : l) ∈ frobeniusCycle k l x by simp [s]] at hy
      rw [show tau y ∈ s ↔ ((tau y : f.rootSet l) : l) ∈
          frobeniusCycle k l x by simp [s]]
      rw [frobenius_cycle_orbit] at hy ⊢
      obtain ⟨g, hgy⟩ := MulAction.mem_orbit_iff.mp hy
      change F • (y : l) ∈ MulAction.orbit Gal(l/k) (x : l)
      rw [← hgy]
      simpa only [mul_smul] using MulAction.mem_orbit (x : l) (F * g)
    · intro y hy
      change y ∈ s at hy
      rw [show y ∈ s ↔ (y : l) ∈ frobeniusCycle k l x by
        simp [s]] at hy
      let z : f.rootSet l := F⁻¹ • y
      have hz : z ∈ s := by
        rw [show z ∈ s ↔ (z : l) ∈ frobeniusCycle k l x by simp [s]]
        rw [frobenius_cycle_orbit] at hy ⊢
        obtain ⟨g, hgy⟩ := MulAction.mem_orbit_iff.mp hy
        change F⁻¹ • (y : l) ∈ MulAction.orbit Gal(l/k) (x : l)
        rw [← hgy]
        simpa only [mul_smul] using MulAction.mem_orbit (x : l) (F⁻¹ * g)
      refine ⟨z, hz, ?_⟩
      apply Subtype.ext
      simp [tau, frobeniusRootPerm, z, F]
  · intro y hy z hz
    change y ∈ s at hy
    change z ∈ s at hz
    rw [show y ∈ s ↔ (y : l) ∈ frobeniusCycle k l x by
      simp [s]] at hy
    rw [show z ∈ s ↔ (z : l) ∈ frobeniusCycle k l x by
      simp [s]] at hz
    rw [frobenius_cycle_orbit] at hy hz
    obtain ⟨g, hgy⟩ := MulAction.mem_orbit_iff.mp hy
    obtain ⟨h, hhz⟩ := MulAction.mem_orbit_iff.mp hz
    obtain ⟨n, hn⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l).2
        (h * g⁻¹)
    refine ⟨(n.1 : ℤ), ?_⟩
    rw [zpow_natCast]
    change ((MulAction.toPermHom Gal(l/k) (f.rootSet l) F) ^ n.1) y = z
    rw [← map_pow]
    apply Subtype.ext
    change (F ^ n.1) • (y : l) = (z : l)
    change F ^ n.1 = h * g⁻¹ at hn
    rw [hn, ← hgy, ← hhz]
    simp only [mul_smul, inv_smul_smul]

/-- Passing from a Frobenius cycle of field elements to the corresponding
finset of polynomial roots does not change its cardinality. -/
theorem card_frobenius_cycle
    (f : k[X]) (x : f.rootSet l) :
    (frobeniusRootCycle k l f x).card =
      Set.ncard (frobeniusCycle k l x) := by
  classical
  let s : Finset (f.rootSet l) := frobeniusRootCycle k l f x
  let t : Set l := frobeniusCycle k l x
  have ht : t ⊆ f.rootSet l :=
    frobenius_cycle_set (k := k) (l := l) x.2
  letI : Fintype {y : l // y ∈ t} := Fintype.ofFinite _
  let e : {y // y ∈ s} ≃ {y : l // y ∈ t} :=
    { toFun := fun y => ⟨(y.1 : l), by
        exact (frobenius_root_cycle k l f x y.1).mp y.2⟩
      invFun := fun y => ⟨⟨y.1, ht y.2⟩, by
        exact (frobenius_root_cycle k l f x ⟨y.1, ht y.2⟩).mpr y.2⟩
      left_inv := fun y => by rfl
      right_inv := fun y => by rfl }
  calc
    s.card = Fintype.card {y // y ∈ s} := by simp
    _ = Nat.card {y : l // y ∈ t} := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr e
    _ = Set.ncard t := Nat.card_coe_set_eq t

end

end Submission.NumberTheory.Milne
