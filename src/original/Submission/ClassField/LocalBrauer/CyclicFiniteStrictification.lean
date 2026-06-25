import Submission.ClassField.LocalBrauer.FiniteInvariantCompatibility

/-!
# Strictifying finite cyclic invariant squares

An injective map between finite cyclic groups can be made compatible with
the standard inclusion of cyclic models by postcomposing the upper cyclic
identification with an automorphism.  This gives a target-side alternative
to proving compatibility through explicit cocycle inflation.
-/

namespace Submission.CField.LBrauer

noncomputable section

open BGroups CProduca

namespace CIStrict

local instance localInvariantLevelDegree_neZero (r : ℕ) :
    NeZero (invariantLevelDegree r) :=
  ⟨(invariant_level_pos r).ne'⟩

/-- Cyclic automorphisms of the multiplicative copy of `ZMod d` are units
of `ZMod d`. -/
noncomputable def zmodAutUnits (d : ℕ) :
    MulAut (Multiplicative (ZMod d)) ≃* (ZMod d)ˣ :=
  (MulAutMultiplicative (ZMod d)).trans (ZMod.AddAutEquivUnits d)

@[simp]
theorem zmod_aut_add (d : ℕ) (u : (ZMod d)ˣ)
    (z : Multiplicative (ZMod d)) :
    ((zmodAutUnits d).symm u z).toAdd =
      (u : ZMod d) * z.toAdd := by
  rfl

/-- An element of order `n` in `ZMod m`, for `n | m`, is a unit multiple of
the standard element `m / n`. -/
theorem unit_div_order
    {n m : ℕ} [NeZero n] [NeZero m] (hnm : n ∣ m)
    (a : ZMod m) (ha : addOrderOf a = n) :
    ∃ u : (ZMod m)ˣ, a = (u : ZMod m) * (m / n : ℕ) := by
  obtain ⟨d, hd, u, hu, hau⟩ := ZMod.eq_unit_mul_divisor a
  let u' : (ZMod m)ˣ := hu.unit
  have hu' : (u' : ZMod m) = u := hu.unit_spec
  by_cases hd0 : d = 0
  · subst d
    simp only [Nat.cast_zero, mul_zero] at hau
    subst a
    have hn : n = 1 := by simpa using ha.symm
    subst n
    exact ⟨1, by simp⟩
  have hm0 : m ≠ 0 := NeZero.ne m
  have horder : addOrderOf (d : ZMod m) = n := by
    rw [hau, ← hu'] at ha
    rw [← ha]
    simpa [Units.smul_def] using
      ((DistribMulAction.toAddEquiv (ZMod m) u').addOrderOf_eq
        (d : ZMod m)).symm
  have hmd : m / d = n := by
    simpa [ZMod.addOrderOf_coe d hm0,
      Nat.gcd_eq_right_iff_dvd.mpr hd] using horder
  have hmul : m = n * d :=
    (Nat.div_eq_iff_eq_mul_left (Nat.pos_of_ne_zero hd0) hd).1 hmd
  have hdiv : m / n = d := by
    apply (Nat.div_eq_iff_eq_mul_left (NeZero.pos n) hnm).2
    simpa [Nat.mul_comm] using hmul
  refine ⟨u', ?_⟩
  rw [hdiv, hu', ← hau]

variable {A B : Type*} [CommGroup A] [CommGroup B]

/-- Generic successor strictification.  If `f : A -> B` and the model
inclusion `i : ZMod n -> ZMod m` are injective, and `i(1) = m/n`, then any
cyclic identifications of `A` and `B` can be adjusted at the upper level so
that their square commutes. -/
theorem upper_mul_compatible
    {n m : ℕ} [NeZero n] [NeZero m] (hnm : n ∣ m)
    (f : A →* B) (hf : Function.Injective f)
    (eA : A ≃* Multiplicative (ZMod n))
    (eB : B ≃* Multiplicative (ZMod m))
    (i : Multiplicative (ZMod n) →* Multiplicative (ZMod m))
    (hi_one : i (Multiplicative.ofAdd (1 : ZMod n)) =
      Multiplicative.ofAdd (m / n : ZMod m)) :
    ∃ eB' : B ≃* Multiplicative (ZMod m),
      ∀ x, eB' (f x) = i (eA x) := by
  let j : Multiplicative (ZMod n) →* Multiplicative (ZMod m) :=
    eB.toMonoidHom.comp (f.comp eA.symm.toMonoidHom)
  have hj : Function.Injective j :=
    eB.injective.comp (hf.comp eA.symm.injective)
  let oneN : Multiplicative (ZMod n) := Multiplicative.ofAdd 1
  have hjOrder : addOrderOf (j oneN).toAdd = n := by
    change orderOf (j oneN) = n
    rw [orderOf_injective j hj]
    exact ZMod.addOrderOf_one n
  obtain ⟨u, hu⟩ := unit_div_order
    hnm (j oneN).toAdd hjOrder
  let beta : MulAut (Multiplicative (ZMod m)) :=
    (zmodAutUnits m).symm u⁻¹
  let eB' : B ≃* Multiplicative (ZMod m) := eB.trans beta
  refine ⟨eB', ?_⟩
  intro x
  let z := eA x
  have hz : z = oneN ^ z.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp [oneN]
  have hgen : beta (j oneN) = i oneN := by
    apply Multiplicative.toAdd.injective
    rw [zmod_aut_add, hu]
    simp [hi_one, oneN]
  change beta (eB (f x)) = i z
  have hjz : j z = eB (f x) := by simp [j, z]
  rw [← hjz]
  rw [hz, map_pow, map_pow, map_pow, hgen]

/-- Multiplicative form of the canonical cyclic model for a factorial
torsion level. -/
def factorialTorsionZ (r : ℕ) :
    Multiplicative (ZMod (invariantLevelDegree r)) ≃*
      invariantTorsionLevel r :=
  (torsionZMod
    (invariantLevelDegree r)).toMultiplicative

/-- The standard inclusion expressed in cyclic `ZMod` coordinates. -/
def factorialZInclusion {r s : ℕ} (h : r ≤ s) :
    Multiplicative (ZMod (invariantLevelDegree r)) →*
      Multiplicative (ZMod (invariantLevelDegree s)) :=
  (factorialTorsionZ s).symm.toMonoidHom.comp
    ((invariantTorsionInclusion r s h).comp
      (factorialTorsionZ r).toMonoidHom)

/-- In cyclic coordinates, factorial torsion inclusion sends `1` to the
degree quotient. -/
theorem factorial_z_inclusion {r s : ℕ} (h : r ≤ s) :
    factorialZInclusion h
        (Multiplicative.ofAdd
          (1 : ZMod (invariantLevelDegree r))) =
      Multiplicative.ofAdd
        (invariantLevelDegree s / invariantLevelDegree r :
          ZMod (invariantLevelDegree s)) := by
  change (factorialTorsionZ s).symm
      (invariantTorsionInclusion r s h
        (factorialTorsionZ r
          (Multiplicative.ofAdd
            (1 : ZMod (invariantLevelDegree r))))) = _
  apply (factorialTorsionZ s).injective
  rw [(factorialTorsionZ s).apply_symm_apply]
  change invariantTorsionInclusion r s h
      (Multiplicative.ofAdd
        (localDivTorsion (invariantLevelDegree r))) =
    factorialTorsionZ s (Multiplicative.ofAdd
      (invariantLevelDegree s / invariantLevelDegree r :
        ZMod (invariantLevelDegree s)))
  have hpow : Multiplicative.ofAdd
      (invariantLevelDegree s / invariantLevelDegree r :
        ZMod (invariantLevelDegree s)) =
      (Multiplicative.ofAdd
        (1 : ZMod (invariantLevelDegree s))) ^
          (invariantLevelDegree s / invariantLevelDegree r) := by
    apply Multiplicative.toAdd.injective
    simp
  rw [hpow, map_pow]
  exact torsion_inclusion_div h

/-- Successor-extension theorem in the exact torsion targets used by the
finite local invariants.  Any lower equivalence can be retained while the
upper equivalence is adjusted to make the transition square commute. -/
theorem upper_torsion_compatible
    {A B : Type*} [CommGroup A] [CommGroup B]
    {r s : ℕ} (h : r ≤ s)
    (f : A →* B) (hf : Function.Injective f)
    (eA : A ≃* invariantTorsionLevel r)
    (eB : B ≃* invariantTorsionLevel s) :
    ∃ eB' : B ≃* invariantTorsionLevel s,
      ∀ x, eB' (f x) = invariantTorsionInclusion r s h (eA x) := by
  let zr := factorialTorsionZ r
  let zs := factorialTorsionZ s
  let eAZ : A ≃* Multiplicative (ZMod (invariantLevelDegree r)) :=
    eA.trans zr.symm
  let eBZ : B ≃* Multiplicative (ZMod (invariantLevelDegree s)) :=
    eB.trans zs.symm
  obtain ⟨eBZ', heBZ'⟩ := upper_mul_compatible
    (invariant_level_dvd h) f hf eAZ eBZ
    (factorialZInclusion h) (factorial_z_inclusion h)
  let eB' : B ≃* invariantTorsionLevel s := eBZ'.trans zs
  refine ⟨eB', ?_⟩
  intro x
  change zs (eBZ' (f x)) = _
  rw [heBZ']
  change zs (zs.symm
    (invariantTorsionInclusion r s h (zr (zr.symm (eA x))))) = _
  rw [zr.apply_symm_apply, zs.apply_symm_apply]

section GlobalStrictification

universe u

variable {G : ℕ → Type u} [∀ r, CommGroup (G r)]
variable (f : ∀ r s : ℕ, r ≤ s → G r →* G s)
variable [DirectedSystem G (fun {_ _} h ↦ f _ _ h)]

/-- Starting with arbitrary cyclic identifications at every factorial level,
recursively adjust only the next identification so that each consecutive
transition square commutes. -/
noncomputable def strictifiedFactorialEquiv
    (hf : ∀ r, Function.Injective (f r (r + 1) (Nat.le_succ r)))
    (e : ∀ r, G r ≃* invariantTorsionLevel r) :
    ∀ r, G r ≃* invariantTorsionLevel r
  | 0 => e 0
  | r + 1 => Classical.choose <|
      upper_torsion_compatible (Nat.le_succ r)
        (f r (r + 1) (Nat.le_succ r)) (hf r)
        (strictifiedFactorialEquiv hf e r) (e (r + 1))

omit [DirectedSystem G fun {r s} h ↦ f r s h] in
/-- Every consecutive square in the recursively strictified family
commutes. -/
theorem strictified_factorial_succ
    (hf : ∀ r, Function.Injective (f r (r + 1) (Nat.le_succ r)))
    (e : ∀ r, G r ≃* invariantTorsionLevel r)
    (r : ℕ) (x : G r) :
    strictifiedFactorialEquiv f hf e (r + 1)
        (f r (r + 1) (Nat.le_succ r) x) =
      invariantTorsionInclusion r (r + 1) (Nat.le_succ r)
        (strictifiedFactorialEquiv f hf e r x) := by
  exact Classical.choose_spec
    (upper_torsion_compatible (Nat.le_succ r)
      (f r (r + 1) (Nat.le_succ r)) (hf r)
      (strictifiedFactorialEquiv f hf e r) (e (r + 1))) x

/-- Consecutive strictification makes the family compatible with every
transition in the directed factorial chain. -/
theorem strict_facto_compa
    (hf : ∀ r, Function.Injective (f r (r + 1) (Nat.le_succ r)))
    (e : ∀ r, G r ≃* invariantTorsionLevel r)
    {r s : ℕ} (hrs : r ≤ s) (x : G r) :
    strictifiedFactorialEquiv f hf e s (f r s hrs x) =
      invariantTorsionInclusion r s hrs
        (strictifiedFactorialEquiv f hf e r x) := by
  induction s, hrs using Nat.le_induction with
  | base =>
      rw [DirectedSystem.map_self
        (f := fun {_ _} h ↦ f _ _ h)]
      rw [DirectedSystem.map_self
        (f := fun {_ _} h ↦ invariantTorsionInclusion _ _ h)]
  | succ s hrs ih =>
      rw [← DirectedSystem.map_map
        (f := fun {_ _} h ↦ f _ _ h) hrs (Nat.le_succ s) x]
      rw [strictified_factorial_succ, ih]
      exact DirectedSystem.map_map
        (f := fun {_ _} h ↦ invariantTorsionInclusion _ _ h)
        hrs (Nat.le_succ s)
        (strictifiedFactorialEquiv f hf e r x)

/-- A compatible finite invariant system over an arbitrary factorial chain. -/
structure FactorialInvariantSystem where
  equiv : ∀ r, G r ≃* invariantTorsionLevel r
  compatible : ∀ r s h x,
    equiv s (f r s h x) =
      invariantTorsionInclusion r s h (equiv r x)

/-- Arbitrary levelwise cyclic equivalences on a directed factorial chain
with injective successor maps can always be strictified into a compatible
finite invariant system. -/
noncomputable def strictifiedFactorialSystem
    (hf : ∀ r, Function.Injective (f r (r + 1) (Nat.le_succ r)))
    (e : ∀ r, G r ≃* invariantTorsionLevel r) :
    FactorialInvariantSystem f where
  equiv := strictifiedFactorialEquiv f hf e
  compatible := fun _ _ h x ↦
    strict_facto_compa f hf e h x

end GlobalStrictification

end CIStrict

end

end Submission.CField.LBrauer
