import Towers.ClassField.LocalBrauer.DivisionAlgebraOrder
import Towers.ClassField.LocalBrauer.DivisionAlgebraIntegers

/-!
# Chapter IV, Section 4: order and integers in a local division algebra

This file identifies the valuation-theoretic definitions of the integer ring
and its maximal ideal with the corresponding inequalities for the rational
order on the division algebra.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [Module.Finite K D]

/-- An element of a local division algebra is integral exactly when its
additive order is nonnegative. -/
theorem integer_subring_nonneg (x : D) :
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : Valuation.RankOne
        (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
      change Valuation.RankOne (valuation K)
      infer_instance
    letI : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
    x ∈ divisionIntegerSubring K D ↔
      0 ≤ divisionAlgebraOrder K (D := D) x := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valuation.RankOne
      (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
    change Valuation.RankOne (valuation K)
    infer_instance
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  rw [division_subring, division_algebra_absolute]
  by_cases hx : x = 0
  · subst x
    simp
  rw [division_ne_zero K (D := D) x hx]
  have h := division_algebra_magnitude K D
    (0 : Additive Dˣ) (Additive.ofMul (Units.mk0 x hx))
  have hone : localRegularMagnitude K D 1 = 1 := by
    change regularValueCandidate K D 1 = 1
    exact regular_value_candidate K D
  change
    localRegularMagnitude K D x ≤ 1 ↔
      (0 : WithTop ℚ) ≤
        (divisionUnitOrder K D
          (Additive.ofMul (Units.mk0 x hx)) : WithTop ℚ)
  rw [WithTop.coe_nonneg]
  rw [← hone]
  simpa using h.symm

/-- An integer of a local division algebra lies in the maximal ideal exactly
when its additive order is positive. -/
theorem division_maximal_pos :
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : Valuation.RankOne
        (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
      change Valuation.RankOne (valuation K)
      infer_instance
    letI : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
    ∀ x : divisionIntegerSubring K D,
      x ∈ divisionMaximalIdeal K D ↔
        0 < divisionAlgebraOrder K (D := D) (x : D) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valuation.RankOne
      (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
    change Valuation.RankOne (valuation K)
    infer_instance
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  intro x
  rw [division_maximal, division_algebra_absolute]
  by_cases hx : (x : D) = 0
  · have hx' : x = 0 := Subtype.ext hx
    subst x
    simp
  rw [division_ne_zero K (D := D) (x : D) hx]
  change
    regularValueCandidate K D (x : D) < 1 ↔
      (0 : WithTop ℚ) <
        (divisionUnitOrder K D
          (Additive.ofMul (Units.mk0 (x : D) hx)) : WithTop ℚ)
  rw [WithTop.coe_pos]
  have h := division_algebra_magnitude K D
    (Additive.ofMul (Units.mk0 (x : D) hx)) (0 : Additive Dˣ)
  have hone : localRegularMagnitude K D 1 = 1 := by
    change regularValueCandidate K D 1 = 1
    exact regular_value_candidate K D
  change
    localRegularMagnitude K D (x : D) < 1 ↔
      0 < divisionUnitOrder K D
        (Additive.ofMul (Units.mk0 (x : D) hx))
  rw [← hone]
  rw [lt_iff_not_ge, lt_iff_not_ge]
  simpa using (not_congr h).symm

/-- On the embedded base field, the division-algebra integer ring restricts
to the usual nonnegative normalized integer order. -/
theorem division_subring_nonneg :
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : Valuation.RankOne
        (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
      change Valuation.RankOne (valuation K)
      infer_instance
    letI : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
    ∀ x : Kˣ,
      algebraMap K D (x : K) ∈ divisionIntegerSubring K D ↔
        0 ≤ localUnitOrder K (Additive.ofMul x) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valuation.RankOne
      (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
    change Valuation.RankOne (valuation K)
    infer_instance
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  intro x
  rw [integer_subring_nonneg K D]
  have hx : algebraMap K D (x : K) ≠ 0 :=
    (map_ne_zero (algebraMap K D)).2 x.ne_zero
  rw [division_ne_zero K (D := D) _ hx]
  have hunit :
      Units.mk0 (algebraMap K D (x : K)) hx =
        Units.map (algebraMap K D).toMonoidHom x := by
    apply Units.ext
    rfl
  rw [hunit]
  have horder :=
    division_algebra_order K D (Additive.ofMul x)
  change
    divisionUnitOrder K D
        (Additive.ofMul (Units.map (algebraMap K D).toMonoidHom x)) =
      (localUnitOrder K (Additive.ofMul x) : ℚ) at horder
  rw [horder]
  rw [WithTop.coe_nonneg]
  exact_mod_cast Iff.rfl

end

end Towers.CField.LBrauer
