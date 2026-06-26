import Submission.NumberTheory.Quadratic.QuadraticUnitExamples
import Submission.ClassField.RayClassGroups.RationalQuotient
import Submission.ClassField.Examples.SqrtSix

/-!
# Chapter V, Section 1, Example 1.8

This file records the elementary parts of the examples: the rational ray
quotient with the infinite prime included, and the displayed norm signs of
the fundamental units in the four real quadratic examples.
-/

namespace Submission.CField.RCGroups

open Submission.NumberTheory.Milne
open Submission.CField.Examples

/-- The elementary model of the ray class group of `Q` for the modulus
`infinity * (m)`. -/
abbrev RationalRayInfinity (m : ℕ) :=
  PositiveCoprimeFraction m ⧸ (positiveCoprimeHom m).ker

/-- Example 1.8(c): for `m > 0`, the rational ray class group modulo
`infinity * (m)` is the group of units modulo `m`. -/
noncomputable def rationalRayInfinity {m : ℕ} (hm : 0 < m) :
    RationalRayInfinity m ≃* (ZMod m)ˣ :=
  coprimeFractionEquiv hm

/-- The displayed fundamental unit `1 + sqrt(2)` has norm `-1`. -/
theorem displayed_unit_norm :
    Zsqrtd.norm (⟨1, 1⟩ : ℤ√(2)) = -1 := by
  norm_num [Zsqrtd.norm_def]

/-- The displayed element `1 + sqrt(2)` is a unit. -/
theorem sqrt_two_displayed : IsUnit (⟨1, 1⟩ : ℤ√(2)) := by
  rw [zsqrtd_pell_equation]
  norm_num

/-- The displayed fundamental unit `2 + sqrt(3)` has norm `1`. -/
theorem sqrt_displayed_norm :
    Zsqrtd.norm (⟨2, 1⟩ : ℤ√(3)) = 1 := by
  norm_num [Zsqrtd.norm_def]

/-- The displayed element `2 + sqrt(3)` is a unit. -/
theorem sqrt_displayed_unit : IsUnit (⟨2, 1⟩ : ℤ√(3)) := by
  rw [zsqrtd_pell_equation]
  norm_num

/-- In the integral basis `1, (1 + sqrt(5))/2`, the displayed fundamental
unit has norm `-1`. -/
theorem five_displayed_norm :
    QuadraticAlgebra.norm (⟨0, 1⟩ : QuadraticAlgebra ℤ 1 1) = -1 := by
  norm_num [QuadraticAlgebra.norm_def]

/-- The displayed element `(1 + sqrt(5))/2` is a unit of its quadratic order. -/
theorem sqrt_five_displayed :
    IsUnit (⟨0, 1⟩ : QuadraticAlgebra ℤ 1 1) := by
  rw [half_pell_equation]
  norm_num

/-- The displayed fundamental unit `5 + 2 sqrt(6)` has norm `1`. -/
theorem sqrt_six_displayed :
    QuadraticAlgebra.norm (⟨5, 2⟩ : SqrtSixIntegers) = 1 :=
  six_fundamental_norm

/-- No unit of `Z[sqrt(6)]` has norm `-1`. -/
theorem sqrt_six_no (u : SqrtSixIntegers) :
    QuadraticAlgebra.norm u ≠ -1 :=
  sqrt_six_ne u

end Submission.CField.RCGroups
