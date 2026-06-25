import Submission.NumberTheory.Quadratic.Units

/-!
# Milne, Algebraic Number Theory, introduction: units of `Z[sqrt 2]`

This records the introductory example that `1 + sqrt 2` is a unit of infinite order and that
every unit of `Z[sqrt 2]` is, up to sign, an integral power of this unit.
-/

namespace Submission.NumberTheory.Milne

open Submission.NumberTheory

/-- The underlying element of the chosen fundamental unit is `1 + sqrt 2`. -/
@[simp] theorem sqrt_fundamental_val :
    ((SqrtTwo.fundamentalUnit : SqrtTwoˣ) : SqrtTwo) =
      1 + Zsqrtd.sqrtd := by
  ext <;> norm_num [SqrtTwo.fundamentalUnit, Zsqrtd.sqrtd]

/-- The element `1 + sqrt 2` is a unit of `Z[sqrt 2]`. -/
theorem sqrt_sqrtd_unit :
    IsUnit (1 + Zsqrtd.sqrtd : SqrtTwo) := by
  rw [← sqrt_fundamental_val]
  exact SqrtTwo.fundamentalUnit.isUnit

/-- Milne's displayed inverse identity
`(1 + sqrt 2) * (-1 + sqrt 2) = 1`. -/
theorem sqrt_fundamental_inverse :
    (SqrtTwo.fundamentalUnit : SqrtTwo) *
        (-(1 : SqrtTwo) + Zsqrtd.sqrtd) = 1 := by
  ext <;> norm_num [SqrtTwo.fundamentalUnit, Zsqrtd.sqrtd]

/-- The unit `1 + sqrt 2` has infinite multiplicative order. -/
theorem sqrt_fundamental_order :
    orderOf SqrtTwo.fundamentalUnit = 0 := by
  rw [orderOf_eq_zero_iff]
  intro hfinite
  have himage : IsOfFinOrder
      (SqrtTwo.unitReal SqrtTwo.fundamentalUnit) :=
    MonoidHom.isOfFinOrder SqrtTwo.unitReal hfinite
  have hnonnegative :
      0 <= SqrtTwo.unitReal SqrtTwo.fundamentalUnit := by
    rw [SqrtTwo.unit_real_fundamental]
    linarith [Real.sqrt_nonneg (2 : Real)]
  have hunitReal : SqrtTwo.unitReal SqrtTwo.fundamentalUnit = 1 :=
    himage.eq_one hnonnegative
  rw [SqrtTwo.unit_real_fundamental] at hunitReal
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- Equivalently, no nonzero integral power of `1 + sqrt 2` is `1`. -/
theorem sqrt_fundamental_zpow {m : ℤ} (hm : m ≠ 0) :
    SqrtTwo.fundamentalUnit ^ m ≠ 1 := by
  have hinjective : Function.Injective
      (fun n : ℤ => SqrtTwo.fundamentalUnit ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr
      (orderOf_eq_zero_iff.mp sqrt_fundamental_order)
  intro hpow
  apply hm
  exact hinjective (by simpa using hpow)

/-- Every unit of `Z[sqrt 2]` is `+(1 + sqrt 2)^m` or
`-(1 + sqrt 2)^m` for an integer `m`. -/
theorem sqrt_or_neg (u : SqrtTwoˣ) :
    ∃ m : ℤ,
      u = SqrtTwo.fundamentalUnit ^ m ∨
        u = -SqrtTwo.fundamentalUnit ^ m :=
  SqrtTwo.power_or_neg u

end Submission.NumberTheory.Milne
