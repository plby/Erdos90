import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Class Field Theory, Introduction: the cyclotomic hint for Exercise 0.15

Inside the twentieth cyclotomic field, a twentieth root of unity simultaneously
provides a square root of `-1` and, through its fourth power, a square root of
`5`.  Their product is therefore a square root of `-5`.
-/

namespace Towers.CField.Examples

open IsCyclotomicExtension

/-- The canonical cyclotomic field used in the hint to Exercise 0.15. -/
abbrev CycloTwenty := _root_.CyclotomicField 20 ℚ

noncomputable section

local instance : IsCyclotomicExtension {20} ℚ CycloTwenty :=
  _root_.CyclotomicField.isCyclotomicExtension 20 ℚ

/-- Our chosen primitive twentieth root of unity. -/
def zeta : CycloTwenty :=
  IsCyclotomicExtension.zeta 20 ℚ CycloTwenty

/-- The fourth root of unity obtained from the twentieth root. -/
def cyclotomic : CycloTwenty := zeta ^ 5

/-- A primitive fifth root of unity obtained from the twentieth root. -/
def fifthRoot : CycloTwenty := zeta ^ 4

/-- The standard cyclotomic expression for a square root of five. -/
def sqrtFive : CycloTwenty :=
  1 + 2 * (fifthRoot + fifthRoot ^ 4)

/-- The product of the cyclotomic square roots of `-1` and `5`. -/
def sqrtNegFive : CycloTwenty :=
  cyclotomic * sqrtFive

private theorem primitive_root_factor {R : Type*} [CommRing R] [IsDomain R]
    {z : R} {m d : ℕ} (hm : 0 < m) (hz : IsPrimitiveRoot z (m * d)) :
    IsPrimitiveRoot (z ^ m) d := by
  constructor
  · rw [← pow_mul]
    exact hz.pow_eq_one
  · intro l hl
    apply (Nat.mul_dvd_mul_iff_left hm).mp
    apply hz.dvd_of_pow_eq_one
    simpa [pow_mul] using hl

theorem i_primitive_root : IsPrimitiveRoot cyclotomic 4 := by
  apply primitive_root_factor (m := 5) (d := 4) (by norm_num)
  exact zeta_spec 20 ℚ CycloTwenty

theorem fifth_root_primitive :
    IsPrimitiveRoot fifthRoot 5 := by
  apply primitive_root_factor (m := 4) (d := 5) (by norm_num)
  exact zeta_spec 20 ℚ CycloTwenty

theorem i_sq : cyclotomic ^ 2 = -1 := by
  apply IsPrimitiveRoot.eq_neg_one_of_two_right
  apply primitive_root_factor (m := 2) (d := 2) (by norm_num)
  simpa [pow_two] using i_primitive_root

theorem sqrtFive_sq : sqrtFive ^ 2 = 5 := by
  let u := fifthRoot
  have hu : IsPrimitiveRoot u 5 := fifth_root_primitive
  have hu5 : u ^ 5 = 1 := hu.pow_eq_one
  have hu8 : u ^ 8 = u ^ 3 := by
    calc
      u ^ 8 = u ^ 5 * u ^ 3 := by ring
      _ = u ^ 3 := by rw [hu5, one_mul]
  have hsum := hu.geom_sum_eq_zero (by norm_num : 1 < 5)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    zero_add] at hsum
  change (1 + 2 * (u + u ^ 4)) ^ 2 = 5
  rw [show (1 + 2 * (u + u ^ 4)) ^ 2 =
      9 + 4 * (u + u ^ 2 + u ^ 3 + u ^ 4) by
        rw [pow_two]
        ring_nf
        rw [hu5, hu8]
        ring]
  linear_combination 4 * hsum

theorem neg_five_sq : sqrtNegFive ^ 2 = -5 := by
  rw [sqrtNegFive, mul_pow, i_sq, sqrtFive_sq]
  norm_num

end

end Towers.CField.Examples
