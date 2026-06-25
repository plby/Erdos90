import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Milne, Algebraic Number Theory, cyclotomic polynomial examples

The small explicit polynomials displayed before Proposition 6.2.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

theorem cyclotomic_three_int :
    cyclotomic 3 ℤ = X ^ 2 + X + 1 :=
  cyclotomic_three ℤ

theorem cyclotomic_four_int :
    cyclotomic 4 ℤ = X ^ 2 + 1 := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1) Nat.prime_two
  norm_num [Finset.sum_range_succ] at h ⊢
  simpa [add_comm] using h

theorem cyclotomic_six_int :
    cyclotomic 6 ℤ = X ^ 2 - X + 1 :=
  cyclotomic_six ℤ

theorem cyclotomic_twelve_int :
    cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 := by
  have h := cyclotomic_expand_eq_cyclotomic Nat.prime_two
    (by norm_num : 2 ∣ 6) ℤ
  rw [cyclotomic_six] at h
  rw [← h, expand_eq_comp_X_pow]
  simp only [add_comp, sub_comp, pow_comp, X_comp, one_comp]
  ring

/-- The explicit factorization of `X^12 - 1` displayed after the small
cyclotomic-polynomial examples. -/
theorem x_twelve_factorization :
    (X : ℤ[X]) ^ 12 - 1 =
      (X - 1) * (X + 1) * (X ^ 2 + X + 1) * (X ^ 2 + 1) *
        (X ^ 2 - X + 1) * (X ^ 4 - X ^ 2 + 1) := by
  ring

end Towers.NumberTheory.Milne
