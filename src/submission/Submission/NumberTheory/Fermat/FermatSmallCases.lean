import Mathlib.NumberTheory.FLT.Three

/-!
# Milne, Algebraic Number Theory, small exponents in Theorem 6.8

The elementary modulo `9` and modulo `25` exclusions for exponents `3` and `5`.
-/

namespace Submission.NumberTheory.Milne

open ZMod

private lemma zmod_9_cube
    (x y z : ZMod 9)
    (hx : ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) x ≠ 0)
    (hy : ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) y ≠ 0)
    (hz : ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) z ≠ 0) :
    x ^ 3 + y ^ 3 ≠ z ^ 3 := by
  revert x y z
  decide

/-- Milne's modulo `9` argument for the first case at exponent `3`. -/
theorem fermat_first_case {x y z : ℤ} (hcoprime : ¬3 ∣ x * y * z) :
    x ^ 3 + y ^ 3 ≠ z ^ 3 := by
  simp_rw [Int.prime_three.dvd_mul, not_or] at hcoprime
  apply mt (congrArg (Int.cast : ℤ → ZMod 9))
  simp_rw [Int.cast_add, Int.cast_pow]
  apply zmod_9_cube
  all_goals
    rw [map_intCast, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  · exact hcoprime.1.1
  · exact hcoprime.1.2
  · exact hcoprime.2

private lemma zmod_25_fifth
    (x y z : ZMod 25)
    (hx : ZMod.castHom (by norm_num : 5 ∣ 25) (ZMod 5) x ≠ 0)
    (hy : ZMod.castHom (by norm_num : 5 ∣ 25) (ZMod 5) y ≠ 0)
    (hz : ZMod.castHom (by norm_num : 5 ∣ 25) (ZMod 5) z ≠ 0) :
    x ^ 5 + y ^ 5 ≠ z ^ 5 := by
  revert x y z
  decide

/-- Milne's modulo `25` argument for the first case at exponent `5`. -/
theorem fermat_five_case {x y z : ℤ} (hcoprime : ¬5 ∣ x * y * z) :
    x ^ 5 + y ^ 5 ≠ z ^ 5 := by
  have hp5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr Nat.prime_five
  simp_rw [hp5.dvd_mul, not_or] at hcoprime
  apply mt (congrArg (Int.cast : ℤ → ZMod 25))
  simp_rw [Int.cast_add, Int.cast_pow]
  apply zmod_25_fifth
  all_goals
    rw [map_intCast, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  · exact hcoprime.1.1
  · exact hcoprime.1.2
  · exact hcoprime.2

end Submission.NumberTheory.Milne
