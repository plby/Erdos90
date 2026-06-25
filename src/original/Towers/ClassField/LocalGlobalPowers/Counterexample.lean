import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Chapter VIII, Section 1: the eighth-power counterexample

Exercise 1.3 uses `16` to show that the roots-of-unity hypothesis in Theorem
1.1 cannot simply be removed.  The real and rational assertions are recorded
exactly.  The assertion that `16` is an eighth power in every odd `p`-adic
field uses the detailed splitting of the eighth cyclotomic field at odd
primes; that local cyclotomic bridge is not currently packaged.
-/

namespace Towers.CField.LGPowers

/-- The real part of Exercise 1.3: `sqrt 2` is an eighth root of `16`. -/
theorem sixteen_eighth_real :
    ∃ x : ℝ, x ^ 8 = 16 := by
  refine ⟨Real.sqrt 2, ?_⟩
  rw [show 8 = 2 * 4 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The ancient-Greek part of Exercise 1.3: `16` is not an eighth power in
the rational numbers. -/
theorem sixteen_eighth_rational :
    ¬∃ x : ℚ, x ^ 8 = 16 := by
  rintro ⟨x, hx⟩
  have hfourSq : (x ^ 4) ^ 2 = (4 : ℚ) ^ 2 := by
    rw [← pow_mul, hx]
    norm_num
  have hfour : x ^ 4 = (4 : ℚ) := by
    rcases eq_or_eq_neg_of_sq_eq_sq (x ^ 4) (4 : ℚ) hfourSq with h | h
    · exact h
    · have hnonneg : (0 : ℚ) ≤ x ^ 4 := by positivity
      linarith
  have htwoSq : (x ^ 2) ^ 2 = (2 : ℚ) ^ 2 := by
    rw [← pow_mul, hfour]
    norm_num
  have htwo : x ^ 2 = (2 : ℚ) := by
    rcases eq_or_eq_neg_of_sq_eq_sq (x ^ 2) (2 : ℚ) htwoSq with h | h
    · exact h
    · have hnonneg : (0 : ℚ) ≤ x ^ 2 := sq_nonneg x
      linarith
  have hsquare : IsSquare (2 : ℚ) := ⟨x, by simpa [pow_two] using htwo.symm⟩
  have hnot : ¬IsSquare (2 : ℚ) := by
    change ¬IsSquare ((2 : ℕ) : ℚ)
    rw [Rat.isSquare_natCast_iff]
    rintro ⟨y, hy⟩
    have hyunit : IsUnit y := by
      have hprime : Nat.Prime 2 := Nat.prime_two
      apply hprime.squarefree y
      refine ⟨1, ?_⟩
      simp [hy]
    have hyone : y = 1 := Nat.isUnit_iff.mp hyunit
    subst y
    norm_num at hy
  exact hnot hsquare

end Towers.CField.LGPowers
