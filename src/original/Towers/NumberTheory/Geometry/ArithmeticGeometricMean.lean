import Mathlib.Analysis.MeanInequalities

/-!
# Milne, Algebraic Number Theory, Lemma 4.25

The finite arithmetic-geometric mean inequality, in both forms used by Milne.
-/

namespace Towers.NumberTheory.Milne

open scoped BigOperators

/-- **Milne, Lemma 4.25.** The geometric mean of a nonempty finite family of
positive real numbers is at most its arithmetic mean. -/
theorem geometric_mean_arithmetic {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    (∏ i, a i) ^ ((n : ℝ)⁻¹) ≤ (∑ i, a i) / n := by
  simpa [hn.ne', ha] using
    (Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin n ↦ (1 : ℝ)) a
      (fun _ _ ↦ zero_le_one)
      (by simpa using (Nat.cast_pos.mpr hn : 0 < (n : ℝ)))
      (fun i _ ↦ (ha i).le))

/-- The power form of Milne's arithmetic-geometric mean inequality. -/
theorem product_average_pow {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    ∏ i, a i ≤ ((∑ i, a i) / n) ^ n := by
  have h := geometric_mean_arithmetic hn a ha
  have hprod : 0 ≤ ∏ i, a i := Finset.prod_nonneg fun i _ ↦ (ha i).le
  have hroot : 0 ≤ (∏ i, a i) ^ ((n : ℝ)⁻¹) := Real.rpow_nonneg hprod _
  have hp := pow_le_pow_left₀ hroot h n
  rwa [Real.rpow_inv_natCast_pow hprod hn.ne'] at hp

/-- Milne's division-free presentation of the power form. -/
theorem product_card_sum {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    (∏ i, a i) * (n : ℝ) ^ n ≤ (∑ i, a i) ^ n := by
  have h := product_average_pow hn a ha
  rw [div_pow] at h
  simpa [mul_comm] using (le_div_iff₀' (by positivity : 0 < (n : ℝ) ^ n)).mp h

end Towers.NumberTheory.Milne
