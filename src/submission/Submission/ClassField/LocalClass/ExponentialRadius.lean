import Submission.NumberTheory.Locals.LocalFieldClassification
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Positive convergence radius for the local exponential

This supplies the analytic input in the characteristic-zero proof of Milne's
Lemma III.2.4.  The restriction of the local norm to `ℚ` is equivalent to
a `p`-adic norm.  Legendre's bound on the valuation of `n!` then gives a
uniform geometric bound for the coefficients of the exponential series.
-/

namespace Submission.CField.LClass

open Submission.NumberTheory.Milne
open scoped ENNReal NNReal NormedField

noncomputable section

/-- In a characteristic-zero nonarchimedean local field, the exponential
power series has a genuinely positive convergence radius. -/
theorem exp_radius_pos
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] [CompleteSpace K] [CharZero K] :
    0 < (NormedSpace.expSeries K K).radius := by
  obtain ⟨p, ⟨hp, hequiv⟩, _hunique⟩ :=
    local_restriction_padic K
  letI : Fact p.Prime := hp
  let v : AbsoluteValue ℚ ℝ :=
    (NormedField.toAbsoluteValue K).comp (algebraMap ℚ K).injective
  let w : AbsoluteValue ℚ ℝ := Rat.AbsoluteValue.padic p
  let pK : K := algebraMap ℚ K p
  have hpK0 : pK ≠ 0 := by
    exact (map_ne_zero (algebraMap ℚ K)).2 (by exact_mod_cast hp.out.ne_zero)
  let r : ℝ≥0 := nnnorm pK
  have hr0 : r ≠ 0 := by
    simpa [r, pK] using hpK0
  have hbound (n : ℕ) :
      ‖NormedSpace.expSeries K K n‖ * (r : ℝ) ^ n ≤ 1 := by
    have hfac0 : (n.factorial : ℚ) ≠ 0 := by
      exact_mod_cast n.factorial_ne_zero
    let qfac : ℚ := (n.factorial : ℚ)⁻¹
    let qp : ℚ := ((p : ℚ)⁻¹) ^ n
    have hpadic : w qfac ≤ w qp := by
      dsimp [qfac, qp]
      rw [map_pow, map_inv₀, map_inv₀]
      change ((padicNorm p (n.factorial : ℚ))⁻¹ : ℝ) ≤
        ((padicNorm p (p : ℚ))⁻¹ : ℝ) ^ n
      norm_cast
      rw [padicNorm.eq_zpow_of_nonzero hfac0,
        padicValRat.of_nat]
      rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hp.out.ne_zero),
        padicValRat.of_nat, padicValNat_self]
      simp only [inv_pow, zpow_neg, zpow_natCast]
      rw [inv_inv, inv_inv, pow_one]
      exact pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le)
        (padicValNat_factorial_le p n)
    have hnorm : v qfac ≤ v qp := (hequiv qfac qp).2 hpadic
    have hcoeff : ‖(n.factorial⁻¹ : K)‖ ≤ ‖pK⁻¹‖ ^ n := by
      change ‖algebraMap ℚ K qfac‖ ≤ ‖algebraMap ℚ K qp‖ at hnorm
      simpa [v, qfac, qp, pK, map_inv₀, map_pow] using hnorm
    rw [NormedSpace.expSeries_eq_ofScalars,
      FormalMultilinearSeries.ofScalars_norm]
    calc
      ‖(n.factorial⁻¹ : K)‖ * (r : ℝ) ^ n ≤
          ‖pK⁻¹‖ ^ n * ‖pK‖ ^ n :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (norm_nonneg _) n)
      _ = 1 := by
        rw [← mul_pow, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hpK0), one_pow]
  have hradius : (r : ℝ≥0∞) ≤ (NormedSpace.expSeries K K).radius :=
    (NormedSpace.expSeries K K).le_radius_of_bound 1 hbound
  exact (ENNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hr0)).trans_le hradius

end

end Submission.CField.LClass
