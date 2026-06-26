import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Coefficientwise continuity of p-adic binomial series

Auxiliary continuity facts for Milne's Example 2.18.
-/

namespace Towers.CField.FGroups

noncomputable section

open scoped PowerSeries.WithPiTopology

variable (p : ℕ) [Fact p.Prime]

/-- The p-adic binomial series varies continuously in the coefficientwise
topology on power series. -/
theorem continuous_binomial_series :
    Continuous (fun a : ℤ_[p] ↦ PowerSeries.binomialSeries ℤ_[p] a) := by
  apply continuous_pi
  intro d
  simpa only [PowerSeries.binomialSeries, PowerSeries.coeff_mk,
    smul_eq_mul, mul_one] using
    PadicInt.continuous_choose (p := p) (d ())

/-- Substitution into a fixed zero-constant power series preserves
coefficientwise continuity of a family of outer power series. At each fixed
degree, only finitely many coefficients of the outer series contribute. -/
theorem continuous_subst_family
    (f : PowerSeries ℤ_[p]) (hf0 : PowerSeries.constantCoeff f = 0)
    (h : ℤ_[p] → PowerSeries ℤ_[p])
    (hh : ∀ d : ℕ, Continuous (fun a ↦ PowerSeries.coeff d (h a)))
    (e : ℕ) :
    Continuous (fun a ↦ PowerSeries.coeff e (PowerSeries.subst f (h a))) := by
  have hformula : (fun a : ℤ_[p] ↦
      PowerSeries.coeff e (PowerSeries.subst f (h a))) =
      fun a ↦ ∑ d ∈ Finset.range (e + 1),
        PowerSeries.coeff d (h a) * PowerSeries.coeff e (f ^ d) := by
    funext a
    rw [PowerSeries.coeff_subst'
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf0)]
    rw [finsum_eq_sum_of_support_subset
      (s := Finset.range (e + 1))]
    · simp only [smul_eq_mul]
    · intro d hd
      simp only [Function.mem_support] at hd
      have hdlt : d < e + 1 := by
        by_contra hde
        have hed : e < d := by omega
        have hed' : (e : ℕ∞) < (d : ℕ∞) :=
          ENat.coe_lt_coe.mpr hed
        have horder : (e : ℕ∞) < (f ^ d).order :=
          hed'.trans_le
            (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hf0)
        have hz : PowerSeries.coeff e (f ^ d) = 0 :=
          PowerSeries.coeff_of_lt_order e horder
        simp [hz] at hd
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hdlt)
  rw [hformula]
  exact continuous_finsetSum _ fun d _ ↦ (hh d).mul continuous_const

end

end Towers.CField.FGroups
