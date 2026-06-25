import Submission.ClassField.FormalGroups.CoordinatewisePerturbation


/-!
# Class Field Theory, Chapter I, Lemma 2.11: unary perturbation

This file proves the left-hand calculation in Milne's homogeneous correction
step.  If `Q` is homogeneous of degree `n >= 2`, then replacing `phi` by
`phi + Q` in a unary series changes its degree-`n` component only through the
linear coefficient of that unary series.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- If two zero-constant series first differ in degree at least `r`, then the
difference of their `m`th powers starts in degree at least `r + m - 1`. -/
private theorem nat_pred_sub
    {A B : MvPowerSeries σ R}
    (hA0 : constantCoeff A = 0) (hB0 : constantCoeff B = 0)
    {r m : ℕ} (_hm : m ≠ 0)
    (hdiff : (r : ℕ∞) ≤ (A - B).order) :
    (r + (m - 1) : ℕ) ≤ (A ^ m - B ^ m).order := by
  let S : MvPowerSeries σ R :=
    ∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i)
  have hterm : ∀ i ∈ Finset.range m,
      ((m - 1 : ℕ) : ℕ∞) ≤ (A ^ i * B ^ (m - 1 - i)).order := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hAi : (i : ℕ∞) ≤ (A ^ i).order :=
      le_order_pow_of_constantCoeff_eq_zero i hA0
    have hBi : ((m - 1 - i : ℕ) : ℕ∞) ≤ (B ^ (m - 1 - i)).order :=
      le_order_pow_of_constantCoeff_eq_zero (m - 1 - i) hB0
    have hmul := nat_order_mul hAi hBi
    have hsum : i + (m - 1 - i) = m - 1 := by omega
    simpa only [hsum] using hmul
  have hS : ((m - 1 : ℕ) : ℕ∞) ≤ S.order :=
    nat_finset_sum hterm
  have hprod : ((r + (m - 1) : ℕ) : ℕ∞) ≤ ((A - B) * S).order :=
    nat_order_mul hdiff hS
  rw [mul_comm, geom_sum₂_mul] at hprod
  exact hprod

/-- The degree-`n` part of `f(phi + Q) - f(phi)` is the linear coefficient
of `f` times `Q`. -/
theorem homogeneous_component_sub
    {f : PowerSeries R} {phi Q : MvPowerSeries σ R}
    (hphi : constantCoeff phi = 0)
    {n : ℕ} (hn : 2 ≤ n) (hQ : IsHomogeneous Q n) :
    homogeneousComponent n
        (PowerSeries.subst (phi + Q) f - PowerSeries.subst phi f) =
      PowerSeries.coeff 1 f • Q := by
  have hQ0 : constantCoeff Q = 0 :=
    constant_coeff_homogeneous hQ (by omega)
  have hphiQ : constantCoeff (phi + Q) = 0 := by
    rw [map_add, hphi, hQ0, add_zero]
  have hdiff : (n : ℕ∞) ≤ ((phi + Q) - phi).order := by
    have horderQ := nat_order_homogeneous hQ
    simpa only [add_sub_cancel_left] using horderQ
  apply MvPowerSeries.ext
  intro d
  rw [coeff_homogeneousComponent, coeff_smul]
  by_cases hd : d.degree = n
  · let hphiQSubst : PowerSeries.HasSubst (phi + Q) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hphiQ
    let hphiSubst : PowerSeries.HasSubst phi :=
      PowerSeries.HasSubst.of_constantCoeff_zero hphi
    have hfinQ := PowerSeries.coeff_subst_finite hphiQSubst f d
    have hfin := PowerSeries.coeff_subst_finite hphiSubst f d
    rw [if_pos hd, map_sub,
      PowerSeries.coeff_subst hphiQSubst,
      PowerSeries.coeff_subst hphiSubst,
      ← finsum_sub_distrib hfinQ hfin]
    rw [finsum_eq_single _ 1]
    · simp only [pow_one, map_add, smul_eq_mul]
      ring
    · intro m hm
      by_cases hm0 : m = 0
      · subst m
        simp
      have hm2 : 2 ≤ m := by omega
      have horder := nat_pred_sub
        hphiQ hphi hm0 hdiff
      have hlt : d.degree < ((phi + Q) ^ m - phi ^ m).order := by
        rw [hd]
        refine lt_of_lt_of_le ?_ horder
        exact_mod_cast (show n < n + (m - 1) by omega)
      have hcoeff := coeff_of_lt_order hlt
      have hpows : coeff d ((phi + Q) ^ m) = coeff d (phi ^ m) := by
        simpa only [map_sub, sub_eq_zero] using hcoeff
      rw [hpows, sub_self]
  · rw [if_neg hd, hQ.coeff_eq_zero hd, mul_zero]

end

end Submission.CField.FGroups
