import Towers.ClassField.FormalGroups.LubinLinearApproximation
import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Class Field Theory, Chapter I, Lemma 2.11: the base approximation

This file proves the degree-one calculation starting Milne's induction.  For
a zero-constant series `phi`, the linear homogeneous component of `f(phi)` is
the linear coefficient of `f` times the linear component of `phi`.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

private theorem coeff_degree_one
    {phi : MvPowerSeries σ R} (hphi : constantCoeff phi = 0)
    {d : σ →₀ ℕ} (hd : d.degree = 1) {n : ℕ} (hn : n ≠ 1) :
    coeff d (phi ^ n) = 0 := by
  classical
  cases n with
  | zero =>
      rw [pow_zero, coeff_one, if_neg]
      intro hzero
      subst d
      simp at hd
  | succ n =>
      have hn0 : n ≠ 0 := by
        intro hnzero
        apply hn
        simp [hnzero]
      apply coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero (n + 1) hphi)
      rw [hd]
      exact_mod_cast (by omega : 1 < n + 1)

/-- The degree-one part of a substituted univariate series. -/
theorem homogeneous_series_subst
    {phi : MvPowerSeries σ R} (hphi : constantCoeff phi = 0)
    (f : PowerSeries R) :
    homogeneousComponent 1 (PowerSeries.subst phi f) =
      PowerSeries.coeff 1 f • homogeneousComponent 1 phi := by
  apply MvPowerSeries.ext
  intro d
  rw [coeff_homogeneousComponent, coeff_smul, coeff_homogeneousComponent]
  by_cases hd : d.degree = 1
  · rw [if_pos hd, if_pos hd, PowerSeries.coeff_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero hphi)]
    rw [finsum_eq_single
      (fun n ↦ PowerSeries.coeff n f • coeff d (phi ^ n)) 1]
    · simp
    · intro n hn
      rw [coeff_degree_one hphi hd hn, smul_zero]
  · simp [hd]

/-- The initial linear form has intertwining error of order at least two.
This is the base case `r = 1` in Milne's proof of Lemma 2.11. -/
theorem form_intertwining_error
    [Fintype σ] {pi : R} {f g : PowerSeries R}
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : PowerSeries.coeff 1 f = pi)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg1 : PowerSeries.coeff 1 g = pi)
    (a : σ → R) :
    2 ≤ (PowerSeries.subst (mvLinearForm a) f -
      MvPowerSeries.subst (coordinatewiseSubst g) (mvLinearForm a)).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hd' : d.degree < 2 := by exact_mod_cast hd
  have hdegree : d.degree = 0 ∨ d.degree = 1 := by omega
  rcases hdegree with hdegree | hdegree
  · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hdegree
    subst d
    simp [PowerSeries.constantCoeff_subst_eq_zero
      (mv_constant_coeff a) f hf0,
      MvPowerSeries.constantCoeff_subst_eq_zero
        (coordinatewise_subst hg0)
        (fun i ↦ coordinatewise_subst_coeff hg0 i)
        (mv_constant_coeff a)]
  · have hleft := congrArg (coeff d)
      (homogeneous_series_subst
        (mv_constant_coeff a) f)
    rw [coeff_homogeneousComponent, if_pos hdegree, coeff_smul,
      coeff_homogeneousComponent, if_pos hdegree, hf1] at hleft
    have hrightComponent :
        homogeneousComponent 1
            (MvPowerSeries.subst (coordinatewiseSubst g) (mvLinearForm a)) =
          pi • homogeneousComponent 1 (mvLinearForm a) := by
      rw [subst_coordinatewise_mv a hg0]
      rw [map_sum, mvLinearForm, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, map_smul]
      rw [homogeneous_series_subst
        (show constantCoeff (MvPowerSeries.X i : MvPowerSeries σ R) = 0 by simp) g,
        hg1, smul_smul]
      simp [smul_smul, mul_comm]
    have hright := congrArg (coeff d) hrightComponent
    rw [coeff_homogeneousComponent, if_pos hdegree, coeff_smul,
      coeff_homogeneousComponent, if_pos hdegree] at hright
    rw [map_sub, hleft, hright, sub_self]

end

end Towers.CField.FGroups
