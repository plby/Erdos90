import Submission.ClassField.FormalGroups.SubstitutionCongruence
import Submission.ClassField.FormalGroups.LubinBaseApproximation


/-!
# Class Field Theory, Chapter I, Lemma 2.11: coordinatewise homogeneous substitution

This file isolates the right-hand substitution calculation in Milne's
homogeneous correction step.  Substitution by a zero-constant unary series
whose linear coefficient is `pi` sends a homogeneous multivariable series of
degree `n` to a series whose degree-`n` part is `pi ^ n` times the original
series.  No terms of smaller total degree are introduced.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

private theorem homogeneous_component_one :
    homogeneousComponent 0 (1 : MvPowerSeries σ R) = 1 := by
  classical
  apply MvPowerSeries.ext
  intro d
  rw [coeff_homogeneousComponent]
  by_cases hd : d = 0
  · subst d
    simp
  · have hdegree : d.degree ≠ 0 := by
      intro h
      exact hd ((Finsupp.degree_eq_zero_iff d).mp h)
    rw [if_neg hdegree, coeff_one, if_neg hd]

private theorem homogeneous_component_x (i : σ) :
    homogeneousComponent 1 (MvPowerSeries.X i : MvPowerSeries σ R) =
      MvPowerSeries.X i := by
  classical
  apply MvPowerSeries.ext
  intro d
  rw [coeff_homogeneousComponent]
  by_cases hd : d = Finsupp.single i 1
  · subst d
    simp
  · have hcoeff : coeff d (MvPowerSeries.X i : MvPowerSeries σ R) = 0 := by
      rw [coeff_X, if_neg hd]
    by_cases hdegree : d.degree = 1
    · rw [if_pos hdegree, hcoeff]
    · rw [if_neg hdegree, hcoeff]

/-- The lowest-degree part of a power of an order-one series is the
corresponding power of its linear homogeneous component. -/
theorem homogeneous_component_order
    {A : MvPowerSeries σ R} (hA : 1 ≤ A.order) (k : ℕ) :
    homogeneousComponent k (A ^ k) = (homogeneousComponent 1 A) ^ k := by
  classical
  have hA0 : constantCoeff A = 0 :=
    one_le_order_iff_constCoeff_eq_zero.mp hA
  induction k with
  | zero =>
      simpa only [pow_zero] using
        (homogeneous_component_one (R := R) (σ := σ))
  | succ k ih =>
      rw [pow_succ, pow_succ]
      rw [homogeneousComponent_mul_of_le_order
        (le_order_pow_of_constantCoeff_eq_zero k hA0) hA]
      rw [ih]

/-- The lowest-degree part of a monomial in order-one series is obtained by
replacing every factor by its linear homogeneous component. -/
theorem homogeneous_component_finsupp
    {a : σ → MvPowerSeries σ R} (ha : ∀ i, 1 ≤ (a i).order)
    (d : σ →₀ ℕ) :
    homogeneousComponent d.degree (d.prod fun i k ↦ (a i) ^ k) =
      d.prod fun i k ↦ (homogeneousComponent 1 (a i)) ^ k := by
  classical
  have aux (s : Finset σ) :
      homogeneousComponent (∑ i ∈ s, d i)
          (∏ i ∈ s, (a i) ^ d i) =
        ∏ i ∈ s, (homogeneousComponent 1 (a i)) ^ d i := by
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty, Finset.prod_empty] using
          (homogeneous_component_one (R := R) (σ := σ))
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
        have hai0 : constantCoeff (a i) = 0 :=
          one_le_order_iff_constCoeff_eq_zero.mp (ha i)
        have hleft : (d i : ℕ∞) ≤ ((a i) ^ d i).order :=
          le_order_pow_of_constantCoeff_eq_zero (d i) hai0
        have hright : ((∑ j ∈ s, d j : ℕ) : ℕ∞) ≤
            (∏ j ∈ s, (a j) ^ d j).order := by
          calc
            ((∑ j ∈ s, d j : ℕ) : ℕ∞) =
                ∑ j ∈ s, (d j : ℕ∞) := by simp
            _ ≤ ∑ j ∈ s, ((a j) ^ d j).order := by
              exact Finset.sum_le_sum fun j _ ↦
                le_order_pow_of_constantCoeff_eq_zero (d j)
                  (one_le_order_iff_constCoeff_eq_zero.mp (ha j))
            _ ≤ (∏ j ∈ s, (a j) ^ d j).order :=
              le_order_prod (fun j ↦ (a j) ^ d j) s
        rw [homogeneousComponent_mul_of_le_order hleft hright,
          homogeneous_component_order (ha i), ih]
  simpa only [Finsupp.prod, Finsupp.degree_apply] using aux d.support

/-- The linear part of coordinatewise substitution by `g` is `pi` times the
corresponding variable when `pi` is the linear coefficient of `g`. -/
theorem homogeneous_coordinatewise_subst
    {g : PowerSeries R} (_hg0 : PowerSeries.constantCoeff g = 0)
    {pi : R} (hg1 : PowerSeries.coeff 1 g = pi) (i : σ) :
    homogeneousComponent 1 (coordinatewiseSubst g i) =
      pi • (MvPowerSeries.X i : MvPowerSeries σ R) := by
  rw [coordinatewiseSubst,
    homogeneous_series_subst (by simp) g, hg1]
  rw [homogeneous_component_x]

/-- Coordinatewise substitution by a zero-constant unary series cannot
create terms below the degree of a homogeneous input. -/
theorem coordinatewise_subst_homogeneous
    [Finite σ] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0)
    {Q : MvPowerSeries σ R} {n : ℕ} (hQ : IsHomogeneous Q n)
    {d : σ →₀ ℕ} (hd : d.degree < n) :
    coeff d (subst (coordinatewiseSubst g) Q) = 0 := by
  apply coeff_of_lt_order
  calc
    (d.degree : ℕ∞) < n := by exact_mod_cast hd
    _ ≤ Q.order := nat_order_homogeneous hQ
    _ ≤ (subst (coordinatewiseSubst g) Q).order := by
      apply order_subst_orders
        (coordinatewise_subst hg0)
      intro i
      exact one_le_order_iff_constCoeff_eq_zero.mpr
        (coordinatewise_subst_coeff hg0 i)

/-- Every homogeneous component strictly below the degree of a homogeneous
input vanishes after coordinatewise zero-constant substitution. -/
theorem homogeneous_component_coordinatewise
    [Finite σ] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0)
    {Q : MvPowerSeries σ R} {n m : ℕ} (hQ : IsHomogeneous Q n)
    (hmn : m < n) :
    homogeneousComponent m (subst (coordinatewiseSubst g) Q) = 0 := by
  ext d
  rw [coeff_homogeneousComponent]
  split_ifs with hd
  · apply coordinatewise_subst_homogeneous hg0 hQ
    simpa [hd] using hmn
  · rfl

/-- The right-hand perturbation calculation in Milne's Lemma 2.11.  If `Q`
is homogeneous of degree `n` and `g(X) = pi X + O(X^2)`, coordinatewise
substitution by `g` multiplies the degree-`n` part of `Q` by `pi ^ n`. -/
theorem component_coordinatewise_subst
    [Finite σ] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0)
    {pi : R} (hg1 : PowerSeries.coeff 1 g = pi)
    {Q : MvPowerSeries σ R} {n : ℕ} (hQ : IsHomogeneous Q n) :
    homogeneousComponent n (subst (coordinatewiseSubst g) Q) =
      pi ^ n • Q := by
  classical
  apply MvPowerSeries.ext
  intro d
  rw [coeff_homogeneousComponent, coeff_smul]
  by_cases hd : d.degree = n
  · rw [if_pos hd]
    have hcoeff :
        coeff d (subst (coordinatewiseSubst g) Q) =
          coeff d
            (subst ((Function.const σ pi) • MvPowerSeries.X) Q) := by
      rw [coeff_subst (coordinatewise_subst hg0),
        coeff_subst (MvPowerSeries.HasSubst.smul_X (Function.const σ pi))]
      apply finsum_congr
      intro e
      by_cases he : e.degree = n
      · have hprod := congrArg (coeff d)
          (homogeneous_component_finsupp
            (a := coordinatewiseSubst g)
            (fun i ↦ one_le_order_iff_constCoeff_eq_zero.mpr
              (coordinatewise_subst_coeff hg0 i)) e)
        rw [coeff_homogeneousComponent, if_pos (hd.trans he.symm)] at hprod
        have hlinear : ∀ i,
            homogeneousComponent 1 (coordinatewiseSubst g i) =
              pi • (MvPowerSeries.X i : MvPowerSeries σ R) :=
          homogeneous_coordinatewise_subst hg0 hg1
        simp_rw [hlinear] at hprod
        simpa only [Pi.smul_apply', Function.const_apply] using
          congrArg (fun x ↦ coeff e Q • x) hprod
      · rw [hQ.coeff_eq_zero he, zero_smul, zero_smul]
    rw [hcoeff, ← MvPowerSeries.rescale_eq_subst]
    have hrescale := MvPowerSeries.rescale_homogeneous_eq_smul
      (r := pi) (f := Q) (n := n) (fun e he ↦ by
        by_contra hdegree
        exact he (hQ.coeff_eq_zero hdegree))
    exact congrArg (coeff d) hrescale
  · rw [if_neg hd, hQ.coeff_eq_zero hd, mul_zero]

end

end Submission.CField.FGroups
