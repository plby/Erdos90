import Towers.ClassField.FormalGroups.LubinBaseApproximation

/-!
# Coefficientwise stable limits of multivariable power series

Milne's proof of Lemma 2.11 constructs compatible finite-degree
approximations. This file gives the algebraic diagonal limit and the bounded
coefficient substitution lemmas needed to pass its intertwining identity to
the limit.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- Two power series agreeing through total degree `n` have powers agreeing
through total degree `n`. -/
theorem coeff_pow_degree
    {phi psi : MvPowerSeries σ R} {n k : ℕ}
    (hcoeff : ∀ d, d.degree ≤ n → coeff d phi = coeff d psi)
    {d : σ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (phi ^ k) = coeff d (psi ^ k) := by
  let p := phi - psi
  have hp : (n + 1 : ℕ∞) ≤ p.order := by
    apply MvPowerSeries.nat_le_order
    intro e he
    have he' : e.degree ≤ n := by
      apply Nat.lt_succ_iff.mp
      exact_mod_cast he
    simp [p, hcoeff e he']
  have hdp : (d.degree : ℕ∞) < p.order := by
    have hdn : (d.degree : ℕ∞) < (n + 1 : ℕ∞) := by
      exact_mod_cast Nat.lt_succ_of_le hd
    exact lt_of_lt_of_le hdn hp
  cases k with
  | zero => rfl
  | succ k =>
      let s : MvPowerSeries σ R :=
        ∑ i ∈ Finset.range (k + 1), phi ^ i * psi ^ (k + 1 - 1 - i)
      have hps : (d.degree : ℕ∞) < (p * s).order := by
        refine lt_of_lt_of_le hdp ?_
        exact le_trans (self_le_add_right p.order s.order) MvPowerSeries.order_mul_ge
      have hz : coeff d (p * s) = 0 := coeff_of_lt_order hps
      rw [mul_comm, geom_sum₂_mul] at hz
      exact sub_eq_zero.mp (by simpa only [p, map_sub] using hz)

/-- A coefficient of `f(phi)` only depends on coefficients of `phi` through
the same total degree. -/
theorem coeff_subst_degree
    {phi psi : MvPowerSeries σ R}
    (hphi : constantCoeff phi = 0) (hpsi : constantCoeff psi = 0)
    {n : ℕ} (hcoeff : ∀ d, d.degree ≤ n → coeff d phi = coeff d psi)
    (f : PowerSeries R) {d : σ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (PowerSeries.subst phi f) =
      coeff d (PowerSeries.subst psi f) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hphi),
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hpsi)]
  apply finsum_congr
  intro k
  rw [coeff_pow_degree hcoeff hd]

/-- A sequence is coefficientwise stable when every coefficient has reached
its final value by the stage immediately after its total degree. -/
def CoefficientwiseStable (a : ℕ → MvPowerSeries σ R) : Prop :=
  ∀ (d : σ →₀ ℕ) (n : ℕ), d.degree < n →
    coeff d (a n) = coeff d (a (d.degree + 1))

/-- The diagonal limit of a sequence of multivariable power series. -/
def stableLimit (a : ℕ → MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d ↦ coeff d (a (d.degree + 1))

@[simp]
theorem coeff_stableLimit (a : ℕ → MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (stableLimit a) = coeff d (a (d.degree + 1)) := rfl

theorem stable_limit
    {a : ℕ → MvPowerSeries σ R} (ha : CoefficientwiseStable a)
    {d : σ →₀ ℕ} {n : ℕ} (hdn : d.degree < n) :
    coeff d (stableLimit a) = coeff d (a n) :=
  (ha d n hdn).symm

/-- Stable approximants and their diagonal limit agree through every degree
strictly below the stage. -/
theorem coeff_stable_limit
    {a : ℕ → MvPowerSeries σ R} (ha : CoefficientwiseStable a)
    {d : σ →₀ ℕ} {n : ℕ} (hdn : d.degree ≤ n) :
    coeff d (stableLimit a) = coeff d (a (n + 1)) :=
  stable_limit ha (Nat.lt_succ_of_le hdn)

/-- Constant coefficients pass to a stable limit. -/
theorem stable_limit_coeff
    {a : ℕ → MvPowerSeries σ R} (hzero : ∀ n, constantCoeff (a n) = 0) :
    constantCoeff (stableLimit a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_stableLimit]
  simpa only [map_zero, zero_add] using hzero 1

/-- Substitution into a univariate series commutes coefficientwise with the
diagonal stable limit. -/
theorem subst_stable_limit
    {a : ℕ → MvPowerSeries σ R} (ha : CoefficientwiseStable a)
    (hzero : ∀ n, constantCoeff (a n) = 0)
    (f : PowerSeries R) (d : σ →₀ ℕ) :
    coeff d (PowerSeries.subst (stableLimit a) f) =
      coeff d (PowerSeries.subst (a (d.degree + 1)) f) := by
  apply coeff_subst_degree
    (stable_limit_coeff hzero) (hzero (d.degree + 1))
  · intro e he
    exact coeff_stable_limit ha he
  · exact le_rfl

end

end Towers.CField.FGroups
