import Towers.ClassField.FormalGroups.LubinTateFiltration

/-!
# Class Field Theory, Chapter I, Section 2: substitution and the degree filtration

Fixed coefficients of a substituted power series depend only on finitely many
coefficients of the inner series.  The order filtration gives a concise form:
agreement through a total degree is preserved by powers and by substitution
into a unary power series.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- Multiplication cannot reveal a coefficient below the order of the left
factor. -/
theorem coeff_order_left
    {A B : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : d.degree < A.order) : coeff d (A * B) = 0 := by
  apply coeff_of_lt_order
  refine h.trans_le ?_
  calc
    A.order = A.order + 0 := (add_zero _).symm
    _ ≤ A.order + B.order := add_le_add le_rfl bot_le
    _ ≤ (A * B).order := le_order_mul

/-- If two series agree through the degree of `d`, so do all of their
powers at coefficient `d`. -/
theorem coeff_order_sub
    {phi psi : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : d.degree < (phi - psi).order) (n : ℕ) :
    coeff d (phi ^ n) = coeff d (psi ^ n) := by
  let S : MvPowerSeries σ R :=
    ∑ i ∈ Finset.range n, phi ^ i * psi ^ (n - 1 - i)
  have hz : coeff d ((phi - psi) * S) = 0 :=
    coeff_order_left h
  rw [mul_comm, geom_sum₂_mul, map_sub] at hz
  exact sub_eq_zero.mp hz

/-- Unary substitution preserves agreement through any fixed total degree. -/
theorem coeff_subst_sub
    {phi psi : MvPowerSeries σ R}
    (hphi : constantCoeff phi = 0) (hpsi : constantCoeff psi = 0)
    {d : σ →₀ ℕ} (h : d.degree < (phi - psi).order)
    (f : PowerSeries R) :
    coeff d (PowerSeries.subst phi f) =
      coeff d (PowerSeries.subst psi f) := by
  rw [PowerSeries.coeff_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero hphi),
    PowerSeries.coeff_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero hpsi)]
  apply finsum_congr
  intro n
  rw [coeff_order_sub h n]

/-- Substitution by series of order at least one cannot decrease total-degree
order. -/
theorem order_subst_orders
    {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (ha1 : ∀ i, 1 ≤ (a i).order)
    (F : MvPowerSeries σ R) :
    F.order ≤ (subst a F).order := by
  have hinf : 1 ≤ ⨅ i, (a i).order := le_iInf fun i ↦ ha1 i
  calc
    F.order = 1 * F.order := (one_mul _).symm
    _ ≤ (⨅ i, (a i).order) * F.order := mul_le_mul_left hinf _
    _ ≤ (subst a F).order := le_order_subst ha F

/-- Multivariable substitution by series of order at least one preserves
agreement through every fixed coefficient. -/
theorem subst_degree_sub
    {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (ha1 : ∀ i, 1 ≤ (a i).order)
    {phi psi : MvPowerSeries σ R} {d : τ →₀ ℕ}
    (h : d.degree < (phi - psi).order) :
    coeff d (subst a phi) = coeff d (subst a psi) := by
  have horder : (phi - psi).order ≤ (subst a (phi - psi)).order :=
    order_subst_orders ha ha1 (phi - psi)
  have hz := coeff_of_lt_order (h.trans_le horder)
  rw [subst_sub ha] at hz
  exact sub_eq_zero.mp hz

/-- Coordinatewise substitution by a zero-constant unary series preserves
agreement through every fixed total degree. -/
theorem coeff_coordinatewise_subst
    [Finite σ] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0)
    {phi psi : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : d.degree < (phi - psi).order) :
    coeff d (subst (coordinatewiseSubst g) phi) =
      coeff d (subst (coordinatewiseSubst g) psi) := by
  apply subst_degree_sub
    (coordinatewise_subst hg0)
  · intro i
    exact one_le_order_iff_constCoeff_eq_zero.mpr
      (coordinatewise_subst_coeff hg0 i)
  · exact h

end

end Towers.CField.FGroups
