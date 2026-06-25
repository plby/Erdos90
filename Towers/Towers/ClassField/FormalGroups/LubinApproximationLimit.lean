import Towers.ClassField.FormalGroups.LubinTateApproximants
import Towers.ClassField.FormalGroups.SubstitutionCongruence

/-!
# Class Field Theory, Chapter I, Lemma 2.11: the coefficientwise limit

The approximants stabilize coefficientwise because the correction at stage
`r` is homogeneous of degree `r+2`.  Their stable diagonal therefore defines
a multivariable power series with the prescribed linear part.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

namespace LTApprox

variable {R σ : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Fintype σ]

variable (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)

/-- The stable diagonal of Milne's successive approximants. -/
def limitSeries (a : σ → R) : MvPowerSeries σ R :=
  fun d ↦ coeff d
    (approximation pi hpi0 hpi hfield f g hf hg a d.degree :
      MvPowerSeries σ R)

@[simp]
theorem coeff_limitSeries (a : σ → R) (d : σ →₀ ℕ) :
    coeff d (limitSeries pi hpi0 hpi hfield f g hf hg a) =
      coeff d
        (approximation pi hpi0 hpi hfield f g hf hg a d.degree :
          MvPowerSeries σ R) := rfl

/-- Every sufficiently late approximant has the same requested coefficient
as the stable diagonal. -/
theorem coeff_limit_approximation
    (a : σ → R) (d : σ →₀ ℕ) {r : ℕ} (hr : d.degree ≤ r) :
    coeff d (limitSeries pi hpi0 hpi hfield f g hf hg a) =
      coeff d
        (approximation pi hpi0 hpi hfield f g hf hg a r :
          MvPowerSeries σ R) := by
  rw [coeff_limitSeries]
  exact (approximation_eq_le
    pi hpi0 hpi hfield f g hf hg a hr d (by omega)).symm

/-- The limit agrees with the prescribed linear form in total degrees zero
and one. -/
theorem coeff_limit_form
    (a : σ → R) (d : σ →₀ ℕ) (hd : d.degree < 2) :
    coeff d (limitSeries pi hpi0 hpi hfield f g hf hg a) =
      coeff d (mvLinearForm a) := by
  rw [coeff_limitSeries]
  have hstable := approximation_eq_le
    pi hpi0 hpi hfield f g hf hg a
    (show 0 ≤ d.degree by omega) d (by omega : d.degree < 0 + 2)
  simpa using hstable

@[simp]
theorem limit_constant_coeff (a : σ → R) :
    constantCoeff (limitSeries pi hpi0 hpi hfield f g hf hg a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_limit_form
      pi hpi0 hpi hfield f g hf hg a 0 (by simp),
    coeff_zero_eq_constantCoeff_apply, mv_constant_coeff]

/-- The limit has exactly the prescribed degree-one homogeneous component. -/
theorem homogeneous_component_limit (a : σ → R) :
    homogeneousComponent 1
        (limitSeries pi hpi0 hpi hfield f g hf hg a) =
      mvLinearForm a := by
  apply MvPowerSeries.ext
  intro d
  rw [coeff_homogeneousComponent]
  split_ifs with hd
  · exact coeff_limit_form
      pi hpi0 hpi hfield f g hf hg a d (by omega)
  · exact (IsHomogeneous.coeff_eq_zero (mv_form_homogeneous a) hd).symm

/-- Stage `r` and the stable diagonal agree in every total degree below
`r+1`. -/
theorem nat_limit_approximation
    (a : σ → R) (r : ℕ) :
    (r + 1 : ℕ) ≤
      (limitSeries pi hpi0 hpi hfield f g hf hg a -
        (approximation pi hpi0 hpi hfield f g hf hg a r :
          MvPowerSeries σ R)).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdegree : d.degree ≤ r := by
    have : d.degree < r + 1 := by exact_mod_cast hd
    omega
  rw [map_sub,
    coeff_limit_approximation
      pi hpi0 hpi hfield f g hf hg a d hdegree,
    sub_self]

/-- Every fixed coefficient of the limiting intertwining error is already
the corresponding coefficient of the approximation at that total degree. -/
theorem limit_error_approximation
    (a : σ → R) (d : σ →₀ ℕ) :
    coeff d
        (lubinIntertwiningError f g
          (limitSeries pi hpi0 hpi hfield f g hf hg a)) =
      coeff d
        (lubinIntertwiningError f g
          (approximation pi hpi0 hpi hfield f g hf hg a d.degree :
            MvPowerSeries σ R)) := by
  let phi := limitSeries pi hpi0 hpi hfield f g hf hg a
  let psi : MvPowerSeries σ R :=
    approximation pi hpi0 hpi hfield f g hf hg a d.degree
  have horder : (d.degree + 1 : ℕ) ≤ (phi - psi).order := by
    simpa [phi, psi] using
      nat_limit_approximation
        pi hpi0 hpi hfield f g hf hg a d.degree
  have hdegree : (d.degree : ℕ∞) < d.degree + 1 := by
    exact_mod_cast Nat.lt_succ_self d.degree
  have hlt : d.degree < (phi - psi).order := hdegree.trans_le horder
  have hleft := coeff_subst_sub
    (limit_constant_coeff pi hpi0 hpi hfield f g hf hg a)
    (approximation_constantCoeff pi hpi0 hpi hfield f g hf hg a d.degree)
    hlt f
  have hright := coeff_coordinatewise_subst
    (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hg.1) hlt
  simpa only [lubinIntertwiningError, map_sub] using
    congrArg₂ (fun x y : R ↦ x - y) hleft hright

/-- If the errors of the approximants acquire arbitrarily high order, the
stable diagonal satisfies the exact intertwining equation. -/
theorem error_approximation_orders
    (a : σ → R)
    (horder : ∀ r : ℕ,
      (r + 1 : ℕ) ≤
        (lubinIntertwiningError f g
          (approximation pi hpi0 hpi hfield f g hf hg a r :
            MvPowerSeries σ R)).order) :
    lubinIntertwiningError f g
        (limitSeries pi hpi0 hpi hfield f g hf hg a) = 0 := by
  apply MvPowerSeries.ext
  intro d
  rw [map_zero,
    limit_error_approximation
      pi hpi0 hpi hfield f g hf hg a d]
  apply coeff_of_lt_order
  refine (show (d.degree : ℕ∞) < d.degree + 1 by
    exact_mod_cast Nat.lt_succ_self d.degree).trans_le ?_
  exact horder d.degree

end LTApprox

end

end Towers.CField.FGroups
