import Towers.ClassField.FormalGroups.LubinIntertwinerExistence
import Towers.ClassField.FormalGroups.LubinIntertwinerUniqueness

/-!
# Class Field Theory, Chapter I, Lemma 2.11

For two Lubin--Tate series and a prescribed linear form, there is a unique
multivariable power series with zero constant term that intertwines them.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Fintype σ]

/-- Milne's Lemma 2.11: existence and uniqueness of the power series with
prescribed linear part satisfying `f (phi) = phi (g, ..., g)`. -/
theorem unique_lubin_intertwiner
    {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    {f g : PowerSeries R}
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : σ → R) :
    ∃! phi : MvPowerSeries σ R, LIntert f g a phi := by
  let phi := LTApprox.limitSeries
    pi hpi0 hpi hfield f g hf hg a
  have hphi : LIntert f g a phi :=
    LTApprox.lubin_intertwiner_limit
      pi hpi0 hpi hfield f g hf hg a
  refine ⟨phi, hphi, ?_⟩
  intro psi hpsi
  apply tate_intertwining_error
    hpi0 hpi hf.2.1
    (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hg.1)
    hg.2.1
    hpsi.constant_coeff_zero hphi.constant_coeff_zero
  · rw [hpsi.homogeneousComponent_one, hphi.homogeneousComponent_one]
  · exact hpsi.error_eq_zero
  · exact hphi.error_eq_zero

end

end Towers.CField.FGroups
