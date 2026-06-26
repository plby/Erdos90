import Towers.ClassField.FormalGroups.LubinDegreeCorrection

/-!
# Class Field Theory, Chapter I, Lemma 2.11: exact intertwiners

This file records the three properties of Milne's unique intertwining series:
zero constant term, prescribed linear part, and the exact intertwining
equation.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- A solution of Milne's intertwining equation with prescribed linear
coefficient vector. -/
def LIntert [Fintype σ]
    (f g : PowerSeries R) (a : σ → R)
    (phi : MvPowerSeries σ R) : Prop :=
  constantCoeff phi = 0 ∧
    homogeneousComponent 1 phi = mvLinearForm a ∧
    lubinIntertwiningError f g phi = 0

namespace LIntert

variable [Fintype σ]
    {f g : PowerSeries R} {a : σ → R}
    {phi : MvPowerSeries σ R}

theorem constant_coeff_zero
    (h : LIntert f g a phi) : constantCoeff phi = 0 :=
  h.1

theorem homogeneousComponent_one
    (h : LIntert f g a phi) :
    homogeneousComponent 1 phi = mvLinearForm a :=
  h.2.1

theorem error_eq_zero
    (h : LIntert f g a phi) :
    lubinIntertwiningError f g phi = 0 :=
  h.2.2

end LIntert

end

end Towers.CField.FGroups
