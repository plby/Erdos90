import Towers.ClassField.FormalGroups.LubinDegreeCorrection
import Towers.ClassField.FormalGroups.SubstitutionCongruence

/-!
# Class Field Theory, Chapter I, Lemma 2.11: lower-degree stability

Adding a homogeneous correction of degree `n` does not alter any coefficient
of the Lubin--Tate intertwining error in total degree below `n`.  This is the
filtration half of Milne's perturbation calculation; only the exact
degree-`n` component remains to be computed.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- A homogeneous correction changes no lower coefficient of the
intertwining error. -/
theorem intertwining_error_homogeneous
    [Finite σ] {f g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0)
    {phi Q : MvPowerSeries σ R} (hphi : constantCoeff phi = 0)
    {n : ℕ} (hn : n ≠ 0) (hQ : IsHomogeneous Q n)
    {d : σ →₀ ℕ} (hd : d.degree < n) :
    coeff d (lubinIntertwiningError f g (phi + Q)) =
      coeff d (lubinIntertwiningError f g phi) := by
  have hQ0 : constantCoeff Q = 0 :=
    constant_coeff_homogeneous hQ hn
  have hphiQ : constantCoeff (phi + Q) = 0 := by
    rw [map_add, hphi, hQ0, add_zero]
  have horderQ : (n : ℕ∞) ≤ Q.order :=
    nat_order_homogeneous hQ
  have hdiff : (phi + Q) - phi = Q := by abel
  have hlt : d.degree < ((phi + Q) - phi).order := by
    rw [hdiff]
    exact lt_of_lt_of_le (by exact_mod_cast hd) horderQ
  have hleft := coeff_subst_sub
    hphiQ hphi hlt f
  have hright := coeff_coordinatewise_subst
    hg0 hlt
  simpa only [lubinIntertwiningError, map_sub] using
    congrArg₂ (fun x y : R ↦ x - y) hleft hright

end

end Towers.CField.FGroups
