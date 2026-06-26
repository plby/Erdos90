import Submission.ClassField.FormalGroups.UnaryPerturbation
import Submission.ClassField.FormalGroups.HomogeneousSubstitution
import Submission.ClassField.FormalGroups.LubinPerturbationLower

/-!
# Class Field Theory, Chapter I, Lemma 2.11: the correction step

This file assembles the two homogeneous perturbation calculations in Milne's
proof.  Adding a degree-`n` homogeneous series `Q` changes the degree-`n`
intertwining error by `(pi - pi^n) Q`.  Consequently the correction selected
by dividing the old error by `pi^n - pi` raises the error order by one.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- Milne's exact degree-`n` perturbation formula. -/
theorem homogeneous_intertwining_error
    [Finite σ] {pi : R} {f g : PowerSeries R}
    (hf1 : PowerSeries.coeff 1 f = pi)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg1 : PowerSeries.coeff 1 g = pi)
    {phi Q : MvPowerSeries σ R} (hphi : constantCoeff phi = 0)
    {n : ℕ} (hn : 2 ≤ n) (hQ : IsHomogeneous Q n) :
    homogeneousComponent n (lubinIntertwiningError f g (phi + Q)) =
      homogeneousComponent n (lubinIntertwiningError f g phi) +
        (pi - pi ^ n) • Q := by
  have hleft := homogeneous_component_sub
    (f := f) hphi hn hQ
  rw [hf1] at hleft
  have hright := component_coordinatewise_subst
    hg0 hg1 hQ
  have herr :
      lubinIntertwiningError f g (phi + Q) =
        lubinIntertwiningError f g phi +
          (PowerSeries.subst (phi + Q) f - PowerSeries.subst phi f) -
          subst (coordinatewiseSubst g) Q := by
    rw [lubinIntertwiningError, lubinIntertwiningError]
    rw [subst_add (coordinatewise_subst hg0)]
    abel
  rw [herr, map_sub, map_add, hleft, hright, sub_smul]
  abel

/-- A homogeneous correction satisfying Milne's correction equation raises
the order of the intertwining error from at least `n` to at least `n+1`. -/
theorem lubin_intertwining_error
    [Finite σ] {pi : R} {f g : PowerSeries R}
    (hf1 : PowerSeries.coeff 1 f = pi)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg1 : PowerSeries.coeff 1 g = pi)
    {phi Q : MvPowerSeries σ R} (hphi : constantCoeff phi = 0)
    {n : ℕ} (hn : 2 ≤ n) (hQ : IsHomogeneous Q n)
    (horder : (n : ℕ∞) ≤ (lubinIntertwiningError f g phi).order)
    (hcorrect : (pi ^ n - pi) • Q =
      homogeneousComponent n (lubinIntertwiningError f g phi)) :
    (n + 1 : ℕ) ≤
      (lubinIntertwiningError f g (phi + Q)).order := by
  apply nat_component_zero horder
  · intro d hd
    exact intertwining_error_homogeneous
      hg0 hphi (by omega) hQ hd
  · apply homogeneous_component_corrected
      (homogeneous_intertwining_error
        hf1 hg0 hg1 hphi hn hQ)
      hcorrect

end

end Submission.CField.FGroups
