import Submission.ClassField.FormalGroups.LubinTatePerturbation
import Submission.ClassField.FormalGroups.LubinTateUniqueness


/-!
# Class Field Theory, Chapter I, Lemma 2.11: full uniqueness

Two exact intertwiners with the same linear part agree degree by degree.  At
the first possible degree `n >= 2`, their discrepancy is homogeneous.  The
perturbation formula shows that it is killed by `pi - pi^n`, which is nonzero
for a nonzero nonunit `pi` in a local domain.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R sigma : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

omit [IsDomain R] [IsLocalRing R] in
/-- Agreement of all homogeneous components below `n` means agreement of
all coefficients below total degree `n`. -/
private theorem homogeneous_component_below
    {phi psi : MvPowerSeries sigma R} {n : Nat}
    (hbelow : forall m, m < n ->
      homogeneousComponent m phi = homogeneousComponent m psi) :
    (n : Nat) <= (phi - psi).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdegree : d.degree < n := hd
  have hcoeff := congrArg (coeff d) (hbelow d.degree hdegree)
  rw [map_sub, sub_eq_zero]
  simpa only [coeff_homogeneousComponent, if_pos rfl] using hcoeff

omit [IsDomain R] [IsLocalRing R] in
/-- Adding the degree-`n` homogeneous component of `phi - psi` to `psi`
makes the result agree with `phi` through degree `n`. -/
private theorem nat_homogeneous_component
    {phi psi : MvPowerSeries sigma R} {n : Nat}
    (hbelow : forall m, m < n ->
      homogeneousComponent m phi = homogeneousComponent m psi) :
    (n + 1 : Nat) <=
      (phi - (psi + homogeneousComponent n (phi - psi))).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdegree : d.degree < n + 1 := hd
  rw [map_sub, map_add, coeff_homogeneousComponent]
  by_cases hdn : d.degree = n
  · rw [if_pos hdn, map_sub]
    abel
  · rw [if_neg hdn]
    have hdlt : d.degree < n := by omega
    have hcoeff := congrArg (coeff d) (hbelow d.degree hdlt)
    have hcoeff' : coeff d phi = coeff d psi := by
      simpa only [coeff_homogeneousComponent, if_pos rfl] using hcoeff
    rw [hcoeff']
    abel

omit [IsDomain R] [IsLocalRing R] in
/-- Errors have the same degree-`n` homogeneous component when their inputs
agree through degree `n`. -/
private theorem homogeneous_component_intertwining
    [Finite sigma] {f g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0)
    {phi psi : MvPowerSeries sigma R}
    (hphi0 : constantCoeff phi = 0)
    (hpsi0 : constantCoeff psi = 0)
    {n : Nat} (horder : (n + 1 : Nat) <= (phi - psi).order) :
    homogeneousComponent n (lubinIntertwiningError f g phi) =
      homogeneousComponent n (lubinIntertwiningError f g psi) := by
  apply MvPowerSeries.ext
  intro d
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
  by_cases hd : d.degree = n
  · rw [if_pos hd, if_pos hd]
    have hlt : (d.degree : ENat) < (phi - psi).order := by
      exact (show (d.degree : ENat) < n + 1 by
        exact_mod_cast (by omega : d.degree < n + 1)).trans_le horder
    have hleft := coeff_subst_sub
      hphi0 hpsi0 hlt f
    have hright := coeff_coordinatewise_subst
      hg0 hlt
    simpa only [lubinIntertwiningError, map_sub] using
      congrArg₂ (fun x y : R => x - y) hleft hright
  · rw [if_neg hd, if_neg hd]

/-- Full uniqueness in Lemma 2.11. -/
theorem tate_intertwining_error
    [Finite sigma] {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    {f g : PowerSeries R}
    (hf1 : PowerSeries.coeff 1 f = pi)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg1 : PowerSeries.coeff 1 g = pi)
    {phi psi : MvPowerSeries sigma R}
    (hphi0 : constantCoeff phi = 0)
    (hpsi0 : constantCoeff psi = 0)
    (hone : homogeneousComponent 1 phi = homogeneousComponent 1 psi)
    (hphi : lubinIntertwiningError f g phi = 0)
    (hpsi : lubinIntertwiningError f g psi = 0) :
    phi = psi := by
  letI := Fintype.ofFinite sigma
  have hzero : homogeneousComponent 0 phi = homogeneousComponent 0 psi := by
    apply MvPowerSeries.ext
    intro d
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases hd : d.degree = 0
    · have hdzero : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd
      subst d
      simp [hphi0, hpsi0]
    · rw [if_neg hd, if_neg hd]
  have hall : forall n,
      homogeneousComponent n phi = homogeneousComponent n psi := by
    intro n
    induction n using Nat.strongRec with
    | ind n ih =>
        by_cases hn0 : n = 0
        · simpa only [hn0] using hzero
        by_cases hn1 : n = 1
        · simpa only [hn1] using hone
        have hn : 2 <= n := by omega
        let Q : MvPowerSeries sigma R := homogeneousComponent n (phi - psi)
        have hQ : IsHomogeneous Q n :=
          isHomogeneous_homogeneousComponent (phi - psi) n
        have hQ0 : constantCoeff Q = 0 :=
          IsHomogeneous.constant_coeff_zero hQ (by omega)
        have hbelow : forall m, m < n ->
            homogeneousComponent m phi = homogeneousComponent m psi :=
          fun m hm => ih m hm
        have hclose : (n + 1 : Nat) <= (phi - (psi + Q)).order := by
          simpa only [Q] using
            nat_homogeneous_component hbelow
        have hpsiQ0 : constantCoeff (psi + Q) = 0 := by
          rw [map_add, hpsi0, hQ0, add_zero]
        have herr :
            homogeneousComponent n (lubinIntertwiningError f g phi) =
              homogeneousComponent n
                (lubinIntertwiningError f g (psi + Q)) :=
          homogeneous_component_intertwining
            hg0 hphi0 hpsiQ0 hclose
        have hperturb :=
          homogeneous_intertwining_error
            hf1 hg0 hg1 hpsi0 hn hQ
        have hscalar : (pi - pi ^ n) • Q = 0 := by
          rw [hphi, map_zero] at herr
          rw [hperturb, hpsi, map_zero, zero_add] at herr
          exact herr.symm
        have hpiEq : pi • Q = pi ^ n • Q := by
          apply sub_eq_zero.mp
          simpa only [sub_smul] using hscalar
        have hQzero : Q = 0 :=
          uniformizer_smul_pow hpi0 hpi hn hpiEq
        change homogeneousComponent n (phi - psi) = 0 at hQzero
        rw [map_sub, sub_eq_zero] at hQzero
        exact hQzero
  apply MvPowerSeries.ext
  intro d
  have hcoeff := congrArg (coeff d) (hall d.degree)
  simpa only [coeff_homogeneousComponent, if_pos rfl] using hcoeff

end

end Submission.CField.FGroups
