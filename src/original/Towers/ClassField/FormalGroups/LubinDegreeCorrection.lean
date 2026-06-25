import Towers.ClassField.FormalGroups.LubinBaseApproximation
import Towers.ClassField.FormalGroups.LubinTateFiltration

/-!
# Class Field Theory, Chapter I, Lemma 2.11: homogeneous corrections

This file packages the correction selected at one total degree in Milne's
successive-approximation proof.  The Frobenius congruence makes the error
divisible by `pi`; the other factor in the denominator is a unit.  Hence the
homogeneous error component has a unique homogeneous quotient.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- The error in the intertwining equation from Lemma 2.11. -/
def lubinIntertwiningError (f g : PowerSeries R)
    (phi : MvPowerSeries σ R) : MvPowerSeries σ R :=
  PowerSeries.subst phi f - subst (coordinatewiseSubst g) phi

/-- Every homogeneous component of a Lubin--Tate intertwining error is still
coefficientwise divisible by the uniformizer. -/
theorem lubin_homogeneous_error
    [Finite σ] (pi : R)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    {f g : PowerSeries R}
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    {phi : MvPowerSeries σ R} (hphi : constantCoeff phi = 0)
    (n : ℕ) (d : σ →₀ ℕ) :
    coeff d
        (homogeneousComponent n (lubinIntertwiningError f g phi)) ∈
      Ideal.span {pi} := by
  rw [coeff_homogeneousComponent]
  split_ifs with hd
  · exact intertwining_error_span
      pi hfield hf hg hphi d
  · exact Ideal.zero_mem _

/-- At every total degree `n ≥ 2`, the homogeneous error has a unique
homogeneous quotient by Milne's correction denominator
`(pi^(n-1) - 1) * pi`. -/
theorem unique_lubin_correction
    [IsDomain R] [IsLocalRing R] [Finite σ]
    {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    {f g : PowerSeries R}
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    {phi : MvPowerSeries σ R} (hphi : constantCoeff phi = 0)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃! Q : MvPowerSeries σ R,
      IsHomogeneous Q n ∧
        ((pi ^ (n - 1) - 1) * pi) • Q =
          homogeneousComponent n (lubinIntertwiningError f g phi) := by
  have hn1 : n - 1 ≠ 0 := by omega
  have hu : IsUnit (pi ^ (n - 1) - 1) :=
    pow_sub_not hpi hn1
  let u : Rˣ := hu.unit
  have hucoe : (u : R) = pi ^ (n - 1) - 1 := hu.unit_spec
  have hhom : IsHomogeneous
      (homogeneousComponent n (lubinIntertwiningError f g phi)) n :=
    isHomogeneous_homogeneousComponent _ _
  have hdiv : ∀ d, coeff d
        (homogeneousComponent n (lubinIntertwiningError f g phi)) ∈
      Ideal.span {pi} :=
    lubin_homogeneous_error
      pi hfield hf hg hphi n
  obtain ⟨Q, hQ, huniq⟩ :=
    unique_homogeneous_span
      hpi0 u hhom hdiv
  refine ⟨Q, ?_, ?_⟩
  · simpa only [hucoe] using hQ
  · intro P hP
    apply huniq P
    simpa only [hucoe] using hP

/-- A positive-degree homogeneous correction has zero constant coefficient. -/
theorem IsHomogeneous.constant_coeff_zero
    {Q : MvPowerSeries σ R} {n : ℕ}
    (hQ : IsHomogeneous Q n) (hn : n ≠ 0) :
    constantCoeff Q = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  apply hQ.coeff_eq_zero
  simpa using hn.symm

/-- A degree-`n` homogeneous correction does not alter any coefficient of
strictly smaller total degree. -/
theorem IsHomogeneous.coeff_zero_below
    {Q : MvPowerSeries σ R} {n : ℕ}
    (hQ : IsHomogeneous Q n) {d : σ →₀ ℕ} (hd : d.degree < n) :
    coeff d Q = 0 := by
  exact hQ.coeff_eq_zero (Nat.ne_of_lt hd)

end

end Towers.CField.FGroups
