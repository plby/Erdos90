import Submission.ClassField.LubinTate.SemilinearConjugate
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Class Field Theory, Chapter I, Proposition 3.10, Step 2: reduction

This file formalizes the reduction-modulo-the-maximal-ideal calculation in
Step 2.  Its characteristic-`p` input is that coefficientwise Frobenius after
the substitution `T |-> T^(p^n)` is the `p^n`-th power of a series.
-/

namespace Submission.CField.LTate

open PowerSeries

noncomputable section

/-- If reduction intertwines `sigma` with the `p^n`-power Frobenius, then the
`p^n`-th power of a reduced series is obtained by first applying `sigma` to
its coefficients and then substituting `T^(p^n)`. -/
theorem subst_x_sigma
    {R S : Type*} [CommRing R] [CommRing S]
    (p n : ℕ) [ExpChar S p]
    (rho : R →+* S) (sigma : R →+* R)
    (hcompat :
      (iterateFrobenius S p n).comp rho = rho.comp sigma)
    (phi : PowerSeries R) :
    PowerSeries.map rho phi ^ (p ^ n) =
      subst (X ^ (p ^ n))
        (PowerSeries.map rho (PowerSeries.map sigma phi)) := by
  have hp : p ≠ 0 := expChar_ne_zero S p
  have hq : p ^ n ≠ 0 := pow_ne_zero n hp
  have hmapPhi :
      PowerSeries.map (iterateFrobenius S p n) (PowerSeries.map rho phi) =
        PowerSeries.map rho (PowerSeries.map sigma phi) := by
    ext m
    simp only [PowerSeries.coeff_map]
    exact congrArg (fun h : R →+* S ↦ h (coeff m phi)) hcompat
  calc
    PowerSeries.map rho phi ^ (p ^ n) =
        PowerSeries.map (iterateFrobenius S p n)
          (PowerSeries.expand (p ^ n) hq (PowerSeries.map rho phi)) :=
      (MvPowerSeries.map_iterateFrobenius_expand
        (p := p) (hp := hp) (R := S)
        (f := PowerSeries.map rho phi) n).symm
    _ = PowerSeries.expand (p ^ n) hq
          (PowerSeries.map (iterateFrobenius S p n)
            (PowerSeries.map rho phi)) := by
      rw [PowerSeries.map_expand]
    _ = PowerSeries.expand (p ^ n) hq
          (PowerSeries.map rho (PowerSeries.map sigma phi)) := by
      rw [hmapPhi]
    _ = subst (X ^ (p ^ n))
          (PowerSeries.map rho (PowerSeries.map sigma phi)) := by
      rw [PowerSeries.expand_apply]

/-- The congruence calculation in Step 2 of Proposition 3.10.  If `rho`
reduces `f` to `T^(p^n)` and carries `sigma` to coefficientwise Frobenius,
then the reduction of `sigma(theta) o f o theta^-1` is `T^(p^n)`. -/
theorem semilinear_x_compatible
    {R S : Type*} [CommRing R] [CommRing S]
    (p n : ℕ) [ExpChar S p]
    (rho : R →+* S) (sigma : R →+* R)
    {theta inverseTheta f : PowerSeries R}
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hf0 : constantCoeff f = 0)
    (hinverse : subst inverseTheta theta = X)
    (hfmap : PowerSeries.map rho f = X ^ (p ^ n))
    (hcompat :
      (iterateFrobenius S p n).comp rho = rho.comp sigma) :
    PowerSeries.map rho
        (semilinearConjugate sigma theta inverseTheta f) =
      X ^ (p ^ n) := by
  have hinverseSubst : PowerSeries.HasSubst inverseTheta :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0
  have hinner0 : constantCoeff (subst inverseTheta f) = 0 :=
    constantCoeff_subst_eq_zero hinverse0 f hf0
  have hmapSigmaInverse0 :
      constantCoeff (PowerSeries.map sigma inverseTheta) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hinverse0, map_zero]
  have hmappedInverseSigma :
      subst (PowerSeries.map sigma inverseTheta)
          (PowerSeries.map sigma theta) = X := by
    calc
      subst (PowerSeries.map sigma inverseTheta)
          (PowerSeries.map sigma theta) =
          PowerSeries.map sigma (subst inverseTheta theta) := by
        simpa using (PowerSeries.map_subst (h := sigma)
          hinverseSubst theta).symm
      _ = PowerSeries.map sigma X := by rw [hinverse]
      _ = X := PowerSeries.map_X sigma
  have hmappedInverse :
      subst (PowerSeries.map rho (PowerSeries.map sigma inverseTheta))
          (PowerSeries.map rho (PowerSeries.map sigma theta)) = X := by
    calc
      subst (PowerSeries.map rho (PowerSeries.map sigma inverseTheta))
          (PowerSeries.map rho (PowerSeries.map sigma theta)) =
          PowerSeries.map rho
            (subst (PowerSeries.map sigma inverseTheta)
              (PowerSeries.map sigma theta)) := by
        simpa using (PowerSeries.map_subst (h := rho)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hmapSigmaInverse0)
          (PowerSeries.map sigma theta)).symm
      _ = PowerSeries.map rho X := by rw [hmappedInverseSigma]
      _ = X := PowerSeries.map_X rho
  have hq : p ^ n ≠ 0 := pow_ne_zero n (expChar_ne_zero S p)
  rw [semilinearConjugate]
  calc
    PowerSeries.map rho
        (subst (subst inverseTheta f) (PowerSeries.map sigma theta)) =
        subst (PowerSeries.map rho (subst inverseTheta f))
          (PowerSeries.map rho (PowerSeries.map sigma theta)) := by
      simpa using PowerSeries.map_subst (h := rho)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hinner0)
        (PowerSeries.map sigma theta)
    _ = subst
          (subst (PowerSeries.map rho inverseTheta) (PowerSeries.map rho f))
          (PowerSeries.map rho (PowerSeries.map sigma theta)) := by
      congr 1
      simpa using PowerSeries.map_subst (h := rho) hinverseSubst f
    _ = subst ((PowerSeries.map rho inverseTheta) ^ (p ^ n))
          (PowerSeries.map rho (PowerSeries.map sigma theta)) := by
      rw [hfmap, PowerSeries.subst_pow (hinverseSubst.map rho),
        PowerSeries.subst_X (hinverseSubst.map rho)]
    _ = subst
          (subst (X ^ (p ^ n))
            (PowerSeries.map rho (PowerSeries.map sigma inverseTheta)))
          (PowerSeries.map rho (PowerSeries.map sigma theta)) := by
      rw [subst_x_sigma
        p n rho sigma hcompat inverseTheta]
    _ = subst (X ^ (p ^ n))
          (subst (PowerSeries.map rho (PowerSeries.map sigma inverseTheta))
            (PowerSeries.map rho (PowerSeries.map sigma theta))) := by
      exact (subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero'
          (by
            rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
              coeff_zero_eq_constantCoeff_apply, hmapSigmaInverse0, map_zero]))
        (PowerSeries.HasSubst.X_pow hq)
        (PowerSeries.map rho (PowerSeries.map sigma theta))).symm
    _ = subst (X ^ (p ^ n)) X := by rw [hmappedInverse]
    _ = X ^ (p ^ n) := PowerSeries.subst_X
      (PowerSeries.HasSubst.X_pow hq)

end

end Submission.CField.LTate
