import Submission.ClassField.FormalGroups.PowerSeriesUnary
import Submission.ClassField.FormalGroups.CompositionalInverse

/-!
# Class Field Theory, Chapter I, Section 3: iterated Lubin--Tate series

The analytic definition of Lubin--Tate torsion in an algebraic closure needs
convergence infrastructure not yet available here.  This file records the
formal-series part of Remark 3.1 and Example 3.2: compositional iterates, and
the explicit formula for the cyclotomic Lubin--Tate series.
-/

namespace Submission.CField.LTate

noncomputable section

open Submission.CField.FGroups

/-- The `n`-fold compositional iterate of a zero-constant power series, with
the zeroth iterate equal to the identity series `X`. -/
def substitutionIterate {R : Type*} [CommRing R]
    (f : PowerSeries R) : ℕ → PowerSeries R
  | 0 => PowerSeries.X
  | n + 1 => PowerSeries.subst (substitutionIterate f n) f

@[simp]
theorem substitutionIterate_zero
    {R : Type*} [CommRing R] (f : PowerSeries R) :
    substitutionIterate f 0 = PowerSeries.X := rfl

@[simp]
theorem substitutionIterate_succ
    {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    substitutionIterate f (n + 1) =
      PowerSeries.subst (substitutionIterate f n) f := rfl

/-- A zero constant coefficient is preserved under compositional iteration. -/
@[simp]
theorem substitution_iterate_coeff
    {R : Type*} [CommRing R] {f : PowerSeries R}
    (hf0 : PowerSeries.constantCoeff f = 0) (n : ℕ) :
    PowerSeries.constantCoeff (substitutionIterate f n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [substitutionIterate_succ]
      exact PowerSeries.constantCoeff_subst_eq_zero ih f hf0

/-- The linear coefficient of the `n`-fold iterate is the `n`th power of
the original linear coefficient. -/
theorem substitution_iterate_one
    {R : Type*} [CommRing R] {f : PowerSeries R}
    (hf0 : PowerSeries.constantCoeff f = 0) (n : ℕ) :
    PowerSeries.coeff 1 (substitutionIterate f n) =
      PowerSeries.coeff 1 f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [substitutionIterate_succ,
        coeff_one_subst (substitution_iterate_coeff hf0 n), ih]
      simp [pow_succ, mul_comm]

/-- Remark 3.1's assertion that the linear term of the `n`-fold iterate of
a Lubin--Tate series is `pi^n T`. -/
theorem substitution_iterate_lubin
    {R : Type*} [CommRing R] {pi : R} {q n : ℕ}
    {f : PowerSeries R} (hf : LubinSeries pi q f) :
    PowerSeries.coeff 1 (substitutionIterate f n) = pi ^ n := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  rw [substitution_iterate_one hf0 n, hf.2.1]

/-- A zero constant coefficient is preserved by polynomial composition
iteration. -/
theorem coeff_zero_iterate
    {R : Type*} [CommRing R] (f : Polynomial R)
    (hf0 : f.coeff 0 = 0) (n : ℕ) :
    (f.comp^[n] Polynomial.X).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.iterate_comp_eval]
  have hfix : f.eval 0 = 0 := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hf0
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hfix]

/-- For a polynomial with zero constant coefficient, power-series
substitution iteration agrees with ordinary polynomial composition
iteration. -/
theorem substitutionIterate_polynomial
    {R : Type*} [CommRing R] (f : Polynomial R)
    (hf0 : f.coeff 0 = 0) (n : ℕ) :
    substitutionIterate (f : PowerSeries R) n =
      ((f.comp^[n] Polynomial.X : Polynomial R) : PowerSeries R) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [substitutionIterate_succ, ih, Function.iterate_succ_apply']
      rw [PowerSeries.subst_coe
        (PowerSeries.HasSubst.of_constantCoeff_zero (by
          simpa using coeff_zero_iterate f hf0 n))]
      rw [Polynomial.comp_eq_aeval]
      have hC :
          (Polynomial.coeToPowerSeries.ringHom :
            Polynomial R →+* PowerSeries R).comp
              (Polynomial.C : R →+* Polynomial R) =
            (PowerSeries.C : R →+* PowerSeries R) := by
        ext a
        simp
      simpa [Polynomial.aeval_def, hC] using
        (Polynomial.hom_eval₂ f (Polynomial.C : R →+* Polynomial R)
          (Polynomial.coeToPowerSeries.ringHom :
            Polynomial R →+* PowerSeries R)
          (f.comp^[n] Polynomial.X)).symm

/-- Evaluation of a base-changed polynomial iterate as a power series agrees
with ordinary polynomial evaluation using the original coefficient map. -/
theorem eval₂_substitutionIterate_map_polynomial
    {R S : Type*} [CommRing R] [CommRing S] [UniformSpace S]
    (rho : R →+* S) (f : Polynomial R)
    (hf0 : f.coeff 0 = 0) (n : ℕ) (x : S) :
    PowerSeries.eval₂ (RingHom.id S) x
        (substitutionIterate (PowerSeries.map rho (f : PowerSeries R)) n) =
      Polynomial.eval₂ rho x (f.comp^[n] Polynomial.X) := by
  have hmap : PowerSeries.map rho (f : PowerSeries R) =
      (f.map rho : PowerSeries S) := by
    exact Polynomial.polynomial_map_coe.symm
  have hfmap0 : (f.map rho).coeff 0 = 0 := by
    simp [hf0]
  have hiter :
      (f.map rho).comp^[n] Polynomial.X =
        (f.comp^[n] Polynomial.X).map rho := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Polynomial.map_comp, ih]
  rw [hmap, substitutionIterate_polynomial (f.map rho) hfmap0 n,
    PowerSeries.eval₂_coe, hiter, Polynomial.eval₂_map]
  rfl

/-- The `n`-fold iterate of `(1+T)^m-1` is `(1+T)^(m^n)-1`. -/
theorem substitutionIterate_cyclotomic
    {R : Type*} [CommRing R] (m n : ℕ) :
    substitutionIterate (cyclotomicPowerSeries (R := R) m) n =
      cyclotomicPowerSeries (R := R) (m ^ n) := by
  induction n with
  | zero =>
      simp [cyclotomicPowerSeries]
  | succ n ih =>
      rw [substitutionIterate_succ, ih, cyclotomic_series_subst,
        pow_succ]

/-- Example 3.2's formal identity for the cyclotomic Lubin--Tate series over
the p-adic integers. -/
theorem padic_substitution_iterate
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    substitutionIterate (cyclotomicPowerSeries (R := ℤ_[p]) p) n =
      (1 + PowerSeries.X) ^ (p ^ n) - 1 := by
  simpa only [cyclotomicPowerSeries] using
    substitutionIterate_cyclotomic (R := ℤ_[p]) p n

end

end Submission.CField.LTate
