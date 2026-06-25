import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.RingTheory.PowerSeries.Binomial
import Submission.ClassField.FormalGroups.PAdicIntegers
import Submission.ClassField.FormalGroups.LubinTateHomomorphism
import Submission.ClassField.FormalGroups.PadicBinomialContinuity

/-!
# Class Field Theory, Chapter I, Example 2.18

For a p-adic integer `a`, Mathlib's binomial-ring structure on `ℤ_[p]`
defines the formal series `(1+T)^a`.  This file records the elementary
formal-series assertions used in Milne's example: subtracting one gives a
series with constant coefficient zero and linear coefficient `a`, and for
natural exponents it agrees with the usual power `(1+T)^n-1`.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

/-- Regard an ordinary power series as a series indexed by `Fin 1`, by
substituting the unique formal variable. -/
noncomputable def powerSeriesUnary
    {R : Type*} [CommRing R] (f : PowerSeries R) : UnarySeries R :=
  PowerSeries.subst FGLaw.unaryX f

/-- An ordinary zero-constant series which commutes with `f` becomes the
exact unary Lubin--Tate intertwiner after reindexing its variable by `Fin 1`. -/
theorem unary_intertwiner_commutes
    {R : Type*} [CommRing R]
    (f h : PowerSeries R) (a : R)
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hh0 : PowerSeries.constantCoeff h = 0)
    (hh1 : PowerSeries.coeff 1 h = a)
    (hcomm : PowerSeries.subst h f = PowerSeries.subst f h) :
    LIntert f f (fun _ : Fin 1 ↦ a)
      (powerSeriesUnary h) := by
  let x : UnarySeries R := FGLaw.unaryX
  let phi : UnarySeries R := PowerSeries.subst x h
  let psi : UnarySeries R := PowerSeries.subst x f
  have hx0 : constantCoeff x = 0 := by
    simp [x, FGLaw.unaryX]
  have hphi0 : constantCoeff phi = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hx0 h hh0
  have hpsi0 : constantCoeff psi = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hx0 f hf0
  have hX1 : homogeneousComponent 1
      (X (0 : Fin 1) : UnarySeries R) = X 0 := by
    ext d
    rw [coeff_homogeneousComponent, coeff_X]
    by_cases hd : d = Finsupp.single (0 : Fin 1) 1
    · subst d
      simp
    · simp [hd]
  refine ⟨by simpa [powerSeriesUnary, phi, x] using hphi0, ?_, ?_⟩
  · rw [powerSeriesUnary,
      homogeneous_series_subst hx0 h, hh1]
    simp [x, FGLaw.unaryX, mvLinearForm, hX1]
  · rw [lubinIntertwiningError, sub_eq_zero]
    have hxSubst : PowerSeries.HasSubst x :=
      PowerSeries.HasSubst.of_constantCoeff_zero hx0
    have hhSubst : PowerSeries.HasSubst (h : PowerSeries R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hh0
    have hfSubst : PowerSeries.HasSubst (f : PowerSeries R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hf0
    have hpsiSubst : HasSubst (fun _ : Fin 1 ↦ psi) :=
      hasSubst_of_constantCoeff_zero (fun _ ↦ hpsi0)
    have hcoord : (coordinatewiseSubst (σ := Fin 1) f) =
        fun _ : Fin 1 ↦ psi := by
      funext i
      fin_cases i
      rfl
    change PowerSeries.subst phi f =
      MvPowerSeries.subst (coordinatewiseSubst f) phi
    rw [hcoord]
    change subst (fun _ : Unit ↦ phi) f =
      subst (fun _ : Fin 1 ↦ psi) phi
    calc
      subst (fun _ : Unit ↦ phi) f =
          PowerSeries.subst x (PowerSeries.subst h f) := by
        exact (PowerSeries.subst_comp_subst_apply hhSubst hxSubst f).symm
      _ = PowerSeries.subst x (PowerSeries.subst f h) := by rw [hcomm]
      _ = subst (fun _ : Unit ↦ psi) h := by
        exact PowerSeries.subst_comp_subst_apply hfSubst hxSubst h
      _ = subst (fun _ : Fin 1 ↦ psi) phi := by
        change subst (fun _ : Unit ↦ psi) h =
          subst (fun _ : Fin 1 ↦ psi) (PowerSeries.subst x h)
        symm
        calc
          subst (fun _ : Fin 1 ↦ psi) (PowerSeries.subst x h) =
              subst (fun _ : Unit ↦
                subst (fun _ : Fin 1 ↦ psi) x) h :=
            MvPowerSeries.subst_comp_subst_apply hxSubst.const hpsiSubst h
          _ = subst (fun _ : Unit ↦ psi) h := by
            congr 1
            funext i
            change subst (fun _ : Fin 1 ↦ psi)
              FGLaw.unaryX = psi
            rw [FGLaw.unaryX, subst_X hpsiSubst]

variable (p : ℕ) [Fact p.Prime]

/-- Milne's p-adic binomial series `(1+T)^a-1`. -/
noncomputable def padicBinomialEndomorphism (a : ℤ_[p]) : PowerSeries ℤ_[p] :=
  PowerSeries.binomialSeries ℤ_[p] a - 1

@[simp]
theorem endomorphism_constant_coeff (a : ℤ_[p]) :
    PowerSeries.constantCoeff (padicBinomialEndomorphism p a) = 0 := by
  simp [padicBinomialEndomorphism]

@[simp]
theorem padic_binomial_endomorphism (a : ℤ_[p]) :
    PowerSeries.coeff 1 (padicBinomialEndomorphism p a) = a := by
  simp [padicBinomialEndomorphism]

/-- For natural exponents, the p-adic binomial series is the ordinary
cyclotomic power series. -/
theorem binomial_endomorphism_nat (n : ℕ) :
    padicBinomialEndomorphism p (n : ℤ_[p]) =
      cyclotomicPowerSeries (R := ℤ_[p]) n := by
  simp [padicBinomialEndomorphism, cyclotomicPowerSeries]

/-- Substitution of the cyclotomic series multiplies its natural exponent.
This is the dense family on which the commutation in Example 2.18 is
elementary. -/
theorem cyclotomic_series_subst
    {R : Type*} [CommRing R] (m n : ℕ) :
    PowerSeries.subst (cyclotomicPowerSeries (R := R) m)
        (cyclotomicPowerSeries (R := R) n) =
      cyclotomicPowerSeries (R := R) (m * n) := by
  have hm0 : PowerSeries.constantCoeff
      (cyclotomicPowerSeries (R := R) m) = 0 := by
    simp [cyclotomicPowerSeries]
  have hmSubst : PowerSeries.HasSubst
      (cyclotomicPowerSeries (R := R) m) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hm0
  change PowerSeries.subst (cyclotomicPowerSeries (R := R) m)
      ((1 + PowerSeries.X) ^ n - 1) =
    (1 + PowerSeries.X) ^ (m * n) - 1
  rw [PowerSeries.subst_sub hmSubst,
    PowerSeries.subst_pow hmSubst, PowerSeries.subst_add hmSubst,
    PowerSeries.subst_X hmSubst]
  have hone : PowerSeries.subst (cyclotomicPowerSeries (R := R) m)
      (1 : PowerSeries R) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hmSubst]
    exact map_one _
  rw [hone]
  simp only [cyclotomicPowerSeries]
  rw [show (1 : PowerSeries R) + ((1 + PowerSeries.X) ^ m - 1) =
      (1 + PowerSeries.X) ^ m by ring]
  rw [pow_mul]

/-- Cyclotomic power series commute under substitution. -/
theorem cyclotomic_subst_commute
    {R : Type*} [CommRing R] (m n : ℕ) :
    PowerSeries.subst (cyclotomicPowerSeries (R := R) m)
        (cyclotomicPowerSeries (R := R) n) =
      PowerSeries.subst (cyclotomicPowerSeries (R := R) n)
        (cyclotomicPowerSeries (R := R) m) := by
  rw [cyclotomic_series_subst, cyclotomic_series_subst, Nat.mul_comm]

/-- Each coefficient of `(1+T)^a` varies continuously with the p-adic
exponent `a`. -/
theorem continuous_binomial_coeff (m : ℕ) :
    Continuous (fun a : ℤ_[p] ↦
      PowerSeries.coeff m (PowerSeries.binomialSeries ℤ_[p] a)) := by
  simpa only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one] using
    PadicInt.continuous_choose (p := p) m

/-- Example 2.18: the p-adic binomial series commutes with the cyclotomic
Lubin--Tate series under substitution.  The identity holds for natural
exponents by elementary power-series algebra, and hence for every p-adic
exponent by coefficientwise continuity and density. -/
theorem endomorphism_subst_commute (a : ℤ_[p]) :
    PowerSeries.subst (padicBinomialEndomorphism p a)
        (cyclotomicPowerSeries (R := ℤ_[p]) p) =
      PowerSeries.subst (cyclotomicPowerSeries (R := ℤ_[p]) p)
        (padicBinomialEndomorphism p a) := by
  open scoped PowerSeries.WithPiTopology in
    have hcontinuous : Continuous (padicBinomialEndomorphism p) := by
      simpa only [padicBinomialEndomorphism] using
        (continuous_binomial_series p).sub continuous_const
    apply PowerSeries.ext
    intro e
    have hleft : Continuous (fun b : ℤ_[p] ↦
        PowerSeries.coeff e
          (PowerSeries.subst (padicBinomialEndomorphism p b)
            (cyclotomicPowerSeries (R := ℤ_[p]) p))) := by
      have hformula : (fun b : ℤ_[p] ↦
          PowerSeries.subst (padicBinomialEndomorphism p b)
            (cyclotomicPowerSeries (R := ℤ_[p]) p)) =
          fun b ↦ (1 + padicBinomialEndomorphism p b) ^ p - 1 := by
        funext b
        have hb0 := endomorphism_constant_coeff p b
        have hbSubst : PowerSeries.HasSubst
            (padicBinomialEndomorphism p b) :=
          PowerSeries.HasSubst.of_constantCoeff_zero' hb0
        rw [cyclotomicPowerSeries, PowerSeries.subst_sub hbSubst,
          PowerSeries.subst_pow hbSubst, PowerSeries.subst_add hbSubst,
          PowerSeries.subst_X hbSubst]
        have hone : PowerSeries.subst (padicBinomialEndomorphism p b)
            (1 : PowerSeries ℤ_[p]) = 1 := by
          rw [← PowerSeries.coe_substAlgHom hbSubst]
          exact map_one _
        rw [hone]
      have hseries : Continuous (fun b : ℤ_[p] ↦
          PowerSeries.subst (padicBinomialEndomorphism p b)
            (cyclotomicPowerSeries (R := ℤ_[p]) p)) := by
        rw [hformula]
        exact ((continuous_const.add hcontinuous).pow p).sub continuous_const
      exact (PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] e).comp hseries
    have hright : Continuous (fun b : ℤ_[p] ↦
        PowerSeries.coeff e
          (PowerSeries.subst (cyclotomicPowerSeries (R := ℤ_[p]) p)
            (padicBinomialEndomorphism p b))) := by
      apply continuous_subst_family p
      · simp [cyclotomicPowerSeries]
      · intro d
        exact (PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] d).comp
          hcontinuous
    exact congr_fun (PadicInt.denseRange_natCast.equalizer hleft hright
      (funext fun n ↦ by
        change PowerSeries.coeff e
            (PowerSeries.subst (padicBinomialEndomorphism p (n : ℤ_[p]))
              (cyclotomicPowerSeries (R := ℤ_[p]) p)) =
          PowerSeries.coeff e
            (PowerSeries.subst (cyclotomicPowerSeries (R := ℤ_[p]) p)
              (padicBinomialEndomorphism p (n : ℤ_[p])))
        rw [binomial_endomorphism_nat p n]
        exact congrArg (PowerSeries.coeff e)
          (cyclotomic_subst_commute (R := ℤ_[p]) n p))) a

/-- The reindexed p-adic binomial series is the exact self-intertwiner with
linear coefficient `a` for the cyclotomic Lubin--Tate series. -/
theorem binomial_endomorphism_intertwiner (a : ℤ_[p]) :
    LIntert
      (cyclotomicPowerSeries (R := ℤ_[p]) p)
      (cyclotomicPowerSeries (R := ℤ_[p]) p)
      (fun _ : Fin 1 ↦ a)
      (powerSeriesUnary (padicBinomialEndomorphism p a)) := by
  apply unary_intertwiner_commutes
  · simp [cyclotomicPowerSeries]
  · exact endomorphism_constant_coeff p a
  · exact padic_binomial_endomorphism p a
  · exact endomorphism_subst_commute p a

/-- Example 2.18: Milne's explicit series `(1+T)^a-1` is the canonical
Lubin--Tate scalar endomorphism `[a]_f` for `f=(1+T)^p-1`. -/
theorem unary_endomorphism_intertwiner
    (a : ℤ_[p]) :
    powerSeriesUnary (padicBinomialEndomorphism p a) =
      tateScalarIntertwiner (p : ℤ_[p]) (padic_int_ne p)
        (padic_int_unit p) (padic_int_field p)
        (cyclotomicPowerSeries (R := ℤ_[p]) p)
        (cyclotomicPowerSeries (R := ℤ_[p]) p)
        (lubin_tate_cyclotomic p)
        (lubin_tate_cyclotomic p) a := by
  exact tate_intertwiner (p : ℤ_[p]) (padic_int_ne p)
    (padic_int_unit p) (padic_int_field p)
    (cyclotomicPowerSeries (R := ℤ_[p]) p)
    (cyclotomicPowerSeries (R := ℤ_[p]) p)
    (lubin_tate_cyclotomic p)
    (lubin_tate_cyclotomic p) (fun _ : Fin 1 ↦ a)
    (binomial_endomorphism_intertwiner p a)

end

end Submission.CField.FGroups
