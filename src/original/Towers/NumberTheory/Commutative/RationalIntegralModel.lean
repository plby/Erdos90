import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Monic integral models of rational polynomials

A nonzero polynomial over `ℚ` can first be made monic by dividing by its
leading coefficient.  Clearing all remaining denominators after scaling the
roots then produces a monic polynomial over `ℤ` of the same degree.  This is
the integral model used to pass from the rational polynomials in ANT,
Examples 8.36 and 8.37, to reduction modulo finite primes.
-/

namespace Towers.NumberTheory.Milne

open Polynomial
open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

/-- The monic associate of a nonzero polynomial over a field. -/
def rationalMonicAssociate (f : ℚ[X]) : ℚ[X] :=
  f * C f.leadingCoeff⁻¹

/-- The common denominator used to scale the roots of the monic associate. -/
def rationalRootDenominator (f : ℚ[X]) : nonZeroDivisors ℤ :=
  IsLocalization.commonDenom (nonZeroDivisors ℤ)
    (rationalMonicAssociate f).support
    (rationalMonicAssociate f).coeff

/-- The rational primes dividing the root-scaling denominator chosen for
`f`. -/
def rationalDenominatorPrimes (f : ℚ[X]) :
    Set (HeightOneSpectrum ℤ) :=
  {v | (rationalRootDenominator f : ℤ) ∈ v.asIdeal}

/-- Only finitely many rational primes divide the chosen root-scaling
denominator. -/
theorem rational_denominator_primes (f : ℚ[X]) :
    (rationalDenominatorPrimes f).Finite := by
  let d := rationalRootDenominator f
  apply (Ideal.finite_factors
    (I := Ideal.span {(d : ℤ)})
    (Ideal.span_singleton_eq_bot.not.mpr (nonZeroDivisors.ne_zero d.2))).subset
  intro v hv
  apply Ideal.dvd_iff_le.mpr
  rw [Ideal.span_singleton_le_iff_mem]
  exact hv

/-- Every nonzero rational polynomial has a monic integral root-scaled model
of the same degree.  The displayed identity records the model exactly: first
divide `f` by its leading coefficient, then multiply every root by the common
denominator `d`.

The subtype `d : nonZeroDivisors ℤ` records at once that only finitely many
rational primes can divide the chosen scaling denominator. -/
theorem monic_integral_model
    (f : ℚ[X]) (hf : f ≠ 0) :
    ∃ (d : nonZeroDivisors ℤ) (g : ℤ[X]),
      g.map (algebraMap ℤ ℚ) =
          (rationalMonicAssociate f).scaleRoots
            (algebraMap ℤ ℚ d) ∧
        g.natDegree = f.natDegree ∧ g.Monic := by
  let fm : ℚ[X] := rationalMonicAssociate f
  have hfm : fm.Monic := by
    exact monic_mul_leadingCoeff_inv hf
  let d : nonZeroDivisors ℤ := rationalRootDenominator f
  have hleading : fm.leadingCoeff ∈ (algebraMap ℤ ℚ).range := by
    rw [hfm.leadingCoeff]
    exact ⟨1, map_one _⟩
  have hlifts :
      fm.scaleRoots (algebraMap ℤ ℚ d) ∈
        Polynomial.lifts (algebraMap ℤ ℚ) := by
    exact IsLocalization.scaleRoots_commonDenom_mem_lifts
      (nonZeroDivisors ℤ) fm hleading
  have hscaled : (fm.scaleRoots (algebraMap ℤ ℚ d)).Monic :=
    (monic_scaleRoots_iff _).2 hfm
  obtain ⟨g, hmap, hdegree, hg⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hscaled
  refine ⟨d, g, hmap, ?_, hg⟩
  rw [hdegree, natDegree_scaleRoots]
  exact natDegree_mul_leadingCoeff_inv f hf

end

end Towers.NumberTheory.Milne
