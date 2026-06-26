import Submission.NumberTheory.Galois.ReducibleLocalRoots
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Chapter V, Section 3: Corollary 3.24

Milne's literal premise says that `f ∈ K[X]` splits into linear factors
modulo all but finitely many finite primes of `K`.  We express that premise
directly, rather than replacing it by the stronger assertion that almost
every prime splits completely in a chosen splitting field.

For a polynomial over the fraction field, reduction at a prime is represented
by an integral multiple whose scalar is nonzero modulo that prime.  Requiring
the reduced polynomial to retain the degree of `f` rules out degeneration of
the leading coefficient.  `Polynomial.Splits` over the residue field is
exactly factorization into linear factors.

The analytic input is `ChebotarevDensityTheorem`.  The only additional bridge
isolated below is the standard algebraic Dedekind comparison: away from
finitely many denominator, discriminant, and ramification primes, complete
linear factorization of the reduction makes the prime split completely in a
splitting field.  The repository contains the underlying monic-integral,
separable-reduction Frobenius/factorization APIs, but not yet this packaged
arbitrary-polynomial clearing-denominators statement.
-/

namespace Submission.CField.ARecip

open IsDedekindDomain NumberField Polynomial
open Submission.NumberTheory.Milne
open scoped nonZeroDivisors Polynomial

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- `f` splits into linear factors modulo the finite prime `p`.

The witness `a` clears the denominators of `f`; its nonvanishing modulo `p`
makes this a legitimate reduction at `p`.  The degree equality excludes a
vanishing reduced leading coefficient. -/
def SplitsFactorsModulo
    (f : K[X]) (p : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ (a : 𝓞 K) (g : (𝓞 K)[X]),
    a ∉ p.asIdeal ∧
      g.map (algebraMap (𝓞 K) K) = C (a : K) * f ∧
      (g.map (Ideal.Quotient.mk p.asIdeal)).natDegree = f.natDegree ∧
      (g.map (Ideal.Quotient.mk p.asIdeal)).Splits

/-- The source's literal phrase "for all but finitely many prime ideals". -/
def SplitsModuloAlmost (f : K[X]) : Prop :=
  {p : HeightOneSpectrum (𝓞 K) |
    ¬SplitsFactorsModulo f p}.Finite

section ChosenSplittingField

variable {L : Type u} [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The exact algebraic reduction adapter still missing as one packaged
theorem from the current APIs.  It does not assume that the splitting primes
are cofinite: it says only that the primes where *linear factorization of the
literal reduction* fails to imply complete splitting form a finite set. -/
def ReductionSplittingExceptions
    (f : K[X]) [IsSplittingField K L f] : Prop :=
  {p : HeightOneSpectrum (𝓞 K) |
    SplitsFactorsModulo f p ∧
      p ∉ splittingPrimes K L}.Finite

/-- Corollary V.3.24 for a chosen splitting field.  The proof uses the
literal reduction predicate, the exact finite-exception comparison adapter,
and only the analytic Chebotarev statement for that splitting field. -/
theorem reductions_almost_everywhere
    (f : K[X]) [IsSplittingField K L f]
    (hreduction : SplitsModuloAlmost f)
    (hcomparison : ReductionSplittingExceptions (L := L) f)
    (hchebotarev : ChebotarevDensityTheorem K L) :
    f.Splits := by
  apply splits_cofinite_chebotarev
    f (IsSplittingField.splits L f) _ hchebotarev
  apply (hreduction.union hcomparison).subset
  intro p hp
  by_cases hred : SplitsFactorsModulo f p
  · exact Or.inr ⟨hred, hp⟩
  · exact Or.inl hred

end ChosenSplittingField

/-- Chebotarev for the canonical splitting field of `f`, isolated as a
proposition because the analytic theorem is not yet proved in the library. -/
def CanonicalSplittingChebotarev (f : K[X]) : Prop := by
  letI : NumberField f.SplittingField := NumberField.of_module_finite K _
  letI : IsGalois K f.SplittingField := ⟨⟩
  exact ChebotarevDensityTheorem K f.SplittingField

/-- The finite algebraic comparison exceptions for the canonical splitting
field. -/
def CanonicalSplittingExceptions (f : K[X]) : Prop := by
  letI : NumberField f.SplittingField := NumberField.of_module_finite K _
  letI : IsGalois K f.SplittingField := ⟨⟩
  exact ReductionSplittingExceptions
    (L := f.SplittingField) f

/-- The literal Corollary V.3.24 follows from the analytic Chebotarev input
and the exact finite algebraic reduction adapter for canonical splitting
fields. -/
theorem splits_modulo_chebotarev
    (hchebotarev : ∀ f : K[X], CanonicalSplittingChebotarev f)
    (hcomparison : ∀ f : K[X],
      CanonicalSplittingExceptions f) :
    (∀ f : K[X],
          SplitsModuloAlmost f → f.Splits) := by
  intro f hreduction
  letI : NumberField f.SplittingField := NumberField.of_module_finite K _
  letI : IsGalois K f.SplittingField := ⟨⟩
  apply reductions_almost_everywhere
    (L := f.SplittingField) f hreduction
  · exact hcomparison f
  · exact hchebotarev f

end

end Submission.CField.ARecip
