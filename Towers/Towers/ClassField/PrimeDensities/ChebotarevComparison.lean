import Towers.ClassField.ArtinReciprocity.SplitsLinearModulo

/-!
# Chapter VI, Section 3, Corollary 3.5

This is the same local-to-global polynomial splitting assertion already
stated as Corollary V.3.24.  We reuse its literal reduction predicate: an
integral multiple clears denominators, its leading degree survives modulo the
prime, and the reduced polynomial splits over the residue field.
-/

namespace Towers.CField.PDensit

open IsDedekindDomain NumberField Polynomial
open Towers.CField.ARecip

noncomputable section

universe u

/-- **Corollary VI.3.5 (source statement).**  If a polynomial over a number
field splits into linear factors modulo all but finitely many finite primes,
then it already splits over the number field. -/
abbrev ChebotarevComparisonStatement
    (K : Type u) [Field K] [NumberField K] : Prop :=
  (∀ f : K[X],
        SplitsModuloAlmost f → f.Splits)

/-- The proof interfaces from Corollary V.3.24 give the repeated statement
here verbatim. -/
theorem chebotarev_reduction_comparison
    {K : Type u} [Field K] [NumberField K]
    (hchebotarev : ∀ f : K[X], CanonicalSplittingChebotarev f)
    (hcomparison : ∀ f : K[X],
      CanonicalSplittingExceptions f) :
    ChebotarevComparisonStatement K :=
  splits_modulo_chebotarev hchebotarev hcomparison

end

end Towers.CField.PDensit
