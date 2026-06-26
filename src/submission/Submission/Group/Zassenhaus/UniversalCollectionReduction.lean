import Submission.Group.Zassenhaus.UniversalCorrectionFactories

/-!
# Universal symbolic Hall-power collection reduction

The standalone theory has now separated the two inputs required from a
universal powered Hall collector:

* higher-word correction identities for each supported adjacent swap; and
* a canonical endpoint builder whose derivation recursively routes the
  normalized higher correction blocks emitted by those swaps.

This file packages those inputs together.  A universal one-stratum derivation
builder supplies the schedule used by filtration recursion, and therefore
constructs the integer-valued coordinate polynomials required by Claim 5.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
The exact remaining one-stratum operational constructor.  For each support
stratum it receives the recursively constructed next-stratum semantic
normalizer and the universal powered-commutator correction identities.  It
must recollect one supported truncated factor into a canonical coordinate
endpoint, witnessed by the list-valued semantic insertion derivation.
-/
structure TDBuildb
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  correctionFactory :
    ∀ lowerWeight : ℕ,
      SEFtry
        (n := n) (inputWeight := inputWeight) H lowerWeight
  insert :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCExpans H inputWeight)
          (factor : SPFactora H inputWeight),
          coordinates.NTBelow lowerWeight →
          lowerWeight ≤ factor.word.weight PEAddres.weight →
          factor.word.weight PEAddres.weight < n →
            ∃ next : CCExpans H inputWeight,
              next.NTBelow lowerWeight ∧
                SSInsertc
                  (n := n) H inputWeight lowerWeight
                    (coordinates.factors (n := n)) factor
                      (next.factors (n := n))

namespace TDBuildb

/--
A universal derivation builder supplies the structured one-stratum insertion
schedule consumed by filtration recursion.
-/
def insertionDerivationSchedule
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H) :
    SIDeriva
      (n := n) (inputWeight := inputWeight) H where
  insert := builder.insert

/--
A universal derivation builder also supplies the semantic normalizer at every
stratum by well-founded filtration recursion.
-/
noncomputable def semanticCoordinateNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H :=
  TSNormalb.recInsertionStep
    hn H hH
      (builder.insertionDerivationSchedule
        |>.recursiveCoordinateInsertion
        |>.recSemanticInsertion)
      lowerWeight

end TDBuildb

namespace TSInput

/--
A correctly sourced repeated-block input and a universal semantic collection
builder construct the integer-valued coordinate polynomials required by
Claim 5.
-/
theorem universalDerivationBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveInsertionDerivation
    hn H hH hsourceSupported
      builder.insertionDerivationSchedule
        hinputWeight

end TSInput

end TCTex
end Submission
