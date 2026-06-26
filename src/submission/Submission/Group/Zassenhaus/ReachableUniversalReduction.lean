import Submission.Group.Zassenhaus.SemanticNormalizerRecursion
import Submission.Group.Zassenhaus.SemanticInsertionDerivations
import Submission.Group.Zassenhaus.SemanticPacketFactories

/-!
# Reachable universal boundary for symbolic Hall-power recollection

The high-weight semantic normalizer closes recursion as soon as
`n ≤ 2 * lowerWeight`.  Consequently, a universal powered Hall collector
should not be required to provide insertion derivations in that unreachable
region.  Moreover, in the remaining class-two band `n ≤ 3 * lowerWeight`,
correction packets are automatic.

This file records the exact reachable operational boundary:

* custom insertion derivations are required only while
  `¬ n ≤ 2 * lowerWeight`;
* custom correction packets are required only while
  `¬ n ≤ 3 * lowerWeight`;
* the intermediate class-two band uses the existing automatic packet factory.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
The reachable recursive insertion obligation.  The insertion kernel is
requested only below the commutative high-weight terminal region.
-/
structure ReachableRecursiveSemantic
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) :
    Prop where
  insert :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          TSInserta
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight) H

namespace TSNormalb

/--
Reachable successive-stratum insertion plus the commutative terminal case
constructs a semantic normalizer at every support stratum.
-/
noncomputable def reachable_rec_insertion
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (step :
      ReachableRecursiveSemantic
        (n := n) (inputWeight := inputWeight) H)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H :=
  if hterminal : n ≤ 2 * lowerWeight then
    of_highWeight hn H hH hterminal
  else
    ofInsertionKernel
      (step.insert lowerWeight hterminal
        (reachable_rec_insertion hn H hH step (lowerWeight + 1)))
termination_by n - lowerWeight
decreasing_by omega

end TSNormalb

/-- List-valued More3 derivations for every reachable active stratum. -/
structure
    RIDeriva
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) :
    Prop where
  insert :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          ∀ (coordinates : CCExpans H inputWeight)
            (factor : SPFactora H inputWeight),
            coordinates.NTBelow lowerWeight →
            lowerWeight ≤
              factor.word.weight PEAddres.weight →
            factor.word.weight PEAddres.weight < n →
              ∃ next : CCExpans H inputWeight,
                next.NTBelow lowerWeight ∧
                  SSInsertc
                    (n := n) H inputWeight lowerWeight
                      (coordinates.factors (n := n)) factor
                        (next.factors (n := n))

namespace
  RIDeriva

/-- Reachable More3 derivations supply the reachable semantic insertion step. -/
def reachableRecursiveSemantic
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      RIDeriva
        (n := n) (inputWeight := inputWeight) H) :
    ReachableRecursiveSemantic
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight hnonterminal normalizer :=
    { insert := by
        intro coordinates factor hcoordinates hfactorSupported
          hfactorTruncated
        rcases schedule.insert lowerWeight hnonterminal normalizer coordinates
            factor hcoordinates hfactorSupported hfactorTruncated with
          ⟨next, hnextSupported, hinsert⟩
        exact ⟨next, hnextSupported, hinsert.listEval_eq⟩ }

end
  RIDeriva

/--
The exact remaining reachable universal derivation builder.

Above the commutative terminal it is never called.  In the class-two band it
receives the automatic packet factory; below that band it receives the custom
factory supplied by `correctionFactory`.
-/
structure
    TDBuild
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  correctionFactory :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 3 * lowerWeight →
        TSFtrya
          (n := n) (inputWeight := inputWeight) H lowerWeight
  insert :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          TSFtrya
              (n := n) (inputWeight := inputWeight) H lowerWeight →
            ∀ (coordinates : CCExpans H inputWeight)
              (factor : SPFactora H inputWeight),
              coordinates.NTBelow lowerWeight →
              lowerWeight ≤
                factor.word.weight PEAddres.weight →
              factor.word.weight PEAddres.weight < n →
                ∃ next : CCExpans H inputWeight,
                  next.NTBelow lowerWeight ∧
                    SSInsertc
                      (n := n) H inputWeight lowerWeight
                        (coordinates.factors (n := n)) factor
                          (next.factors (n := n))

namespace
  TDBuild

open TSNormalb

/-- Use the automatic class-two packets whenever the active stratum permits it. -/
def packetFactoryAt
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (builder :
      TDBuild
        (n := n) (inputWeight := inputWeight) H)
    (lowerWeight : ℕ) :
    TSFtrya
      (n := n) (inputWeight := inputWeight) H lowerWeight :=
  if hclassTwo : n ≤ 3 * lowerWeight then
    TSFtrya.of_classTwo
      H hclassTwo
  else
    builder.correctionFactory lowerWeight hclassTwo

/-- A reachable universal builder supplies the reachable More3 schedule. -/
def reachableRecursiveDerivation
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (builder :
      TDBuild
        (n := n) (inputWeight := inputWeight) H) :
    RIDeriva
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight hnonterminal normalizer :=
    builder.insert lowerWeight hnonterminal normalizer
      (builder.packetFactoryAt H lowerWeight)

/-- A reachable universal builder supplies a semantic normalizer at every stratum. -/
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
      TDBuild
        (n := n) (inputWeight := inputWeight) H)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H :=
  reachable_rec_insertion hn H hH
    (builder.reachableRecursiveDerivation
      |>.reachableRecursiveSemantic)
    lowerWeight

end
  TDBuild

namespace TSInput

/--
A reachable universal powered builder and graded Hall bases construct the
integer-valued coordinate polynomials required by Claim 5.
-/
theorem
    reachableDerivationBuilder
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
      TDBuild
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.supportedSemanticNormalizer
    hsourceSupported
      (builder.semanticCoordinateNormalizer hn H hH inputWeight)
        hinputWeight

end TSInput

end TCTex
end Submission
