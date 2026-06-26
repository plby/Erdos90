import
  Submission.Group.Zassenhaus.FixedRestartRouting
import Submission.Group.Zassenhaus.CanonicalHallRecollection

/-!
# Fixed-packet global polynomial boundary for generated structural restarts

The global automatic comparison collector uses one selected Hall-Petresco
packet.  Fixed-packet generated structural restart routing provides its
basic-residual recollections without assuming ordered splits for unrelated
packets at the same cutoff.

This file packages the corrected final adapter.  Construction of the
arbitrary-cutoff canonical packet and its remaining local recursion data stay
visible as explicit obligations.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open RRSchedua

/--
Fixed-packet generated structural restart inputs sufficient to construct the
automatic comparison collector and hence the global Claim 5 polynomials.
-/
structure
    SRBuilda
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  hinputWeight :
    0 < inputWeight
  routing :
    PRRouteb
      d n inputWeight packet hinputWeight
  normalizerAbove :
    ∀ lowerWeight strongerWeight : ℕ,
      lowerWeight < strongerWeight →
        TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d)
  cases :
    ∀ (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (rankDefect : ℕ),
      TruncatedBranchCase
        (n := n) factor rankDefect
  rankDefect :
    ∀ _factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      ℕ

namespace
  SRBuilda

/-- The selected cutoff packet supplies every correction stratum. -/
noncomputable def supportedCorrectionFactory
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      SRBuilda.{u}
        (inputWeight := inputWeight) hn hH) :
    TFSched
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d) where
  factory lowerWeight :=
    (builder.packet.powerSupportedFactory
      builder.hinputWeight lowerWeight)
      |>.correctionPacketFactory

/--
Compile fixed-packet generated structural restarts into the automatic
comparison collector consumed by global coordinate-polynomial construction.
-/
noncomputable def automaticComparisonCollection
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      SRBuilda.{u}
        (inputWeight := inputWeight) hn hH) :
    ACBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  basicResidual _lowerWeight _hnonterminal factor _hfactorWeight
      _hfactorTruncated :=
    structural_restart_cases
      hn hH builder.routing builder.supportedCorrectionFactory
        builder.normalizerAbove builder.cases factor (builder.rankDefect factor)

end
  SRBuilda

namespace TSInput

/--
For canonical Hall families, fixed-packet generated structural restart routing
constructs the Claim 5 coordinate polynomials.
-/
theorem
    coordRestartBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      SRBuilda.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.automaticComparisonBuilder
    hn hsourceSupported builder.automaticComparisonCollection
      hinputWeight

end TSInput

end TCTex
end Submission
