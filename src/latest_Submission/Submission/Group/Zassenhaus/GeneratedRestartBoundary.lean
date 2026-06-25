import Submission.Group.Zassenhaus.GeneratedRestartRouting
import Submission.Group.Zassenhaus.CanonicalHallRecollection

/-!
# Global polynomial boundary for generated structural restarts

The automatic comparison collector constructs Claim 5 coordinate polynomials
once every concrete basic-reduction residual has an upward recollection.
Generated structural restart routing and Hall-ranked recursion provide those
residual recollections from a finite collection of explicit local inputs.

This file packages that final adapter.  It does not hide the remaining
arbitrary-cutoff obligations: packet ordering, smaller-root restarts, active
powered recollections, deeper normalizers, and Hall-ranked branch cases remain
visible in the routing fields.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Generated structural restart inputs sufficient to construct the automatic
comparison collector and hence the global Claim 5 coordinate polynomials.
-/
structure
    GSRestar
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
    CSRestara
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
  GSRestar

/-- The cutoff Hall-Petresco packet supplies every correction stratum. -/
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
      GSRestar.{u}
        (inputWeight := inputWeight) hn hH) :
    TFSched
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d) where
  factory lowerWeight :=
    (builder.packet.powerSupportedFactory
      builder.hinputWeight lowerWeight)
      |>.correctionPacketFactory

/--
Compile generated structural restart routing into the automatic comparison
collector consumed by global coordinate-polynomial construction.
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
      GSRestar.{u}
        (inputWeight := inputWeight) hn hH) :
    ACBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  basicResidual _lowerWeight _hnonterminal factor _hfactorWeight
      _hfactorTruncated :=
    RRSchedua.recollect_restart_cases
      hn hH builder.routing builder.supportedCorrectionFactory
        builder.normalizerAbove builder.cases factor (builder.rankDefect factor)

end
  GSRestar

namespace TSInput

/--
For canonical Hall families, generated structural restart routing constructs
the Claim 5 coordinate polynomials.
-/
theorem
    structuralRestartBuilder
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
      GSRestar.{u}
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
