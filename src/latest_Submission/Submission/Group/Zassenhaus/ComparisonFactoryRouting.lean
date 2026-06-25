import
Submission.Group.Zassenhaus.ResidualFactoryComparison
import Submission.Group.Zassenhaus.ResidualReachableScheduler

/-!
# Ranked residual routing from comparison recollections

The reachable Hall-ranked scheduler consumes a factory for child-to-parent
outer residuals.  Such a factory can be recovered from independently
recollected atomic-to-child comparisons and full basic residuals.

This file packages those smaller inputs as routing data and connects the
quotient construction directly to ranked scheduling.  It is intentionally
not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Local ranked-routing inputs with outer residuals represented by independently
recollected atomic-to-child comparisons and full basic residuals.
-/
structure
    FRData
    {d n inputWeight : ℕ} where
  factory :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)
            (factor.word.weight PEAddres.weight)
  sharp :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d)
  nextNormalizer :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
          (concreteBasicCommutators.{u} d)
  comparisonFactory :
    TruncatedComparisonFactory
      d n inputWeight
  residualFactory :
    ReductionRecollectionFactory
      d n inputWeight

namespace
  FRData

open
  IRFtry

/--
Recover the ordinary outer-factory routing data consumed by both unrestricted
and reachable ranked schedulers.
-/
noncomputable def outerFactoryRouting
    {d n inputWeight : ℕ}
    (routing :
      FRData
        (d := d) (n := n) (inputWeight := inputWeight)) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) where
  factory := routing.factory
  sharp := routing.sharp
  nextNormalizer := routing.nextNormalizer
  outerFactory :=
    comparisonResidualFactories routing.comparisonFactory
      routing.residualFactory

/--
A correction schedule and strictly deeper normalizers supply the operational
part of comparison-factory routing.
-/
noncomputable def
    schedule_residual_factories
    {d n inputWeight : ℕ}
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (comparisonFactory :
      TruncatedComparisonFactory
        d n inputWeight)
    (residualFactory :
      ReductionRecollectionFactory
        d n inputWeight) :
    FRData
      (d := d) (n := n) (inputWeight := inputWeight) where
  factory factor :=
    schedule.factory
      (factor.word.weight PEAddres.weight)
  sharp factor :=
    SSNormal.ofNormalizerAbove
      (normalizerAbove
        (factor.word.weight PEAddres.weight))
  nextNormalizer factor :=
    normalizerAbove
      (factor.word.weight PEAddres.weight)
      (factor.word.weight PEAddres.weight + 1) (by omega)
  comparisonFactory := comparisonFactory
  residualFactory := residualFactory

end
  FRData

end TCTex
end Submission
