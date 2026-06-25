import Towers.Group.Zassenhaus.Active
import Towers.Group.Zassenhaus.SharpHigherRouting

/-!
# Eliminating the separate symbolic Hall-power higher-tail obligation

Sharp correction normalization and cutoff-defect multiset recursion construct
the higher-tail route schedule from stratum-indexed packet factories.  A sharp
normalizer family also supplies singleton factor residual routes directly.
Consequently, once fixed-weight active-block merge routes are available, the
remaining active insertion step and Claim 5 polynomial data follow without a
separate higher-tail routing hypothesis.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
Universal higher-word correction factories available at every support
stratum.
-/
structure SFScheda
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  factory :
    ∀ lowerWeight : ℕ,
      SEFtry
        (n := n) (inputWeight := inputWeight) H lowerWeight

namespace SFScheda

/-- Truncate every universal correction factory to obtain semantic packets. -/
def supportedCorrectionFactory
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      SFScheda
        (n := n) (inputWeight := inputWeight) H) :
    TFSched
      (n := n) (inputWeight := inputWeight) H where
  factory lowerWeight :=
    (schedule.factory lowerWeight).correctionPacketFactory

/--
Universal higher-word correction factories and a sharp normalizer family
construct recursive higher-tail routes.
-/
noncomputable def recursiveSemanticSchedule
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      SFScheda
        (n := n) (inputWeight := inputWeight) H)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H) :
    RHRoute
      (n := n) (inputWeight := inputWeight) H :=
  schedule.supportedCorrectionFactory
    |>.recursiveSemanticSchedule family

end SFScheda

namespace TDBuildb

/-- A universal builder exposes its correction factories stratum by stratum. -/
def expansionFactorySchedule
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H) :
    SFScheda
      (n := n) (inputWeight := inputWeight) H where
  factory := builder.correctionFactory

/--
The correction factories and recursively constructed normalizers carried by a
universal builder discharge its higher-tail routing obligation.
-/
noncomputable def sharpRecursiveSchedule
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
        (n := n) (inputWeight := inputWeight) H) :
    RHRoute
      (n := n) (inputWeight := inputWeight) H :=
  builder.expansionFactorySchedule
    |>.recursiveSemanticSchedule
      (builder.supportedSemanticFamily hn H hH)

end TDBuildb

namespace TRSched

/--
A sharp normalizer family supplies the singleton factor route omitted by the
merge-only active-block schedule.
-/
noncomputable def activeNormalizerFamily
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (schedule :
      TRSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H) :
    RRSchedb
      (n := n) (inputWeight := inputWeight) hn H hH where
  routeMerge := schedule.routeMerge
  routeFactor lowerWeight _normalizer factor hfactorWeight hfactorTruncated :=
    (TANorm.ofNormalizer
      (family.normalizer lowerWeight) factor (by omega)
        hfactorTruncated).factorResidualRoute hn H hH hfactorWeight
          hfactorTruncated

/--
Merge-only active-block routes, correction packets, and a sharp normalizer
family construct the complete filtration-recursive semantic insertion step.
-/
noncomputable def recursiveSharpRouting
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (schedule :
      TRSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (packetSchedule :
      TFSched
        (n := n) (inputWeight := inputWeight) H)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H :=
  TDSched.recSemanticInsertion
    (schedule.activeNormalizerFamily family
      |>.delegatedRouteSchedule)
    (packetSchedule.recursiveSemanticSchedule family)

end TRSched

namespace TSInput

/--
Fixed-weight More3 merge routes, stratum-indexed correction packets, and a
sharp normalizer family construct the Claim 5 polynomial data.
-/
theorem
  mergeSharpRouting
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
    (schedule :
      TRSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (packetSchedule :
      TFSched
        (n := n) (inputWeight := inputWeight) H)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported
      (schedule.recursiveSharpRouting
        packetSchedule family)
      hinputWeight

/--
The universal builder discharges the formerly separate higher-tail schedule in
the merge-only Claim 5 reduction.
-/
theorem coordRouteBuilder
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
    (schedule :
      TRSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordMergeHigher
    hn H hH hsourceSupported schedule builder
      (builder.sharpRecursiveSchedule
        hn H hH)
      hinputWeight

end TSInput

end TCTex
end Towers
