import Towers.Group.Zassenhaus.SharpActiveInterleaving

/-!
# Sharp symbolic Hall-power collector reduction

Sharp correction packets and a stratum-indexed normalizer family now provide
all nonterminal routing operations.  Stable interleaving constructs the
fixed-weight merge residual route, sharp normalization supplies singleton
factor residual routes, and cutoff-defect recursion supplies higher-tail
routes.

This file packages those constructions into the recursive semantic insertion
step and removes the formerly separate active-block merge schedule hypothesis
from the Claim 5 reduction.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace TFSched

open TANorm

/--
A stratum-indexed packet supply and a sharp normalizer family construct every
delegated active-block residual route.
-/
noncomputable def delegatedSharpInterleaving
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight) H)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H) :
    TDSched
      (n := n) (inputWeight := inputWeight) hn H hH where
  routeMerge lowerWeight _normalizer coordinates factor _hcoordinates
      _hfactorWeight _hfactorTruncated :=
    (schedule.factory lowerWeight)
      |>.supportedDelegatedMerge
        hn H hH family coordinates factor
  routeFactor lowerWeight _normalizer factor hfactorWeight hfactorTruncated :=
    (ofNormalizer (family.normalizer lowerWeight) factor (by omega)
        hfactorTruncated).factorResidualRoute hn H hH hfactorWeight
          hfactorTruncated

/--
Sharp active-block interleaving and sharp higher-tail recursion construct the
complete filtration-recursive semantic insertion step.
-/
noncomputable def recursiveSharpInterleaving
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight) H)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H :=
  (schedule.delegatedSharpInterleaving
      hn H hH family).recSemanticInsertion
    (schedule.recursiveSemanticSchedule family)

end TFSched

namespace TDBuildb

/--
A universal builder carries enough sharp data to construct the complete
filtration-recursive semantic insertion step.
-/
noncomputable def sharpRecursiveInsertion
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
    RIStep
      (n := n) (inputWeight := inputWeight) H :=
  builder.expansionFactorySchedule
    |>.supportedCorrectionFactory
    |>.recursiveSharpInterleaving
      hn H hH (builder.supportedSemanticFamily hn H hH)

end TDBuildb

namespace TSInput

/--
A universal semantic builder now discharges active-block merge routing,
singleton factor routing, and higher-tail routing.  It therefore constructs
the Claim 5 coordinate-polynomial data without separate operational schedule
hypotheses.
-/
theorem builderSharpInterleaving
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
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported
      (builder.sharpRecursiveInsertion hn H hH)
      hinputWeight

end TSInput

end TCTex
end Towers
