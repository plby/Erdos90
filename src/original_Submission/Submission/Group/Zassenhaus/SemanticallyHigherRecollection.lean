import Submission.Group.Zassenhaus.SourceRecollectionOperations
import Submission.Group.Zassenhaus.CoordinateEndpointStrata

/-!
# Recollecting semantically higher symbolic Hall-power sources

A symbolic source can be physically supported in one Hall-weight stratum
while its evaluated product starts one lower-central layer higher.  Normalize
the source at its physical support bound.  The lower-central membership
hypothesis forces the normalized active coordinate block to vanish, so the
strictly higher coordinate tail recollects the original source.

This is the non-atomic analogue of the final tail extraction in atomic source
normalization.  It assumes a current-stratum semantic normalizer rather than
constructing that normalizer from atomic factors.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TSNormalb

/--
Extract an upward recollection from a physically supported source whose
evaluated product starts one lower-central layer higher.
-/
noncomputable def source_recollection_series
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H)
    (source : List (SPFactora H inputWeight))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hsourceTruncated : SPFactora.IsTruncated n source)
    (hsourceSupported :
      SPFactora.WordWeightLeast lowerWeight source)
    (hsourceMem :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q source ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1) H source := by
  let normalization :=
    normalizer.normalize source hsourceTruncated hsourceSupported
  let coordinates := Classical.choose normalization
  have hcoordinates := (Classical.choose_spec normalization).1
  have heval := (Classical.choose_spec normalization).2
  refine
    {
      higherSource := coordinates.tailFactors (n := n) lowerWeight
      higher_source_truncated :=
        coordinates.truncated_factors (by omega)
      higher_weight_least :=
        coordinates.word_least_factors
      list_higher_raw := ?_
    }
  intro q
  have hcoordinatesMem :
      collectedHallProduct (n := n) H (coordinates.eval q) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          lowerWeight := by
    rw [← coordinates.listEval_factors, heval q]
    exact hsourceMem q
  have hactiveCoordinates :
      coordinates.eval q lowerWeight = 0 := by
    exact
      imp_coordinates_below
        (r := lowerWeight + 1) hn H hH (coordinates.eval q)
          (by simpa using hcoordinatesMem) lowerWeight hlowerWeightPos
            (by omega) hlowerWeightTruncated
  rw [← heval q,
    coordinates.append_no_below
      hcoordinates hlowerWeightPos (by omega),
    SPFactora.listEval_append,
    coordinates.list_weight_factors,
    hactiveCoordinates,
    BCWta.collected_weight_productzero,
    one_mul]

end TSNormalb

end TCTex
end Submission
