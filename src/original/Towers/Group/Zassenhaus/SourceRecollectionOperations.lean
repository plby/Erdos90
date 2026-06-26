import Towers.Group.Zassenhaus.ReductionComparison

/-!
# Operations on symbolic Hall-power source recollections

An upward recollection of a symbolic source can be inverted without running
the collector again.  Inverting both lists preserves truncation and physical
support, while list evaluation changes by group inversion on both sides.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- Semantic upward recollection of an arbitrary symbolic factor source. -/
structure TSRecol
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (rawSource : List (SPFactora H inputWeight)) where
  higherSource : List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_weight_least :
    SPFactora.WordWeightLeast lowerWeight higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q rawSource

namespace TSRecol

/-- Invert an upward recollection by inverting its collected source. -/
noncomputable def inverse
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {rawSource : List (SPFactora H inputWeight)}
    (recollection :
      TSRecol
        (n := n) (lowerWeight := lowerWeight) H rawSource) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
        (SPFactora.inverseList rawSource) where
  higherSource := SPFactora.inverseList recollection.higherSource
  higher_source_truncated :=
    SPFactora.truncated_inverse_list
      recollection.higher_source_truncated
  higher_weight_least :=
    SPFactora.least_inverse_list
      recollection.higher_weight_least
  list_higher_raw := by
    intro q
    rw [SPFactora.list_eval_inverse,
      SPFactora.list_eval_inverse,
      recollection.list_higher_raw]

end TSRecol

end TCTex
end Towers
