import Submission.Group.Zassenhaus.SourceRecollectionOperations

/-!
# Congruence for symbolic source recollections

Semantic recollection depends only on the evaluated value of a raw symbolic
source.  A recollected source can therefore be reused for any pointwise
evaluation-equivalent raw source.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace TSRecol

/-- Transport a semantic recollection across pointwise source evaluation equality. -/
def of_list_eq
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {source target : List (SPFactora H inputWeight)}
    (recollection :
      TSRecol
        (n := n) (lowerWeight := lowerWeight) H source)
    (heval :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q source =
          SPFactora.listEval q target) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H target where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := by
    intro q
    exact (recollection.list_higher_raw q).trans (heval q)

end TSRecol
end TCTex
end Submission
