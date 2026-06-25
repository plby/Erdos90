import Submission.Group.Zassenhaus.SourceRecollectionOperations

/-!
# Composition operations for symbolic Hall-power source recollections

Recursive collection produces finite families of independently recollected
symbolic sources.  This file records the source-level operations needed to
assemble them: the empty recollection, concatenation, and finite `flatMap`
composition.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u v

namespace TSRecol

/-- The empty source recollects to itself at every support bound. -/
def empty
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    TSRecol
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H [] where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro q
    rfl

/-- Concatenate independently recollected symbolic sources. -/
def append
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {leftSource rightSource : List (SPFactora H inputWeight)}
    (left :
      TSRecol
        (n := n) (lowerWeight := lowerWeight) H leftSource)
    (right :
      TSRecol
        (n := n) (lowerWeight := lowerWeight) H rightSource) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H (leftSource ++ rightSource) where
  higherSource := left.higherSource ++ right.higherSource
  higher_source_truncated := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_source_truncated factor hfactor
    · exact right.higher_source_truncated factor hfactor
  higher_weight_least := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_weight_least factor hfactor
    · exact right.higher_weight_least factor hfactor
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append,
      SPFactora.listEval_append,
      left.list_higher_raw,
      right.list_higher_raw]

/-- Recollect a finite `flatMap` source from recollections of its pieces. -/
def flatMap
    {α : Type v}
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (items : List α)
    (rawSource : α → List (SPFactora H inputWeight))
    (recollection :
      ∀ item ∈ items,
        TSRecol
          (n := n) (lowerWeight := lowerWeight) H (rawSource item)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H (items.flatMap rawSource) := by
  induction items with
  | nil =>
      exact empty
  | cons head tail ih =>
      exact
        append
          (recollection head (by simp))
          (ih fun item hitem => recollection item (by simp [hitem]))

end TSRecol

end TCTex
end Submission
