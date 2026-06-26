import Submission.Group.Zassenhaus.RankedTaskInduction
import Submission.Group.Zassenhaus.SourceRecollectionComposition

/-!
# Composing concrete residual recollections over ranked child tasks

Every ranked outer-bracket task eventually supplies a concrete basic-reduction
residual recollection.  Those recollections have task-specific support bounds.
This file weakens them to one common bound and folds a finite ranked child
source into a single recollection of all child residual sources.

This is the finite recursive-composition layer used after Hall-rank scheduling.
This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HEWord

namespace
  TSRecollb

/-- View a concrete basic residual recollection at any weaker support bound. -/
noncomputable def toRecollectionAt
    {d n inputWeight lowerWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (recollection :
      TSRecollb
        (n := n) factor)
    (hlowerWeight :
      lowerWeight ≤
        factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (basicRawSource factor) where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least := by
    intro x hx
    exact hlowerWeight.trans
      (recollection.higher_least_succ x hx)
  list_higher_raw :=
    recollection.list_higher_raw

end
  TSRecollb

namespace SPFactora
namespace RCSrc

/--
Fold concrete basic residual recollections for all ranked children into one
recollection of their concatenated raw residual sources.
-/
noncomputable def flatRawSource
    {d n inputWeight lowerWeight parentRankDefect : ℕ}
    {parent :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (source :
      RCSrc (n := n) parent parentRankDefect)
    (residual :
      ∀ task ∈ source.tasks,
        TSRecollb
          (n := n) task.1)
    (hlowerWeight :
      ∀ task ∈ source.tasks,
        lowerWeight ≤
          task.1.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (source.tasks.flatMap fun task =>
        basicRawSource task.1) :=
  TSRecol.flatMap
    source.tasks
    (fun task => basicRawSource task.1)
    (fun task htask =>
      (residual task htask).toRecollectionAt
        (hlowerWeight task htask))

end RCSrc
end SPFactora

namespace CBWorka

/--
Every ranked child emitted by an inner-packet outer-bracket worklist has
residual support at least one layer above the original inner packet.
-/
theorem task_ranked_tasks
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (unchanged : HallTree (FreeGenerator.{u} d))
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask : task ∈ rankedTasks packet hinputWeight inner right unchanged) :
    inner.word.weight PEAddres.weight + 1 ≤
      task.1.word.weight PEAddres.weight + 1 := by
  rcases
      factor_ranked_tasks
        packet hinputWeight inner right unchanged htask with
    ⟨x, hx, rfl⟩
  exact Nat.add_le_add_right
    (weight_least_factors packet hinputWeight inner right x hx) 1

/--
Fold recursively supplied child residual recollections for the concrete
ranked task list at the common support bound one layer above the inner packet.
-/
noncomputable def basicSourcesRecollection
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (unchanged : HallTree (FreeGenerator.{u} d))
    (residual :
      ∀ task ∈ rankedTasks packet hinputWeight inner right unchanged,
        TSRecollb
          (n := n) task.1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      ((rankedTasks packet hinputWeight inner right unchanged).flatMap
        fun task => basicRawSource task.1) :=
  TSRecol.flatMap
    (rankedTasks packet hinputWeight inner right unchanged)
    (fun task => basicRawSource task.1)
    (fun task htask =>
      (residual task htask).toRecollectionAt
        (task_ranked_tasks
          packet hinputWeight inner right unchanged htask))

end CBWorka
end TCTex
end Submission
