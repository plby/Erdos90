import Towers.Group.Zassenhaus.RankedTaskInduction
import Towers.Group.Zassenhaus.SourceRecollectionComposition

/-!
# Recollecting ranked symbolic Hall child sources

A ranked child source is consumed semantically after each of its finite tasks
has been recollected.  This file assembles those per-task recollections with
the source-level `flatMap` operation.

The singleton specialization is the direct interface for a scheduler whose
erased task list is itself the raw symbolic source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactora
namespace RCSrc

/--
Assemble a recollection of an erased ranked source from recollections of
arbitrary finite pieces indexed by its ranked tasks.
-/
noncomputable def recollection_task_sources
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    (rawSource :
      SPFactora H inputWeight × ℕ →
        List (SPFactora H inputWeight))
    (hfactorSource :
      source.factorSource = source.tasks.flatMap rawSource)
    (recollection :
      ∀ task ∈ source.tasks,
        TSRecol
          (n := n) (lowerWeight := lowerWeight) H (rawSource task)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H source.factorSource := by
  rw [hfactorSource]
  exact
    TSRecol.flatMap
      source.tasks rawSource recollection

/--
If each emitted factor recollects individually, their concatenation recollects
the complete erased ranked source.
-/
noncomputable def source_recollection_singletons
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    (recollection :
      ∀ task ∈ source.tasks,
        TSRecol
          (n := n) (lowerWeight := lowerWeight) H [task.1]) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H source.factorSource :=
  source.recollection_task_sources
    (fun task => [task.1])
    (by
      simp only [factorSource]
      induction source.tasks with
      | nil =>
          rfl
      | cons task tasks ih =>
          simp only [List.map_cons, List.flatMap_cons, List.singleton_append, ih])
    recollection

end RCSrc
end SPFactora
end TCTex
end Towers
