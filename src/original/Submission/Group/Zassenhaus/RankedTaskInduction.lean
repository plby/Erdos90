import Submission.Group.Zassenhaus.RankedTaskSource

/-!
# Induction over ranked child sources

A Hall-ranked child source packages both a finite emitted source and strict
lexicographic descent for every task.  This file turns that package into the
well-founded recursion principle consumed by a symbolic Hall collector.

It also records the erased-source view: every emitted symbolic factor has some
rank at which the recursive motive is available.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SPFactora
namespace RCSrc

/-- A parent induction hypothesis supplies the motive for every ranked task. -/
theorem motive_tasks
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    {motive : SPFactora H inputWeight → ℕ → Prop}
    (ih :
      ∀ child childRankDefect,
        HallRankedDescends n child childRankDefect parent parentRankDefect →
          motive child childRankDefect)
    {task : SPFactora H inputWeight × ℕ}
    (htask : task ∈ source.tasks) :
    motive task.1 task.2 :=
  ih task.1 task.2 (source.tasks_descend task htask)

/--
After erasing recursion ranks, every emitted symbolic factor still has a rank
at which the parent induction hypothesis supplies its motive.
-/
theorem rank_defect_motive
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent child : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    {motive : SPFactora H inputWeight → ℕ → Prop}
    (ih :
      ∀ descendant descendantRankDefect,
        HallRankedDescends n descendant descendantRankDefect parent
            parentRankDefect →
          motive descendant descendantRankDefect)
    (hchild : child ∈ source.factorSource) :
    ∃ childRankDefect : ℕ,
      motive child childRankDefect := by
  rcases source.rank_ranked_descends
      hchild with
    ⟨childRankDefect, _htask, hdescends⟩
  exact ⟨childRankDefect, ih child childRankDefect hdescends⟩

end RCSrc

/--
A finite Hall-ranked child-source scheduler supplies a recursion principle for
the cutoff-defect/Hall-rank relation.
-/
theorem induction_child_sources
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {motive : SPFactora H inputWeight → ℕ → Prop}
    (children :
      ∀ parent parentRankDefect,
        RCSrc (n := n) parent parentRankDefect)
    (step :
      ∀ parent parentRankDefect,
        (∀ task ∈ (children parent parentRankDefect).tasks,
          motive task.1 task.2) →
            motive parent parentRankDefect)
    (factor : SPFactora H inputWeight)
    (rankDefect : ℕ) :
    motive factor rankDefect :=
  descends_induction_children
    (fun parent parentRankDefect =>
      (children parent parentRankDefect).tasks)
    (fun parent parentRankDefect task htask =>
      (children parent parentRankDefect).tasks_descend task htask)
    step factor rankDefect

end SPFactora
end TCTex
end Submission
