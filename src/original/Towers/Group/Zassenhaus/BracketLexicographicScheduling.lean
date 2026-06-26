import Towers.Group.Zassenhaus.Packet

/-!
# Lexicographic scheduling for outer brackets

The cutoff-defect/Hall-rank relation is useful to a recursive collector only
after finite emitted sources are packaged as child tasks.  This file records
the generic finite-child recursion principle and constructs the child-task
list emitted by one concrete inner-packet outer-bracket worklist.

This is the scheduler-facing interface for the lexicographic descent proved
in the preceding module.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactora

/--
To prove a motive for every Hall-ranked task, it suffices to prove it from the
motive on any finite list of strictly descending child tasks.
-/
theorem descends_induction_children
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {motive : SPFactora H inputWeight → ℕ → Prop}
    (children :
      SPFactora H inputWeight →
        ℕ →
          List (SPFactora H inputWeight × ℕ))
    (children_descend :
      ∀ parent parentRankDefect child,
        child ∈ children parent parentRankDefect →
          HallRankedDescends n child.1 child.2 parent parentRankDefect)
    (step :
      ∀ parent parentRankDefect,
        (∀ child ∈ children parent parentRankDefect,
          motive child.1 child.2) →
            motive parent parentRankDefect)
    (factor : SPFactora H inputWeight)
    (rankDefect : ℕ) :
    motive factor rankDefect := by
  refine ranked_descends_induction (n := n) ?_ factor rankDefect
  intro parent parentRankDefect ih
  refine step parent parentRankDefect ?_
  intro child hchild
  exact
    ih child.1 child.2
      (children_descend parent parentRankDefect child hchild)

end SPFactora

namespace CBWorka

open HEWord

/--
Attach to every emitted worklist factor the Hall-bracket rank defect of its
outer bracket with the unchanged right tree.
-/
noncomputable def rankedTasks
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (unchanged : HallTree (FreeGenerator.{u} d)) :
    List
      (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ) :=
  (factors packet hinputWeight inner right).map fun x =>
    (x,
      HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        (tree x.word) unchanged)

/-- Membership in the ranked child-task list exposes its emitted factor. -/
theorem factor_ranked_tasks
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
    ∃ x ∈ factors packet hinputWeight inner right,
      task =
        (x,
          HallTree.bracketRankDefect
            ((tree inner.word).weight + unchanged.weight)
            (tree x.word) unchanged) := by
  rw [rankedTasks] at htask
  rcases List.mem_map.mp htask with ⟨x, hx, htask⟩
  exact ⟨x, hx, htask.symm⟩

/-- Every concrete ranked child task strictly descends from its parent task. -/
theorem ranked_descends_tasks
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask : task ∈ rankedTasks packet hinputWeight inner right unchanged) :
    SPFactora.HallRankedDescends n
      task.1 task.2 inner
        (HallTree.bracketRankDefect
          ((tree inner.word).weight + unchanged.weight)
          originalLeft originalRight) := by
  rcases
      factor_ranked_tasks
        packet hinputWeight inner right unchanged htask with
    ⟨x, hx, rfl⟩
  exact
    ranked_descends_factors packet hinputWeight inner right hx
      hinnerTruncated added originalRight unchanged originalLeft hinnerTree
        hRightLeft hRightUnchanged hunchangedBasic

/--
A parent Hall-ranked induction hypothesis supplies the motive for every
concrete child task emitted by the exact worklist.
-/
theorem motive_ranked_tasks
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    {motive :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ →
          Prop}
    (ih :
      ∀ child childRankDefect,
        SPFactora.HallRankedDescends n
            child childRankDefect inner
              (HallTree.bracketRankDefect
                ((tree inner.word).weight + unchanged.weight)
                originalLeft originalRight) →
          motive child childRankDefect)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask : task ∈ rankedTasks packet hinputWeight inner right unchanged) :
    motive task.1 task.2 :=
  ih task.1 task.2
    (ranked_descends_tasks packet hinputWeight inner right
      hinnerTruncated added originalRight unchanged originalLeft hinnerTree
        hRightLeft hRightUnchanged hunchangedBasic htask)

/--
A parent Hall-ranked induction hypothesis supplies the motive for the complete
finite list of exact worklist tasks.
-/
theorem forall_tasks_motive
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    {motive :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ →
          Prop}
    (ih :
      ∀ child childRankDefect,
        SPFactora.HallRankedDescends n
            child childRankDefect inner
              (HallTree.bracketRankDefect
                ((tree inner.word).weight + unchanged.weight)
                originalLeft originalRight) →
          motive child childRankDefect) :
    ∀ task ∈ rankedTasks packet hinputWeight inner right unchanged,
      motive task.1 task.2 := by
  intro task htask
  exact
    motive_ranked_tasks packet hinputWeight inner right hinnerTruncated
      added originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic ih htask

end CBWorka
end TCTex
end Towers
