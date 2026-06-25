import Submission.Group.Zassenhaus.BracketLexicographicScheduling

/-!
# Ranked child sources for concrete inner-packet outer brackets

The lexicographic scheduler attaches a Hall-rank defect to every factor in an
exact inner-packet outer-bracket worklist.  This file packages those ranked
children together with their strict descent proof and records that forgetting
the ranks recovers the original exact symbolic source.

This is the source-facing interface needed by a recursive Hall collector.
This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace SPFactora

/--
A finite symbolic source whose factors carry ranks strictly below one parent
task in the cutoff-defect/Hall-rank relation.
-/
structure RCSrc
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (parent : SPFactora H inputWeight)
    (parentRankDefect : ℕ) where
  tasks : List (SPFactora H inputWeight × ℕ)
  tasks_descend :
    ∀ task ∈ tasks,
      HallRankedDescends n task.1 task.2 parent parentRankDefect

namespace RCSrc

/-- Forget the recursion ranks and retain the emitted symbolic factors. -/
def factorSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect) :
    List (SPFactora H inputWeight) :=
  source.tasks.map Prod.fst

/-- Every emitted factor has a rank making it a strict child of the parent. -/
theorem rank_ranked_descends
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent factor : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    (hfactor : factor ∈ source.factorSource) :
    ∃ rankDefect : ℕ,
      (factor, rankDefect) ∈ source.tasks ∧
        HallRankedDescends n factor rankDefect parent parentRankDefect := by
  rw [factorSource] at hfactor
  rcases List.mem_map.mp hfactor with ⟨task, htask, hfactor⟩
  subst factor
  exact ⟨task.2, by simpa using htask, source.tasks_descend task htask⟩

end RCSrc
end SPFactora

namespace CBWorka

open HEWord

/--
Package the exact concrete outer-bracket worklist as a finite list of strict
Hall-ranked child tasks.
-/
noncomputable def rankedTaskSource
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
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactora.RCSrc
      (n := n) inner
        (HallTree.bracketRankDefect
          ((tree inner.word).weight + unchanged.weight)
          originalLeft originalRight) where
  tasks := rankedTasks packet hinputWeight inner right unchanged
  tasks_descend := by
    intro task htask
    exact
      ranked_descends_tasks packet hinputWeight inner right
        hinnerTruncated added originalRight unchanged originalLeft hinnerTree
          hRightLeft hRightUnchanged hunchangedBasic htask

/-- Forgetting task ranks recovers the exact concrete worklist source. -/
@[simp]
theorem factor_ranked_task
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
    (hunchangedBasic : unchanged.IsBasic) :
    (rankedTaskSource packet hinputWeight inner right hinnerTruncated added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic).factorSource =
      factors packet hinputWeight inner right := by
  simp [rankedTaskSource,
    SPFactora.RCSrc.factorSource, rankedTasks,
    List.map_map, Function.comp_def]

/--
The factor source underlying the ranked children still evaluates exactly to
the outer bracket of the reduced inner packet and the unchanged right factor.
-/
theorem list_ranked_task
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
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (rankedTaskSource packet hinputWeight inner right hinnerTruncated added
          originalRight unchanged originalLeft hinnerTree hRightLeft
            hRightUnchanged hunchangedBasic).factorSource =
      ⁅SPFactora.listEval (n := n) q
          (basicReductionFactors inner),
        right.eval (n := n) q⁆ := by
  rw [factor_ranked_task]
  exact listEval_factors packet hinputWeight inner right q

/-- The ranked factor source remains physically truncated. -/
theorem truncated_ranked_task
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
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactora.IsTruncated n
      (rankedTaskSource packet hinputWeight inner right hinnerTruncated added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic).factorSource := by
  rw [factor_ranked_task]
  exact isTruncated_factors packet hinputWeight inner right hinnerTruncated

/-- The ranked factor source retains the inner packet's support bound. -/
theorem least_ranked_task
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
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactora.WordWeightLeast
      (inner.word.weight PEAddres.weight)
      (rankedTaskSource packet hinputWeight inner right hinnerTruncated added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic).factorSource := by
  rw [factor_ranked_task]
  exact weight_least_factors packet hinputWeight inner right

end CBWorka
end TCTex
end Submission
