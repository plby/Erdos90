import Submission.Group.Zassenhaus.ReductionOuter
import Submission.Group.Zassenhaus.ResidualRecursion

/-!
# Local branches for Hall-ranked concrete residual recursion

The global Hall-ranked residual scheduler is assembled from one local branch
for every ranked symbolic factor.  A branch packages its strict child source
with the step that reconstructs the parent's concrete basic residual from
recursive recollections of those children.

This file records that intermediate interface and instantiates it for
recipe-correct inner reduction under an outer bracket.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
One local step of Hall-ranked concrete residual recursion: a strict child
source and a constructor for the parent's residual recollection.
-/
structure RRBrancha
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) where
  children :
    SPFactora.RCSrc
      (n := n) factor rankDefect
  recollect :
    (∀ task ∈ children.tasks,
      TSRecollb
        (n := n) task.1) →
      TSRecollb
        (n := n) factor

namespace
  RRSchedua

/-- Assemble a global Hall-ranked scheduler from one local branch per task. -/
noncomputable def ofBranches
    {d n inputWeight : ℕ}
    (branches :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        RRBrancha
          (n := n) factor rankDefect) :
    RRSchedua
      (d := d) (n := n) (inputWeight := inputWeight) where
  children factor rankDefect := (branches factor rankDefect).children
  recollect factor rankDefect residual :=
    (branches factor rankDefect).recollect residual

/--
Run well-founded Hall-ranked recursion directly from one local branch per
ranked factor.
-/
noncomputable def residual_recollection_branches
    {d n inputWeight : ℕ}
    (branches :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        RRBrancha
          (n := n) factor rankDefect)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) :
    TSRecollb
      (n := n) factor :=
  (ofBranches branches).residualRecollection factor rankDefect

end
  RRSchedua

namespace RRBrancha

open
  TSRecollb

/--
Recipe-correct reduction of an inner Hall tree under one unchanged outer
right tree gives a complete local Hall-ranked residual branch.
-/
noncomputable def inner_outer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      HEWord.tree innerWord =
        .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    RRBrancha
      (n := n) factor
      (HallTree.bracketRankDefect
        ((HEWord.tree innerWord).weight + unchanged.weight)
        originalLeft originalRight) where
  children :=
    CIChildr.rankedTaskSource
      (n := n) factor innerWord rightWord hword added originalRight unchanged
        originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
  recollect residual :=
    ranked_task_residuals
      hn hH family factor innerWord rightWord hword hfactorTruncated added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic residual

end RRBrancha

end TCTex
end Submission
