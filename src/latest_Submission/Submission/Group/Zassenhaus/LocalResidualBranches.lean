import Submission.Group.Zassenhaus.OuterBracketRecollection
import Submission.Group.Zassenhaus.RankedResidualRecursion
import Submission.Group.Zassenhaus.SignedReductionFactors

/-!
# Local branches for Hall-ranked concrete residual recursion

A branch packages a strict child source with the step that reconstructs the
parent residual from recursive recollections of those children.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- One local step of Hall-ranked concrete residual recursion. -/
structure TRBrancha
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) where
  children :
    SPFactor.RCSrc
      (n := n) factor rankDefect
  recollect :
    (∀ task ∈ children.tasks,
      TRRecoll
        (n := n) task.1) →
      TRRecoll
        (n := n) factor

namespace
  TRSchedu

/-- Assemble a global scheduler from one local branch per ranked factor. -/
noncomputable def ofBranches
    {d n : ℕ}
    {ι : Type}
    (branches :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        TRBrancha
          (n := n) factor rankDefect) :
    TRSchedu
      (d := d) (n := n) (ι := ι) where
  children factor rankDefect := (branches factor rankDefect).children
  recollect factor rankDefect residual :=
    (branches factor rankDefect).recollect residual

/-- Run well-founded recursion directly from one local branch per factor. -/
noncomputable def residual_recollection_branches
    {d n : ℕ}
    {ι : Type}
    (branches :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        TRBrancha
          (n := n) factor rankDefect)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) :
    TRRecoll
      (n := n) factor :=
  (ofBranches branches).residualRecollection factor rankDefect

end
  TRSchedu

namespace TRBrancha

open
  TRRecoll

/-- Recipe-correct inner reduction gives a complete local ranked branch. -/
noncomputable def inner_outer
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      CEWord.tree innerWord =
        .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    TRBrancha
      (n := n) factor
      (HallTree.bracketRankDefect
        ((CEWord.tree innerWord).weight +
          unchanged.weight)
        originalLeft originalRight) where
  children :=
    IRChildr.rankedTaskSource
      (n := n) factor innerWord rightWord hword added originalRight unchanged
        originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
  recollect residual :=
    ranked_task_residuals
      hn hH family factor innerWord rightWord hword hfactorTruncated added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic residual

end TRBrancha

end TCTex
end Submission

/-!
# Leaf branches for Hall-ranked concrete polynomial residual recursion

Several concrete residuals recollect without recursive tasks: cutoff
endpoints, basic expanded trees, self-commutators, reversed-basic words, and
weight-one factors.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SPFactor
namespace RCSrc

/-- The empty ranked source is strict for every parent task. -/
def empty
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (parent : SPFactor H ι)
    (parentRankDefect : ℕ) :
    RCSrc (n := n) parent parentRankDefect where
  tasks := []
  tasks_descend := by
    simp

@[simp]
theorem tasks_empty
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (parent : SPFactor H ι)
    (parentRankDefect : ℕ) :
    (empty (n := n) parent parentRankDefect).tasks = [] :=
  rfl

@[simp]
theorem factorSource_empty
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (parent : SPFactor H ι)
    (parentRankDefect : ℕ) :
    (empty (n := n) parent parentRankDefect).factorSource = [] :=
  rfl

end RCSrc
end SPFactor

namespace TRBrancha

open
  TRRecoll

/-- Compile an already recollected residual into a childless ranked branch. -/
noncomputable def ofResidRecollect
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (residual :
      TRRecoll
        (n := n) factor) :
    TRBrancha
      (n := n) factor rankDefect where
  children := SPFactor.RCSrc.empty
    (n := n) factor rankDefect
  recollect := fun _ => residual

/-- The truncation endpoint is a Hall-ranked leaf branch. -/
noncomputable def leaf_of_terminal
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1) :
    TRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (of_terminal factor hcutoff)

/-- A basic expanded Hall tree is a Hall-ranked leaf branch. -/
noncomputable def leaf_tree_basic
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (htreeBasic : (CEWord.tree factor.word).IsBasic) :
    TRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (tree_basic factor htreeBasic)

/-- A symbolic self-commutator is a Hall-ranked leaf branch. -/
noncomputable def leaf_commutator_self
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator word word) :
    TRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (word_commutator_self factor word hword)

/-- A reversed-basic symbolic word is a Hall-ranked leaf branch. -/
noncomputable def leaf_reversed_basic
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hreversed :
      CEWord.IsReversedBasic factor.word) :
    TRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (reversed_basic factor hreversed)

/-- A weight-one symbolic factor is a Hall-ranked leaf branch. -/
noncomputable def leaf_weight_one
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = 1) :
    TRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (of_weight_one factor hfactorWeight)

end TRBrancha

/-- Immediate concrete residual cases with no recursively scheduled children. -/
inductive RankedLeafCase
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) : Type u
  | terminal
      (hcutoff :
        n ≤ factor.word.weight HEAddres.weight + 1)
  | tree_isBasic
      (htreeBasic :
        (CEWord.tree factor.word).IsBasic)
  | commutator_self
      (word :
        CWord
          (HEAddres (concreteBasicCommutators.{u} d)))
      (hword : factor.word = .commutator word word)
  | isReversedBasic
      (hreversed :
        CEWord.IsReversedBasic factor.word)
  | weight_one
      (hfactorWeight :
        factor.word.weight HEAddres.weight = 1)

namespace TRBrancha

/-- Compile any immediate concrete residual case into a ranked leaf. -/
noncomputable def ofLeafCase
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (leaf :
      RankedLeafCase
        (n := n) factor) :
    TRBrancha
      (n := n) factor rankDefect := by
  cases leaf with
  | terminal hcutoff =>
      exact leaf_of_terminal factor rankDefect hcutoff
  | tree_isBasic htreeBasic =>
      exact leaf_tree_basic factor rankDefect htreeBasic
  | commutator_self word hword =>
      exact leaf_commutator_self factor rankDefect word hword
  | isReversedBasic hreversed =>
      exact leaf_reversed_basic factor rankDefect hreversed
  | weight_one hfactorWeight =>
      exact leaf_weight_one factor rankDefect hfactorWeight

end TRBrancha

end TCTex
end Submission

/-!
# Cases for Hall-ranked concrete polynomial residual branches

A branch either closes immediately or performs recipe-correct reduction of an
inner Hall tree below one unchanged outer bracket. Compiling one classified
case per ranked factor produces the global well-founded scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- Data for recipe-correct inner reduction at its classical Hall-rank defect. -/
structure
    TruncatedRankedCase
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) where
  innerWord :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  rightWord :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  hword : factor.word = .commutator innerWord rightWord
  hfactorTruncated :
    factor.word.weight HEAddres.weight < n
  added :
    HallTree (FreeGenerator.{u} d)
  originalRight :
    HallTree (FreeGenerator.{u} d)
  unchanged :
    HallTree (FreeGenerator.{u} d)
  originalLeft :
    HallTree (FreeGenerator.{u} d)
  hinnerTree :
    CEWord.tree innerWord =
      .commutator added originalRight
  hRightLeft : originalRight < originalLeft
  hRightUnchanged : originalRight < unchanged
  hunchangedBasic : unchanged.IsBasic
  rankDefect_eq :
    rankDefect =
      HallTree.bracketRankDefect
        ((CEWord.tree innerWord).weight +
          unchanged.weight)
        originalLeft originalRight

/-- One complete local case for Hall-ranked residual recursion. -/
inductive RankedBranchCase
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) : Type u
  | leaf
      (leafCase :
        RankedLeafCase
          (n := n) factor)
  | innerReductionOuter
      (innerCase :
        TruncatedRankedCase
          (n := n) factor rankDefect)

namespace TRBrancha

/-- Compile one indexed inner-reduction case into its recursive branch. -/
noncomputable def innerOuterCase
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (branchCase :
      TruncatedRankedCase
        (n := n) factor rankDefect) :
    TRBrancha
      (n := n) factor rankDefect := by
  rcases branchCase with
    ⟨innerWord, rightWord, hword, hfactorTruncated, added, originalRight,
      unchanged, originalLeft, hinnerTree, hRightLeft, hRightUnchanged,
      hunchangedBasic, rankDefect_eq⟩
  subst rankDefect
  exact
    inner_outer hn hH family factor innerWord rightWord hword
      hfactorTruncated added originalRight unchanged originalLeft hinnerTree
        hRightLeft hRightUnchanged hunchangedBasic

/-- Compile either a leaf or recipe-correct inner-reduction local case. -/
noncomputable def ofCase
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (branchCase :
      RankedBranchCase
        (n := n) factor rankDefect) :
    TRBrancha
      (n := n) factor rankDefect := by
  cases branchCase with
  | leaf leafCase =>
      exact ofLeafCase factor rankDefect leafCase
  | innerReductionOuter innerCase =>
      exact
        innerOuterCase hn hH family factor rankDefect innerCase

end TRBrancha

namespace
  TRSchedu

/-- Compile classified local cases into a global well-founded scheduler. -/
noncomputable def ofCases
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        RankedBranchCase
          (n := n) factor rankDefect) :
    TRSchedu
      (d := d) (n := n) (ι := ι) :=
  ofBranches fun factor rankDefect =>
    TRBrancha.ofCase
      hn hH family factor rankDefect (cases factor rankDefect)

/-- Run well-founded recursion directly from classified local cases. -/
noncomputable def residual_recollection_cases
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        RankedBranchCase
          (n := n) factor rankDefect)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) :
    TRRecoll
      (n := n) factor :=
  (ofCases hn hH family cases).residualRecollection factor rankDefect

end
  TRSchedu

end TCTex
end Submission
