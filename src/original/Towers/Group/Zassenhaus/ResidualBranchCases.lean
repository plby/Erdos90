import Towers.Group.Zassenhaus.ResidualBaseBranches

/-!
# Cases for Hall-ranked concrete residual branches

A concrete residual branch either closes immediately or performs the
recipe-correct reduction of an inner Hall tree below one unchanged outer
bracket.  The recursive case records its exact classical Hall-rank defect.

This file compiles a family of such local cases into the global well-founded
ranked scheduler.  The remaining universal obligation is therefore exposed as
a classification problem together with the semantic normalizer family needed
by the recursive case.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
The data needed to use recipe-correct inner reduction as one branch at its
natural classical Hall-rank defect.
-/
structure
    RankedInnerCase
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) where
  innerWord :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  rightWord :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  hword : factor.word = .commutator innerWord rightWord
  hfactorTruncated :
    factor.word.weight PEAddres.weight < n
  added :
    HallTree (FreeGenerator.{u} d)
  originalRight :
    HallTree (FreeGenerator.{u} d)
  unchanged :
    HallTree (FreeGenerator.{u} d)
  originalLeft :
    HallTree (FreeGenerator.{u} d)
  hinnerTree :
    HEWord.tree innerWord =
      .commutator added originalRight
  hRightLeft : originalRight < originalLeft
  hRightUnchanged : originalRight < unchanged
  hunchangedBasic : unchanged.IsBasic
  rankDefect_eq :
    rankDefect =
      HallTree.bracketRankDefect
        ((HEWord.tree innerWord).weight + unchanged.weight)
        originalLeft originalRight

/--
One complete local case for Hall-ranked concrete residual recursion.
-/
inductive TruncatedBranchCase
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) : Type u
  | leaf
      (leafCase :
        TruncatedLeafCase
          (n := n) factor)
  | innerReductionOuter
      (innerCase :
        RankedInnerCase
          (n := n) factor rankDefect)

namespace RRBrancha

/-- Compile one indexed inner-reduction case into its recursive branch. -/
noncomputable def innerOuterCase
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
    (rankDefect : ℕ)
    (branchCase :
      RankedInnerCase
        (n := n) factor rankDefect) :
    RRBrancha
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
    (rankDefect : ℕ)
    (branchCase :
      TruncatedBranchCase
        (n := n) factor rankDefect) :
    RRBrancha
      (n := n) factor rankDefect := by
  cases branchCase with
  | leaf leafCase =>
      exact ofLeafCase factor rankDefect leafCase
  | innerReductionOuter innerCase =>
      exact
        innerOuterCase hn hH family factor rankDefect innerCase

end RRBrancha

namespace
  RRSchedua

/--
Compile one classified local case for every ranked factor into a global
well-founded residual scheduler.
-/
noncomputable def ofCases
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
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        TruncatedBranchCase
          (n := n) factor rankDefect) :
    RRSchedua
      (d := d) (n := n) (inputWeight := inputWeight) :=
  ofBranches fun factor rankDefect =>
    RRBrancha.ofCase
      hn hH family factor rankDefect (cases factor rankDefect)

/--
Run well-founded residual recursion directly from one classified local case
for every ranked factor.
-/
noncomputable def residual_recollection_cases
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
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        TruncatedBranchCase
          (n := n) factor rankDefect)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) :
    TSRecollb
      (n := n) factor :=
  (ofCases hn hH family cases).residualRecollection factor rankDefect

end
  RRSchedua

end TCTex
end Towers
