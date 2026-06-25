import Towers.Group.Zassenhaus.Jacobi
import Towers.Group.Zassenhaus.ChildrenRankedOrientation
import Towers.Group.Zassenhaus.FactoryBranchCases

/-!
# Flattened Hall-ranked branches for expanded Hall-power Jacobi residuals

The two ordinary descendants of one expanded Jacobi root inherit the root
Hall-rank defect, so they are not themselves strict recursive tasks. Each
descendant is, however, a recipe-correct inner-reduction case. This file
flattens those two reductions into one branch whose exposed grandchildren
strictly descend.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace SPFactora
namespace RCSrc

/--
Transport a strict child source to a parent with the same ordinary word
weight and the same Hall-rank defect.
-/
def reparent
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {oldParent newParent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source :
      RCSrc (n := n) oldParent parentRankDefect)
    (hweight :
      oldParent.word.weight PEAddres.weight =
        newParent.word.weight PEAddres.weight) :
    RCSrc (n := n) newParent parentRankDefect where
  tasks := source.tasks
  tasks_descend := by
    intro task htask
    simpa only [HallRankedDescends, hallRankedMeasure, cutoffDefect, hweight] using
      source.tasks_descend task htask

@[simp]
theorem tasks_reparent
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {oldParent newParent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source :
      RCSrc (n := n) oldParent parentRankDefect)
    (hweight :
      oldParent.word.weight PEAddres.weight =
        newParent.word.weight PEAddres.weight) :
    (source.reparent hweight).tasks = source.tasks :=
  rfl

/-- Concatenate two strict child sources for the same ranked parent. -/
def append
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (left right :
      RCSrc (n := n) parent parentRankDefect) :
    RCSrc (n := n) parent parentRankDefect where
  tasks := left.tasks ++ right.tasks
  tasks_descend := by
    intro task htask
    rcases List.mem_append.mp htask with htask | htask
    · exact left.tasks_descend task htask
    · exact right.tasks_descend task htask

@[simp]
theorem tasks_append
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (left right :
      RCSrc (n := n) parent parentRankDefect) :
    (left.append right).tasks = left.tasks ++ right.tasks :=
  rfl

end RCSrc
end SPFactora

namespace RRBrancha

open
  TSRecollb
  CDRecoll
  TJRecoll

/--
Transport a reversed two-basic-child branch back to the original factor
while preserving its strict child source.
-/
noncomputable def childrenSwap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : HEWord.tree factor.word =
      .commutator left right)
    (rankDefect : ℕ)
    (reversed :
      RRBrancha
        (n := n)
        (childrenSwapFactor factor left right hleftBasic hrightBasic
          htree)
        rankDefect)
    (valueResidualInverse :
      TIRecoll
        (n := n) factor left right hleftBasic hrightBasic htree) :
    RRBrancha
      (n := n) factor rankDefect where
  children :=
    reversed.children.reparent
      (basic_children_swap factor left right hleftBasic
        hrightBasic htree)
  recollect := fun residual =>
    TSRecollb.children_swap
      factor left right hleftBasic hrightBasic htree
        (reversed.recollect fun task htask => residual task htask)
        valueResidualInverse

/--
Flatten an expanded Jacobi root and the inner reductions of both descendants
into a single strictly descending Hall-ranked branch.
-/
noncomputable def expanded_ranked_decomp
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (ranked :
      TRDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (valueResidual :
      TJRecoll
        (n := n) factor ranked.decomposition) :
    RRBrancha
      (n := n) factor
        (expandedParentDefect ranked.decomposition) := by
  let first :=
    innerOuterFactory hn hH routing
      (expandedJacobiFactor factor ranked.decomposition)
      (expandedParentDefect ranked.decomposition)
      (ranked.firstCase hfactorTruncated)
  let second :=
    innerOuterFactory hn hH routing
      (expandedJacobiSecond factor ranked.decomposition)
      (expandedParentDefect ranked.decomposition)
      (ranked.secondCase hfactorTruncated)
  exact
    {
      children :=
        (first.children.reparent
          (expanded_jacobi_factor
            factor ranked.decomposition)).append
          (second.children.reparent
            (expanded_second_factor
              factor ranked.decomposition))
      recollect := fun residual =>
        let firstResidual :=
          first.recollect fun task htask =>
            residual task (List.mem_append_left _ htask)
        let secondResidual :=
          second.recollect fun task htask =>
            residual task (List.mem_append_right _ htask)
        let continuation :=
          of_routedFirst
            (routing.factory factor) (routing.sharp factor)
            factor ranked.decomposition rfl hfactorTruncated
            firstResidual secondResidual valueResidual.toInverseRecollection
        expanded_reduction hn hH
          (routing.factory factor) (routing.sharp factor)
          (routing.nextNormalizer factor)
          factor ranked.decomposition rfl hfactorTruncated
          continuation.expandedContinuationRecollection
    }

/--
Compile either ranked Hall orientation of a two-basic-child Jacobi frontier
into one strict branch.
-/
noncomputable def basicChildrenDispatch
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
    (valueResidual :
      ∀
        (childFactor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (ranked :
          TRDecomp
            childFactor),
        childFactor.word.weight PEAddres.weight < n →
          TJRecoll
            (n := n) childFactor ranked.decomposition)
    (swapValueInverse :
      ∀
        (childFactor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (left right : HallTree (FreeGenerator.{u} d))
        (hleftBasic : left.IsBasic)
        (hrightBasic : right.IsBasic)
        (htree : tree childFactor.word = .commutator left right),
        childFactor.word.weight PEAddres.weight < n →
          TIRecoll
            (n := n) childFactor left right hleftBasic hrightBasic htree)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (dispatch :
      CRDispat factor left right hleftBasic
        hrightBasic htree) :
    RRBrancha
      (n := n) factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) := by
  cases dispatch with
  | forward ranked =>
      rw [←
        CRDispat.forward_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      exact
        expanded_ranked_decomp hn hH routing factor ranked
          hfactorTruncated (valueResidual factor ranked hfactorTruncated)
  | swapped ranked =>
      rw [←
        CRDispat.swapped_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      exact
        childrenSwap factor left right hleftBasic hrightBasic htree
          (expandedParentDefect ranked.decomposition)
          (expanded_ranked_decomp hn hH routing
            (childrenSwapFactor factor left right hleftBasic hrightBasic
              htree)
            ranked
            (by
              simpa only [basic_children_swap] using
                hfactorTruncated)
            (valueResidual
              (childrenSwapFactor factor left right hleftBasic
                hrightBasic htree)
              ranked
              (by
                simpa only [basic_children_swap] using
                  hfactorTruncated)))
          (swapValueInverse factor left right hleftBasic hrightBasic
            htree hfactorTruncated)

/--
Choose the ranked Hall orientation and compile one two-basic-child Jacobi
frontier into a strict branch.
-/
noncomputable def basicChildrenJacobi
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
    (valueResidual :
      ∀
        (childFactor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (ranked :
          TRDecomp
            childFactor),
        childFactor.word.weight PEAddres.weight < n →
          TJRecoll
            (n := n) childFactor ranked.decomposition)
    (swapValueInverse :
      ∀
        (childFactor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (left right : HallTree (FreeGenerator.{u} d))
        (hleftBasic : left.IsBasic)
        (hrightBasic : right.IsBasic)
        (htree : tree childFactor.word = .commutator left right),
        childFactor.word.weight PEAddres.weight < n →
          TIRecoll
            (n := n) childFactor left right hleftBasic hrightBasic htree)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    RRBrancha
      (n := n) factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) :=
  basicChildrenDispatch hn hH routing valueResidual
    swapValueInverse factor left right hleftBasic hrightBasic htree
      hfactorTruncated
        (childrenJacobiDispatch factor left right hleftBasic
          hrightBasic htree hchildrenNe hforwardNonbasic hreverseNonbasic)

end RRBrancha

end TCTex
end Towers
