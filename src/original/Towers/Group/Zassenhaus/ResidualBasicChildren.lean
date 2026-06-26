import Towers.Group.HallBasic.StandardSequence
import
  Towers.Group.Zassenhaus.ChildrenSwapValue
import Towers.Group.Zassenhaus.BasicTreeReduction
import Towers.Group.Zassenhaus.Jacobi
import Towers.Group.Zassenhaus.JacobiRankedBranch
import Towers.Group.Zassenhaus.RootSwapRecollection
import Towers.Group.Zassenhaus.RootSwapValue
import Towers.Group.Zassenhaus.CanonicalHallRecollection
import Towers.Group.Zassenhaus.ReductionOuter
import Towers.Group.Zassenhaus.ComparisonFactoryRouting
import Towers.Group.Zassenhaus.RetainedInsertionCollection


-- Merged from ResidualBasicChildrenReachability.lean

/-!
# Reachable two-basic-child Hall-power ranked residual tasks

After one recipe-correct inner reduction, every exposed recursive task is a
bracket of two Hall-basic trees. Its numerical rank defect is the canonical
symmetric bracket defect and its symbolic factor remains physically
truncated. This file records that reachable task predicate and derives it
directly from membership in an inner-reduction child packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

/--
A reachable ranked residual task exposed by inner Hall reduction has two
basic children and carries their canonical symmetric bracket-rank defect.
-/
structure
    TCReacha
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) where
  left : HallTree (FreeGenerator.{u} d)
  right : HallTree (FreeGenerator.{u} d)
  left_isBasic : left.IsBasic
  right_isBasic : right.IsBasic
  tree_eq :
    tree factor.word = .commutator left right
  factor_truncated :
    factor.word.weight PEAddres.weight < n
  rankDefect_eq :
    rankDefect =
      HallTree.bracketRankDefect
        (left.weight + right.weight) left right

namespace
  TCReacha

/--
Every member of a recipe-correct ranked inner-reduction packet is a reachable
two-basic-child task, provided the retained right word expands to the basic
unchanged tree recorded by the recipe.
-/
noncomputable def ranked_tasks
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (unchanged : HallTree (FreeGenerator.{u} d))
    (hrightTree : tree rightWord = unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask :
      task ∈
        CIChildr.rankedTasks
          factor innerWord rightWord hword unchanged) :
    TCReacha
      (n := n) task.1 task.2 := by
  let indexExists :=
    CIChildr.index_ranked_tasks
      factor innerWord rightWord hword unchanged htask
  let i := Classical.choose indexExists
  have htask_eq := Classical.choose_spec indexExists
  rw [htask_eq]
  refine
    { left := HallTree.indexedBasicTree i
      right := unchanged
      left_isBasic := HallTree.indexed_tree i
      right_isBasic := hunchangedBasic
      tree_eq := ?_
      factor_truncated := ?_
      rankDefect_eq := ?_ }
  · rw [inner_reduction_factor, tree_commutator, tree_atom,
      basicReductionAddress, concreteBasicTree, hrightTree]
  · rw [inner_outer_factor]
    exact hfactorTruncated
  · rw [HallTree.indexed_tree_weight]

end
  TCReacha

end TCTex
end Towers

-- Merged from ResidualBasicChildrenScheduler.lean

/-!
# Reachable scheduling for two-basic-child Hall-power residuals

Every strict task exposed by a flattened Jacobi frontier is again a bracket
of two basic trees.  This file proves that closure property and uses it to
classify reachable tasks: terminal, basic, self, and reversed-basic roots
close immediately, while the remaining roots flatten one Jacobi step and
schedule only their strictly descending grandchildren.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace
  TCReacha

/--
Children emitted by one compiled recipe-correct inner reduction are again
reachable two-basic-child tasks when the retained right word expands to the
recorded unchanged tree.
-/
noncomputable def reduction_factory_children
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
    (rankDefect : ℕ)
    (branchCase :
      RankedInnerCase
        (n := n) factor rankDefect)
    (hrightTree : tree branchCase.rightWord = branchCase.unchanged)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask :
      task ∈
        (RRBrancha.innerOuterFactory
          hn hH routing factor rankDefect branchCase).children.tasks) :
    TCReacha
      (n := n) task.1 task.2 := by
  rcases branchCase with
    ⟨innerWord, rightWord, hword, hfactorTruncated, added, originalRight,
      unchanged, originalLeft, hinnerTree, hRightLeft, hRightUnchanged,
      hunchangedBasic, rankDefect_eq⟩
  subst rankDefect
  exact
    ranked_tasks factor innerWord rightWord hword unchanged hrightTree
      hunchangedBasic hfactorTruncated (by
        simpa only [
          RRBrancha.innerOuterFactory,
          RRBrancha.innerComparisonFactory,
          CIChildr.tasks_ranked_task]
          using htask)

/--
The children exposed by one flattened ranked Jacobi decomposition are
reachable two-basic-child tasks.
-/
noncomputable def expanded_jacobi_children
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
        (n := n) factor ranked.decomposition)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask :
      task ∈
        (RRBrancha.expanded_ranked_decomp
          hn hH routing factor ranked hfactorTruncated valueResidual).children.tasks) :
    TCReacha
      (n := n) task.1 task.2 := by
  let firstCase := ranked.firstCase hfactorTruncated
  let secondCase := ranked.secondCase hfactorTruncated
  let first :=
    RRBrancha.innerOuterFactory
      hn hH routing
        (expandedJacobiFactor factor ranked.decomposition)
        (expandedParentDefect ranked.decomposition) firstCase
  let second :=
    RRBrancha.innerOuterFactory
      hn hH routing
        (expandedJacobiSecond factor ranked.decomposition)
        (expandedParentDefect ranked.decomposition) secondCase
  have htask' : task ∈ first.children.tasks ++ second.children.tasks := by
    simpa only [
      RRBrancha.expanded_ranked_decomp,
      SPFactora.RCSrc.tasks_append,
      SPFactora.RCSrc.tasks_reparent]
      using htask
  classical
  by_cases htaskFirst : task ∈ first.children.tasks
  · exact
      reduction_factory_children hn hH routing
        (expandedJacobiFactor factor ranked.decomposition)
        (expandedParentDefect ranked.decomposition) firstCase
          (by rfl) htaskFirst
  · have htaskSecond : task ∈ second.children.tasks :=
      (List.mem_append.mp htask').resolve_left htaskFirst
    exact
      reduction_factory_children hn hH routing
        (expandedJacobiSecond factor ranked.decomposition)
        (expandedParentDefect ranked.decomposition) secondCase
          (by rfl) htaskSecond

end
  TCReacha

namespace
  RRBranch

/-- Lift an already closed residual recollection to any reachable predicate. -/
noncomputable def ofResidRecollect
    {d n inputWeight : ℕ}
    {Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (residual :
      TSRecollb
        (n := n) factor) :
    RRBranch
      (n := n) Reachable factor rankDefect where
  branch :=
    RRBrancha.ofResidRecollect
      factor rankDefect residual
  children_reachable := by
    simp [
      RRBrancha.ofResidRecollect,
      SPFactora.RCSrc.empty]

/--
A flattened ranked Jacobi decomposition is a reachable branch for the
two-basic-child task predicate.
-/
noncomputable def basic_children_jacobi
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
    RRBranch
      (n := n)
      (fun child childRankDefect =>
        Nonempty
          (TCReacha
            (n := n) child childRankDefect))
      factor (expandedParentDefect ranked.decomposition) where
  branch :=
    RRBrancha.expanded_ranked_decomp
      hn hH routing factor ranked hfactorTruncated valueResidual
  children_reachable := by
    intro task htask
    exact
      ⟨TCReacha.expanded_jacobi_children
        hn hH routing factor ranked hfactorTruncated valueResidual htask⟩

/--
Compile either ranked Hall orientation directly as a reachable branch.  The
rank rewrite happens outside the child-source projections, so the closure
proof remains at the decomposition's native rank.
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
    RRBranch
      (n := n)
      (fun child childRankDefect =>
        Nonempty
          (TCReacha
            (n := n) child childRankDefect))
      factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) := by
  cases dispatch with
  | forward ranked =>
      rw [←
        CRDispat.forward_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      exact
        basic_children_jacobi hn hH routing factor
          ranked hfactorTruncated (valueResidual factor ranked hfactorTruncated)
  | swapped ranked =>
      rw [←
        CRDispat.swapped_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      let swappedFactor :=
        childrenSwapFactor factor left right hleftBasic hrightBasic htree
      have hswappedTruncated :
          swappedFactor.word.weight PEAddres.weight < n := by
        simpa only [swappedFactor, basic_children_swap] using
          hfactorTruncated
      let reversed :=
        basic_children_jacobi hn hH routing
          swappedFactor ranked hswappedTruncated
            (valueResidual swappedFactor ranked hswappedTruncated)
      exact
        { branch :=
            RRBrancha.childrenSwap
              factor left right hleftBasic hrightBasic htree
                (expandedParentDefect ranked.decomposition)
                reversed.branch
                (swapValueInverse factor left right hleftBasic
                  hrightBasic htree hfactorTruncated)
          children_reachable := by
            intro task htask
            exact reversed.children_reachable task (by
              simpa only [
                RRBrancha.childrenSwap,
                SPFactora.RCSrc.tasks_reparent]
                using htask) }

/-- Choose the Hall orientation and compile its reachable flattened branch. -/
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
    RRBranch
      (n := n)
      (fun child childRankDefect =>
        Nonempty
          (TCReacha
            (n := n) child childRankDefect))
      factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) :=
  basicChildrenDispatch hn hH routing valueResidual
    swapValueInverse factor left right hleftBasic hrightBasic htree
      hfactorTruncated
        (childrenJacobiDispatch factor left right hleftBasic
          hrightBasic htree hchildrenNe hforwardNonbasic hreverseNonbasic)

/--
Classify one reachable two-basic-child task.  Immediate endpoints close with
no recursive children; every remaining root is a flattened ranked Jacobi
frontier.
-/
noncomputable def basicChildrenReachable
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
    (rankDefect : ℕ)
    (reachable :
      TCReacha
        (n := n) factor rankDefect) :
    RRBranch
      (n := n)
      (fun child childRankDefect =>
        Nonempty
          (TCReacha
            (n := n) child childRankDefect))
      factor rankDefect := by
  rcases reachable with
    ⟨left, right, hleftBasic, hrightBasic, htree, hfactorTruncated,
      rankDefect_eq⟩
  subst rankDefect
  by_cases hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1
  · exact
      ofResidRecollect factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right)
        (TSRecollb.of_terminal
          factor hcutoff)
  · by_cases hforwardBasic : (HallTree.commutator left right).IsBasic
    · exact
        ofResidRecollect factor
          (HallTree.bracketRankDefect
            (left.weight + right.weight) left right)
          (TSRecollb.tree_basic
            factor (by
              rw [htree]
              exact hforwardBasic))
    · by_cases hchildrenEq : left = right
      · exact
          ofResidRecollect factor
            (HallTree.bracketRankDefect
              (left.weight + right.weight) left right)
            (TSRecollb.tree_commutator_self
              factor left (by simpa only [hchildrenEq] using htree))
      · by_cases hreverseBasic : (HallTree.commutator right left).IsBasic
        · exact
            ofResidRecollect factor
              (HallTree.bracketRankDefect
                (left.weight + right.weight) left right)
              (TSRecollb.tree_swap_basic
                factor right left htree hreverseBasic)
        · exact
            basicChildrenJacobi hn hH routing valueResidual
              swapValueInverse factor left right hleftBasic
                hrightBasic htree hchildrenEq hforwardBasic hreverseBasic
                  hfactorTruncated

end
  RRBranch

namespace
  TRSchedua

/--
Compile the reachable two-basic-child classifier into a restricted
well-founded Hall-ranked scheduler.
-/
noncomputable def ofBasicChildren
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
            (n := n) childFactor left right hleftBasic hrightBasic htree) :
    TRSchedua
      (d := d) (n := n) (inputWeight := inputWeight)
      (fun
        (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        rankDefect =>
        Nonempty
          (TCReacha
            (n := n) factor rankDefect)) :=
  TRSchedua.ofBranches
    fun factor rankDefect hreachable =>
      RRBranch.basicChildrenReachable
        hn hH routing valueResidual swapValueInverse factor rankDefect
          (Classical.choice hreachable)

/--
Run restricted Hall-ranked recursion from one reachable two-basic-child task.
-/
noncomputable def residual_recollection_children
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
    (rankDefect : ℕ)
    (hreachable :
      Nonempty
        (TCReacha
          (n := n) factor rankDefect)) :
    TSRecollb
      (n := n) factor :=
  (ofBasicChildren hn hH routing valueResidual swapValueInverse)
    |>.residualRecollection factor rankDefect hreachable

end
  TRSchedua

end TCTex
end Towers

-- Merged from ResidualBasicChildrenCanonicalRouting.lean

/-!
# Canonical routing for reachable two-basic-child Hall-power residuals

The reachable scheduler needs outer-residual routing and semantic
normalization of the two value residuals introduced by forward and swapped
Jacobi orientations.  A single powered semantic normalizer family supplies
both value normalizations.

This file packages those inputs and exposes the canonical endpoints:
well-founded recollection of an individual reachable two-basic-child task,
and recollection of an oriented expanded-Jacobi root after flattening its two
ordinary descendants into strictly descending grandchildren.

The comparison-routing constructor keeps the outer-factory input
non-circular: child-to-parent outer residuals are recovered as quotients of
independently recollected atomic comparisons and full basic residuals.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

/--
Canonical routing inputs for the reachable two-basic-child ranked residual
scheduler.
-/
structure
    SCRouteb
    {d n inputWeight : ℕ} where
  outerRouting :
    OFRoute.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  normalizerFamily :
    SSNormala
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d)

namespace
  SCRouteb

/--
Recover canonical routing from independently recollected atomic comparisons
and full basic residuals.
-/
noncomputable def comparison_factory_routing
    {d n inputWeight : ℕ}
    (routing :
      FRData
        (d := d) (n := n) (inputWeight := inputWeight))
    (normalizerFamily :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    SCRouteb
      (d := d) (n := n) (inputWeight := inputWeight) where
  outerRouting := routing.outerFactoryRouting
  normalizerFamily := normalizerFamily

/-- Normalize the forward expanded-Jacobi value residual at its own weight. -/
noncomputable def valueResidual
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRouteb
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (ranked :
      TRDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TJRecoll
      (n := n) factor ranked.decomposition :=
  TJRecoll.ofNormalizerFamily
    hn hH routing.normalizerFamily factor ranked.decomposition rfl
      hfactorTruncated

/-- Normalize the inverse skew-value residual at its own weight. -/
noncomputable def swapValueInverse
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRouteb
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TIRecoll
      (n := n) factor left right hleftBasic hrightBasic htree :=
  TIRecoll.ofNormalizerFamily
    hn hH routing.normalizerFamily factor left right hleftBasic hrightBasic
      htree rfl hfactorTruncated

/-- Compile canonical routing into the restricted ranked residual scheduler. -/
noncomputable def scheduler
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRouteb
        (d := d) (n := n) (inputWeight := inputWeight)) :
    TRSchedua
      (d := d) (n := n) (inputWeight := inputWeight)
      (fun
        (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        rankDefect =>
        Nonempty
          (TCReacha
            (n := n) factor rankDefect)) :=
  TRSchedua.ofBasicChildren
    hn hH routing.outerRouting (routing.valueResidual hn hH)
      (routing.swapValueInverse hn hH)

/-- Recollect one certified reachable two-basic-child residual task. -/
noncomputable def residualRecollection
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRouteb
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hreachable :
      Nonempty
        (TCReacha
          (n := n) factor rankDefect)) :
    TSRecollb
      (n := n) factor :=
  (routing.scheduler hn hH).residualRecollection factor rankDefect hreachable

/--
Flatten one ranked expanded-Jacobi root and recollect its certified strict
grandchildren with the canonical scheduler.
-/
noncomputable def expanded_ranked_decomposition
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRouteb
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (ranked :
      TRDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  let branch :=
    RRBranch.basic_children_jacobi
      hn hH routing.outerRouting factor ranked hfactorTruncated
        (routing.valueResidual hn hH factor ranked hfactorTruncated)
  branch.branch.recollect fun task htask =>
    routing.residualRecollection hn hH task.1 task.2
      (branch.children_reachable task htask)

end
  SCRouteb

end TCTex
end Towers

-- Merged from ResidualBasicChildrenFrontierCollection.lean

/-!
# Ranked collection at Hall-power Jacobi frontiers with two basic children

The older Jacobi-frontier adapter routes a two-basic-child obstruction
through raw expanded-Jacobi descendants. Those descendants retain the parent
rank, so they are not suitable recursive tasks themselves.

The reachable ranked scheduler instead flattens each oriented Jacobi step:
it reduces both ordinary descendants immediately and recursively schedules
only the strictly descending grandchildren. This file installs that route at
the collector-facing Hall-power Jacobi frontier. Frontiers with a genuinely
nonbasic child remain explicit for the next layer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

/--
Canonical ranked routing for powered two-basic-child frontiers, with only
nonbasic-child frontiers left to the caller.
-/
structure
    CJBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  nonbasicChildResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ¬(tree factor.word).IsBasic →
                ∀ left right : HallTree (FreeGenerator.{u} d),
                  tree factor.word = .commutator left right →
                    left ≠ right →
                      ¬(HallTree.commutator right left).IsBasic →
                        (¬left.IsBasic ∨ ¬right.IsBasic) →
                          TSRecollb
                            (n := n) factor

namespace
  CJBuild

/--
Compile reachable ranked collection for powered two-basic-child frontiers
into the ordinary Jacobi-frontier collector.
-/
noncomputable def jacobiCollectionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      CJBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    TFBuildc.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  jacobiFrontierResidual := by
    intro lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      htreeNonbasic left right htree hchildrenNe hreverseNonbasic
    by_cases hleftBasic : left.IsBasic
    · by_cases hrightBasic : right.IsBasic
      · exact
          builder.routing.residualRecollection hn hH factor
            (HallTree.bracketRankDefect
              (left.weight + right.weight) left right)
            ⟨{
              left := left
              right := right
              left_isBasic := hleftBasic
              right_isBasic := hrightBasic
              tree_eq := htree
              factor_truncated := hfactorTruncated
              rankDefect_eq := rfl
            }⟩
      · exact
          builder.nonbasicChildResidual lowerWeight hnonterminal factor
            hfactorWeight hfactorTruncated htreeNonbasic left right htree
              hchildrenNe hreverseNonbasic (Or.inr hrightBasic)
    · exact
        builder.nonbasicChildResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated htreeNonbasic left right htree
            hchildrenNe hreverseNonbasic (Or.inl hleftBasic)

end
  CJBuild

namespace TSInput

/--
For canonical Hall families, ranked powered two-basic-child scheduling and
explicit nonbasic-child residuals construct the Claim 5 coordinate
polynomials for a supported sourced input.
-/
theorem
    rankedChildrenBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      CJBuild.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.jacobiFrontierBuilder
    hn hsourceSupported builder.jacobiCollectionBuilder
      hinputWeight

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedLeftFrontierCollection.lean

/-!
# Ranked Hall-power frontiers reduced to nonbasic left children

The reachable scheduler closes every Jacobi frontier with two basic children.
For a remaining frontier, a nonbasic left child is already in the orientation
needed by outer induction. If only the right child is nonbasic, an exact
sign-corrected root swap exposes it on the left and contributes one separately
recollected skew-value residual.

This file packages that orientation step. The only remaining recursive
boundary is a frontier with an explicitly nonbasic left child.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

/--
Reachable ranked routing for two-basic-child frontiers, root-swap value
recollections, and residuals for frontiers with a nonbasic left child.
-/
structure
    TJFront
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  leftNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ left right : HallTree (FreeGenerator.{u} d),
                tree factor.word = .commutator left right →
                  ¬left.IsBasic →
                    left ≠ right →
                      ¬(HallTree.commutator right left).IsBasic →
                        TSRecollb
                          (n := n) factor

namespace
  TJFront

open
  TSRecollb

/--
Orient every genuinely nonbasic-child frontier so that its nonbasic child is
on the left, using one exact root swap when necessary.
-/
noncomputable def nonbasicChildResidual
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TJFront.{u}
        (inputWeight := inputWeight) hn hH)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (htreeNonbasic : ¬(tree factor.word).IsBasic)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = .commutator left right)
    (hchildrenNe : left ≠ right)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hchild : ¬left.IsBasic ∨ ¬right.IsBasic) :
    TSRecollb
      (n := n) factor := by
  by_cases hleftBasic : left.IsBasic
  · have hrightNonbasic : ¬right.IsBasic := by
      intro hrightBasic
      exact hchild.elim (fun h => h hleftBasic) (fun h => h hrightBasic)
    cases right with
    | atom generator =>
        exact False.elim (hrightNonbasic (HallTree.isBasic_atom generator))
    | commutator right₁ right₂ =>
        cases hword : factor.word with
        | atom address =>
            exfalso
            apply htreeNonbasic
            rw [hword]
            exact concrete_hall_tree address.2
        | commutator leftWord rightWord =>
            have htree' := htree
            rw [hword, tree_commutator] at htree'
            injection htree' with hleftTree hrightTree
            let reversed :=
              expandedSwapFactor factor leftWord rightWord hword
            exact
              expanded_swap factor leftWord rightWord hword
                (builder.leftNonbasicResidual lowerWeight hnonterminal
                  reversed
                    (by
                      dsimp only [reversed]
                      simpa only [expanded_root_factor] using
                        hfactorWeight)
                    (by
                      dsimp only [reversed]
                      simpa only [expanded_root_factor] using
                        hfactorTruncated)
                  (.commutator right₁ right₂) left
                    (by
                      dsimp only [reversed]
                      rw [tree_expanded_swap, hrightTree,
                        hleftTree])
                    hrightNonbasic hchildrenNe.symm
                    (by
                      rw [← htree]
                      exact htreeNonbasic))
                (builder.rootSwapResidual lowerWeight hnonterminal factor
                  leftWord rightWord hword hfactorWeight hfactorTruncated)
  · exact
      builder.leftNonbasicResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated left right htree hleftBasic hchildrenNe
          hreverseNonbasic

/--
Compile nonbasic-left orientation into the collector-facing frontier
interface.
-/
noncomputable def rankedChildrenJacobi
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TJFront.{u}
        (inputWeight := inputWeight) hn hH) :
    CJBuild.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  nonbasicChildResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        htreeNonbasic left right htree hchildrenNe hreverseNonbasic hchild =>
      builder.nonbasicChildResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated htreeNonbasic left right htree
          hchildrenNe hreverseNonbasic hchild

end
  TJFront

namespace TSInput

/--
For canonical Hall families, ranked powered two-basic-child scheduling,
root-swap orientation, and explicit nonbasic-left residuals construct the
Claim 5 coordinate polynomials for a supported sourced input.
-/
theorem
    coordJacobiBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TJFront.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.rankedChildrenBuilder
    hn hsourceSupported
      builder.rankedChildrenJacobi hinputWeight

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsFrontierCollection.lean

/-!
# Ranked Hall-power frontiers with exposed nested words

After root-swap orientation, every remaining frontier has a nonbasic left
child. Such a child cannot be an atom. Both nonbasic layers therefore come
from commutator-shaped symbolic words, and the existing syntactic Jacobi
decomposition chooser exposes those words.

This file packages that exposure step. The remaining boundary receives an
explicit left-normed symbolic decomposition suitable for structural
outer-induction classification.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

/-- A left-normed nonbasic frontier together with its exposed symbolic words. -/
structure
    WFCase
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) where
  left :
    HallTree (FreeGenerator.{u} d)
  middle :
    HallTree (FreeGenerator.{u} d)
  right :
    HallTree (FreeGenerator.{u} d)
  tree_eq :
    tree factor.word = .commutator (.commutator left middle) right
  outer_nonbasic :
    ¬(HallTree.commutator (.commutator left middle) right).IsBasic
  inner_nonbasic :
    ¬(HallTree.commutator left middle).IsBasic
  children_ne :
    HallTree.commutator left middle ≠ right
  reverse_nonbasic :
    ¬(HallTree.commutator right (.commutator left middle)).IsBasic
  decomposition :
    SyntacticJacobiDecomposition factor.word

/--
Reachable ranked routing and residuals for explicitly exposed nested symbolic
frontiers.
-/
structure
    TCBuilda
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  nestedWordsResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              WFCase
                  factor →
                TSRecollb
                  (n := n) factor

namespace
  TCBuilda

/-- Expose nested words at one explicitly nonbasic-left frontier. -/
noncomputable def leftNonbasicResidual
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TCBuilda.{u}
        (inputWeight := inputWeight) hn hH)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = .commutator left right)
    (hleftNonbasic : ¬left.IsBasic)
    (hchildrenNe : left ≠ right)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    TSRecollb
      (n := n) factor := by
  cases left with
  | atom generator =>
      exact False.elim (hleftNonbasic (HallTree.isBasic_atom generator))
  | commutator left middle =>
      have houterNonbasic :
          ¬(HallTree.commutator (.commutator left middle) right).IsBasic := by
        intro hbasic
        exact
          hleftNonbasic
            ((HallTree.isBasic_commutator (.commutator left middle) right).mp
              hbasic).1
      let decomposition :=
        syntacticTreeNonbasic
          factor.word left middle right (by simpa only using htree)
            houterNonbasic hleftNonbasic
      exact
        builder.nestedWordsResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated
            {
              left := left
              middle := middle
              right := right
              tree_eq := by simpa only using htree
              outer_nonbasic := houterNonbasic
              inner_nonbasic := hleftNonbasic
              children_ne := hchildrenNe
              reverse_nonbasic := hreverseNonbasic
              decomposition := decomposition
            }

/-- Compile nested-word exposure into the nonbasic-left frontier interface. -/
noncomputable def
    rankedChildrenExpanded
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TCBuilda.{u}
        (inputWeight := inputWeight) hn hH) :
    TJFront.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  leftNonbasicResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        left right htree hleftNonbasic hchildrenNe hreverseNonbasic =>
      builder.leftNonbasicResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated left right htree hleftNonbasic
          hchildrenNe hreverseNonbasic

end
  TCBuilda

namespace TSInput

/--
For canonical Hall families, ranked powered scheduling, root-swap
orientation, and explicit nested-word residuals construct the Claim 5
coordinate polynomials for a supported sourced input.
-/
theorem
    coordChildrenBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TCBuilda.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordJacobiBuilder
    hn hsourceSupported
      builder.rankedChildrenExpanded
        hinputWeight

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsStructuralCases.lean

/-!
# Structural inner-span cases for exposed nested Hall-power frontiers

An explicitly nested frontier does not carry enough Hall inequalities to
choose a recursive branch automa. Once a caller supplies the
recipe-correct inner-span case, however, the existing outer-factory branch
emits only reachable two-basic-child tasks. The canonical restricted
scheduler therefore recollects every strict child without a parent-stratum
fallback.

This file packages that local structural certificate and compiles a family of
such certificates into the exposed nested-word frontier interface.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

/--
A recipe-correct structural inner-span branch for one exposed nested-word
frontier. The retained right-word equality is exactly the extra fact needed
to prove that every generated child is a reachable two-basic-child task.
-/
structure
    TWCase
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) where
  rankDefect : ℕ
  innerReductionOuter :
    RankedInnerCase
      (n := n) factor rankDefect
  right_tree :
    tree innerReductionOuter.rightWord = innerReductionOuter.unchanged

namespace
  TWCase

/--
When the exposed inner right tree is smaller than the retained outer basic
tree, the nested frontier is a direct structural inner-span case.
-/
noncomputable def inner_right_outer
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (hinnerRightOuterRight : frontier.middle < frontier.right)
    (houterRightBasic : frontier.right.IsBasic) :
    TWCase
      (n := n) factor := by
  have hdecompositionTree :
      tree factor.word =
        HallTree.commutator
          (.commutator
            (tree frontier.decomposition.left)
            (tree frontier.decomposition.middle))
          (tree frontier.decomposition.right) := by
    have htree := congrArg tree frontier.decomposition.word_eq
    simpa only [tree_commutator] using htree
  have hroot :
      HallTree.commutator
          (.commutator
            (tree frontier.decomposition.left)
            (tree frontier.decomposition.middle))
          (tree frontier.decomposition.right) =
        .commutator (.commutator frontier.left frontier.middle)
          frontier.right := by
    exact hdecompositionTree.symm.trans frontier.tree_eq
  injection hroot with hinner hright
  injection hinner with hleft hmiddle
  exact
    {
      rankDefect :=
        HallTree.bracketRankDefect
          ((tree (.commutator frontier.decomposition.left
              frontier.decomposition.middle)).weight +
            frontier.right.weight)
          (.commutator frontier.left frontier.middle) frontier.middle
      innerReductionOuter :=
        {
          innerWord :=
            .commutator frontier.decomposition.left
              frontier.decomposition.middle
          rightWord := frontier.decomposition.right
          hword := frontier.decomposition.word_eq
          hfactorTruncated := hfactorTruncated
          added := frontier.left
          originalRight := frontier.middle
          unchanged := frontier.right
          originalLeft := .commutator frontier.left frontier.middle
          hinnerTree := by
            simp only [tree_commutator, hleft, hmiddle]
          hRightLeft :=
            HallTree.weight_add_left frontier.left frontier.middle
              (.commutator frontier.left frontier.middle) rfl
          hRightUnchanged := hinnerRightOuterRight
          hunchangedBasic := houterRightBasic
          rankDefect_eq := rfl
        }
      right_tree := hright
    }

/--
Compile one admissible structural inner-span case and recursively recollect
its strict two-basic-child tasks with the canonical reachable scheduler.
-/
noncomputable def residualRecollection
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRouteb
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (structural :
      TWCase
        (n := n) factor) :
    TSRecollb
      (n := n) factor :=
  let branch :=
    RRBrancha.innerOuterFactory
      hn hH routing.outerRouting factor structural.rankDefect
        structural.innerReductionOuter
  branch.recollect fun task htask =>
    routing.residualRecollection hn hH task.1 task.2
      ⟨TCReacha.reduction_factory_children
        hn hH routing.outerRouting factor structural.rankDefect
          structural.innerReductionOuter structural.right_tree htask⟩

end
  TWCase

/--
Reachable ranked routing plus a structural Hall-algorithm classification for
every exposed nested-word frontier.
-/
structure
    TEBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  nestedStructuralCase :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              WFCase
                  factor →
                TWCase
                  (n := n) factor

namespace
  TEBuild

/--
Compile structural nested-word classification into the residual-valued
nested-word frontier interface.
-/
noncomputable def
    rankedWordsBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TEBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    TCBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedWordsResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier =>
      let structural :=
        builder.nestedStructuralCase lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier
      structural.residualRecollection hn hH builder.routing factor

end
  TEBuild

/--
Reachable ranked routing plus direct inner-span inequalities for every
exposed nested-word frontier.
-/
structure
    TNBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  nestedInnerOuter :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.middle < frontier.right
  nestedOuterBasic :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic

namespace
  TNBuild

/--
Compile local direct-inner-span inequalities into structural nested-word
classification.
-/
noncomputable def
    rankedWordsStructural
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TNBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    TEBuild.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedStructuralCase :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier =>
      TWCase.inner_right_outer
        factor frontier hfactorTruncated
          (builder.nestedInnerOuter lowerWeight hnonterminal
            factor hfactorWeight hfactorTruncated frontier)
          (builder.nestedOuterBasic lowerWeight hnonterminal factor
            hfactorWeight hfactorTruncated frontier)

end
  TNBuild

namespace TSInput

/--
Structural classification of exposed nested-word frontiers constructs the
Claim 5 coordinate polynomials for a supported sourced input.
-/
theorem
    childrenExpandedBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TEBuild.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordChildrenBuilder
    hn hsourceSupported
      builder.rankedWordsBuilder
        hinputWeight

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsInnerSpanCollection.lean

/-!
# Direct inner-span collection for exposed nested Hall-power frontiers

The structural nested-word case applies automa when the retained
outer-right tree is basic and the inner-right tree is smaller. These are the
local inequalities inherited by ordinary descendants of a Hall-oriented
Jacobi step.

This file installs that direct branch automa and narrows the remaining
frontier boundary to nested roots where either inequality is unavailable.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
Reachable ranked routing, root-swap residuals, and a fallback only for nested
frontiers outside the direct structural inner-span case.
-/
structure
    TFBuildb
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  nestedWordsFallback :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                (¬frontier.middle < frontier.right ∨
                    ¬frontier.right.IsBasic) →
                  TSRecollb
                    (n := n) factor

namespace
  TFBuildb

/--
Use direct structural inner-span recollection whenever its local inequalities
hold, leaving only the complementary nested cases to the caller.
-/
noncomputable def
    rankedWordsBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TFBuildb.{u}
        (inputWeight := inputWeight) hn hH) :
    TCBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedWordsResidual := by
    intro lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier
    by_cases hinnerRightOuterRight : frontier.middle < frontier.right
    · by_cases houterRightBasic : frontier.right.IsBasic
      · exact
          (TWCase.inner_right_outer
            factor frontier hfactorTruncated hinnerRightOuterRight
              houterRightBasic).residualRecollection hn hH builder.routing
                factor
      · exact
          builder.nestedWordsFallback lowerWeight hnonterminal factor
            hfactorWeight hfactorTruncated frontier (Or.inr houterRightBasic)
    · exact
        builder.nestedWordsFallback lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier
            (Or.inl hinnerRightOuterRight)

end
  TFBuildb

namespace TSInput

/--
Direct nested inner-span collection with an explicit complementary fallback
constructs the Claim 5 coordinate polynomials for a supported sourced input.
-/
theorem
    coordPolyBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TFBuildb.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordChildrenBuilder
    hn hsourceSupported
      builder.rankedWordsBuilder
        hinputWeight

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsRecursiveBoundaryCollection.lean

/-!
# Recursive boundaries after direct nested Hall-power inner-span collection

Direct inner-span collection closes an exposed nested frontier whenever the
retained outer-right tree is basic and the inner-right tree is smaller. The
complement naturally separates into two recursive Hall-algorithm boundaries:

* a nonbasic retained outer-right tree must be normalized before it can serve
  as the unchanged outer factor;
* a basic retained outer-right tree with failed inner-span order carries the
  reverse inequality needed for a Jacobi recursion step.

This file packages that classification while leaving the two recursive
recollections explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
Reachable ranked routing, root-swap residuals, and the two recursive
boundaries left after direct nested inner-span collection.
-/
structure
    TBBuilda
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  retainedNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                ¬frontier.right.IsBasic →
                  TSRecollb
                    (n := n) factor
  failedInnerOrder :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right ≤ frontier.middle →
                    TSRecollb
                      (n := n) factor

namespace
  TBBuilda

/--
Classify every complement of the direct inner-span branch into retained-right
normalization or failed-order Jacobi recursion.
-/
noncomputable def
    rankedChildrenWords
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TBBuilda.{u}
        (inputWeight := inputWeight) hn hH) :
    TFBuildb.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedWordsFallback := by
    intro lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier hcomplement
    by_cases hrightBasic : frontier.right.IsBasic
    · have hfailedOrder : ¬frontier.middle < frontier.right := by
        intro hinnerRightOuterRight
        exact
          hcomplement.elim
            (fun h => h hinnerRightOuterRight)
            (fun h => h hrightBasic)
      exact
        builder.failedInnerOrder lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier hrightBasic
            (le_of_not_gt hfailedOrder)
    · exact
        builder.retainedNonbasicResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier hrightBasic

end
  TBBuilda

namespace TSInput

/--
Recursive-boundary classification after direct nested inner-span collection
constructs the Claim 5 coordinate polynomials for a supported sourced input.
-/
theorem
    coordBoundaryBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TBBuilda.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordPolyBuilder
    hn hsourceSupported
      builder.rankedChildrenWords
        hinputWeight

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsFailedOrderCollection.lean

/-!
# Strict Jacobi recursion for failed nested Hall-power inner-span order

When direct inner-span collection fails with a basic retained outer-right
tree, the reverse inequality `right ≤ middle` is available. In the strict
Hall-oriented subcase

`right < middle < left`

with basic inner children, the exposed nested root is exactly a ranked
expanded-Jacobi decomposition. Canonical routing flattens its two ordinary
descendants and recollects only strict grandchildren.

This file installs that branch automa and leaves four smaller
recursive boundaries explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
Reachable ranked routing and the recursive boundaries left after installing
the strict basic-right failed-order Jacobi branch.
-/
structure
    TFBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  retainedNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                ¬frontier.right.IsBasic →
                  TSRecollb
                    (n := n) factor
  repeatedRightResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    TSRecollb
                      (n := n) factor
  leftNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    ¬frontier.left.IsBasic →
                      TSRecollb
                        (n := n) factor
  middleNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle.IsBasic →
                        TSRecollb
                          (n := n) factor
  failedInnerChildren :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      frontier.middle.IsBasic →
                        ¬frontier.middle < frontier.left →
                          TSRecollb
                            (n := n) factor

namespace
  TFBuild

/--
Install strict basic-right failed-order Jacobi recursion and leave only its
smaller complementary boundaries explicit.
-/
noncomputable def
    rankedChildrenFrontier
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TFBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    TBBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  retainedNonbasicResidual := builder.retainedNonbasicResidual
  failedInnerOrder := by
    intro lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier hrightBasic hrightMiddle
    by_cases hrightEqMiddle : frontier.right = frontier.middle
    · exact
        builder.repeatedRightResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier hrightBasic hrightEqMiddle
    · have hrightLtMiddle : frontier.right < frontier.middle :=
        lt_of_le_of_ne hrightMiddle hrightEqMiddle
      by_cases hleftBasic : frontier.left.IsBasic
      · by_cases hmiddleBasic : frontier.middle.IsBasic
        · by_cases hmiddleLtLeft : frontier.middle < frontier.left
          · let ranked :=
              TRDecomp.nonbasic_commutator_tree
                factor frontier.left frontier.middle frontier.right
                  frontier.tree_eq frontier.outer_nonbasic hrightLtMiddle
                    hmiddleLtLeft hleftBasic hmiddleBasic
            exact
              builder.routing
                |>.expanded_ranked_decomposition
                  hn hH factor ranked hfactorTruncated
          · exact
              builder.failedInnerChildren lowerWeight
                hnonterminal factor hfactorWeight hfactorTruncated frontier
                  hrightBasic hrightLtMiddle hleftBasic hmiddleBasic
                    hmiddleLtLeft
        · exact
            builder.middleNonbasicResidual lowerWeight hnonterminal factor
              hfactorWeight hfactorTruncated frontier hrightBasic
                hrightLtMiddle hleftBasic hmiddleBasic
      · exact
          builder.leftNonbasicResidual lowerWeight hnonterminal factor
            hfactorWeight hfactorTruncated frontier hrightBasic
              hrightLtMiddle hleftBasic

end
  TFBuild

namespace TSInput

/--
Strict failed-order Jacobi collection with explicit smaller boundaries
constructs the Claim 5 coordinate polynomials for a supported sourced input.
-/
theorem
    coordFailedBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TFBuild.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordBoundaryBuilder
    hn hsourceSupported
      builder.rankedChildrenFrontier
        hinputWeight

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsRetainedRightRecollection.lean

/-!
# Structural recollection for nonbasic retained-right Hall-power frontiers

An exposed nested frontier `[[left, middle], right]` cannot use direct
inner-span collection when `right` is nonbasic. Swapping the root once gives
`[right, [left, middle]]`. Exposing `right = [rightLeft, rightMiddle]` and
applying Jacobi produces two descendants whose retained outer-right trees are
the proper subtrees `rightMiddle` and `rightLeft`.

This file records that structural step and reconstructs the original
residual from recollections of the two proper-subtree descendants.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

/-- Swap an exposed nested frontier so that its retained right tree is on the left. -/
noncomputable def rootSwapFactor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor) :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight :=
  expandedSwapFactor factor
    (.commutator frontier.decomposition.left frontier.decomposition.middle)
    frontier.decomposition.right frontier.decomposition.word_eq

@[simp]
theorem root_swap_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor) :
    (rootSwapFactor factor frontier).word.weight
        PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  exact
    expanded_root_factor factor
      (.commutator frontier.decomposition.left frontier.decomposition.middle)
      frontier.decomposition.right frontier.decomposition.word_eq

/-- The symbolic words exposed by a nested frontier have the advertised trees. -/
theorem trees_decomposition_frontier
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor) :
    tree frontier.decomposition.left = frontier.left ∧
      tree frontier.decomposition.middle = frontier.middle ∧
        tree frontier.decomposition.right = frontier.right := by
  have htree := congrArg tree frontier.decomposition.word_eq
  simp only [tree_commutator] at htree
  have hroot := htree.symm.trans frontier.tree_eq
  injection hroot with hinner hright
  injection hinner with hleft hmiddle
  exact ⟨hleft, hmiddle, hright⟩

@[simp]
theorem tree_swap_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor) :
    tree (rootSwapFactor factor frontier).word =
      .commutator frontier.right (.commutator frontier.left frontier.middle) := by
  rcases trees_decomposition_frontier factor frontier with
    ⟨hleft, hmiddle, hright⟩
  simp only [rootSwapFactor,
    tree_expanded_swap, tree_commutator, hleft, hmiddle, hright]

/--
The reversed retained-right frontier together with the exposed children of
its nonbasic left root.
-/
structure
    CJDecomp
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor) where
  left :
    HallTree (FreeGenerator.{u} d)
  middle :
    HallTree (FreeGenerator.{u} d)
  right_eq : frontier.right = .commutator left middle
  decomposition :
    ExpandedJacobiDecomposition
      (rootSwapFactor factor frontier).word
  left_tree : tree decomposition.left = left
  middle_tree : tree decomposition.middle = middle
  right_tree :
    tree decomposition.right = .commutator frontier.left frontier.middle

namespace
  CJDecomp

/-- Expose the two children of a nonbasic retained-right tree after one root swap. -/
noncomputable def ofNonbasic
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic) :
    CJDecomp
      factor frontier := by
  cases hright : frontier.right with
  | atom generator =>
      exfalso
      apply hrightNonbasic
      rw [hright]
      exact HallTree.isBasic_atom generator
  | commutator left middle =>
      have htree :
          tree (rootSwapFactor factor frontier).word =
            .commutator (.commutator left middle)
              (.commutator frontier.left frontier.middle) := by
        rw [tree_swap_factor, hright]
      have houterNonbasic :
          ¬(HallTree.commutator (.commutator left middle)
              (.commutator frontier.left frontier.middle)).IsBasic := by
        intro hbasic
        apply hrightNonbasic
        rw [hright]
        exact (HallTree.isBasic_commutator _ _).mp hbasic |>.1
      let decomposition :=
        expandedTreeNonbasic
          (rootSwapFactor factor frontier).word left middle
            (.commutator frontier.left frontier.middle) htree houterNonbasic
      have hroot :
          HallTree.commutator
              (.commutator (tree decomposition.left)
                (tree decomposition.middle))
              (tree decomposition.right) =
            .commutator (.commutator left middle)
              (.commutator frontier.left frontier.middle) :=
        decomposition.tree_eq.symm.trans htree
      injection hroot with hinner hrightTree
      injection hinner with hleftTree hmiddleTree
      exact
        {
          left := left
          middle := middle
          right_eq := hright
          decomposition := decomposition
          left_tree := hleftTree
          middle_tree := hmiddleTree
          right_tree := hrightTree
        }

/-- The first retained-right descendant ends in the second proper subtree. -/
@[simp]
theorem tree_first_factor
    {d inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {frontier :
      WFCase
        factor}
    (retained :
      CJDecomp
        factor frontier) :
    tree
        (expandedJacobiFactor
          (rootSwapFactor factor frontier)
          retained.decomposition).word =
      .commutator
        (.commutator retained.left
          (.commutator frontier.left frontier.middle))
        retained.middle := by
  rw [tree_expanded_factor]
  simp only [HallTree.leftJacobiDescendant, retained.left_tree,
    retained.middle_tree, retained.right_tree]

/-- The second retained-right descendant ends in the first proper subtree. -/
@[simp]
theorem tree_second_factor
    {d inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {frontier :
      WFCase
        factor}
    (retained :
      CJDecomp
        factor frontier) :
    tree
        (expandedJacobiSecond
          (rootSwapFactor factor frontier)
          retained.decomposition).word =
      .commutator
        (.commutator retained.middle
          (.commutator frontier.left frontier.middle))
        retained.left := by
  rw [tree_expanded_jacobi]
  simp only [HallTree.leftSecondDescendant, retained.left_tree,
    retained.middle_tree, retained.right_tree]

/-- The first child exposed from the retained right root is strictly smaller. -/
theorem left_lt_right
    {d inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {frontier :
      WFCase
        factor}
    (retained :
      CJDecomp
        factor frontier) :
    retained.left < frontier.right := by
  rw [retained.right_eq]
  exact HallTree.lt_commutator_left retained.left retained.middle

/-- The second child exposed from the retained right root is strictly smaller. -/
theorem middle_lt_right
    {d inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {frontier :
      WFCase
        factor}
    (retained :
      CJDecomp
        factor frontier) :
    retained.middle < frontier.right := by
  rw [retained.right_eq]
  exact HallTree.lt_commutator_right retained.left retained.middle

end
  CJDecomp

namespace
  TSRecollb

open
  CJDecomp

/--
Swap one nonbasic retained-right frontier, recurse on its two proper-subtree
Jacobi descendants, and reconstruct the original residual.
-/
noncomputable def retained_right_nonbasic
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (normalizerFamily :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (first :
      let retained := ofNonbasic factor frontier hrightNonbasic
      TSRecollb
        (n := n)
        (expandedJacobiFactor
          (rootSwapFactor factor frontier)
          retained.decomposition))
    (second :
      let retained := ofNonbasic factor frontier hrightNonbasic
      TSRecollb
        (n := n)
        (expandedJacobiSecond
          (rootSwapFactor factor frontier)
          retained.decomposition))
    (rootSwapResidual :
      TSRecolla
        (n := n) factor
          (.commutator frontier.decomposition.left frontier.decomposition.middle)
          frontier.decomposition.right frontier.decomposition.word_eq) :
    TSRecollb
      (n := n) factor :=
  let retained := ofNonbasic factor frontier hrightNonbasic
  let reversed := rootSwapFactor factor frontier
  let reversedResidual :=
    expanded_normalizer_family hn hH packet hinputWeight
      normalizerFamily reversed retained.decomposition
      (by simpa only [reversed, root_swap_factor]
        using hfactorWeight)
      (by
        simpa only [reversed, root_swap_factor]
          using hfactorTruncated)
      first second
  expanded_swap factor
    (.commutator frontier.decomposition.left frontier.decomposition.middle)
    frontier.decomposition.right frontier.decomposition.word_eq
      reversedResidual rootSwapResidual

end
  TSRecollb

end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsRetainedRightCollection.lean

/-!
# Structural recursion for nonbasic retained-right Hall-power frontiers

The retained-right reconstruction primitive replaces one nonbasic retained
outer-right frontier by two Jacobi descendants whose retained right trees are
proper subtrees. This file installs that primitive in the collector-facing
failed-order interface.

The old opaque retained-right residual callback is replaced by recollections
of the two proper-subtree descendants. The remaining boundaries are smaller
Hall-algorithm cases left explicit for the next layer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open
  HEWord
  CJDecomp

/--
Reachable ranked routing and the recursive boundaries left after replacing a
nonbasic retained-right root by its two proper-subtree Jacobi descendants.
-/
structure
    FCBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  inputWeight_pos : 1 ≤ inputWeight
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  retainedFirstResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ (frontier :
                WFCase
                  factor)
                (hrightNonbasic : ¬frontier.right.IsBasic),
                let retained :=
                  ofNonbasic factor frontier hrightNonbasic
                TSRecollb
                  (n := n)
                  (expandedJacobiFactor
                    (rootSwapFactor factor frontier)
                    retained.decomposition)
  retainedSecondResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ (frontier :
                WFCase
                  factor)
                (hrightNonbasic : ¬frontier.right.IsBasic),
                let retained :=
                  ofNonbasic factor frontier hrightNonbasic
                TSRecollb
                  (n := n)
                  (expandedJacobiSecond
                    (rootSwapFactor factor frontier)
                    retained.decomposition)
  repeatedRightResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    TSRecollb
                      (n := n) factor
  leftNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    ¬frontier.left.IsBasic →
                      TSRecollb
                        (n := n) factor
  middleNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle.IsBasic →
                        TSRecollb
                          (n := n) factor
  failedInnerChildren :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      frontier.middle.IsBasic →
                        ¬frontier.middle < frontier.left →
                          TSRecollb
                            (n := n) factor

namespace
  FCBuild

open
  TSRecollb

/--
Swap one nonbasic retained-right frontier, recurse on its two proper-subtree
Jacobi descendants, and reconstruct the original residual.
-/
noncomputable def retainedNonbasicResidual
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      FCBuild.{u}
        (inputWeight := inputWeight) hn hH)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (frontier :
      WFCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic) :
    TSRecollb
      (n := n) factor :=
  retained_right_nonbasic hn hH builder.packet builder.inputWeight_pos
    builder.routing.normalizerFamily factor frontier hrightNonbasic
      hfactorWeight hfactorTruncated
      (builder.retainedFirstResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic)
      (builder.retainedSecondResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic)
      (builder.rootSwapResidual lowerWeight hnonterminal factor
        (.commutator frontier.decomposition.left frontier.decomposition.middle)
        frontier.decomposition.right frontier.decomposition.word_eq
          hfactorWeight hfactorTruncated)

/-- Compile structural retained-right recursion into the strict failed-order builder. -/
noncomputable def
    expandedWordsFailed
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      FCBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    TFBuild.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  retainedNonbasicResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier hrightNonbasic =>
      builder.retainedNonbasicResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic
  repeatedRightResidual := builder.repeatedRightResidual
  leftNonbasicResidual := builder.leftNonbasicResidual
  middleNonbasicResidual := builder.middleNonbasicResidual
  failedInnerChildren := builder.failedInnerChildren

end
  FCBuild

namespace TSInput

/--
Structural retained-right Jacobi recursion with explicit smaller boundaries
constructs the Claim 5 coordinate polynomials for a supported sourced input.
-/
theorem
    coordFrontierBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      FCBuild.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordFailedBuilder
    hn hsourceSupported
      builder.expandedWordsFailed
        builder.inputWeight_pos

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsRetainedRightDescendants.lean

/-!
# Certified descendants for retained-right Hall-power recursion

The retained-right Jacobi step produces two recursive factor residuals. This
file packages each one with the proper-subtree inequality proved by the
structural decomposition:

* the first descendant retains the second child of the old right root;
* the second descendant retains the first child of the old right root.

Both children are strictly smaller than the old retained right tree. A
single callback over certified descendants therefore replaces the two
unstructured recursive callbacks.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord
open
  CJDecomp

universe u

/-- One Hall-power factor residual generated with a strictly smaller retained right tree. -/
structure
    CDCase
    {d inputWeight : ℕ}
    (parent :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        parent) where
  factor :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight
  left :
    HallTree (FreeGenerator.{u} d)
  retainedRight :
    HallTree (FreeGenerator.{u} d)
  tree_eq :
    tree factor.word = .commutator left retainedRight
  retainedRight_lt : retainedRight < frontier.right

namespace
  CDCase

/-- The first reversed Jacobi descendant retains the second proper subtree. -/
noncomputable def first
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic) :
    CDCase
      factor frontier :=
  let retained := ofNonbasic factor frontier hrightNonbasic
  {
    factor :=
      expandedJacobiFactor
        (rootSwapFactor factor frontier) retained.decomposition
    left :=
      .commutator retained.left (.commutator frontier.left frontier.middle)
    retainedRight := retained.middle
    tree_eq := retained.tree_first_factor
    retainedRight_lt := retained.middle_lt_right
  }

/-- The second reversed Jacobi descendant retains the first proper subtree. -/
noncomputable def second
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic) :
    CDCase
      factor frontier :=
  let retained := ofNonbasic factor frontier hrightNonbasic
  {
    factor :=
      expandedJacobiSecond
        (rootSwapFactor factor frontier) retained.decomposition
    left :=
      .commutator retained.middle (.commutator frontier.left frontier.middle)
    retainedRight := retained.left
    tree_eq := retained.tree_second_factor
    retainedRight_lt := retained.left_lt_right
  }

end
  CDCase

/--
Reachable ranked routing and the recursive boundaries left after retained
right Jacobi recursion has been reduced to certified proper-subtree
descendants.
-/
structure
    TDBuilda
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  inputWeight_pos : 1 ≤ inputWeight
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  retainedDescendantResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ (frontier :
                WFCase
                  factor)
                (_hrightNonbasic : ¬frontier.right.IsBasic)
                (descendant :
                  CDCase
                    factor frontier),
                  TSRecollb
                    (n := n) descendant.factor
  repeatedRightResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    TSRecollb
                      (n := n) factor
  leftNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    ¬frontier.left.IsBasic →
                      TSRecollb
                        (n := n) factor
  middleNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle.IsBasic →
                        TSRecollb
                          (n := n) factor
  failedInnerChildren :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      frontier.middle.IsBasic →
                        ¬frontier.middle < frontier.left →
                          TSRecollb
                            (n := n) factor

namespace
  TDBuilda

open
  CDCase

/-- Compile the two retained-right descendant slots from one certified callback. -/
noncomputable def frontierCollectionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TDBuilda.{u}
        (inputWeight := inputWeight) hn hH) :
    FCBuild.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  inputWeight_pos := builder.inputWeight_pos
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  retainedFirstResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier hrightNonbasic =>
      builder.retainedDescendantResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic
          (first factor frontier hrightNonbasic)
  retainedSecondResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier hrightNonbasic =>
      builder.retainedDescendantResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic
          (second factor frontier hrightNonbasic)
  repeatedRightResidual := builder.repeatedRightResidual
  leftNonbasicResidual := builder.leftNonbasicResidual
  middleNonbasicResidual := builder.middleNonbasicResidual
  failedInnerChildren := builder.failedInnerChildren

end
  TDBuilda

namespace TSInput

/--
Certified retained-right descendants with explicit smaller boundaries
construct the Claim 5 coordinate polynomials for a supported sourced input.
-/
theorem
    coordDescendantsBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TDBuilda.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordFrontierBuilder
    hn hsourceSupported builder.frontierCollectionBuilder

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsOuterRightContextualCollection.lean

/-!
# Contextual collection for basic outer-right Hall-power frontiers

For an exposed nested frontier `[[left, middle], right]`, full-context inner
reduction is stronger than the direct ranked inner-span wrapper. If `right`
is Hall-basic, reducing the immediate inner bracket emits a finite packet
`[basic_i, right]`, and each emitted child has its own canonical
two-basic-child rank.

Thus every basic outer-right frontier recollects contextually, independently
of the order or Hall shape of its inner children. The only remaining nested
boundary has nonbasic retained right tree. Its established root-swap Jacobi
step produces two certified descendants with proper-subtree retained rights.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord
open
  CJDecomp
  CDCase

namespace
  TSRecollb

/--
Fold independently recollected concrete residuals over an arbitrary finite
Hall-power source.
-/
noncomputable def source_recollection_residuals
    {d n inputWeight lowerWeight : ℕ}
    (source :
      List
        (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight))
    (hsourceTruncated :
      SPFactora.IsTruncated n source)
    (hsourceSupported :
      SPFactora.WordWeightLeast lowerWeight source)
    (residual :
      ∀ factor ∈ source,
        TSRecollb
          (n := n) factor) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) source := by
  have hsource :
      source.flatMap
          (fun factor :
              SPFactora
                (concreteBasicCommutators.{u} d) inputWeight =>
            [factor]) =
        source := by
    clear hsourceTruncated hsourceSupported residual
    induction source with
    | nil =>
        rfl
    | cons factor source ih =>
        simp only [List.flatMap_cons, List.singleton_append, ih]
  rw [← hsource]
  exact
    TSRecol.flatMap
      source
      (fun factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight =>
        [factor])
      (fun factor hfactor =>
        (residual factor hfactor).singletonSourceRecollection
          (hsourceTruncated factor hfactor)
          (hsourceSupported factor hfactor))

end
  TSRecollb

namespace
  TCReacha

/--
Every full-weight child emitted by contextual inner reduction is
independently reachable once the retained right word expands to a Hall-basic
tree.
-/
noncomputable def inner_reduction_outer
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (unchanged : HallTree (FreeGenerator.{u} d))
    (hrightTree : tree rightWord = unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    {child :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hchild :
      child ∈
        HEWord.innerOuterFactors
          factor innerWord rightWord hword) :
    Σ rankDefect : ℕ,
      TCReacha
        (n := n) child rankDefect := by
  rw [HEWord.innerOuterFactors] at hchild
  let indexExists := List.mem_map.mp hchild
  let i := Classical.choose indexExists
  have hi := Classical.choose_spec indexExists
  have hchild_eq := hi.2
  rw [← hchild_eq]
  exact
    ⟨HallTree.bracketRankDefect
        ((HallTree.indexedBasicTree i).weight + unchanged.weight)
        (HallTree.indexedBasicTree i) unchanged,
      {
        left := HallTree.indexedBasicTree i
        right := unchanged
        left_isBasic := HallTree.indexed_tree i
        right_isBasic := hunchangedBasic
        tree_eq := by
          rw [inner_reduction_factor, tree_commutator, tree_atom,
            basicReductionAddress, concreteBasicTree, hrightTree]
        factor_truncated := by
          rw [inner_outer_factor]
          exact hfactorTruncated
        rankDefect_eq := rfl
      }⟩

end
  TCReacha

namespace
  TSRecollb

/--
Recollect a parent by reducing its immediate inner bracket at full parent
weight and routing every emitted two-basic-child factor independently.
-/
noncomputable def
    inner_reduction_residuals
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
    (residual :
      ∀ child ∈
          HEWord.innerOuterFactors
            factor innerWord rightWord hword,
        TSRecollb
          (n := n) child) :
    TSRecollb
      (n := n) factor := by
  let children :=
    source_recollection_residuals
      (HEWord.innerOuterFactors
        factor innerWord rightWord hword)
      (HEWord.truncated_inner_factors
        factor innerWord rightWord hword hfactorTruncated)
      (HEWord.least_inner_factors
        factor innerWord rightWord hword)
      residual
  let normalizer :=
    family.normalizer
      (factor.word.weight PEAddres.weight)
  let comparison :=
    normalizer.child_normalized_raw
      hn hH factor innerWord rightWord hword rfl factor.word_weight_pos
        hfactorTruncated children
  let outer :=
    normalizer.recollection_inner_raw
      hn hH factor innerWord rightWord hword rfl factor.word_weight_pos
        hfactorTruncated
  exact
    inner_child_normalization factor innerWord rightWord
      hword children
      (by
        simpa only [
          HEWord.innerChildNormalized]
          using comparison)
      outer

end
  TSRecollb

namespace
  WFCase

/--
Collect any nested Hall-power frontier whose retained outer-right tree is
Hall-basic. The complete parent coefficient remains attached to every
reworded child.
-/
noncomputable def outerResidualRecollect
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRouteb
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor)
    (hrightBasic : frontier.right.IsBasic)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor := by
  let innerWord :=
    CWord.commutator frontier.decomposition.left
      frontier.decomposition.middle
  let rightWord := frontier.decomposition.right
  have hrightTree : tree rightWord = frontier.right := by
    exact (trees_decomposition_frontier factor frontier).2.2
  apply
    TSRecollb.inner_reduction_residuals
      hn hH routing.normalizerFamily factor innerWord rightWord
        frontier.decomposition.word_eq hfactorTruncated
  intro child hchild
  let reachable :=
    TCReacha.inner_reduction_outer
      factor innerWord rightWord frontier.decomposition.word_eq
        frontier.right hrightTree hrightBasic hfactorTruncated hchild
  exact
    routing.residualRecollection hn hH child reachable.1 ⟨reachable.2⟩

end
  WFCase

/--
Reachable ranked routing and one recursive proper-subtree boundary for
nonbasic retained outer-right trees.
-/
structure
    TCBuildd
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  inputWeight_pos : 1 ≤ inputWeight
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  retainedDescendantResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ (frontier :
                WFCase
                  factor)
                (_hrightNonbasic : ¬frontier.right.IsBasic)
                (descendant :
                  CDCase
                    factor frontier),
                  TSRecollb
                    (n := n) descendant.factor

namespace
  TCBuildd

/--
Compile contextual basic-right collection and retained-right subtree
recursion directly into the exposed nested-word frontier interface.
-/
noncomputable def
    expandedWordsBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TCBuildd.{u}
        (inputWeight := inputWeight) hn hH) :
    TCBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedWordsResidual := by
    intro lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier
    by_cases hrightBasic : frontier.right.IsBasic
    · exact
        WFCase.outerResidualRecollect
          hn hH builder.routing factor frontier hrightBasic hfactorTruncated
    · exact
        TSRecollb.retained_right_nonbasic
          hn hH builder.packet builder.inputWeight_pos
            builder.routing.normalizerFamily factor frontier hrightBasic
              hfactorWeight hfactorTruncated
              (builder.retainedDescendantResidual lowerWeight
                hnonterminal factor hfactorWeight hfactorTruncated frontier
                  hrightBasic (first factor frontier hrightBasic))
              (builder.retainedDescendantResidual lowerWeight
                hnonterminal factor hfactorWeight hfactorTruncated frontier
                  hrightBasic (second factor frontier hrightBasic))
              (builder.rootSwapResidual lowerWeight hnonterminal factor
                (.commutator frontier.decomposition.left
                  frontier.decomposition.middle)
                frontier.decomposition.right frontier.decomposition.word_eq
                  hfactorWeight hfactorTruncated)

end
  TCBuildd

namespace TSInput

/--
Contextual basic-right collection and certified retained-right subtree
recursion construct the Claim 5 coordinate polynomials for a supported
sourced input.
-/
theorem
    coordContextualBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TCBuildd.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordChildrenBuilder
    hn hsourceSupported
      builder.expandedWordsBuilder
        builder.inputWeight_pos

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsOuterRightSubtreeRecursion.lean

/-!
# Well-founded recursion for retained-right Hall-power frontiers

Every exposed nested frontier `[[left, middle], right]` with Hall-basic
`right` recollects contextually. When `right` is nonbasic, the retained-right
Jacobi step produces two descendants whose new retained-right trees are
proper subtrees of `right`.

This file closes that final recursive boundary. A recursive task carries an
exposed nested frontier and its fixed Hall-power weight. Each actual Jacobi
descendant is classified at its new root:

* basic, self, and reverse-basic roots recollect immediately;
* the remaining root is another exposed nested frontier;
* its retained-right tree is strictly smaller than the parent task's tree.

The resulting recursion is well founded by `HallTree.lt_wellFounded`.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord
open
  TSRecollb
  CJDecomp
  CDCase

/-- One exposed nested Hall-power frontier scheduled at a fixed weight. -/
structure
    TSTask
    {d n inputWeight : ℕ}
    (lowerWeight : ℕ) where
  factor :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight
  factor_weight :
    factor.word.weight PEAddres.weight = lowerWeight
  factor_truncated :
    factor.word.weight PEAddres.weight < n
  frontier :
    WFCase
      factor

namespace
  TSTask

/-- Recursive tasks decrease by their retained outer-right Hall tree. -/
def RetainedRightLT
    {d n inputWeight lowerWeight : ℕ}
    (child parent :
      TSTask.{u}
        (d := d) (n := n) (inputWeight := inputWeight) lowerWeight) :
    Prop :=
  child.frontier.right < parent.frontier.right

/-- Retained-right Hall-power task recursion is well founded by the Hall-tree order. -/
theorem well_founded_right
    {d n inputWeight lowerWeight : ℕ} :
    WellFounded
      (RetainedRightLT.{u}
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)) := by
  unfold RetainedRightLT
  exact InvImage.wf
    (fun task :
        TSTask.{u}
          (d := d) (n := n) (inputWeight := inputWeight) lowerWeight =>
      task.frontier.right)
    (HallTree.lt_wellFounded (α := FreeGenerator.{u} d))

/--
Classify one actual retained-right descendant. Terminal roots recollect
immediately. Every surviving Jacobi root becomes a strictly smaller task.
-/
noncomputable def residual_recollection_descendant
    {d n inputWeight lowerWeight : ℕ}
    {parent :
      TSTask.{u}
        (d := d) (n := n) (inputWeight := inputWeight) lowerWeight}
    (descendant :
      CDCase
        parent.factor parent.frontier)
    (newLeft newMiddle : HallTree (FreeGenerator.{u} d))
    (hdescendantLeft :
      descendant.left = .commutator newLeft newMiddle)
    (hnewMiddleNonbasic : ¬newMiddle.IsBasic)
    (hfactorWeight :
      descendant.factor.word.weight PEAddres.weight =
        lowerWeight)
    (hfactorTruncated :
      descendant.factor.word.weight PEAddres.weight < n)
    (recursive :
      ∀ child :
          TSTask.{u}
            (d := d) (n := n) (inputWeight := inputWeight) lowerWeight,
        RetainedRightLT child parent →
          TSRecollb
            (n := n) child.factor) :
    TSRecollb
      (n := n) descendant.factor := by
  by_cases htreeBasic : (tree descendant.factor.word).IsBasic
  · exact tree_basic descendant.factor htreeBasic
  · by_cases hchildrenEq : descendant.left = descendant.retainedRight
    · exact
        tree_commutator_self descendant.factor descendant.left
          (by simpa only [hchildrenEq] using descendant.tree_eq)
    · by_cases hreverseBasic :
          (HallTree.commutator descendant.retainedRight descendant.left).IsBasic
      · exact
          tree_swap_basic descendant.factor descendant.retainedRight
            descendant.left descendant.tree_eq hreverseBasic
      · have htree :
            tree descendant.factor.word =
              .commutator (.commutator newLeft newMiddle)
                descendant.retainedRight := by
          rw [descendant.tree_eq, hdescendantLeft]
        have houterNonbasic :
            ¬(HallTree.commutator (.commutator newLeft newMiddle)
                descendant.retainedRight).IsBasic := by
          intro hbasic
          apply htreeBasic
          rw [htree]
          exact hbasic
        have hinnerNonbasic :
            ¬(HallTree.commutator newLeft newMiddle).IsBasic := by
          intro hbasic
          exact
            hnewMiddleNonbasic
              ((HallTree.isBasic_commutator newLeft newMiddle).mp hbasic).2.1
        let decomposition :=
          syntacticTreeNonbasic
            descendant.factor.word newLeft newMiddle descendant.retainedRight
              htree houterNonbasic hinnerNonbasic
        let child :
            TSTask.{u}
              (d := d) (n := n) (inputWeight := inputWeight) lowerWeight :=
          {
            factor := descendant.factor
            factor_weight := hfactorWeight
            factor_truncated := hfactorTruncated
            frontier :=
              {
                left := newLeft
                middle := newMiddle
                right := descendant.retainedRight
                tree_eq := htree
                outer_nonbasic := houterNonbasic
                inner_nonbasic := hinnerNonbasic
                children_ne := by
                  simpa only [← hdescendantLeft] using hchildrenEq
                reverse_nonbasic := by
                  simpa only [← hdescendantLeft] using hreverseBasic
                decomposition := decomposition
              }
          }
        exact
          recursive child (by
            simpa only [RetainedRightLT, child] using
              descendant.retainedRight_lt)

end
  TSTask

/--
Canonical powered routing data is enough to close retained-right subtree
recursion. The same normalizer family carried by routing also recollects
root-swap value packets.
-/
structure
    TSBuildb
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  inputWeight_pos : 1 ≤ inputWeight
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)

namespace
  TSBuildb

open
  TSTask

/-- Resolve one retained-right subtree task, assuming smaller tasks resolved. -/
noncomputable def resolveTaskStep
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TSBuildb.{u}
        (inputWeight := inputWeight) hn hH)
    (task :
      TSTask.{u}
        (d := d) (n := n) (inputWeight := inputWeight) lowerWeight)
    (recursive :
      ∀ child :
          TSTask.{u}
            (d := d) (n := n) (inputWeight := inputWeight) lowerWeight,
        RetainedRightLT child task →
          TSRecollb
            (n := n) child.factor) :
    TSRecollb
      (n := n) task.factor := by
  by_cases hrightBasic : task.frontier.right.IsBasic
  · exact
      WFCase.outerResidualRecollect
        hn hH builder.routing task.factor task.frontier hrightBasic
          task.factor_truncated
  · let retained := ofNonbasic task.factor task.frontier hrightBasic
    let firstDescendant := first task.factor task.frontier hrightBasic
    let secondDescendant := second task.factor task.frontier hrightBasic
    have hfirstWeight :
        firstDescendant.factor.word.weight PEAddres.weight =
          lowerWeight := by
      simpa only [firstDescendant, first,
        expanded_jacobi_factor,
        root_swap_factor] using task.factor_weight
    have hfirstTruncated :
        firstDescendant.factor.word.weight PEAddres.weight <
          n := by
      simpa only [firstDescendant, first,
        expanded_jacobi_factor,
        root_swap_factor] using
          task.factor_truncated
    have hsecondWeight :
        secondDescendant.factor.word.weight PEAddres.weight =
          lowerWeight := by
      simpa only [secondDescendant, second,
        expanded_second_factor,
        root_swap_factor] using task.factor_weight
    have hsecondTruncated :
        secondDescendant.factor.word.weight PEAddres.weight <
          n := by
      simpa only [secondDescendant, second,
        expanded_second_factor,
        root_swap_factor] using
          task.factor_truncated
    let firstResidual :=
      residual_recollection_descendant firstDescendant retained.left
        (.commutator task.frontier.left task.frontier.middle) (by rfl)
          task.frontier.inner_nonbasic hfirstWeight hfirstTruncated recursive
    let secondResidual :=
      residual_recollection_descendant secondDescendant retained.middle
        (.commutator task.frontier.left task.frontier.middle) (by rfl)
          task.frontier.inner_nonbasic hsecondWeight hsecondTruncated recursive
    let reversed := rootSwapFactor task.factor task.frontier
    let reversedResidual :=
      expanded_normalizer_family hn hH builder.packet
        builder.inputWeight_pos builder.routing.normalizerFamily reversed
          retained.decomposition
        (by
          simpa only [reversed,
            root_swap_factor] using
              task.factor_weight)
        (by
          simpa only [reversed,
            root_swap_factor] using
              task.factor_truncated)
        firstResidual secondResidual
    exact
      expanded_swap task.factor
        (.commutator task.frontier.decomposition.left
          task.frontier.decomposition.middle)
        task.frontier.decomposition.right task.frontier.decomposition.word_eq
          reversedResidual
          (TSRecolla.ofNormalizerFamily
            hn hH builder.routing.normalizerFamily task.factor
              (.commutator task.frontier.decomposition.left
                task.frontier.decomposition.middle)
              task.frontier.decomposition.right
                task.frontier.decomposition.word_eq task.factor_weight
                  task.factor_truncated)

/-- Run the retained-right resolver by well-founded Hall-tree recursion. -/
noncomputable def taskResidualRecollection
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TSBuildb.{u}
        (inputWeight := inputWeight) hn hH)
    (task :
      TSTask.{u}
        (d := d) (n := n) (inputWeight := inputWeight) lowerWeight) :
    TSRecollb
      (n := n) task.factor :=
  (well_founded_right
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight)).fix
    (fun task recursive => builder.resolveTaskStep task recursive) task

/--
Compile closed retained-right recursion into the exposed nested-word
frontier interface.
-/
noncomputable def
    expandedWordsBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TSBuildb.{u}
        (inputWeight := inputWeight) hn hH) :
    TCBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := by
    intro _lowerWeight _hnonterminal factor left right hword hfactorWeight
      hfactorTruncated
    exact
      TSRecolla.ofNormalizerFamily
        hn hH builder.routing.normalizerFamily factor left right hword
          hfactorWeight hfactorTruncated
  nestedWordsResidual :=
    fun lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        frontier =>
      builder.taskResidualRecollection
        {
          factor := factor
          factor_weight := hfactorWeight
          factor_truncated := hfactorTruncated
          frontier := frontier
        }

end
  TSBuildb

open TSBuildb

namespace TSInput

/--
Closed retained-right subtree recursion constructs the Claim 5 coordinate
polynomials for a supported sourced input.
-/
theorem
    coordSubtreeBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TSBuildb.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordChildrenBuilder
    hn hsourceSupported
      builder.expandedWordsBuilder
        builder.inputWeight_pos

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsOuterRightSubtreeRecursionFromNormalizer.lean

/-!
# Closed retained-right Hall-power recursion from normalizer families

The closed retained-right subtree resolver needs a Hall-Petresco packet,
positive input weight, and canonical ranked routing. A semantic normalizer
family and correction-factory schedule provide that routing directly.

For retained recipe coefficients, the product law supplies both the integral
packet and the correction-factory schedule. This file packages the resulting
compatibility endpoint while leaving the same-stratum normalizer family
explicit.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open
  CCThree
open
  CPSplita

namespace
  SCRouteb

/--
A complete powered semantic normalizer family and correction schedule supply
canonical ranked routing.
-/
noncomputable def normalizers_factory_schedule
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
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    SCRouteb
      (d := d) (n := n) (inputWeight := inputWeight) where
  outerRouting :=
    OFRoute.normalizers_factory_schedule
      hn hH family schedule
  normalizerFamily := family

end
  SCRouteb

namespace
  TSBuildb

/--
Compile a complete normalizer family and correction schedule into the closed
retained-right subtree resolver.
-/
noncomputable def normalizers_factory_schedule
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    TSBuildb.{u}
      (inputWeight := inputWeight) hn hH where
  packet := packet
  inputWeight_pos := hinputWeight
  routing :=
    SCRouteb.normalizers_factory_schedule
      hn hH family schedule

/--
Retained recipe coefficients provide the integral packet and correction
schedule consumed by the closed subtree resolver.
-/
noncomputable def normalizers_recipe_trace
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    TSBuildb.{u}
      (inputWeight := inputWeight) hn
        (forms_associated_below
          d n) :=
  normalizers_factory_schedule hn
    (forms_associated_below
      d n)
    (retainedAllPacket hrecipes)
    hinputWeight family
    {
      factory := fun lowerWeight =>
        TDBuild.retainedRecipeFactory
          (lowerWeight := lowerWeight) hinputWeight hrecipes
    }

end
  TSBuildb

namespace TSInput

/--
A complete normalizer family and correction schedule route a supported
sourced input through closed retained-right subtree recursion.
-/
theorem
    coordFactorySchedule
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordSubtreeBuilder
    hn hsourceSupported
      (TSBuildb.normalizers_factory_schedule
        hn
          (forms_associated_below
            d n)
          packet hinputWeight family schedule)

/--
Retained recipe coefficients and a complete normalizer family route a
supported sourced input through closed retained-right subtree recursion.
-/
theorem
    coordPolyCoeff
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordSubtreeBuilder
    hn hsourceSupported
      (TSBuildb.normalizers_recipe_trace
        hn hinputWeight hrecipes family)

end TSInput
end TCTex
end Towers

-- Merged from
-- ResidualBasicChildrenExpandedNestedWordsOuterRightSubtreeRecursionFromReachableBuilder.lean

/-!
# Closed retained-right Hall-power recursion from reachable builders

A reachable universal powered collector already supplies a semantic
normalizer family and a correction-packet schedule. This file routes those
derived families through the closed retained-right Hall-tree recursion.

For retained recipe coefficients, the product law and a packet-free reachable
insertion schedule construct the reachable builder automa.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open
  CCThree
open
  CPSplita

namespace
  TSBuildb

/--
Route an existing reachable universal powered collector through closed
retained-right subtree recursion.
-/
noncomputable def ofReachableBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (builder :
      TDBuild
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d)) :
    TSBuildb.{u}
      (inputWeight := inputWeight) hn
        (forms_associated_below
          d n) :=
  normalizers_factory_schedule hn
    (forms_associated_below
      d n)
    packet hinputWeight
    (builder.supportedSemanticFamily hn
      (concreteCommutatorsWeight.{u} d)
        (forms_associated_below
          d n))
    (builder.supportedCorrectionFactory
      (concreteCommutatorsWeight.{u} d))

/--
Retained recipe coefficients and a packet-free reachable insertion schedule
route through closed retained-right subtree recursion.
-/
noncomputable def
    recipe_reachable_schedule
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      RIDeriva
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d)) :
    TSBuildb.{u}
      (inputWeight := inputWeight) hn
        (forms_associated_below
          d n) :=
  ofReachableBuilder hn
    (retainedAllPacket hrecipes)
    hinputWeight
    (TDBuild.recipe_coeff_trace
      hinputWeight hrecipes schedule)

end
  TSBuildb

namespace TSInput

/--
A reachable universal powered collector routes a supported sourced input
through closed retained-right subtree recursion.
-/
theorem
    recursionReachableBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (builder :
      TDBuild
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordSubtreeBuilder
    hn hsourceSupported
      (TSBuildb.ofReachableBuilder
        hn packet hinputWeight builder)

/--
Retained recipe coefficients and a packet-free reachable insertion schedule
route a supported sourced input through closed retained-right subtree
recursion.
-/
theorem
    reachableInsertionSchedule
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      RIDeriva
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordSubtreeBuilder
    hn hsourceSupported
      (TSBuildb.recipe_reachable_schedule
        hn hinputWeight hrecipes schedule)

end TSInput
end TCTex
end Towers

-- Merged from ResidualBasicChildrenExpandedNestedWordsRepeatedRightCases.lean

/-!
# Structural cases for repeated-right Hall-power recursion

The repeated-right frontier `[[left, middle], middle]` is the one place where
root Jacobi recursion does not move: its first ordinary descendant is the
parent again and its second descendant is a self-commutator.

When `left` and `middle` are basic and `middle < left`, the exposed nonbasic
inner bracket forces a more useful obstruction. The basic tree `left` must
itself be a commutator `[leftLeft, leftRight]`, and Hall admissibility fails
exactly far enough to give

`middle < leftRight`.

This file packages that structural case and narrows the repeated-right
boundary to contextual recursion on the exposed nested left tree.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
The genuinely recursive repeated-right case: a basic left root has exposed
basic children, and the repeated middle tree lies strictly below its right
child.
-/
structure
    CRCase
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor) where
  leftLeft :
    HallTree (FreeGenerator.{u} d)
  leftRight :
    HallTree (FreeGenerator.{u} d)
  left_eq :
    frontier.left = .commutator leftLeft leftRight
  left_isBasic :
    frontier.left.IsBasic
  middle_isBasic :
    frontier.middle.IsBasic
  middle_lt_left :
    frontier.middle < frontier.left
  left_basic :
    leftLeft.IsBasic
  left_right_basic :
    leftRight.IsBasic
  left_right :
    leftRight < leftLeft
  middle_left_right :
    frontier.middle < leftRight

namespace
  CRCase

/--
Expose the failed Hall-admissibility witness inside an ordered basic-left
repeated-right frontier.
-/
noncomputable def ofBasicOrdered
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (frontier :
      WFCase
        factor)
    (hrightBasic : frontier.right.IsBasic)
    (hrightEqMiddle : frontier.right = frontier.middle)
    (hleftBasic : frontier.left.IsBasic)
    (hmiddleLtLeft : frontier.middle < frontier.left) :
    CRCase
      factor frontier := by
  have hmiddleBasic : frontier.middle.IsBasic := by
    rw [← hrightEqMiddle]
    exact hrightBasic
  cases hleft : frontier.left with
  | atom generator =>
      have hmiddleLtAtom :
          frontier.middle < HallTree.atom generator := by
        rw [← hleft]
        exact hmiddleLtLeft
      have hinnerBasic :
          (HallTree.commutator (.atom generator) frontier.middle).IsBasic :=
        HallTree.basic_commutator_admissible
          (HallTree.isBasic_atom generator) hmiddleBasic hmiddleLtAtom trivial
      exfalso
      apply frontier.inner_nonbasic
      simpa only [hleft] using hinnerBasic
  | commutator leftLeft leftRight =>
      have hleftBasic' :
          (HallTree.commutator leftLeft leftRight).IsBasic := by
        rw [← hleft]
        exact hleftBasic
      have hmiddleLtLeft' :
          frontier.middle < HallTree.commutator leftLeft leftRight := by
        rw [← hleft]
        exact hmiddleLtLeft
      have hleftData :=
        (HallTree.isBasic_commutator leftLeft leftRight).mp hleftBasic'
      have hnotLeftRightLeMiddle : ¬leftRight ≤ frontier.middle := by
        intro hleftRightLeMiddle
        have hinnerBasic :
            (HallTree.commutator
              (.commutator leftLeft leftRight) frontier.middle).IsBasic :=
          HallTree.basic_commutator_admissible hleftBasic' hmiddleBasic
            hmiddleLtLeft' hleftRightLeMiddle
        apply frontier.inner_nonbasic
        simpa only [hleft] using hinnerBasic
      exact
        {
          leftLeft := leftLeft
          leftRight := leftRight
          left_eq := hleft
          left_isBasic := hleftBasic
          middle_isBasic := hmiddleBasic
          middle_lt_left := hmiddleLtLeft
          left_basic := hleftData.1
          left_right_basic := hleftData.2.1
          left_right := hleftData.2.2.1
          middle_left_right := lt_of_not_ge hnotLeftRightLeMiddle
        }

end
  CRCase

/--
Reachable ranked routing and the recursive boundaries left after exposing the
structural obstruction inside repeated-right frontiers.
-/
structure
    TRBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  inputWeight_pos : 1 ≤ inputWeight
  routing :
    SCRouteb.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
  rootSwapResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword
  retainedDescendantResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ (frontier :
                WFCase
                  factor)
                (_hrightNonbasic : ¬frontier.right.IsBasic)
                (descendant :
                  CDCase
                    factor frontier),
                  TSRecollb
                    (n := n) descendant.factor
  repeatedNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    ¬frontier.left.IsBasic →
                      TSRecollb
                        (n := n) factor
  repeatedFailedInner :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle < frontier.left →
                        TSRecollb
                          (n := n) factor
  repeatedRightNested :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ (frontier :
                WFCase
                  factor)
                (_hrightBasic : frontier.right.IsBasic)
                (_hrightEqMiddle : frontier.right = frontier.middle)
                (_nested :
                  CRCase
                    factor frontier),
                  TSRecollb
                    (n := n) factor
  leftNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    ¬frontier.left.IsBasic →
                      TSRecollb
                        (n := n) factor
  middleNonbasicResidual :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle.IsBasic →
                        TSRecollb
                          (n := n) factor
  failedInnerChildren :
    ∀ (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ∀ frontier :
                WFCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      frontier.middle.IsBasic →
                        ¬frontier.middle < frontier.left →
                          TSRecollb
                            (n := n) factor

namespace
  TRBuild

open
  CRCase

/-- Compile repeated-right structural classification into the previous builder. -/
noncomputable def descendantsJacobiBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TRBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    TDBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  inputWeight_pos := builder.inputWeight_pos
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  retainedDescendantResidual := builder.retainedDescendantResidual
  repeatedRightResidual := by
    intro lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier hrightBasic hrightEqMiddle
    by_cases hleftBasic : frontier.left.IsBasic
    · by_cases hmiddleLtLeft : frontier.middle < frontier.left
      · exact
          builder.repeatedRightNested lowerWeight hnonterminal
            factor hfactorWeight hfactorTruncated frontier hrightBasic
              hrightEqMiddle
                (ofBasicOrdered factor frontier hrightBasic hrightEqMiddle
                  hleftBasic hmiddleLtLeft)
      · exact
          builder.repeatedFailedInner lowerWeight
            hnonterminal factor hfactorWeight hfactorTruncated frontier
              hrightBasic hrightEqMiddle hleftBasic hmiddleLtLeft
    · exact
        builder.repeatedNonbasicResidual lowerWeight hnonterminal
          factor hfactorWeight hfactorTruncated frontier hrightBasic
            hrightEqMiddle hleftBasic
  leftNonbasicResidual := builder.leftNonbasicResidual
  middleNonbasicResidual := builder.middleNonbasicResidual
  failedInnerChildren := builder.failedInnerChildren

end
  TRBuild

namespace TSInput

/--
Repeated-right structural cases with explicit contextual recursion boundaries
construct the Claim 5 coordinate polynomials for a supported sourced input.
-/
theorem
    coordRepeatedBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TRBuild.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordDescendantsBuilder
    hn hsourceSupported
      builder.descendantsJacobiBuilder

end TSInput
end TCTex
end Towers
