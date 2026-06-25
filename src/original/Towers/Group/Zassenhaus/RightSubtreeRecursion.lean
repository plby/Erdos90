import Towers.Group.HallBasic.StandardSequence
import Towers.Group.Zassenhaus.RightContextualCollection
import Towers.Group.Zassenhaus.RootSwapNormalization
import Towers.Group.Zassenhaus.PolynomialConcrete

/-!
# Well-founded recursion for retained-right polynomial frontiers

Every exposed nested frontier `[[left, middle], right]` with Hall-basic
`right` recollects contextually.  When `right` is nonbasic, the retained-right
Jacobi step produces two descendants whose new retained-right trees are
proper subtrees of `right`.

This file closes that final recursive boundary.  A recursive task carries an
exposed nested frontier and its fixed polynomial weight.  Each actual Jacobi
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

open CEWord
open
  TRRecoll
  RCDecomp
  TDCase

/-
The retained-right task and recursive builder are already provided by the
imported PolynomialConcrete module.

/-- One exposed nested frontier scheduled at a fixed polynomial weight. -/
structure
    PSTask
    {d n : ℕ}
    {ι : Type}
    (lowerWeight : ℕ) where
  factor :
    SPFactor
      (concreteBasicCommutators.{u} d) ι
  factor_weight :
    factor.word.weight HEAddres.weight = lowerWeight
  factor_truncated :
    factor.word.weight HEAddres.weight < n
  frontier :
    NWCase
      factor

namespace
  PSTask

/-- Recursive tasks decrease by their retained outer-right Hall tree. -/
def RetainedRightLT
    {d n lowerWeight : ℕ}
    {ι : Type}
    (child parent :
      PSTask.{u}
        (d := d) (n := n) (ι := ι) lowerWeight) :
    Prop :=
  child.frontier.right < parent.frontier.right

/-- Retained-right task recursion is well founded by the Hall-tree order. -/
theorem well_founded_right
    {d n lowerWeight : ℕ}
    {ι : Type} :
    WellFounded
      (RetainedRightLT.{u}
        (d := d) (n := n) (ι := ι) (lowerWeight := lowerWeight)) := by
  unfold RetainedRightLT
  exact InvImage.wf
    (fun task :
        PSTask.{u}
          (d := d) (n := n) (ι := ι) lowerWeight =>
      task.frontier.right)
    (HallTree.lt_wellFounded (α := FreeGenerator.{u} d))

/--
Classify one actual retained-right descendant.  Terminal roots recollect
immediately.  Every surviving Jacobi root becomes a strictly smaller task.
-/
noncomputable def residual_recollection_descendant
    {d n lowerWeight : ℕ}
    {ι : Type}
    {parent :
      PSTask.{u}
        (d := d) (n := n) (ι := ι) lowerWeight}
    (descendant :
      TDCase
        parent.factor parent.frontier)
    (newLeft newMiddle : HallTree (FreeGenerator.{u} d))
    (hdescendantLeft :
      descendant.left = .commutator newLeft newMiddle)
    (hnewMiddleNonbasic : ¬newMiddle.IsBasic)
    (hfactorWeight :
      descendant.factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      descendant.factor.word.weight HEAddres.weight < n)
    (recursive :
      ∀ child :
          PSTask.{u}
            (d := d) (n := n) (ι := ι) lowerWeight,
        RetainedRightLT child parent →
          TRRecoll
            (n := n) child.factor) :
    TRRecoll
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
            PSTask.{u}
              (d := d) (n := n) (ι := ι) lowerWeight :=
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
  PSTask

/--
Canonical routing data is enough to close retained-right subtree recursion.
The same normalizer family carried by routing also recollects root-swap
value packets.
-/
structure
    SJBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι

namespace
  SJBuild

open
  PSTask

/--
Reuse the packet and canonical routing prepared by the ranked basic-children
collector, while replacing its compatibility fallback by subtree recursion.
-/
noncomputable def canonicalCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (canonical :
      CCBuild.{u}
        (d := d) (n := n) hn) :
    SJBuild.{u}
      (d := d) (n := n) hn where
  packet := canonical.packet
  routing := canonical.routing

/--
Build closed subtree-recursive collection from the reachable signed-semantic
schedule and normalizer derivation.
-/
noncomputable def ofReachableBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    SJBuild.{u}
      (d := d) (n := n) hn :=
  canonicalCollectionBuilder
    (CCBuild.ofReachableBuilder
      packet builder)

/-- Resolve one retained-right subtree task, assuming smaller tasks resolved. -/
noncomputable def resolveTaskStep
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn)
    (task :
      PSTask.{u}
        (d := d) (n := n) (ι := ι) lowerWeight)
    (recursive :
      ∀ child :
          PSTask.{u}
            (d := d) (n := n) (ι := ι) lowerWeight,
        RetainedRightLT child task →
          TRRecoll
            (n := n) child.factor) :
    TRRecoll
      (n := n) task.factor := by
  by_cases hrightBasic : task.frontier.right.IsBasic
  · exact
      NWCase.outerResidualRecollect
        hn (builder.routing ι) task.factor task.frontier hrightBasic
          task.factor_truncated
  · let retained := ofNonbasic task.factor task.frontier hrightBasic
    let firstDescendant := first task.factor task.frontier hrightBasic
    let secondDescendant := second task.factor task.frontier hrightBasic
    have hfirstWeight :
        firstDescendant.factor.word.weight HEAddres.weight =
          lowerWeight := by
      simpa only [firstDescendant, first,
        expanded_jacobi_factor,
        word_swap_factor] using task.factor_weight
    have hfirstTruncated :
        firstDescendant.factor.word.weight HEAddres.weight < n := by
      simpa only [firstDescendant, first,
        expanded_jacobi_factor,
        word_swap_factor] using task.factor_truncated
    have hsecondWeight :
        secondDescendant.factor.word.weight HEAddres.weight =
          lowerWeight := by
      simpa only [secondDescendant, second,
        expanded_second_factor,
        word_swap_factor] using task.factor_weight
    have hsecondTruncated :
        secondDescendant.factor.word.weight HEAddres.weight < n := by
      simpa only [secondDescendant, second,
        expanded_second_factor,
        word_swap_factor] using task.factor_truncated
    let firstResidual :=
      residual_recollection_descendant firstDescendant retained.left
        (.commutator task.frontier.left task.frontier.middle) (by rfl)
          task.frontier.inner_nonbasic hfirstWeight hfirstTruncated recursive
    let secondResidual :=
      residual_recollection_descendant secondDescendant retained.middle
        (.commutator task.frontier.left task.frontier.middle) (by rfl)
          task.frontier.inner_nonbasic hsecondWeight hsecondTruncated recursive
    let reversed := retainedSwapFactor task.factor task.frontier
    let reversedResidual :=
      expanded_normalizer_family hn builder.packet
        (builder.routing ι).normalizerFamily reversed retained.decomposition
        (by
          simpa only [reversed, word_swap_factor] using
            task.factor_weight)
        (by
          simpa only [reversed, word_swap_factor] using
            task.factor_truncated)
        firstResidual secondResidual
    exact
      expanded_swap task.factor
        (.commutator task.frontier.decomposition.left
          task.frontier.decomposition.middle)
        task.frontier.decomposition.right task.frontier.decomposition.word_eq
          reversedResidual
          (PSRecoll.ofNormalizerFamily
            hn
            (fun s hs hsn =>
              concrete_forms_associated
                d n s hs hsn)
            (builder.routing ι).normalizerFamily task.factor
              (.commutator task.frontier.decomposition.left
                task.frontier.decomposition.middle)
              task.frontier.decomposition.right
                task.frontier.decomposition.word_eq task.factor_weight
                  task.factor_truncated)

/-- Run the retained-right resolver by well-founded Hall-tree recursion. -/
noncomputable def taskResidualRecollection
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn)
    (task :
      PSTask.{u}
        (d := d) (n := n) (ι := ι) lowerWeight) :
    TRRecoll
      (n := n) task.factor :=
  (well_founded_right
      (d := d) (n := n) (ι := ι) (lowerWeight := lowerWeight)).fix
    (fun task recursive => builder.resolveTaskStep task recursive) task

/--
Compile closed retained-right recursion into the exposed nested-word
frontier interface.
-/
noncomputable def
    expandedWordsBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn) :
    CNBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := by
    intro ι _lowerWeight _hnonterminal factor left right hword hfactorWeight
      hfactorTruncated
    exact
      PSRecoll.ofNormalizerFamily
        hn
        (fun s hs hsn =>
          concrete_forms_associated d n s hs hsn)
        (builder.routing ι).normalizerFamily factor left right hword
          hfactorWeight hfactorTruncated
  nestedWordsResidual :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        frontier =>
      builder.taskResidualRecollection
        {
          factor := factor
          factor_weight := hfactorWeight
          factor_truncated := hfactorTruncated
          frontier := frontier
        }

end
  SJBuild
-/

/--
Closed retained-right subtree recursion constructs product coordinate
polynomials.
-/
theorem
    subtree_jacobi_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_ranked_builder
    hn e builder.expandedWordsBuilder

/--
Closed retained-right subtree recursion constructs inverse coordinate
polynomials.
-/
theorem
    commutators_subtree_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  ranked_expanded_builder
    hn e builder.expandedWordsBuilder

/--
Route a reachable signed-semantic builder through closed retained-right
subtree recursion to construct product coordinate polynomials.
-/
theorem
    basic_subtree_recursion
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  subtree_jacobi_builder
    hn e
      (SJBuild.ofReachableBuilder
        packet builder)

/--
Route a reachable signed-semantic builder through closed retained-right
subtree recursion to construct inverse coordinate polynomials.
-/
theorem
    outer_subtree_recursion
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_subtree_builder
    hn e
      (SJBuild.ofReachableBuilder
        packet builder)

end TCTex
end Towers
