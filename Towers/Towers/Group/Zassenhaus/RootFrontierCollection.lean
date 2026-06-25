import Towers.Group.Zassenhaus.RootSwapRecollection
import Towers.Group.Zassenhaus.CanonicalHallRecollection

/-!
# Routing every concrete Jacobi frontier into expanded recursion

A surviving Jacobi-frontier bracket either has two basic children or contains
a nonbasic child.  The two-basic-child case is handled by Hall orientation.
For a nonbasic left child, the original bracket is already an expanded
left-normed Jacobi root.  For a nonbasic right child, an exact sign-corrected
expanded-root swap exposes such a root.

Thus the remaining frontier data consists only of expanded Jacobi recursion
and forward recollections of the generic root-swap skew packets.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

/--
Expanded Jacobi recursion plus generic root-swap packets recollects every
concrete Jacobi frontier.
-/
structure
    TEBuilda
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  basicChildren :
    JOBuild.{u}
      (inputWeight := inputWeight) hn hH
  hinputWeight : 1 ≤ inputWeight
  normalizerAbove :
    ∀ lowerWeight strongerWeight : ℕ,
      lowerWeight < strongerWeight →
        TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d)
  rootSwapResidual :
    ∀ lowerWeight : ℕ,
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

namespace
  TEBuilda

open
  TSRecollb

/--
Route one frontier with a nonbasic child into expanded Jacobi recursion,
using a signed root swap exactly when the nonbasic child is on the right.
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
      TEBuilda.{u}
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
    (_hchildrenNe : left ≠ right)
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
                (builder.basicChildren.expandedJacobi
                  |>.jacobiTreeNonbasic
                    builder.hinputWeight lowerWeight hnonterminal
                      (builder.normalizerAbove lowerWeight) reversed
                        right₁ right₂ left
                          (by
                            dsimp only [reversed]
                            rw [tree_expanded_swap, hrightTree,
                              hleftTree])
                          (by simpa only using hreverseNonbasic)
                          (by
                            dsimp only [reversed]
                            simpa only [expanded_root_factor] using
                              hfactorWeight)
                          (by
                            dsimp only [reversed]
                            simpa only [expanded_root_factor] using
                              hfactorTruncated))
                (builder.rootSwapResidual lowerWeight hnonterminal factor
                  leftWord rightWord hword hfactorWeight hfactorTruncated)
  · cases left with
    | atom generator =>
        exact False.elim (hleftBasic (HallTree.isBasic_atom generator))
    | commutator left₁ left₂ =>
        exact
          builder.basicChildren.expandedJacobi
            |>.jacobiTreeNonbasic
              builder.hinputWeight lowerWeight hnonterminal
                (builder.normalizerAbove lowerWeight) factor left₁ left₂
                  right (by simpa only using htree)
                    (by
                      rw [htree] at htreeNonbasic
                      exact htreeNonbasic)
                      hfactorWeight hfactorTruncated

/--
Compile the expanded-root frontier route into the nonbasic-child interface.
-/
noncomputable def nonbasicChildBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TEBuilda.{u}
        (inputWeight := inputWeight) hn hH) :
    NCJacobi.{u}
      (inputWeight := inputWeight) hn hH where
  basicChildren := builder.basicChildren
  hinputWeight := builder.hinputWeight
  normalizerAbove := builder.normalizerAbove
  nonbasicChildResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        htreeNonbasic left right htree hchildrenNe hreverseNonbasic hchild =>
      builder.nonbasicChildResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated htreeNonbasic left right htree
          hchildrenNe hreverseNonbasic hchild

/-- Compile the expanded-root route into the arbitrary Jacobi frontier. -/
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
      TEBuilda.{u}
        (inputWeight := inputWeight) hn hH) :
    TFBuildc.{u}
      (inputWeight := inputWeight) hn hH :=
  builder.nonbasicChildBuilder
    |>.jacobiCollectionBuilder

end
  TEBuilda

end TCTex
end Towers
