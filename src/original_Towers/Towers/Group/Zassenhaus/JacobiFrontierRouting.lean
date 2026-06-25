import Towers.Group.Zassenhaus.SignCorrectedSwaps
import Towers.Group.Zassenhaus.NonbasicChildFrontier

/-!
# Routing every polynomial Jacobi frontier into expanded recursion

A surviving Jacobi-frontier bracket either has two basic children or
contains a nonbasic child.  The two-basic-child case is handled by Hall
orientation.  A nonbasic left child is already an expanded left-normed root.
For a nonbasic right child, an exact sign-corrected root swap exposes one.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

/--
Expanded Jacobi recursion plus generic root-swap packets recollects every
concrete polynomial Jacobi frontier.
-/
structure
    EFBuilda
    {d n : ℕ}
    (hn : 2 ≤ n) where
  basicChildren :
    COBuild.{u}
      (d := d) (n := n) hn
  normalizerAbove :
    ∀ lowerWeight strongerWeight : ℕ,
      lowerWeight < strongerWeight →
        TSNormal
          (n := n) (lowerWeight := strongerWeight)
            (concreteBasicCommutators.{u} d)
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword

namespace
  EFBuilda

open
  TRRecoll

/--
Route one frontier with a nonbasic child into expanded Jacobi recursion,
using a signed root swap exactly when the nonbasic child is on the right.
-/
noncomputable def nonbasicChildResidual
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      EFBuilda.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (htreeNonbasic : ¬(tree factor.word).IsBasic)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = .commutator left right)
    (_hchildrenNe : left ≠ right)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hchild : ¬left.IsBasic ∨ ¬right.IsBasic) :
    TRRecoll
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
                    lowerWeight hnonterminal
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
              lowerWeight hnonterminal (builder.normalizerAbove lowerWeight)
                factor left₁ left₂ right (by simpa only using htree)
                  (by
                    rw [htree] at htreeNonbasic
                    exact htreeNonbasic)
                    hfactorWeight hfactorTruncated

/--
Compile the expanded-root frontier route into the nonbasic-child interface.
-/
noncomputable def nonbasicChildBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      EFBuilda.{u}
        (d := d) (n := n) hn) :
    NCBuild.{u}
      (d := d) (n := n) hn where
  basicChildren := builder.basicChildren
  normalizerAbove := builder.normalizerAbove
  nonbasicChildResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        htreeNonbasic left right htree hchildrenNe hreverseNonbasic hchild =>
      builder.nonbasicChildResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated htreeNonbasic left right htree
          hchildrenNe hreverseNonbasic hchild

/-- Compile the expanded-root route into the arbitrary Jacobi frontier. -/
noncomputable def jacobiCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      EFBuilda.{u}
        (d := d) (n := n) hn) :
    JFBuild.{u}
      (d := d) (n := n) hn :=
  builder.nonbasicChildBuilder
    |>.jacobiCollectionBuilder

end
  EFBuilda

end TCTex
end Towers
