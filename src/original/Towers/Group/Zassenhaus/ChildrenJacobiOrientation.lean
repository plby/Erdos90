import Towers.Group.HallBasic.JacobiFrontierChildren
import Towers.Group.Zassenhaus.ChildrenSwapResidual
import Towers.Group.Zassenhaus.Jacobi


/-!
# Orienting concrete Jacobi frontiers with basic children

For two distinct basic children whose bracket is nonbasic in both
orientations, Hall admissibility identifies a left-normed Jacobi root in one
of the two orientations.  The forward orientation enters expanded Jacobi
recursion directly.  The reverse orientation uses the sign-corrected swapped
factor and the skew-value residual decomposition.

This file packages that orientation split while leaving only the genuinely
recursive inverse skew-value residual as an explicit recollection input.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

/-- Upward recollection of an inverse sign-corrected skew-value residual. -/
structure
    TIRecoll
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : HEWord.tree factor.word =
      .commutator left right) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (basicChildrenSwap factor left right
            hleftBasic hrightBasic htree)

namespace
  TSRecollb

/--
Recollect the original residual from a recollection of its sign-corrected
reversed residual and a recollection of the inverse skew-value residual.
-/
noncomputable def children_swap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : HEWord.tree factor.word =
      .commutator left right)
    (reversed :
      TSRecollb
        (n := n)
        (childrenSwapFactor factor left right hleftBasic hrightBasic
          htree))
    (valueResidualInverse :
      TIRecoll
        (n := n) factor left right hleftBasic hrightBasic htree) :
    TSRecollb
      (n := n) factor where
  higherSource := reversed.higherSource ++ valueResidualInverse.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact reversed.higher_source_truncated x hx
    · exact valueResidualInverse.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simpa only [basic_children_swap] using
        reversed.higher_least_succ x hx
    · exact valueResidualInverse.higher_least_succ x hx
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append,
      reversed.list_higher_raw q,
      valueResidualInverse.list_higher_raw q,
      ←
        children_swap_decomposition
          factor left right hleftBasic hrightBasic htree q]
    rw [childrenSwapDecomposition,
      SPFactora.listEval_append]

/--
If the right basic child is itself a commutator, reverse orientation and then
enter expanded left-normed Jacobi recursion.
-/
noncomputable def children_expanded_jacobi
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      ECBuild.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right right₁ right₂ : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : HEWord.tree factor.word =
      .commutator left right)
    (hright : right = .commutator right₁ right₂)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (valueResidualInverse :
      TIRecoll
        (n := n) factor left right hleftBasic hrightBasic htree) :
    TSRecollb
      (n := n) factor :=
  let reversed :=
    childrenSwapFactor factor left right hleftBasic hrightBasic htree
  children_swap factor left right hleftBasic hrightBasic htree
    (builder.jacobiTreeNonbasic
      hinputWeight lowerWeight hnonterminal normalizerAbove reversed
        right₁ right₂ left
        (by
          dsimp only [reversed]
          simp only [tree_children_swap, hright])
        (by
          simpa only [hright] using hreverseNonbasic)
        (by
          dsimp only [reversed]
          simpa only [basic_children_swap] using
            hfactorWeight)
        (by
          dsimp only [reversed]
          simpa only [basic_children_swap] using
            hfactorTruncated))
    valueResidualInverse

end
  TSRecollb

/-- Chosen left-normed orientation of a two-basic-child Jacobi frontier. -/
inductive PowerChildrenOrientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d)) where
  | left
      (left₁ left₂ : HallTree (FreeGenerator.{u} d))
      (tree_eq : left = .commutator left₁ left₂)
  | right
      (right₁ right₂ : HallTree (FreeGenerator.{u} d))
      (tree_eq : right = .commutator right₁ right₂)

/-- The Hall admissibility frontier admits one chosen left-normed orientation. -/
theorem children_jacobi_orientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    Nonempty (PowerChildrenOrientation left right) := by
  rcases
      HallTree.inadmissible_orientation_children
        left right hleftBasic hrightBasic hchildrenNe hforwardNonbasic
          hreverseNonbasic with
    hleft | hright
  · rcases hleft with ⟨left₁, left₂, hleft, _hrightLeft, _hbad⟩
    exact ⟨.left left₁ left₂ hleft⟩
  · rcases hright with ⟨right₁, right₂, hright, _hleftRight, _hbad⟩
    exact ⟨.right right₁ right₂ hright⟩

/-- Choose a left-normed orientation of a two-basic-child Jacobi frontier. -/
noncomputable def basicChildrenOrientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    PowerChildrenOrientation left right :=
  Classical.choice
    (children_jacobi_orientation left right hleftBasic hrightBasic
      hchildrenNe hforwardNonbasic hreverseNonbasic)

/--
Expanded Jacobi recursion plus the remaining inverse skew-value recollections
orients every two-basic-child Jacobi frontier.
-/
structure
    JOBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  expandedJacobi :
    ECBuild.{u}
      (inputWeight := inputWeight) hn hH
  swapValueInverse :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right : HallTree (FreeGenerator.{u} d))
          (hleftBasic : left.IsBasic)
          (hrightBasic : right.IsBasic)
          (htree : HEWord.tree factor.word =
            .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TIRecoll
                (n := n) factor left right hleftBasic hrightBasic htree

namespace
  JOBuild

open
  TSRecollb

/--
Orient and recollect one Jacobi-frontier bracket with two basic children.
-/
noncomputable def residual
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      JOBuild.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : HEWord.tree factor.word =
      .commutator left right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hchildrenNe : left ≠ right)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor := by
  let orientation :=
    basicChildrenOrientation left right hleftBasic hrightBasic
      hchildrenNe hforwardNonbasic hreverseNonbasic
  cases orientation with
  | left left₁ left₂ hleft =>
    exact
      builder.expandedJacobi.jacobiTreeNonbasic
        hinputWeight lowerWeight hnonterminal normalizerAbove factor
          left₁ left₂ right
          (by simpa only [hleft] using htree)
          (by simpa only [hleft] using hforwardNonbasic)
          hfactorWeight hfactorTruncated
  | right right₁ right₂ hright =>
    exact
      children_expanded_jacobi builder.expandedJacobi
        hinputWeight hnonterminal normalizerAbove factor left right
          right₁ right₂ hleftBasic hrightBasic htree hright
            hreverseNonbasic hfactorWeight hfactorTruncated
              (builder.swapValueInverse lowerWeight hnonterminal
                factor left right hleftBasic hrightBasic htree
                  hfactorWeight hfactorTruncated)

end
  JOBuild

end TCTex
end Towers
