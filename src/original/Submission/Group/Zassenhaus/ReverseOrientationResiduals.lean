import Submission.Group.HallBasic.SwapCoordinateScaling
import Submission.Group.HallBasic.SwapValueScaling
import Submission.Group.Zassenhaus.SignCorrectedSwaps
import Submission.Group.Zassenhaus.SignedReductionFactors
import Submission.Group.Zassenhaus.PolynomialRankedSupport
import Submission.Group.HallBasic.JacobiFrontierChildren
import Submission.Group.Zassenhaus.PolynomialBracketSupport
import Submission.Group.Zassenhaus.JacobiContinuationBuilders


/-!
# Reverse-orientation residuals for polynomial brackets with basic children

Reversing two basic children and negating the coefficient formula preserves
the explicit Hall-reduction packet.  The values differ by a next-stratum
skew-symmetry residual.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace CEWord

universe u

/-- Canonical symbolic word for the reversed bracket of two basic trees. -/
noncomputable def childrenSwapWord
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic) :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d)) :=
  .commutator
    (.atom (addressBasicTree right hrightBasic))
    (.atom (addressBasicTree left hleftBasic))

@[simp]
theorem tree_basic_children
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic) :
    tree (childrenSwapWord left right hleftBasic hrightBasic) =
      .commutator right left := by
  rw [childrenSwapWord, tree_commutator,
    tree_atom_address, tree_atom_address]

/-- Sign-corrected reversed factor. -/
noncomputable def childrenSwapFactor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    SPFactor
      (concreteBasicCommutators.{u} d) ι :=
  (factor.reword
    (childrenSwapWord left right hleftBasic hrightBasic)
    (by
      rw [← tree_weight factor.word, htree]
      change
        HEAddres.weight
              (addressBasicTree right hrightBasic) +
            HEAddres.weight
              (addressBasicTree left hleftBasic) =
          left.weight + right.weight
      rw [address_tree_weight, address_tree_weight]
      omega)).neg

@[simp]
theorem tree_children_swap
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    tree
        (childrenSwapFactor factor left right hleftBasic hrightBasic
          htree).word =
      .commutator right left := by
  simp [childrenSwapFactor]

@[simp]
theorem coefficient_children_swap
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (childrenSwapFactor factor left right hleftBasic hrightBasic
      htree).coefficient.eval e =
      -factor.coefficient.eval e := by
  rw [childrenSwapFactor,
    SPFactor.coefficient_eval_neg,
    SPFactor.coefficient_eval_reword]

@[simp]
theorem basic_children_swap
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    (childrenSwapFactor factor left right hleftBasic hrightBasic
      htree).word.weight HEAddres.weight =
        factor.word.weight HEAddres.weight := by
  simp only [childrenSwapFactor,
    SPFactor.word_neg,
    SPFactor.word_reword]
  rw [← tree_weight factor.word, htree]
  change
    HEAddres.weight
          (addressBasicTree right hrightBasic) +
        HEAddres.weight
          (addressBasicTree left hleftBasic) =
      left.weight + right.weight
  rw [address_tree_weight, address_tree_weight]
  omega

/-- The atomic Hall-reduction packet is unchanged by signed reversal. -/
theorem children_swap_factor
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicReductionFactors factor) =
      SPFactor.listEval e
        (basicReductionFactors
          (childrenSwapFactor factor left right hleftBasic hrightBasic
            htree)) := by
  rw [list_basic_factors, list_basic_factors,
    htree, tree_children_swap,
    coefficient_children_swap,
    HallTree.scaled_swap_neg]

/-- Value-level skew residual: original inverse followed by signed reverse. -/
noncomputable def childrenSwapSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  [factor.neg,
    childrenSwapFactor factor left right hleftBasic hrightBasic htree]

/-- Truncation of the original factor truncates its skew-value residual. -/
theorem children_swap_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (childrenSwapSource factor left right hleftBasic
        hrightBasic htree) := by
  intro x hx
  simp only [childrenSwapSource, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simpa only [SPFactor.word_neg] using hfactor
  · simpa only [basic_children_swap] using hfactor

/-- The skew-value residual evaluates one lower-central layer higher. -/
theorem
    children_raw_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (childrenSwapSource factor left right hleftBasic
          hrightBasic htree) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  have hfree :=
    HallTree.swap_zpow_series
      left right (factor.coefficient.eval e)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [← tree_weight factor.word, htree]
          exact hfree))
  rw [childrenSwapSource,
    SPFactor.listEval_cons,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one]
  rw [← htree,
    ← tree_basic_children left right hleftBasic hrightBasic] at hmap
  rw [map_mul, map_inv, map_zpow, map_zpow,
    lower_truncation_tree,
    lower_truncation_tree] at hmap
  rw [SPFactor.eval_neg,
    SPFactor.eval,
    SPFactor.eval,
    coefficient_children_swap]
  simpa only [SPFactor.eval_neg,
    SPFactor.eval, SPFactor.wordValue,
    childrenSwapFactor, SPFactor.word_neg,
    SPFactor.word_reword,
    SPFactor.coefficient_eval_neg,
    SPFactor.coefficient_eval_reword,
    zpow_neg] using hmap

/-- Inverse orientation of the symbolic skew-value residual. -/
noncomputable def basicChildrenSwap
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList
    (childrenSwapSource factor left right hleftBasic
      hrightBasic htree)

/-- Truncation is preserved by inversion of the skew-value residual. -/
theorem truncated_children_swap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (basicChildrenSwap factor left right
        hleftBasic hrightBasic htree) := by
  exact
    SPFactor.truncated_inverse_list
      (children_swap_source factor left right
        hleftBasic hrightBasic htree hfactor)

/-- The inverse skew-value residual also lies one layer higher. -/
theorem
    children_swap_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicChildrenSwap factor left right
          hleftBasic hrightBasic htree) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [basicChildrenSwap,
    SPFactor.list_eval_inverse]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)).inv_mem
        (children_raw_series
          factor left right hleftBasic hrightBasic htree e)

/--
Recursive source for the original residual: recollect the reversed residual,
then append the inverse skew-value residual.
-/
noncomputable def childrenSwapDecomposition
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  basicRawSource
      (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree) ++
    basicChildrenSwap factor left right
      hleftBasic hrightBasic htree

/-- The reverse-orientation recursive source is physically truncated. -/
theorem truncated_children_decomposition
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (childrenSwapDecomposition factor left right
        hleftBasic hrightBasic htree) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      truncated_reduction_source
        (childrenSwapFactor factor left right hleftBasic hrightBasic
          htree)
        (by simpa only [basic_children_swap] using hfactor)
        x hx
  · exact
      truncated_children_swap factor left
        right hleftBasic hrightBasic htree hfactor x hx

/-- The recursive source evaluates exactly to the original true residual. -/
theorem
    children_swap_decomposition
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (childrenSwapDecomposition factor left right
          hleftBasic hrightBasic htree) =
      SPFactor.listEval e
        (basicRawSource factor) := by
  simp only [childrenSwapDecomposition,
    basicChildrenSwap,
    childrenSwapSource,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    reduction_raw_source,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one,
    SPFactor.eval_neg]
  rw [←
    children_swap_factor factor left right
      hleftBasic hrightBasic htree e]
  group

/-- The reverse-orientation recursive source lies one layer higher. -/
theorem
    children_decomposition_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (childrenSwapDecomposition factor left right
          hleftBasic hrightBasic htree) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [
    children_swap_decomposition
      factor left right hleftBasic hrightBasic htree e]
  exact
    list_reduction_series
      factor e

end CEWord
end TCTex
end Submission

/-!
# Singleton recollection from concrete signed-polynomial basic residuals

A concrete basic-reduction residual recollects the quotient between one
symbolic factor and its finite atomic Hall packet.  Prefixing the recollected
residual by that packet reconstructs the original singleton source.

This file packages that exact reconstruction and folds it over ranked child
sources.  It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace
  TRRecoll

/--
Prefix a recollected concrete residual by its atomic Hall packet to recollect
the original singleton factor at any weaker support bound.
-/
noncomputable def singletonSourceRecollection
    {d n lowerWeight : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (recollection :
      TRRecoll
        (n := n) factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (hlowerWeight :
      lowerWeight ≤
        factor.word.weight HEAddres.weight) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) [factor] where
  higherSource := basicReductionFactors factor ++ recollection.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact truncated_reduction_factors factor hfactorTruncated x hx
    · exact recollection.higher_source_truncated x hx
  higher_weight_least := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hlowerWeight.trans
        (least_reduction_factors factor x hx)
    · exact hlowerWeight.trans (Nat.le_succ _ |>.trans
        (recollection.higher_least_succ x hx))
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_append,
      recollection.list_higher_raw,
      reduction_raw_source]
    simp only [SPFactor.listEval_cons,
      SPFactor.listEval_nil, mul_one]
    group

end
  TRRecoll

namespace SPFactor
namespace RCSrc

/-- A ranked task's factor belongs to the erased source. -/
theorem fst_factor_tasks
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    {task : SPFactor H ι × ℕ}
    (htask : task ∈ source.tasks) :
    task.1 ∈ source.factorSource :=
  List.mem_map.mpr ⟨task, htask, rfl⟩

/--
Recollect an erased canonical Hall-ranked source from recursively supplied
concrete basic residual recollections for all of its child tasks.
-/
noncomputable def recollection_basic_residuals
    {d n lowerWeight parentRankDefect : ℕ}
    {ι : Type}
    {parent :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (source :
      RCSrc (n := n) parent parentRankDefect)
    (hsourceTruncated :
      SPFactor.IsTruncated n source.factorSource)
    (hsourceSupported :
      SPFactor.WordWeightLeast
        lowerWeight source.factorSource)
    (residual :
      ∀ task ∈ source.tasks,
        TRRecoll
          (n := n) task.1) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) source.factorSource :=
  source.source_recollection_singletons fun task htask =>
    (residual task htask).singletonSourceRecollection
      (hsourceTruncated task.1
        (source.fst_factor_tasks htask))
      (hsourceSupported task.1
        (source.fst_factor_tasks htask))

end RCSrc
end SPFactor

end TCTex
end Submission

/-!
# Orienting polynomial Jacobi frontiers with basic children

For two distinct basic children whose bracket is nonbasic in both
orientations, Hall admissibility chooses a left-normed Jacobi root.  Reverse
orientation is handled by the sign-corrected swap residual.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

/-- Upward recollection of an inverse sign-corrected skew-value residual. -/
structure
    TVRecoll
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : CEWord.tree factor.word =
      .commutator left right) where
  higherSource :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (basicChildrenSwap factor left right
            hleftBasic hrightBasic htree)

namespace
  TRRecoll

/-- Recollect an original residual from its reversed residual and skew packet. -/
noncomputable def children_swap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : CEWord.tree factor.word =
      .commutator left right)
    (reversed :
      TRRecoll
        (n := n)
        (childrenSwapFactor factor left right hleftBasic hrightBasic
          htree))
    (valueResidualInverse :
      TVRecoll
        (n := n) factor left right hleftBasic hrightBasic htree) :
    TRRecoll
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
    intro e
    rw [SPFactor.listEval_append,
      reversed.list_higher_raw e,
      valueResidualInverse.list_higher_raw e,
      ←
        children_swap_decomposition
          factor left right hleftBasic hrightBasic htree e]
    rw [childrenSwapDecomposition,
      SPFactor.listEval_append]

/-- Reverse orientation and enter expanded recursion through a right commutator. -/
noncomputable def children_expanded_jacobi
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      CDBuilda.{u}
        (d := d) (n := n) hn)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right right₁ right₂ : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : CEWord.tree factor.word =
      .commutator left right)
    (hright : right = .commutator right₁ right₂)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (valueResidualInverse :
      TVRecoll
        (n := n) factor left right hleftBasic hrightBasic htree) :
    TRRecoll
      (n := n) factor :=
  let reversed :=
    childrenSwapFactor factor left right hleftBasic hrightBasic htree
  children_swap factor left right hleftBasic hrightBasic htree
    (builder.jacobiTreeNonbasic
      lowerWeight hnonterminal normalizerAbove reversed right₁ right₂ left
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
  TRRecoll

/-- Chosen left-normed orientation of a two-basic-child Jacobi frontier. -/
inductive BasicJacobiOrientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d)) where
  | left
      (left₁ left₂ : HallTree (FreeGenerator.{u} d))
      (tree_eq : left = .commutator left₁ left₂)
  | right
      (right₁ right₂ : HallTree (FreeGenerator.{u} d))
      (tree_eq : right = .commutator right₁ right₂)

/-- Hall admissibility provides one left-normed orientation. -/
theorem nonempty_jacobi_orientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    Nonempty (BasicJacobiOrientation left right) := by
  rcases
      HallTree.inadmissible_orientation_children
        left right hleftBasic hrightBasic hchildrenNe hforwardNonbasic
          hreverseNonbasic with
    hleft | hright
  · rcases hleft with ⟨left₁, left₂, hleft, _hrightLeft, _hbad⟩
    exact ⟨.left left₁ left₂ hleft⟩
  · rcases hright with ⟨right₁, right₂, hright, _hleftRight, _hbad⟩
    exact ⟨.right right₁ right₂ hright⟩

/-- Choose a left-normed orientation. -/
noncomputable def basicJacobiOrientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    BasicJacobiOrientation left right :=
  Classical.choice
    (nonempty_jacobi_orientation left right hleftBasic hrightBasic
      hchildrenNe hforwardNonbasic hreverseNonbasic)

/-- Expanded recursion plus the remaining inverse skew-value recollections. -/
structure
    COBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  expandedJacobi :
    CDBuilda.{u}
      (d := d) (n := n) hn
  swapValueInverse :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right : HallTree (FreeGenerator.{u} d))
          (hleftBasic : left.IsBasic)
          (hrightBasic : right.IsBasic)
          (htree : CEWord.tree factor.word =
            .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TVRecoll
                (n := n) factor left right hleftBasic hrightBasic htree

namespace
  COBuild

open
  TRRecoll

/-- Orient and recollect one frontier bracket with two basic children. -/
noncomputable def residual
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      COBuild.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : CEWord.tree factor.word =
      .commutator left right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hchildrenNe : left ≠ right)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor := by
  let orientation :=
    basicJacobiOrientation left right hleftBasic hrightBasic
      hchildrenNe hforwardNonbasic hreverseNonbasic
  cases orientation with
  | left left₁ left₂ hleft =>
    exact
      builder.expandedJacobi.jacobiTreeNonbasic
        lowerWeight hnonterminal normalizerAbove factor left₁ left₂ right
          (by simpa only [hleft] using htree)
          (by simpa only [hleft] using hforwardNonbasic)
          hfactorWeight hfactorTruncated
  | right right₁ right₂ hright =>
    exact
      children_expanded_jacobi builder.expandedJacobi
        hnonterminal normalizerAbove factor left right right₁ right₂
          hleftBasic hrightBasic htree hright hreverseNonbasic hfactorWeight
            hfactorTruncated
              (builder.swapValueInverse lowerWeight hnonterminal
                factor left right hleftBasic hrightBasic htree
                  hfactorWeight hfactorTruncated)

end
  COBuild
end TCTex
end Submission

/-!
# Normalizing polynomial basic-children swap value residuals

The sign-corrected reverse orientation for a bracket with two basic children
leaves an inverse skew-value residual.  Its factors remain physically
supported at the parent Hall weight, while skew symmetry places its value one
lower-central layer higher.  A signed semantic normalizer recollects it into
a strictly higher tail.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

namespace
  TVRecoll

/-- Normalize the inverse skew-value residual into a strictly higher tail. -/
noncomputable def ofNormalizer
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TVRecoll
      (n := n) factor left right hleftBasic hrightBasic htree := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    normalizer.source_recollection_series hn
      (concreteBasicCommutators.{u} d) hH
      (basicChildrenSwap factor left right
        hleftBasic hrightBasic htree)
      hlowerWeightPos (by omega)
      (truncated_children_swap factor left
        right hleftBasic hrightBasic htree hfactorTruncated)
      (by
        rw [basicChildrenSwap]
        apply SPFactor.least_inverse_list
        intro x hx
        simp only [childrenSwapSource, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · simpa only [SPFactor.word_neg] using
            hfactorWeight.ge
        · simpa only [basic_children_swap] using
            hfactorWeight.ge)
      (by
        intro e
        simpa only [hfactorWeight] using
          children_swap_series
            factor left right hleftBasic hrightBasic htree e)
  exact
    {
      higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_least_succ := by
        simpa only [hfactorWeight] using
          recollection.higher_weight_least
      list_higher_raw :=
        recollection.list_higher_raw
    }

/-- Use a normalizer family at the parent Hall-weight stratum. -/
noncomputable def ofNormalizerFamily
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TVRecoll
      (n := n) factor left right hleftBasic hrightBasic htree :=
  ofNormalizer hn hH (family.normalizer lowerWeight) factor left right
    hleftBasic hrightBasic htree hfactorWeight hfactorTruncated

end
  TVRecoll

namespace
  EABuild

open
  TVRecoll

/--
Compile automatic expanded-Jacobi and swap-value normalization into the
two-basic-child Jacobi orientation builder.
-/
noncomputable def childrenOrientationBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      EABuild.{u}
        (d := d) (n := n) hn) :
    COBuild
      (d := d) (n := n) hn where
  expandedJacobi :=
    builder.expandedContinuationBuilder
  swapValueInverse :=
    fun _lowerWeight _hnonterminal factor left right hleftBasic hrightBasic
        htree hfactorWeight hfactorTruncated =>
      ofNormalizerFamily hn
        (fun s hs hsn =>
          concrete_forms_associated d n s hs hsn)
        builder.normalizerFamily factor left right hleftBasic hrightBasic htree
          hfactorWeight hfactorTruncated

end
  EABuild

end TCTex
end Submission
