import Towers.Group.HallBasic.SwapCoordinateScaling
import Towers.Group.HallBasic.SwapValueScaling
import Towers.Group.Zassenhaus.SignedReductionFactors
import Towers.Group.Zassenhaus.CoefficientNegationRouting
import Towers.Group.Zassenhaus.PolynomialBracketSupport
import Towers.Group.HallBasic.JacobiValueScaling
import Towers.Group.Zassenhaus.Polynomial
import Towers.Group.Zassenhaus.SignedCorrectionSemantics

/-!
# Sign-corrected swaps of expanded polynomial roots

When a polynomial factor is exposed as a commutator word, swap its two root
words and negate its coefficient formula.  The explicit reduction packets
agree and the values differ by a next-stratum skew residual.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

universe u

/-- Swap two exposed root words and negate the coefficient formula. -/
noncomputable def expandedSwapFactor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    SPFactor
      (concreteBasicCommutators.{u} d) ι :=
  (factor.reword (.commutator right left) (by
    rw [hword]
    simp only [CWord.weight_commutator]
    omega)).neg

@[simp]
theorem word_expanded_swap
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    (expandedSwapFactor factor left right hword).word =
      .commutator right left := by
  simp [expandedSwapFactor]

@[simp]
theorem tree_expanded_swap
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    tree (expandedSwapFactor factor left right hword).word =
      .commutator (tree right) (tree left) := by
  simp [expandedSwapFactor]

@[simp]
theorem coefficient_expanded_swap
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (expandedSwapFactor factor left right hword).coefficient.eval e =
      -factor.coefficient.eval e := by
  rw [expandedSwapFactor,
    SPFactor.coefficient_eval_neg,
    SPFactor.coefficient_eval_reword]

@[simp]
theorem expanded_root_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    (expandedSwapFactor factor left right hword).word.weight
        HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  rw [word_expanded_swap, hword]
  simp only [CWord.weight_commutator]
  omega

/-- The atomic reduction packet is invariant under signed root swap. -/
theorem expanded_swap_factor
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicReductionFactors factor) =
      SPFactor.listEval e
        (basicReductionFactors
          (expandedSwapFactor factor left right hword)) := by
  have htree :
      tree factor.word = .commutator (tree left) (tree right) := by
    rw [hword, tree_commutator]
  rw [list_basic_factors, list_basic_factors,
    htree, tree_expanded_swap,
    coefficient_expanded_swap,
    HallTree.scaled_swap_neg]

/-- Value-level skew residual for an exposed signed root swap. -/
noncomputable def expandedSwapRaw
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  [factor.neg, expandedSwapFactor factor left right hword]

/-- Truncation of the factor truncates its root-swap residual. -/
theorem truncated_expanded_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (expandedSwapRaw factor left right hword) := by
  intro x hx
  simp only [expandedSwapRaw, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simpa only [SPFactor.word_neg] using hfactor
  · simpa only [expanded_root_factor] using hfactor

/-- The signed root-swap value residual evaluates one stratum higher. -/
theorem expanded_raw_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedSwapRaw factor left right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  have hfree :=
    HallTree.swap_zpow_series
      (tree left) (tree right) (factor.coefficient.eval e)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [hword, CWord.weight_commutator, ← tree_weight left,
            ← tree_weight right]
          exact hfree))
  rw [expandedSwapRaw,
    SPFactor.listEval_cons,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one]
  rw [← tree_commutator left right, ← tree_commutator right left] at hmap
  rw [map_mul, map_inv, map_zpow, map_zpow,
    lower_truncation_tree,
    lower_truncation_tree] at hmap
  rw [SPFactor.eval_neg,
    SPFactor.eval,
    SPFactor.eval,
    coefficient_expanded_swap]
  simpa only [SPFactor.eval_neg,
    SPFactor.eval, SPFactor.wordValue,
    expandedSwapFactor, SPFactor.word_neg,
    SPFactor.word_reword,
    SPFactor.coefficient_eval_neg,
    SPFactor.coefficient_eval_reword, hword,
    zpow_neg] using hmap

/-- Inverse orientation of the root-swap value residual. -/
noncomputable def expandedSwapSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList
    (expandedSwapRaw factor left right hword)

/-- Truncation is preserved by inversion of the root-swap value residual. -/
theorem truncated_expanded_swap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (expandedSwapSource factor left right
        hword) :=
  SPFactor.truncated_inverse_list
    (truncated_expanded_source factor left right
      hword hfactor)

/-- The inverse root-swap residual also lies one stratum higher. -/
theorem
    expanded_swap_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedSwapSource factor left right
          hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [expandedSwapSource,
    SPFactor.list_eval_inverse]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)).inv_mem
        (expanded_raw_series
          factor left right hword e)

/-- Recursive source for a signed root-swap reduction. -/
noncomputable def expandedSwapDecomposition
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  basicRawSource
      (expandedSwapFactor factor left right hword) ++
    expandedSwapSource factor left right hword

/-- The signed root-swap decomposition evaluates to the original residual. -/
theorem
    expanded_swap_decomposition
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedSwapDecomposition factor left right
          hword) =
      SPFactor.listEval e
        (basicRawSource factor) := by
  simp only [expandedSwapDecomposition,
    expandedSwapSource,
    expandedSwapRaw,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    reduction_raw_source,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one,
    SPFactor.eval_neg]
  rw [←
    expanded_swap_factor factor left right
      hword e]
  group

end CEWord
end TCTex
end Towers

/-!
# Expanded Jacobi decomposition for concrete Hall-polynomial factors

An expanded Hall-tree root may hide a basic inner bracket inside one
canonical Hall address.  This file re-encodes basic subtrees by canonical
addresses and exposes symbolic representatives for all three Jacobi
branches.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

universe u

/-- Compress one basic Hall tree back into its canonical Hall address. -/
noncomputable def addressBasicTree
    {d : ℕ}
    (basicTree : HallTree (FreeGenerator.{u} d))
    (hbasic : basicTree.IsBasic) :
    HEAddres (concreteBasicCommutators.{u} d) :=
  ⟨basicTree.weight,
    Classical.choose (concrete_basic_tree hbasic rfl)⟩

@[simp]
theorem address_tree_weight
    {d : ℕ}
    (basicTree : HallTree (FreeGenerator.{u} d))
    (hbasic : basicTree.IsBasic) :
    HEAddres.weight (addressBasicTree basicTree hbasic) =
      basicTree.weight :=
  rfl

@[simp]
theorem tree_atom_address
    {d : ℕ}
    (basicTree : HallTree (FreeGenerator.{u} d))
    (hbasic : basicTree.IsBasic) :
    tree (.atom (addressBasicTree basicTree hbasic)) = basicTree := by
  exact Classical.choose_spec (concrete_basic_tree hbasic rfl)

/-- Symbolic representatives for the branches of an expanded Jacobi root. -/
structure ExpandedJacobiDecomposition
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))) where
  left :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  middle :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  right :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  tree_eq :
    tree word =
      .commutator (.commutator (tree left) (tree middle)) (tree right)

/--
Every nonbasic expanded left-normed root admits symbolic representatives for
its three Jacobi branches.
-/
theorem nonempty_expanded_tree
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      tree word = .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic) :
    Nonempty (ExpandedJacobiDecomposition word) := by
  rcases
      words_tree_basic word
        (.commutator left middle) right htree houterNonbasic with
    ⟨innerWord, rightWord, hword, hinnerTree, hrightTree⟩
  by_cases hinnerBasic : (HallTree.commutator left middle).IsBasic
  · have hleftBasic :=
      (HallTree.isBasic_commutator left middle).mp hinnerBasic |>.1
    have hmiddleBasic :=
      (HallTree.isBasic_commutator left middle).mp hinnerBasic |>.2.1
    exact
      ⟨{ left := .atom (addressBasicTree left hleftBasic)
         middle := .atom (addressBasicTree middle hmiddleBasic)
         right := rightWord
         tree_eq := by
           rw [hword, tree_commutator, tree_atom_address,
             tree_atom_address, hrightTree, hinnerTree] }⟩
  · rcases
        words_tree_basic innerWord
          left middle hinnerTree hinnerBasic with
      ⟨leftWord, middleWord, hinnerWord, hleftTree, hmiddleTree⟩
    exact
      ⟨{ left := leftWord
         middle := middleWord
         right := rightWord
         tree_eq := by
           rw [hword, tree_commutator, hinnerWord, tree_commutator,
             hleftTree, hmiddleTree, hrightTree] }⟩

/-- Choose symbolic representatives for an expanded nonbasic Jacobi root. -/
noncomputable def
    expandedTreeNonbasic
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      tree word = .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic) :
    ExpandedJacobiDecomposition word :=
  Classical.choice
    (nonempty_expanded_tree
      word left middle right htree houterNonbasic)

/-- The first descendant factor of an expanded Jacobi decomposition. -/
noncomputable def expandedJacobiFactor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    SPFactor
      (concreteBasicCommutators.{u} d) ι :=
  factor.reword
    (.commutator (.commutator decomposition.left decomposition.right)
      decomposition.middle)
    (by
      have hweight := congrArg HallTree.weight decomposition.tree_eq
      simp only [HallTree.weight_commutator, tree_weight] at hweight
      simp only [CWord.weight_commutator]
      omega)

/-- The negatively signed second descendant of an expanded Jacobi decomposition. -/
noncomputable def expandedJacobiSecond
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    SPFactor
      (concreteBasicCommutators.{u} d) ι :=
  (factor.reword
    (.commutator (.commutator decomposition.middle decomposition.right)
      decomposition.left)
    (by
      have hweight := congrArg HallTree.weight decomposition.tree_eq
      simp only [HallTree.weight_commutator, tree_weight] at hweight
      simp only [CWord.weight_commutator]
      omega)).neg

@[simp]
theorem coefficient_expanded_jacobi
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (expandedJacobiFactor factor decomposition).coefficient.eval e =
      factor.coefficient.eval e := by
  rw [expandedJacobiFactor,
    SPFactor.coefficient_eval_reword]

@[simp]
theorem expanded_jacobi_second
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (expandedJacobiSecond factor decomposition).coefficient.eval e =
      -factor.coefficient.eval e := by
  rw [expandedJacobiSecond,
    SPFactor.coefficient_eval_neg,
    SPFactor.coefficient_eval_reword]

@[simp]
theorem expanded_jacobi_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    (expandedJacobiFactor factor decomposition).word.weight
        HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  have hweight := congrArg HallTree.weight decomposition.tree_eq
  simp only [HallTree.weight_commutator, tree_weight] at hweight
  simp only [expandedJacobiFactor,
    SPFactor.word_reword,
    CWord.weight_commutator]
  omega

@[simp]
theorem expanded_second_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    (expandedJacobiSecond factor decomposition).word.weight
        HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  have hweight := congrArg HallTree.weight decomposition.tree_eq
  simp only [HallTree.weight_commutator, tree_weight] at hweight
  simp only [expandedJacobiSecond,
    SPFactor.word_neg,
    SPFactor.word_reword,
    CWord.weight_commutator]
  omega

/-- Atomic packet residual attached to an expanded Jacobi decomposition. -/
noncomputable def expandedJacobiReduction
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList (basicReductionFactors factor) ++
    basicReductionFactors (expandedJacobiFactor factor decomposition) ++
      basicReductionFactors (expandedJacobiSecond factor decomposition)

/-- Continuation left after peeling an expanded atomic Jacobi packet. -/
noncomputable def expandedContinuationSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList
      (basicReductionFactors
        (expandedJacobiSecond factor decomposition)) ++
    SPFactor.inverseList
      (basicReductionFactors
        (expandedJacobiFactor factor decomposition)) ++
      [factor]

/-- Truncation of the original factor truncates its expanded Jacobi packet. -/
theorem expanded_jacobi_reduction
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (expandedJacobiReduction factor decomposition) := by
  intro x hx
  simp only [expandedJacobiReduction, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact
      SPFactor.truncated_inverse_list
        (truncated_reduction_factors factor hfactor) x hx
  · exact
      truncated_reduction_factors
        (expandedJacobiFactor factor decomposition)
        (by
          simpa only [expanded_jacobi_factor] using hfactor)
        x hx
  · exact
      truncated_reduction_factors
        (expandedJacobiSecond factor decomposition)
        (by
          simpa only [expanded_second_factor] using hfactor)
        x hx

/-- Truncation of the original factor truncates its expanded continuation. -/
theorem truncated_expanded_continuation
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (expandedContinuationSource factor decomposition) := by
  intro x hx
  simp only [expandedContinuationSource, List.mem_append,
    List.mem_singleton] at hx
  rcases hx with (hx | hx) | hx
  · exact
      SPFactor.truncated_inverse_list
        (truncated_reduction_factors
          (expandedJacobiSecond factor decomposition)
          (by
            simpa only [expanded_second_factor] using hfactor))
        x hx
  · exact
      SPFactor.truncated_inverse_list
        (truncated_reduction_factors
          (expandedJacobiFactor factor decomposition)
          (by
            simpa only [expanded_jacobi_factor] using hfactor))
        x hx
  · subst x
    exact hfactor

/--
The expanded atomic Jacobi packet and continuation multiply to the true
factor residual.
-/
theorem
    expanded_jacobi_continuation
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedJacobiReduction factor decomposition) *
      SPFactor.listEval e
        (expandedContinuationSource factor decomposition) =
      SPFactor.listEval e
        (basicRawSource factor) := by
  simp only [expandedJacobiReduction,
    expandedContinuationSource,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    reduction_raw_source,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one]
  group

/-- The continuation is atomic-correction division of the residual. -/
theorem
    expanded_continuation_residual
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedContinuationSource factor decomposition) =
      (SPFactor.listEval e
        (expandedJacobiReduction factor decomposition))⁻¹ *
        SPFactor.listEval e
          (basicRawSource factor) := by
  rw [←
    expanded_jacobi_continuation
      factor decomposition e]
  group

/-- Every factor in the expanded Jacobi correction is an atom in its layer. -/
theorem atom_expanded_jacobi
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ expandedJacobiReduction factor decomposition) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧
        address.weight =
          factor.word.weight HEAddres.weight := by
  simp only [expandedJacobiReduction, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact atom_reduction_factors factor hx
  · rcases
      atom_basic_factors
        (expandedJacobiFactor factor decomposition) hx with
      ⟨address, haddress, hweight⟩
    exact
      ⟨address, haddress,
        hweight.trans
          (expanded_jacobi_factor factor decomposition)⟩
  · rcases
      atom_basic_factors
        (expandedJacobiSecond factor decomposition) hx with
      ⟨address, haddress, hweight⟩
    exact
      ⟨address, haddress,
        hweight.trans
          (expanded_second_factor factor decomposition)⟩

/-- The expanded Jacobi correction evaluates one lower-central layer higher. -/
theorem expanded_reduction_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedJacobiReduction factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  have hfree :=
    HallTree.scaled_jacobi_series
      (tree decomposition.left) (tree decomposition.middle)
        (tree decomposition.right) (factor.coefficient.eval e)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [← tree_weight factor.word, decomposition.tree_eq]
          exact hfree))
  rw [expandedJacobiReduction,
    SPFactor.listEval_append,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    list_basic_factors, list_basic_factors,
    list_basic_factors]
  rw [coefficient_expanded_jacobi,
    expanded_jacobi_second]
  simpa only [map_mul, map_inv, tree_commutator,
    expandedJacobiFactor, expandedJacobiSecond,
    SPFactor.word_neg,
    SPFactor.word_reword,
    SPFactor.coefficient_eval_neg,
    SPFactor.coefficient_eval_reword,
    decomposition.tree_eq, mul_assoc] using hmap

/-- The expanded Jacobi continuation also evaluates one layer higher. -/
theorem jacobi_continuation_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedContinuationSource factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [expanded_continuation_residual
    factor decomposition e]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)).mul_mem
        (Subgroup.inv_mem _
          (expanded_reduction_series
            factor decomposition e))
        (list_reduction_series
          factor e)

end CEWord
end TCTex
end Towers

/-!
# Recollections for sign-corrected expanded polynomial root swaps

The exact expanded-root swap decomposition reduces the original residual to
the residual of the signed reversed factor and one next-stratum skew packet.
Generic signed-source inversion supplies the orientation needed by that
decomposition from a forward recollection of the packet.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

/-- Upward recollection of a forward expanded-root skew-value residual. -/
structure
    PSRecoll
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) where
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
          (expandedSwapRaw factor left right hword)

namespace
  PSRecoll

/-- View a root-swap value recollection as a generic source recollection. -/
noncomputable def toSourceRecollection
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    {left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))}
    {hword : factor.word = .commutator left right}
    (recollection :
      PSRecoll
        (n := n) factor left right hword) :
    SSRecol
      (n := n)
      (lowerWeight := factor.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (expandedSwapRaw factor left right hword) where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_least_succ
  list_higher_raw :=
    recollection.list_higher_raw

end
  PSRecoll

namespace
  TRRecoll

/--
Recollect an expanded-root residual from its signed reverse and a forward
recollection of the skew-value packet.
-/
noncomputable def expanded_swap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (reversed :
      TRRecoll
        (n := n) (expandedSwapFactor factor left right hword))
    (valueResidual :
      PSRecoll
        (n := n) factor left right hword) :
    TRRecoll
      (n := n) factor := by
  let inverse := valueResidual.toSourceRecollection.inverse
  exact
    { higherSource := reversed.higherSource ++ inverse.higherSource
      higher_source_truncated := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact reversed.higher_source_truncated x hx
        · exact inverse.higher_source_truncated x hx
      higher_least_succ := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · simpa only [expanded_root_factor] using
            reversed.higher_least_succ x hx
        · exact inverse.higher_weight_least x hx
      list_higher_raw := by
        intro e
        rw [SPFactor.listEval_append,
          reversed.list_higher_raw e,
          inverse.list_higher_raw e,
          ←
            expanded_swap_decomposition
              factor left right hword e]
        rw [expandedSwapDecomposition,
          SPFactor.listEval_append,
          expandedSwapSource] }

end
  TRRecoll

end TCTex
end Towers

/-!
# Trees underlying expanded polynomial Jacobi descendants

Expanded symbolic Jacobi recollection leaves the two ordinary descendant
residuals as same-weight recursive obligations.  This file records their
underlying Hall trees explicitly.

It also isolates an important obstruction to a naive recursive closure:
following the first raw Jacobi descendant twice returns to the original
left-normed tree.  A terminating collector must therefore reduce the inner
bracket to its finite atomic Hall packet before recursing on the outer
brackets.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers

namespace HallTree

universe u

/-- The first tree produced by the left-normed Jacobi rewrite. -/
def jacobiFirstDescendant
    {α : Type u}
    (left middle right : HallTree α) :
    HallTree α :=
  .commutator (.commutator left right) middle

/-- The second tree produced by the left-normed Jacobi rewrite. -/
def jacobiSecondDescendant
    {α : Type u}
    (left middle right : HallTree α) :
    HallTree α :=
  .commutator (.commutator middle right) left

@[simp]
theorem jacobi_first_descendant
    {α : Type u}
    (left middle right : HallTree α) :
    (jacobiFirstDescendant left middle right).weight =
      (.commutator (.commutator left middle) right : HallTree α).weight := by
  simp only [jacobiFirstDescendant, weight_commutator]
  omega

@[simp]
theorem jacobi_second_descendant
    {α : Type u}
    (left middle right : HallTree α) :
    (jacobiSecondDescendant left middle right).weight =
      (.commutator (.commutator left middle) right : HallTree α).weight := by
  simp only [jacobiSecondDescendant, weight_commutator]
  omega

/--
Following the first raw Jacobi branch twice returns to the original tree.
Consequently raw first-descendant recursion alone is not well-founded.
-/
@[simp]
theorem jacobi_descendant_cycle
    {α : Type u}
    (left middle right : HallTree α) :
    jacobiFirstDescendant left right middle =
      .commutator (.commutator left middle) right :=
  rfl

end HallTree

namespace TCTex
namespace CEWord

universe u

/-- The expanded symbolic first descendant has the expected Hall tree. -/
@[simp]
theorem tree_expanded_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    tree (expandedJacobiFactor factor decomposition).word =
      HallTree.jacobiFirstDescendant
        (tree decomposition.left) (tree decomposition.middle)
          (tree decomposition.right) := by
  simp only [expandedJacobiFactor, SPFactor.word_reword,
    tree_commutator, HallTree.jacobiFirstDescendant]

/-- The expanded symbolic second descendant has the expected Hall tree. -/
@[simp]
theorem tree_expanded_jacobi
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    tree (expandedJacobiSecond factor decomposition).word =
      HallTree.jacobiSecondDescendant
        (tree decomposition.left) (tree decomposition.middle)
          (tree decomposition.right) := by
  simp only [expandedJacobiSecond, SPFactor.word_neg,
    SPFactor.word_reword, tree_commutator,
    HallTree.jacobiSecondDescendant]

end CEWord
end TCTex
end Towers

/-!
# Expanded signed-polynomial Jacobi value residuals

The expanded Jacobi value packet compares the original nested value with its
two signed descendant values, including the case where a basic inner bracket
was re-encoded by a canonical Hall address.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

universe u

/-- Value-level residual attached to an expanded Jacobi decomposition. -/
noncomputable def expandedJacobiRaw
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  [factor.neg,
    expandedJacobiFactor factor decomposition,
    expandedJacobiSecond factor decomposition]

/-- Truncation of the original factor truncates its expanded value residual. -/
theorem expanded_jacobi_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (expandedJacobiRaw factor decomposition) := by
  intro x hx
  simp only [expandedJacobiRaw, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · simpa only [SPFactor.word_neg] using hfactor
  · simpa only [expanded_jacobi_factor] using hfactor
  · simpa only [expanded_second_factor] using hfactor

/-- The expanded Jacobi value residual evaluates one stratum higher. -/
theorem list_expanded_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedJacobiRaw factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  have hfree :=
    HallTree.jacobi_zpow_series
      (tree decomposition.left) (tree decomposition.middle)
        (tree decomposition.right) (factor.coefficient.eval e)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [← tree_weight factor.word, decomposition.tree_eq]
          exact hfree))
  rw [expandedJacobiRaw,
    SPFactor.listEval_cons,
    SPFactor.listEval_cons,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one]
  rw [← decomposition.tree_eq,
    ← tree_commutator decomposition.left decomposition.right,
    ← tree_commutator (.commutator decomposition.left decomposition.right)
      decomposition.middle,
    ← tree_commutator decomposition.middle decomposition.right,
    ← tree_commutator (.commutator decomposition.middle decomposition.right)
      decomposition.left] at hmap
  rw [map_mul, map_inv, map_zpow, map_mul, map_zpow, map_zpow,
    lower_truncation_tree,
    lower_truncation_tree,
    lower_truncation_tree] at hmap
  rw [SPFactor.eval_neg,
    SPFactor.eval, SPFactor.eval,
    SPFactor.eval,
    coefficient_expanded_jacobi,
    expanded_jacobi_second]
  simpa only [map_mul, map_inv, map_zpow,
    SPFactor.eval,
    SPFactor.wordValue,
    expandedJacobiFactor, expandedJacobiSecond,
    SPFactor.word_neg,
    SPFactor.word_reword, decomposition.tree_eq,
    zpow_neg] using hmap

/-- Inverse orientation of the expanded Jacobi value residual. -/
noncomputable def expandedJacobiSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList
    (expandedJacobiRaw factor decomposition)

/-- Truncation is preserved by inversion of the expanded value residual. -/
theorem truncated_expanded_jacobi
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (expandedJacobiSource factor decomposition) := by
  exact
    SPFactor.truncated_inverse_list
      (expanded_jacobi_source
        factor decomposition hfactor)

/-- The inverse expanded value residual also lies one stratum higher. -/
theorem
    expanded_jacobi_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedJacobiSource factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [expandedJacobiSource,
    SPFactor.list_eval_inverse]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)).inv_mem
        (list_expanded_series
          factor decomposition e)

end CEWord
end TCTex
end Towers

/-!
# Recursive decomposition of the expanded polynomial Jacobi continuation

After the atomic packet is peeled, the expanded continuation is the second
descendant residual, the conjugated first descendant residual, and the
inverse expanded value residual.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

universe u

/-- Recursive source whose evaluation is the expanded Jacobi continuation. -/
noncomputable def expandedContinuationDecomposition
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  basicRawSource
      (expandedJacobiSecond factor decomposition) ++
    [(expandedJacobiSecond factor decomposition).neg] ++
      basicRawSource
          (expandedJacobiFactor factor decomposition) ++
        [expandedJacobiSecond factor decomposition] ++
          expandedJacobiSource factor decomposition

/-- Truncation of the factor truncates its recursive continuation. -/
theorem expanded_continuation_decomposition
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (expandedContinuationDecomposition
        factor decomposition) := by
  have hfirst :
      (expandedJacobiFactor factor decomposition).word.weight
          HEAddres.weight < n := by
    simpa only [expanded_jacobi_factor] using hfactor
  have hsecond :
      (expandedJacobiSecond factor decomposition).word.weight
          HEAddres.weight < n := by
    simpa only [expanded_second_factor] using hfactor
  intro x hx
  simp only [expandedContinuationDecomposition,
    List.mem_append] at hx
  rcases hx with (((hx | hx) | hx) | hx) | hx
  · exact
      truncated_reduction_source
        (expandedJacobiSecond factor decomposition) hsecond x hx
  · simp only [List.mem_singleton] at hx
    subst x
    simpa only [SPFactor.word_neg] using hsecond
  · exact
      truncated_reduction_source
        (expandedJacobiFactor factor decomposition) hfirst x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hsecond
  · exact
      truncated_expanded_jacobi
        factor decomposition hfactor x hx

/-- The recursive decomposition evaluates exactly to the continuation. -/
theorem
    expanded_continuation_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedContinuationDecomposition
          factor decomposition) =
      SPFactor.listEval e
        (expandedContinuationSource factor decomposition) := by
  simp only [expandedContinuationDecomposition,
    expandedContinuationSource,
    expandedJacobiSource,
    expandedJacobiRaw,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    reduction_raw_source,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one,
    SPFactor.eval_neg]
  group

/-- The recursive decomposition inherits next-stratum membership. -/
theorem
    expanded_continuation_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedContinuationDecomposition
          factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [
    expanded_continuation_source
      factor decomposition e]
  exact
    jacobi_continuation_series
      factor decomposition e

end CEWord
end TCTex
end Towers

/-!
# Recursive interface for expanded polynomial Jacobi continuations

Expanded Jacobi decompositions include roots whose inner basic bracket is
compressed into a canonical Hall address.  Their atomic correction routes
upward through the supported packet factory, leaving recollection of the
explicit continuation decomposition as the recursive boundary.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

namespace TSFtry

/-- Route an expanded atomic Jacobi correction one stratum higher. -/
noncomputable def higher_expanded_raw
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ higherSource :
        List
          (SPFactor
            (concreteBasicCommutators.{u} d) ι),
      SPFactor.IsTruncated n higherSource ∧
        SPFactor.WordWeightLeast
          (lowerWeight + 1) higherSource ∧
            ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
              SPFactor.listEval (n := n) e higherSource =
                SPFactor.listEval e
                  (expandedJacobiReduction factor decomposition) := by
  apply factory.higher_atoms_series
      hn (concreteBasicCommutators.{u} d) hH sharp nextNormalizer
        (expandedJacobiReduction factor decomposition)
  · have hfactorPos := factor.word_weight_pos
    omega
  · omega
  · exact
      expanded_jacobi_reduction factor decomposition
        hfactorTruncated
  · intro x hx
    rcases
        atom_expanded_jacobi
          factor decomposition hx with
      ⟨address, haddress, haddressWeight⟩
    exact ⟨address, haddress, haddressWeight.trans hfactorWeight⟩
  · intro e
    simpa only [hfactorWeight] using
      expanded_reduction_series
        factor decomposition e

end TSFtry

/-- Semantic recollection data for an expanded Jacobi continuation. -/
structure
    ExpandedContinuationRecollection
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
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
          (expandedContinuationSource factor decomposition)

namespace
  TRRecoll

/-- Combine an expanded atomic correction with its continuation recollection. -/
noncomputable def expanded_raw_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (jacobiHigherSource :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι))
    (hjacobiTruncated :
      SPFactor.IsTruncated n jacobiHigherSource)
    (hjacobiSupported :
      SPFactor.WordWeightLeast
        (factor.word.weight HEAddres.weight + 1)
        jacobiHigherSource)
    (hjacobiEval :
      ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
        SPFactor.listEval (n := n) e jacobiHigherSource =
          SPFactor.listEval e
            (expandedJacobiReduction factor decomposition))
    (continuation :
      ExpandedContinuationRecollection
        (n := n) factor decomposition) :
    TRRecoll
      (n := n) factor where
  higherSource := jacobiHigherSource ++ continuation.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiTruncated x hx
    · exact continuation.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiSupported x hx
    · exact continuation.higher_least_succ x hx
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_append, hjacobiEval e,
      continuation.list_higher_raw e,
      expanded_jacobi_continuation]

/-- Route the expanded atomic packet and leave only its continuation input. -/
noncomputable def expanded_reduction
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (continuation :
      ExpandedContinuationRecollection
        (n := n) factor decomposition) :
    TRRecoll
      (n := n) factor := by
  let jacobi :=
    factory.higher_expanded_raw hn hH
      sharp nextNormalizer factor decomposition hfactorWeight hfactorTruncated
  let jacobiHigherSource := Classical.choose jacobi
  have hjacobiTruncated := (Classical.choose_spec jacobi).1
  have hjacobiSupported := (Classical.choose_spec jacobi).2.1
  have hjacobiEval := (Classical.choose_spec jacobi).2.2
  exact
    expanded_raw_source factor decomposition
      jacobiHigherSource hjacobiTruncated
        (by simpa only [hfactorWeight] using hjacobiSupported)
          hjacobiEval continuation

/-- Compile a Hall-Petresco packet and deeper normalizers for one expanded residual. -/
noncomputable def expanded_normalizer_above
    {d n lowerWeight : ℕ}
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
    {ι : Type}
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (continuation :
      ExpandedContinuationRecollection
        (n := n) factor decomposition) :
    TRRecoll
      (n := n) factor :=
  expanded_reduction hn hH
    ((packet.supportedWordFactory
      (WBForm.chooseNormalizerFamily
        (concreteBasicCommutators.{u} d))
      lowerWeight).correctionPacketFactory)
    (TSNormala.ofNormalizerAbove
      normalizerAbove)
    (normalizerAbove (lowerWeight + 1) (by omega))
    factor decomposition hfactorWeight hfactorTruncated continuation

end
  TRRecoll

/-- Recollection data for the explicit expanded recursive decomposition. -/
structure
    TDRecoll
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  higherSource :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight + 1) higherSource
  list_decomposition_raw :
    ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (expandedContinuationDecomposition
            factor decomposition)

namespace
  TDRecoll

/-- Forget the recursive shape after compiling it into a continuation recollection. -/
noncomputable def expandedContinuationRecollection
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    {decomposition : ExpandedJacobiDecomposition factor.word}
    (recollection :
      TDRecoll
        (n := n) factor decomposition) :
    ExpandedContinuationRecollection
      (n := n) factor decomposition where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_least_succ :=
    recollection.higher_least_succ
  list_higher_raw := by
    intro e
    rw [recollection.list_decomposition_raw e,
      expanded_continuation_source]

end
  TDRecoll

/-- A packet and recursive recollections for expanded Jacobi continuations. -/
structure
    CDBuilda
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  expandedJacobiDecomposition :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TDRecoll
                (n := n) factor decomposition

namespace
  CDBuilda

open
  TRRecoll

/-- Lift one expanded Jacobi factor from recollection of its decomposition. -/
noncomputable def jacobiResidual
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      CDBuilda.{u}
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
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  expanded_normalizer_above hn
    (fun s hs hsn =>
      concrete_forms_associated d n s hs hsn)
    builder.packet normalizerAbove factor decomposition hfactorWeight
      hfactorTruncated
        (builder.expandedJacobiDecomposition lowerWeight
          hnonterminal factor decomposition hfactorWeight hfactorTruncated
          |>.expandedContinuationRecollection)

/-- Every expanded nonbasic left-normed root enters the recursive collector. -/
noncomputable def jacobiTreeNonbasic
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      CDBuilda.{u}
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
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      CEWord.tree factor.word =
        .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  let decomposition :=
    expandedTreeNonbasic
      factor.word left middle right htree houterNonbasic
  builder.jacobiResidual lowerWeight hnonterminal normalizerAbove factor
    decomposition hfactorWeight hfactorTruncated

end
  CDBuilda
end TCTex
end Towers

/-!
# Splicing recursive expanded polynomial Jacobi continuations

The recursive expanded Jacobi continuation contains the second descendant
residual, the first descendant residual conjugated by the second descendant
value, and the inverse value-level Jacobi residual.  This file packages
independent upward recollections of those three pieces into the continuation
recollection consumed by expanded Jacobi recursion.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

/-- Raw source for the first descendant residual conjugated by the second. -/
noncomputable def expandedConjugatedSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  [(expandedJacobiSecond factor decomposition).neg] ++
    basicRawSource
      (expandedJacobiFactor factor decomposition) ++
    [expandedJacobiSecond factor decomposition]

/--
The expanded continuation decomposition is the concatenation of the second
descendant residual, the conjugated first residual, and the inverse
value-level residual.
-/
theorem continuation_decomposition_splice
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    expandedContinuationDecomposition factor decomposition =
      basicRawSource
          (expandedJacobiSecond factor decomposition) ++
        expandedConjugatedSource factor decomposition ++
          expandedJacobiSource factor decomposition := by
  simp [expandedContinuationDecomposition,
    expandedConjugatedSource, List.append_assoc]

/-- Upward recollection of the conjugated first descendant residual. -/
structure
    TCRecolla
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
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
          (expandedConjugatedSource
            factor decomposition)

/-- Upward recollection of the inverse value-level Jacobi residual. -/
structure
    ExpandedJacobiRecollection
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
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
          (expandedJacobiSource factor decomposition)

namespace
  TDRecoll

/--
Splice independently recollected recursive pieces into an upward recollection
of the full expanded Jacobi continuation decomposition.
-/
noncomputable def of_spliced
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (second :
      TRRecoll
        (n := n) (expandedJacobiSecond factor decomposition))
    (conjugatedFirst :
      TCRecolla
        (n := n) factor decomposition)
    (valueResidualInverse :
      ExpandedJacobiRecollection
        (n := n) factor decomposition) :
    TDRecoll
      (n := n) factor decomposition where
  higherSource :=
    second.higherSource ++
      conjugatedFirst.higherSource ++
        valueResidualInverse.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact second.higher_source_truncated x hx
      · exact conjugatedFirst.higher_source_truncated x hx
    · exact valueResidualInverse.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · simpa only [expanded_second_factor] using
          second.higher_least_succ x hx
      · exact conjugatedFirst.higher_least_succ x hx
    · exact valueResidualInverse.higher_least_succ x hx
  list_decomposition_raw := by
    intro e
    rw [SPFactor.listEval_append,
      SPFactor.listEval_append,
      second.list_higher_raw e,
      conjugatedFirst.list_higher_raw e,
      valueResidualInverse.list_higher_raw e,
      continuation_decomposition_splice,
      SPFactor.listEval_append,
      SPFactor.listEval_append]

end
  TDRecoll

/-- Explicit recollections of the three expanded-Jacobi continuation pieces. -/
structure
    CSBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  secondResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecoll
                (n := n) (expandedJacobiSecond factor decomposition)
  conjugatedFirstResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TCRecolla
                (n := n) factor decomposition
  valueResidualInverse :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ExpandedJacobiRecollection
                (n := n) factor decomposition

namespace
  CSBuild

open
  TDRecoll

/--
Compile explicit recursive-piece recollections into the continuation builder
consumed by expanded Jacobi collection.
-/
noncomputable def expandedContinuationBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      CSBuild.{u}
        (d := d) (n := n) hn) :
    CDBuilda
      (d := d) (n := n) hn where
  packet := builder.packet
  expandedJacobiDecomposition :=
    fun lowerWeight hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      of_spliced factor decomposition
          (builder.secondResidual lowerWeight hnonterminal factor decomposition
            hfactorWeight hfactorTruncated)
          (builder.conjugatedFirstResidual lowerWeight hnonterminal factor
            decomposition hfactorWeight hfactorTruncated)
          (builder.valueResidualInverse lowerWeight hnonterminal factor
            decomposition hfactorWeight hfactorTruncated)

end
  CSBuild

end TCTex
end Towers

/-!
# Routing conjugated expanded polynomial Jacobi residuals

The recursive expanded Jacobi continuation contains the conjugated source

`second⁻¹ * R(first) * second`.

Once `R(first)` has been recollected one stratum higher, the sharp signed
higher-tail router moves `second` left across that source.  Its leading copy
cancels semantically with `second⁻¹`, leaving a physically higher source.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

namespace
  TCRecolla

/--
Route the second descendant across an upward recollection of the first
descendant residual.
-/
noncomputable def of_firstResidual
    {d n lowerWeight : ℕ}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (first :
      TRRecoll
        (n := n) (expandedJacobiFactor factor decomposition)) :
    TCRecolla
      (n := n) factor decomposition := by
  have hsecondWeight :
      (expandedJacobiSecond factor decomposition).word.weight
          HEAddres.weight = lowerWeight := by
    simpa only [expanded_second_factor] using hfactorWeight
  have hsecondTruncated :
      (expandedJacobiSecond factor decomposition).word.weight
          HEAddres.weight < n := by
    simpa only [expanded_second_factor] using hfactorTruncated
  have hfirstSupported :
      SPFactor.WordWeightLeast
        (lowerWeight + 1) first.higherSource := by
    simpa only [expanded_jacobi_factor, hfactorWeight] using
      first.higher_least_succ
  let routed :=
    factory.conjugated_recollection_normalizer sharp
      (expandedJacobiSecond factor decomposition) hsecondWeight
        hsecondTruncated
          (basicRawSource
            (expandedJacobiFactor factor decomposition))
          first.higherSource first.higher_source_truncated hfirstSupported
            first.list_higher_raw
  exact
    { higherSource := routed.higherSource
      higher_source_truncated := routed.higher_source_truncated
      higher_least_succ := by
        simpa only [hfactorWeight] using
          routed.higher_least_succ
      list_higher_raw := by
        intro e
        simpa only [expandedConjugatedSource,
          SPFactor.conjugatedRawSource] using
            routed.higher_conjugated_raw e }

/--
Compile a Hall-Petresco packet and strictly deeper normalizers into the route
for the conjugated first descendant residual.
-/
noncomputable def first_normalizer_above
    {d n lowerWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (first :
      TRRecoll
        (n := n) (expandedJacobiFactor factor decomposition)) :
    TCRecolla
      (n := n) factor decomposition :=
  of_firstResidual
    ((packet.supportedWordFactory
      (WBForm.chooseNormalizerFamily
        (concreteBasicCommutators.{u} d))
      lowerWeight).correctionPacketFactory)
    (TSNormala.ofNormalizerAbove
      normalizerAbove)
    factor decomposition hfactorWeight hfactorTruncated first

end
  TCRecolla

namespace
  TDRecoll

open
  TCRecolla

/--
Splice the recursive expanded Jacobi continuation after routing the
conjugation surrounding the first descendant residual.
-/
noncomputable def of_routedFirst
    {d n lowerWeight : ℕ}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (first :
      TRRecoll
        (n := n) (expandedJacobiFactor factor decomposition))
    (second :
      TRRecoll
        (n := n) (expandedJacobiSecond factor decomposition))
    (valueResidualInverse :
      ExpandedJacobiRecollection
        (n := n) factor decomposition) :
    TDRecoll
      (n := n) factor decomposition :=
  of_spliced factor decomposition second
    (of_firstResidual
      factory sharp factor decomposition hfactorWeight hfactorTruncated first)
    valueResidualInverse

/--
Compile a Hall-Petresco packet and strictly deeper normalizers into the
expanded Jacobi continuation splice.
-/
noncomputable def routed_normalizer_above
    {d n lowerWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (first :
      TRRecoll
        (n := n) (expandedJacobiFactor factor decomposition))
    (second :
      TRRecoll
        (n := n) (expandedJacobiSecond factor decomposition))
    (valueResidualInverse :
      ExpandedJacobiRecollection
        (n := n) factor decomposition) :
    TDRecoll
      (n := n) factor decomposition :=
  of_spliced factor decomposition second
    (first_normalizer_above
      packet normalizerAbove factor decomposition hfactorWeight
        hfactorTruncated first)
    valueResidualInverse

end
  TDRecoll

end TCTex
end Towers
