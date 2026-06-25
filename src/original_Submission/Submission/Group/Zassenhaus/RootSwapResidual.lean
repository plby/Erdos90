import Submission.Group.HallBasic.SwapCoordinateScaling
import Submission.Group.HallBasic.SwapValueScaling
import Submission.Group.Zassenhaus.BasicTreeReduction

/-!
# Sign-corrected swaps of expanded symbolic roots

When a symbolic Hall-power factor is already exposed as a commutator word,
its two root words can be swapped without compressing either subtree into a
canonical address.  Negating the exponent gives the sign-corrected reversed
factor.

The explicit Hall-reduction packets agree exactly.  The values differ by a
next-stratum skew residual, so recollection of the original true residual
reduces to recollection of the reversed residual and the inverse skew packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/-- Swap the two exposed root words and negate the symbolic exponent. -/
noncomputable def expandedSwapFactor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight :=
  (factor.reword (.commutator right left) (by
    rw [hword]
    simp only [CWord.weight_commutator]
    omega)).neg

@[simp]
theorem word_expanded_swap
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    (expandedSwapFactor factor left right hword).word =
      .commutator right left := by
  simp [expandedSwapFactor]

@[simp]
theorem tree_expanded_swap
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    tree (expandedSwapFactor factor left right hword).word =
      .commutator (tree right) (tree left) := by
  simp [expandedSwapFactor]

@[simp]
theorem exponent_expanded_swap
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (q : ℕ) :
    (expandedSwapFactor factor left right hword).exponent q =
      -factor.exponent q := by
  simp [expandedSwapFactor]

@[simp]
theorem expanded_root_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    (expandedSwapFactor factor left right hword).word.weight
        PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  rw [word_expanded_swap, hword]
  simp only [CWord.weight_commutator]
  omega

/-- The atomic Hall-reduction packet is invariant under signed root swap. -/
theorem expanded_swap_factor
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionFactors factor) =
      SPFactora.listEval q
        (basicReductionFactors
          (expandedSwapFactor factor left right hword)) := by
  rw [list_basic_factors, list_basic_factors,
    hword, tree_commutator, tree_expanded_swap,
    exponent_expanded_swap,
    HallTree.scaled_swap_neg]

/-- Value-level skew residual: original inverse followed by signed reverse. -/
noncomputable def expandedSwapRaw
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  [factor.neg, expandedSwapFactor factor left right hword]

/-- Truncation of the original factor truncates its root-swap residual. -/
theorem truncated_expanded_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (expandedSwapRaw factor left right hword) := by
  intro x hx
  simp only [expandedSwapRaw, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simpa only [SPFactora.word_neg] using hfactor
  · simpa only [expanded_root_factor] using hfactor

/-- The signed root-swap value residual evaluates one stratum higher. -/
theorem expanded_raw_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedSwapRaw factor left right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  have hfree :=
    HallTree.swap_zpow_series
      (tree left) (tree right) (factor.exponent q)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [hword, CWord.weight_commutator, ← tree_weight left,
            ← tree_weight right]
          exact hfree))
  rw [expandedSwapRaw,
    SPFactora.listEval_cons,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one]
  rw [← tree_commutator left right, ← tree_commutator right left] at hmap
  rw [map_mul, map_inv, map_zpow, map_zpow,
    lower_truncation_tree,
    lower_truncation_tree] at hmap
  simpa only [SPFactora.eval_neg,
    SPFactora.eval, SPFactora.wordValue,
    expandedSwapFactor, SPFactora.word_neg,
    SPFactora.word_reword, SPFactora.exponent_neg,
    SPFactora.exponent_reword, hword, zpow_neg] using hmap

/-- Inverse orientation of the root-swap value residual. -/
noncomputable def expandedSwapSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
    (expandedSwapRaw factor left right hword)

/-- Truncation is preserved by inversion of the root-swap value residual. -/
theorem truncated_expanded_swap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (expandedSwapSource factor left right
        hword) :=
  SPFactora.truncated_inverse_list
    (truncated_expanded_source factor left right
      hword hfactor)

/-- The inverse root-swap value residual also lies one stratum higher. -/
theorem
    expanded_swap_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedSwapSource factor left right
          hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [expandedSwapSource,
    SPFactora.list_eval_inverse]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)).inv_mem
        (expanded_raw_series
          factor left right hword q)

/-- Recursive source for a signed root-swap reduction. -/
noncomputable def expandedSwapDecomposition
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  basicRawSource
      (expandedSwapFactor factor left right hword) ++
    expandedSwapSource factor left right hword

/-- The signed root-swap decomposition evaluates to the original residual. -/
theorem
    expanded_swap_decomposition
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedSwapDecomposition factor left right
          hword) =
      SPFactora.listEval q
        (basicRawSource factor) := by
  simp only [expandedSwapDecomposition,
    expandedSwapSource,
    expandedSwapRaw,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    reduction_raw_source,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one,
    SPFactora.eval_neg]
  rw [←
    expanded_swap_factor factor left right
      hword q]
  group

end HEWord
end TCTex
end Submission
