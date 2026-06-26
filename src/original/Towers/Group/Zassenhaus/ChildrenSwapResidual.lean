import Towers.Group.HallBasic.SwapCoordinateScaling
import Towers.Group.HallBasic.SwapValueScaling
import Towers.Group.Zassenhaus.Jacobi

/-!
# Reverse-orientation residuals for brackets with basic children

When both children of an expanded bracket are basic, they can be compressed
back into canonical Hall addresses.  Reversing those addresses and negating
the symbolic exponent produces a sign-corrected reversed factor.

Its explicit Hall-reduction packet agrees exactly with the packet of the
original factor.  The values differ by a next-stratum skew-symmetry residual,
so the original true reduction residual factors through the reversed one.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace HEWord

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

/--
Sign-corrected reversed factor.  It carries the reversed bracket word and the
negative of the original exponent.
-/
noncomputable def childrenSwapFactor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight :=
  (factor.reword
    (childrenSwapWord left right hleftBasic hrightBasic)
    (by
      rw [← tree_weight factor.word, htree]
      change
        PEAddres.weight
              (addressBasicTree right hrightBasic) +
            PEAddres.weight
              (addressBasicTree left hleftBasic) =
          left.weight + right.weight
      rw [address_tree_weight, address_tree_weight]
      omega)).neg

@[simp]
theorem tree_children_swap
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
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
theorem exponent_children_swap
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (q : ℕ) :
    (childrenSwapFactor factor left right hleftBasic hrightBasic
      htree).exponent q =
      -factor.exponent q := by
  simp [childrenSwapFactor]

@[simp]
theorem basic_children_swap
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    (childrenSwapFactor factor left right hleftBasic hrightBasic
      htree).word.weight PEAddres.weight =
        factor.word.weight PEAddres.weight := by
  simp only [childrenSwapFactor, SPFactora.word_neg,
    SPFactora.word_reword]
  rw [← tree_weight factor.word, htree]
  change
    PEAddres.weight
          (addressBasicTree right hrightBasic) +
        PEAddres.weight
          (addressBasicTree left hleftBasic) =
      left.weight + right.weight
  rw [address_tree_weight, address_tree_weight]
  omega

/--
The atomic Hall-reduction packet is unchanged by the sign-corrected reverse
orientation.
-/
theorem children_swap_factor
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionFactors factor) =
      SPFactora.listEval q
        (basicReductionFactors
          (childrenSwapFactor factor left right hleftBasic hrightBasic
            htree)) := by
  rw [list_basic_factors, list_basic_factors,
    htree, tree_children_swap,
    exponent_children_swap,
    HallTree.scaled_swap_neg]

/-- Value-level skew residual: original inverse followed by signed reverse. -/
noncomputable def childrenSwapSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  [factor.neg,
    childrenSwapFactor factor left right hleftBasic hrightBasic htree]

/-- Truncation of the original factor truncates its skew-value residual. -/
theorem children_swap_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (childrenSwapSource factor left right hleftBasic
        hrightBasic htree) := by
  intro x hx
  simp only [childrenSwapSource, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simpa only [SPFactora.word_neg] using hfactor
  · simpa only [basic_children_swap] using hfactor

/-- The symbolic skew-value residual evaluates one lower-central layer higher. -/
theorem
    children_raw_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (childrenSwapSource factor left right hleftBasic
          hrightBasic htree) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  have hfree :=
    HallTree.swap_zpow_series
      left right (factor.exponent q)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [← tree_weight factor.word, htree]
          exact hfree))
  rw [childrenSwapSource,
    SPFactora.listEval_cons,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one]
  rw [← htree,
    ← tree_basic_children left right hleftBasic hrightBasic] at hmap
  rw [map_mul, map_inv, map_zpow, map_zpow,
    lower_truncation_tree,
    lower_truncation_tree] at hmap
  simpa only [SPFactora.eval_neg,
    SPFactora.eval, SPFactora.wordValue,
    childrenSwapFactor, SPFactora.word_neg,
    SPFactora.word_reword, SPFactora.exponent_neg,
    SPFactora.exponent_reword, zpow_neg] using hmap

/-- Inverse orientation of the symbolic skew-value residual. -/
noncomputable def basicChildrenSwap
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
    (childrenSwapSource factor left right hleftBasic
      hrightBasic htree)

/-- Truncation is preserved by inversion of the skew-value residual. -/
theorem truncated_children_swap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (basicChildrenSwap factor left right
        hleftBasic hrightBasic htree) := by
  exact
    SPFactora.truncated_inverse_list
      (children_swap_source factor left right
        hleftBasic hrightBasic htree hfactor)

/-- The inverse skew-value residual also lies one lower-central layer higher. -/
theorem
    children_swap_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicChildrenSwap factor left right
          hleftBasic hrightBasic htree) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [basicChildrenSwap,
    SPFactora.list_eval_inverse]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)).inv_mem
        (children_raw_series
          factor left right hleftBasic hrightBasic htree q)

/--
Recursive source for the original residual: recollect the sign-corrected
reversed residual, then append the inverse skew-value residual.
-/
noncomputable def childrenSwapDecomposition
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  basicRawSource
      (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree) ++
    basicChildrenSwap factor left right
      hleftBasic hrightBasic htree

/-- The reverse-orientation recursive source is physically truncated. -/
theorem truncated_children_decomposition
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
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

/--
The reverse-orientation recursive source evaluates exactly to the original
true residual.
-/
theorem
    children_swap_decomposition
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (childrenSwapDecomposition factor left right
          hleftBasic hrightBasic htree) =
      SPFactora.listEval q
        (basicRawSource factor) := by
  simp only [childrenSwapDecomposition,
    basicChildrenSwap,
    childrenSwapSource,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    reduction_raw_source,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one,
    SPFactora.eval_neg]
  rw [←
    children_swap_factor factor left right
      hleftBasic hrightBasic htree q]
  group

/-- The reverse-orientation recursive source lies one layer higher. -/
theorem
    children_decomposition_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (childrenSwapDecomposition factor left right
          hleftBasic hrightBasic htree) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [
    children_swap_decomposition
      factor left right hleftBasic hrightBasic htree q]
  exact
    list_reduction_series
      factor q

end HEWord
end TCTex
end Towers
