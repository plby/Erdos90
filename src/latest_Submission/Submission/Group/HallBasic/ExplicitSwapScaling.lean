import Submission.Group.HallBasic.ExplicitCoordinateIdentities
import Submission.Group.HallBasic.ExplicitReductionScaling

/-!
# Exact scaled explicit reduction for reversed basic Hall brackets

If swapping the children of a Hall-tree bracket makes it basic, graded
skew-symmetry and Hall-basis uniqueness force the original explicit reduction
packet to be the corresponding singleton with coefficient `-1`.  Its scaled
compression product therefore evaluates exactly to the original reversed
bracket power.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/-- A product with one distinguished nonidentity term collapses to that term. -/
private theorem list_ite_nodup
    {ι G : Type*}
    [DecidableEq ι]
    [Monoid G]
    (L : List ι)
    (i : ι)
    (g : G)
    (hL : L.Nodup)
    (hi : i ∈ L) :
    (L.map fun j => if j = i then g else 1).prod = g := by
  induction L with
  | nil =>
      simp at hi
  | cons head tail ih =>
      simp only [List.nodup_cons] at hL
      rcases hL with ⟨hhead, htail⟩
      by_cases h : head = i
      · subst head
        have htailProd :
            (tail.map fun j => if j = i then g else 1).prod = 1 := by
          apply List.prod_eq_one
          intro x hx
          rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
          simp only [ite_eq_right_iff]
          intro hji
          subst j
          exact (hhead hj).elim
        simp [htailProd]
      · have hiTail : i ∈ tail := by
          rcases List.mem_cons.mp hi with hi | hi
          · exact False.elim (h hi.symm)
          · exact hi
        simpa [h] using ih htail hiTail

/--
The explicit reduction coordinates of a reversed basic bracket are a
singleton with coefficient `-1`.
-/
theorem coordinates_single_swap
    (u v : HallTree α)
    (hswapBasic : (commutator u v).IsBasic) :
    ∃ i : BasicIndex (α := α) (commutator v u).weight,
      basicReductionCoordinates (commutator v u) =
          Finsupp.single i (-1 : ℤ) ∧
        indexedBasicTree i = commutator u v := by
  obtain ⟨i, hi⟩ :=
    indexed_basic_tree
      (r := (commutator v u).weight) hswapBasic (by
        simp only [weight_commutator]
        exact Nat.add_comm _ _)
  refine ⟨i, ?_, hi⟩
  apply
    (indexed_tree_layers
      (α := α) (r := (commutator v u).weight)
      (commutator v u).weight_pos).finsuppLinearCombination_injective
  rw [reduction_coordinates_combination,
    Finsupp.linearCombination_single]
  simp only [neg_smul, one_smul]
  calc
    _ = -(commutator u v).freeLowerWeight (by
        simp only [weight_commutator]
        exact Nat.add_comm _ _) :=
      free_lower_swap v u
    _ = -(indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) := by
      exact
        congrArg Neg.neg
          (free_lower_congr hi
            (indexed_tree_weight i) (by
              simp only [weight_commutator]
              exact Nat.add_comm _ _)).symm

/--
Coordinatewise scaling of a reversed basic bracket's explicit packet is the
corresponding negative power of the basic orientation.
-/
theorem scaled_zpow_swap
    (u v : HallTree α)
    (hswapBasic : (commutator u v).IsBasic)
    (z : ℤ) :
    basicReductionScaled (commutator v u) z =
      (commutator u v).toCWord.eval FreeGroup.of ^ (-z) := by
  obtain ⟨i, hcoordinates, hi⟩ :=
    coordinates_single_swap
      u v hswapBasic
  unfold basicReductionScaled basicScaledTerm
  rw [hcoordinates]
  have hterm :
      ((Finset.univ.sort
          fun j k : BasicIndex (α := α) (commutator v u).weight =>
            j ≤ k).map
        fun j =>
          indexedTreeRep j ^
            (Finsupp.single i (-1 : ℤ) j * z)).prod =
        indexedTreeRep i ^ (-z) := by
    rw [show
        ((Finset.univ.sort
            fun j k : BasicIndex (α := α) (commutator v u).weight =>
              j ≤ k).map
          fun j =>
            indexedTreeRep j ^
              (Finsupp.single i (-1 : ℤ) j * z)).prod =
          ((Finset.univ.sort
              fun j k : BasicIndex (α := α) (commutator v u).weight =>
                j ≤ k).map
            fun j =>
              if j = i then indexedTreeRep i ^ (-z)
                else 1).prod by
          congr 1
          apply List.map_congr_left
          intro j _hj
          by_cases hji : j = i
          · subst j
            rw [Finsupp.single_eq_same, neg_one_mul, if_pos rfl]
          · rw [Finsupp.single_eq_of_ne hji, zero_mul, zpow_zero,
              if_neg hji]]
    exact
      list_ite_nodup
        (Finset.univ.sort
          fun j k : BasicIndex (α := α) (commutator v u).weight =>
            j ≤ k)
        i (indexedTreeRep i ^ (-z))
        (Finset.sort_nodup _ _)
        ((Finset.mem_sort _).2 (Finset.mem_univ i))
  calc
    _ = ((indexedTreeRep i ^ (-z) :
        Subgroup.lowerCentralSeries (FreeGroup α) ((commutator v u).weight - 1)) :
          FreeGroup α) :=
      congrArg Subtype.val hterm
    _ = (indexedBasicTree i).toCWord.eval FreeGroup.of ^ (-z) := by
      exact
        congrArg (fun x : FreeGroup α => x ^ (-z))
          (coe_indexed_rep i)
    _ = (commutator u v).toCWord.eval FreeGroup.of ^ (-z) := by
      rw [hi]

/--
Coordinatewise scaling of a reversed basic bracket's explicit packet is
literally the corresponding reversed bracket power.
-/
theorem basic_scaled_swap
    (u v : HallTree α)
    (hswapBasic : (commutator u v).IsBasic)
    (z : ℤ) :
    basicReductionScaled (commutator v u) z =
      (commutator v u).toCWord.eval FreeGroup.of ^ z := by
  rw [scaled_zpow_swap
    u v hswapBasic z]
  rw [zpow_neg, ← inv_zpow]
  exact
    congrArg (fun x : FreeGroup α => x ^ z) (commutatorElement_inv _ _)

end HallTree
end Submission
