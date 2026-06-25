import Submission.Group.HallBasic.LowWeightCoordinates
import Submission.Group.HallBasic.StandardSequence

/-!
# Exact explicit reduction coordinates for basic Hall trees

The foliage parser for ordered Hall standard sequences supplies all-weight
PBW uniqueness.  Consequently the spanning-based explicit reducer chooses the
singleton Kronecker packet whenever its input Hall tree is already basic.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The completed foliage parser supplies linear independence of indexed basic
Hall classes in every positive weight.
-/
theorem indexed_tree_layers
    {r : ℕ}
    (hr : 0 < r) :
    LinearIndependent ℤ
      (fun i : BasicIndex (α := α) r =>
        (indexedBasicTree i).freeLowerWeight
          (indexed_tree_weight i)) := by
  let P : HPUniq (α := α) ℤ :=
    (foliageFactorizationInput (α := α)).pbwUniquenessInt
  exact
    P.indeba_fregr_laywe hr

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
Explicit reduction of a basic Hall tree is the singleton Kronecker packet at
an index representing that tree.
-/
theorem basic_coordinates_single
    (w : HallTree α)
    (hwBasic : w.IsBasic) :
    ∃ i : BasicIndex (α := α) w.weight,
      basicReductionCoordinates w = Finsupp.single i 1 ∧
        indexedBasicTree i = w := by
  obtain ⟨i, hi⟩ := indexed_basic_tree hwBasic rfl
  refine ⟨i, ?_, hi⟩
  have hLI :
      LinearIndependent ℤ
        (fun j : BasicIndex (α := α) w.weight =>
          (indexedBasicTree j).freeLowerWeight
            (indexed_tree_weight j)) :=
    indexed_tree_layers
      (α := α) w.weight_pos
  apply hLI.finsuppLinearCombination_injective
  rw [reduction_coordinates_combination]
  rw [Finsupp.linearCombination_single, one_smul]
  change
    w.freeLowerWeight rfl =
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i)
  exact
    (free_lower_congr hi
      (indexed_tree_weight i) rfl).symm

/--
Explicit reduction of a basic Hall tree is literally its original free-group
Hall value.
-/
theorem basic_reduction_eval
    (w : HallTree α)
    (hwBasic : w.IsBasic) :
    basicReductionProduct w =
      w.toCWord.eval FreeGroup.of := by
  obtain ⟨i, hcoordinates, hi⟩ :=
    basic_coordinates_single w hwBasic
  unfold basicReductionProduct basicReductionTerm
  rw [hcoordinates]
  have hterm :
      ((Finset.univ.sort
          fun j k : BasicIndex (α := α) w.weight => j ≤ k).map
        fun j =>
          indexedTreeRep j ^
            Finsupp.single i (1 : ℤ) j).prod =
        indexedTreeRep i := by
    rw [show
        ((Finset.univ.sort
            fun j k : BasicIndex (α := α) w.weight => j ≤ k).map
          fun j =>
            indexedTreeRep j ^
              Finsupp.single i (1 : ℤ) j).prod =
          ((Finset.univ.sort
              fun j k : BasicIndex (α := α) w.weight => j ≤ k).map
            fun j =>
              if j = i then indexedTreeRep i
                else 1).prod by
          congr 1
          apply List.map_congr_left
          intro j _hj
          by_cases hji : j = i
          · subst j
            simp
          · simp [hji]]
    exact
      list_ite_nodup
        (Finset.univ.sort
          fun j k : BasicIndex (α := α) w.weight => j ≤ k)
        i (indexedTreeRep i)
        (Finset.sort_nodup _ _) (by simp)
  calc
    _ = (indexedTreeRep i : FreeGroup α) :=
      congrArg Subtype.val hterm
    _ = (indexedBasicTree i).toCWord.eval FreeGroup.of := by
      rw [coe_indexed_rep]
    _ = w.toCWord.eval FreeGroup.of := by
      rw [hi]

end HallTree
end Submission
