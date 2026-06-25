import Submission.Group.HallBasic.ExplicitReductionCoordinates

/-!
# Exact explicit Hall-tree reduction coordinates in low weights

The spanning-based Hall-tree reducer chooses one finite coordinate packet for
every tree.  In weights one through three, the indexed basic Hall classes are
already known to be linearly independent.  Consequently the chosen packet of
an indexed basic tree is exactly its singleton Kronecker packet.

This file is intentionally not imported by the existing collection proof.
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

/-- Reindexing a subgroup-family element does not change its ambient value. -/
private theorem coe_cast_family
    {G ι : Type*}
    [Group G]
    (S : ι → Subgroup G)
    {i j : ι}
    (h : i = j)
    (x : S i) :
    ((cast (congrArg (fun k => ↥(S k)) h) x : S j) : G) = x := by
  subst j
  rfl

/--
In every verified positive weight through three, explicit reduction of a
basic Hall tree is the singleton Kronecker packet at an index representing
that tree.
-/
theorem coordinates_single_three
    (w : HallTree α)
    (hwBasic : w.IsBasic)
    (hw : w.weight ≤ 3) :
    ∃ i : BasicIndex (α := α) w.weight,
      basicReductionCoordinates w = Finsupp.single i 1 ∧
        indexedBasicTree i = w := by
  obtain ⟨i, hi⟩ := indexed_basic_tree hwBasic rfl
  refine ⟨i, ?_, hi⟩
  apply
    (indexed_layers_independent
      (α := α) w.weight_pos hw).finsuppLinearCombination_injective
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
The reindexed lower-central representative of a basic index has its expected
ambient free-group value.
-/
@[simp]
theorem coe_indexed_rep
    {r : ℕ}
    (i : BasicIndex (α := α) r) :
    (indexedTreeRep i : FreeGroup α) =
      (indexedBasicTree i).toCWord.eval FreeGroup.of := by
  unfold indexedTreeRep
  unfold freeRepWeight
  exact
    coe_cast_family
      (fun k => Subgroup.lowerCentralSeries (FreeGroup α) (k - 1))
      (indexed_tree_weight i)
      (indexedBasicTree i).freeCentralRep

/--
In weights through three, explicit reduction of a basic Hall tree is
literally the original free-group Hall value, not merely congruent to it in
the associated-graded layer.
-/
theorem basic_reduction_three
    (w : HallTree α)
    (hwBasic : w.IsBasic)
    (hw : w.weight ≤ 3) :
    basicReductionProduct w =
      w.toCWord.eval FreeGroup.of := by
  obtain ⟨i, hcoordinates, hi⟩ :=
    coordinates_single_three
      w hwBasic hw
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
