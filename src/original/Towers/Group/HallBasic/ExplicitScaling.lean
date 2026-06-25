import Towers.Group.HallBasic.ExplicitCoordinates
import Towers.Group.HallBasic.ExplicitReductionScaling

/-!
# Exact scaled explicit reductions for basic Hall trees

For any basic Hall tree, all-weight PBW uniqueness makes its extracted
reduction packet a singleton.  Coordinatewise scaling therefore agrees
literally with taking an integer power of the original Hall value.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
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
Coordinatewise scaling of a basic tree's explicit reduction packet is
literally the corresponding integer power of the Hall-tree value.
-/
theorem reduction_scaled_zpow
    (w : HallTree α)
    (hwBasic : w.IsBasic)
    (z : ℤ) :
    basicReductionScaled w z =
      w.toCWord.eval FreeGroup.of ^ z := by
  obtain ⟨i, hcoordinates, hi⟩ :=
    basic_coordinates_single w hwBasic
  unfold basicReductionScaled basicScaledTerm
  rw [hcoordinates]
  have hterm :
      ((Finset.univ.sort
          fun j k : BasicIndex (α := α) w.weight => j ≤ k).map
        fun j =>
          indexedTreeRep j ^
            (Finsupp.single i (1 : ℤ) j * z)).prod =
        indexedTreeRep i ^ z := by
    rw [show
        ((Finset.univ.sort
            fun j k : BasicIndex (α := α) w.weight => j ≤ k).map
          fun j =>
            indexedTreeRep j ^
              (Finsupp.single i (1 : ℤ) j * z)).prod =
          ((Finset.univ.sort
              fun j k : BasicIndex (α := α) w.weight => j ≤ k).map
            fun j =>
              if j = i then indexedTreeRep i ^ z
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
        i (indexedTreeRep i ^ z)
        (Finset.sort_nodup _ _) (by simp)
  calc
    _ = ((indexedTreeRep i ^ z :
        Subgroup.lowerCentralSeries (FreeGroup α) (w.weight - 1)) : FreeGroup α) :=
      congrArg Subtype.val hterm
    _ = (indexedBasicTree i).toCWord.eval FreeGroup.of ^ z := by
      exact
        congrArg (fun x : FreeGroup α => x ^ z)
          (coe_indexed_rep i)
    _ = w.toCWord.eval FreeGroup.of ^ z := by
      rw [hi]

end HallTree
end Towers
