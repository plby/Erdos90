import Submission.Group.NilpotentProducts.OddClassThree
import Submission.Group.NilpotentProducts.AdmissibleOrders
import Submission.Group.HallBasic.Word

/-!
# Orders of Hall-tree commutators in class three

For a Hall tree, recursively take the gcd of the prescribed orders of its
leaves.  In a class-three group, evaluation of the tree has order dividing
that recursive gcd whenever every leaf order is odd or zero.
-/

namespace Struik
namespace P1960

open Submission
open Submission.HallTree
open Submission.Edmonton
open scoped commutatorElement

universe u v

/-- The recursive gcd of the orders attached to the leaves of a Hall tree. -/
def hallTreeOrder {ι : Type u} (order : ι → ℕ) :
    HallTree ι → ℕ
  | .atom i => order i
  | .commutator left right =>
      Nat.gcd (hallTreeOrder order left) (hallTreeOrder order right)

/-- A generator occurs as a leaf of a Hall tree. -/
def hallTreeUses {ι : Type u} (a : ι) :
    HallTree ι → Prop
  | .atom b => b = a
  | .commutator left right =>
      hallTreeUses a left ∨ hallTreeUses a right

noncomputable instance treeUsesDecidable
    {ι : Type u}
    (a : ι) (tree : HallTree ι) :
    Decidable (hallTreeUses a tree) :=
  Classical.propDecidable _

/-- The recursive Hall order divides the prescribed order of every leaf
that occurs in the tree. -/
theorem tree_dvd_uses
    {ι : Type u} (order : ι → ℕ) (a : ι) :
    ∀ {tree : HallTree ι}, hallTreeUses a tree →
      hallTreeOrder order tree ∣ order a
  | .atom b, huses => by
      subst b
      simp [hallTreeOrder]
  | .commutator left right, huses => by
      rcases huses with hleft | hright
      · exact (Nat.gcd_dvd_left _ _).trans
          (tree_dvd_uses order a hleft)
      · exact (Nat.gcd_dvd_right _ _).trans
          (tree_dvd_uses order a hright)

/-- If an element is annihilated by the prescribed order of every leaf used
by a Hall tree, it is annihilated by the recursive Hall order. -/
theorem tree_order_uses
    {ι : Type u} {G : Type v} [Group G]
    (order : ι → ℕ) (x : G) :
    ∀ tree : HallTree ι,
      (∀ a, hallTreeUses a tree → x ^ order a = 1) →
        x ^ hallTreeOrder order tree = 1
  | .atom a, hleaf => hleaf a (by simp [hallTreeUses])
  | .commutator left right, hleaf =>
      pow_gcd_eq_one.mpr
        ⟨tree_order_uses order x left
            (fun a huses => hleaf a (Or.inl huses)),
          tree_order_uses order x right
            (fun a huses => hleaf a (Or.inr huses))⟩

/-- Recursive gcds of admissible orders remain admissible. -/
theorem tree_order_admissible
    {ι : Type u} (order : ι → ℕ)
    (horder : ∀ i, AOrd (order i))
    (tree : HallTree ι) :
    AOrd (hallTreeOrder order tree) := by
  induction tree with
  | atom i => exact horder i
  | commutator left right ihLeft ihRight =>
      exact ihLeft.gcd ihRight

/-- Recursive gcds are positive when every prescribed leaf order is
positive. -/
theorem tree_order_pos
    {ι : Type u} (order : ι → ℕ)
    (horder : ∀ i, 0 < order i)
    (tree : HallTree ι) :
    0 < hallTreeOrder order tree := by
  induction tree with
  | atom i => exact horder i
  | commutator left right ihLeft ihRight =>
      exact Nat.gcd_pos_of_pos_left _ ihLeft

/-- Every Hall-tree commutator inherits the recursive gcd of the specified
leaf orders in a group with trivial fourth lower-central term. -/
theorem tree_order_three
    {ι : Type u} {G : Type v} [Group G]
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (order : ι → ℕ)
    (horder : ∀ i, AOrd (order i))
    (value : ι → G)
    (hvalue : ∀ i, value i ^ order i = 1)
    (tree : HallTree ι) :
    tree.toCWord.eval value ^ hallTreeOrder order tree = 1 := by
  induction tree with
  | atom i =>
      simpa [hallTreeOrder, HallTree.toCWord] using hvalue i
  | commutator left right ihLeft ihRight =>
      simp only [HallTree.toCWord,
        CWord.eval_commutator, hallTreeOrder]
      exact
        element_gcd_odd
          hG4
          (tree_order_admissible order horder left)
          (tree_order_admissible order horder right)
          ihLeft ihRight

end P1960
end Struik
