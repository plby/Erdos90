import Towers.Group.NilpotentProducts.LeafPowering
import Towers.Group.NilpotentProducts.HallTrees

/-!
# Orders of commutators in the last surviving weight

If `γ_(r+1)` is trivial, changing one leaf occurrence in a weight-`r`
commutator by an `m`th power changes the value by its `m`th power only.
Applying this separately to every leaf occurrence and combining the resulting
annihilating exponents by gcd proves the top-weight case of Struik's Lemma 1.
-/

namespace Struik
namespace P1960

open Towers
open Towers.HallTree

universe u v

namespace HallTree

private theorem tree_leaf_occurrences
    {α : Type u} {G : Type v} [Group G]
    (order : α → ℕ) (x : G) :
    ∀ tree : HallTree α,
      (∀ leaf : LOccur tree, x ^ order leaf.label = 1) →
        x ^ hallTreeOrder order tree = 1
  | .atom a, hleaf => hleaf (.atom a)
  | .commutator left right, hleaf =>
      pow_gcd_eq_one.mpr
        ⟨tree_leaf_occurrences order x left
            (fun leaf => hleaf (.left leaf)),
          tree_leaf_occurrences order x right
            (fun leaf => hleaf (.right leaf))⟩

/-- A weight-`r` Hall-tree commutator has order dividing the recursive gcd
of its leaf orders whenever the next lower-central term `γ_(r+1)` is
trivial. -/
theorem tree_top_weight
    {α : Type u} {G : Type v} [Group G]
    (order : α → ℕ) (value : α → G)
    (hvalue : ∀ a, value a ^ order a = 1)
    (tree : HallTree α)
    (hnext : Subgroup.lowerCentralSeries G tree.weight = ⊥) :
    tree.toCWord.eval value ^ hallTreeOrder order tree = 1 := by
  apply tree_leaf_occurrences order
  intro leaf
  have herror :=
    leaf_occurrence_series
      value tree leaf (order leaf.label)
  rw [hnext] at herror
  have hscaled :
      leafOccurrencePow value (order leaf.label) tree leaf = 1 :=
    eval_leaf_occurrence
      value (order leaf.label) leaf (hvalue leaf.label)
  rw [hscaled, one_mul] at herror
  simpa using herror

end HallTree

end P1960
end Struik
