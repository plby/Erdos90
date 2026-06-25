import Submission.Group.HallBasic.ExplicitCoordinates

/-!
# Exact identities for explicit Hall-tree reduction coordinates

The spanning-based explicit reducer chooses coordinates in the indexed Hall
basis.  All-weight PBW independence makes those coordinates unique.  This
file records the exact coordinate identities induced by the graded
skew-symmetry, self-bracket, and Jacobi relations.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
Reindex the explicit reduction coordinates of a Hall tree into an explicitly
chosen equal weight.
-/
noncomputable def basicCoordinatesWeight
    (w : HallTree α)
    {r : ℕ}
    (hweight : w.weight = r) :
    BasicIndex (α := α) r →₀ ℤ :=
  cast
    (congrArg (fun s => BasicIndex (α := α) s →₀ ℤ) hweight)
    (basicReductionCoordinates w)

/-- Reindexed explicit coordinates still reconstruct the Hall-tree class. -/
theorem basic_coordinates_combination
    (w : HallTree α)
    {r : ℕ}
    (hweight : w.weight = r) :
    Finsupp.linearCombination ℤ
        (fun i : BasicIndex (α := α) r =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i))
        (basicCoordinatesWeight w hweight) =
      w.freeLowerWeight hweight := by
  subst r
  simpa [basicCoordinatesWeight] using
    reduction_coordinates_combination w

/-- Swapping the children of a Hall-tree bracket negates its explicit coordinates. -/
theorem basic_coordinates_swap
    (u v : HallTree α)
    {r : ℕ}
    (hweight : (commutator u v).weight = r) :
    basicCoordinatesWeight (commutator u v) hweight =
      -basicCoordinatesWeight (commutator v u) (by
        simp only [weight_commutator] at hweight ⊢
        omega) := by
  apply
    (indexed_tree_layers
      (α := α) (r := r)
      (by
        have hu := u.weight_pos
        have hv := v.weight_pos
        simp only [weight_commutator] at hweight
        omega)).finsuppLinearCombination_injective
  rw [basic_coordinates_combination, map_neg,
    basic_coordinates_combination]
  exact free_commutator_swap u v hweight

/-- A Hall-tree self-bracket has zero explicit coordinates. -/
theorem basic_coordinates_self
    (u : HallTree α)
    {r : ℕ}
    (hweight : (commutator u u).weight = r) :
    basicCoordinatesWeight (commutator u u) hweight = 0 := by
  apply
    (indexed_tree_layers
      (α := α) (r := r)
      (by
        have hu := u.weight_pos
        simp only [weight_commutator] at hweight
        omega)).finsuppLinearCombination_injective
  rw [basic_coordinates_combination, map_zero]
  exact free_commutator_self u hweight

/--
The Jacobi rewrite of a left-normed Hall-tree triple is exact on explicit
reduction coordinates.
-/
theorem coordinates_jacobi_rewrite
    (u v w : HallTree α)
    {r : ℕ}
    (hweight : (commutator (commutator u v) w).weight = r) :
    basicCoordinatesWeight (commutator (commutator u v) w)
        hweight =
      basicCoordinatesWeight (commutator (commutator u w) v) (by
          simp only [weight_commutator] at hweight ⊢
          omega) -
        basicCoordinatesWeight (commutator (commutator v w) u) (by
          simp only [weight_commutator] at hweight ⊢
          omega) := by
  apply
    (indexed_tree_layers
      (α := α) (r := r)
      (by
        have hu := u.weight_pos
        have hv := v.weight_pos
        have hw := w.weight_pos
        simp only [weight_commutator] at hweight
        omega)).finsuppLinearCombination_injective
  rw [basic_coordinates_combination, map_sub,
    basic_coordinates_combination,
    basic_coordinates_combination]
  exact
    free_jacobi_rewrite
      u v w hweight

end HallTree
end Submission
