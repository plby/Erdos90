import Submission.Group.HallBasic.ExplicitCoordinateIdentities

/-!
# Explicit coordinates for outer brackets of reduced inner packets

Hall reduction of an inner tree gives a finite integer packet of indexed
basic Hall trees.  Bracketing that packet with one fixed right tree and then
reducing each resulting full outer bracket gives an explicit coordinate
packet in the total weight.  Bilinearity of the associated-graded bracket
shows that this packet is exactly the ordinary reduction coordinates of the
original outer bracket.

This is the coordinate-level counterpart of the classical Hall reduction
step: reduce the inner bracket first, then recurse on full outer brackets.
The emitted outer brackets retain the total weight, which is important for
later symbolic repeated-power recipes.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The total-weight coordinate packet obtained by reducing an inner tree and
then reducing every full outer bracket with one fixed right tree.
-/
noncomputable def innerOuterCoordinates
    (inner right : HallTree α) :
    BasicIndex (α := α) (inner.weight + right.weight) →₀ ℤ :=
  (basicReductionCoordinates inner).sum fun i coefficient =>
    coefficient •
      basicCoordinatesWeight
        (commutator (indexedBasicTree i) right) (by
          simp only [weight_commutator, indexed_tree_weight])

/--
Linear combination of the explicit outer coordinate packet is the
associated-graded bracket of the inner class with the fixed right class.
-/
theorem linear_combination_coordinates
    (inner right : HallTree α) :
    Finsupp.linearCombination ℤ
        (fun i : BasicIndex (α := α) (inner.weight + right.weight) =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i))
        (innerOuterCoordinates inner right) =
      (commutator inner right).freeLowerWeight rfl := by
  rw [innerOuterCoordinates]
  simp_rw [map_finsuppSum, map_smul,
    basic_coordinates_combination]
  let outer :=
    fun x =>
      TBluepr.lowerBracketClass
        (inner.weight - 1) (right.weight - 1)
        (inner.weight + right.weight - 1) (by
          have hinner := inner.weight_pos
          have hright := right.weight_pos
          omega)
        x (right.freeLowerWeight rfl)
  have hroot :
      (commutator inner right).freeLowerWeight rfl =
        outer (inner.freeLowerWeight rfl) := by
    dsimp only [outer]
    convert
      free_lower_weights
        inner right rfl rfl rfl using 1
  have hindexed :
      ∀ i : BasicIndex (α := α) inner.weight,
        (commutator (indexedBasicTree i) right).freeLowerWeight
            (by
              simp only [weight_commutator, indexed_tree_weight]) =
          outer
            ((indexedBasicTree i).freeLowerWeight
              (indexed_tree_weight i)) := by
    intro i
    dsimp only [outer]
    convert
      free_lower_weights
        (indexedBasicTree i) right (indexed_tree_weight i) rfl rfl using 1
  rw [hroot]
  simp_rw [hindexed]
  rw [← basic_coordinates_combination inner rfl]
  rw [Finsupp.linearCombination_apply]
  change
    (basicReductionCoordinates inner).sum
        (fun i coefficient =>
          coefficient •
            outer
              ((indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i))) =
      outer
        ((basicReductionCoordinates inner).sum
          (fun i coefficient =>
            coefficient •
              (indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i)))
  induction basicReductionCoordinates inner using Finsupp.induction with
  | zero =>
      simp [outer]
  | @single_add i coefficient coordinates hi hcoefficient ih =>
      simp [Finsupp.sum_add_index, outer, ih, add_smul,
        TBluepr.central_bracket_left,
        TBluepr.bracket_zsmul_left]

/--
Reducing the inner packet first and then every full outer bracket gives
literally the same total-weight coordinates as reducing the original outer
bracket directly.
-/
theorem coordinates_inner_outer
    (inner right : HallTree α) :
    basicCoordinatesWeight (commutator inner right) rfl =
      innerOuterCoordinates inner right := by
  apply
    (indexed_tree_layers
      (α := α) (r := inner.weight + right.weight)
      (by
        have hinner := inner.weight_pos
        omega)).finsuppLinearCombination_injective
  calc
    _ = (commutator inner right).freeLowerWeight rfl :=
      basic_coordinates_combination
        (commutator inner right) rfl
    _ = _ :=
      (linear_combination_coordinates inner right).symm

/--
Before expanding the full outer brackets into basic coordinates, the
inner-reduction coefficients already reconstruct the original outer class.
-/
theorem inner_reduction_sum
    (inner right : HallTree α) :
    (basicReductionCoordinates inner).sum
        (fun i coefficient =>
          coefficient •
            (commutator (indexedBasicTree i) right).freeLowerWeight
              (by
                simp only [weight_commutator, indexed_tree_weight])) =
      (commutator inner right).freeLowerWeight rfl := by
  rw [← linear_combination_coordinates inner right]
  rw [innerOuterCoordinates, map_finsuppSum]
  simp_rw [map_smul, basic_coordinates_combination]
  rfl

/-- Integer scaling distributes through the full outer-child coordinate packet. -/
theorem inner_reduction_smul
    (inner right : HallTree α)
    (z : ℤ) :
    (basicReductionCoordinates inner).sum
        (fun i coefficient =>
          (coefficient * z) •
            (commutator (indexedBasicTree i) right).freeLowerWeight
              (by
                simp only [weight_commutator, indexed_tree_weight])) =
      z • (commutator inner right).freeLowerWeight rfl := by
  rw [← inner_reduction_sum inner right, Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro i _hi
  rw [smul_smul, mul_comm]

end HallTree
end Submission
