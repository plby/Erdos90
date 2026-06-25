import Towers.Group.HallBasic.ExplicitScaling

/-!
# Vanishing explicit reduction coordinates

All-weight Hall-basis independence makes the spanning-based coordinate packet
unique.  In particular, a Hall tree with zero associated-graded class has the
zero packet.  Self-commutators are the first operationally useful case.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/-- A zero associated-graded Hall-tree class has the zero reduction packet. -/
theorem basic_reduction_coordinates
    (w : HallTree α)
    (hzero : w.freeCentralLayer = 0) :
    basicReductionCoordinates w = 0 := by
  have hLI :
      LinearIndependent ℤ
        (fun i : BasicIndex (α := α) w.weight =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) :=
    indexed_tree_layers
      (α := α) w.weight_pos
  apply hLI.finsuppLinearCombination_injective
  rw [reduction_coordinates_combination]
  simpa only [map_zero] using hzero

/-- The explicit reduction packet of a self-commutator is zero. -/
theorem reduction_coordinates_self
    (w : HallTree α) :
    basicReductionCoordinates (commutator w w) = 0 := by
  apply
    basic_reduction_coordinates
  simpa only [freeLowerWeight] using
    free_lower_self w

/-- Scaling a zero coordinate packet gives the identity compression product. -/
theorem basic_scaled_coordinates
    (w : HallTree α)
    (z : ℤ)
    (hzero : basicReductionCoordinates w = 0) :
    basicReductionScaled w z = 1 := by
  simp [basicReductionScaled, basicScaledTerm,
    hzero]

/-- Every scaled explicit reduction of a self-commutator is trivial. -/
theorem basic_scaled_self
    (w : HallTree α)
    (z : ℤ) :
    basicReductionScaled (commutator w w) z = 1 :=
  basic_scaled_coordinates
    (commutator w w) z (reduction_coordinates_self w)

end HallTree
end Towers
