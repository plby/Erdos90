import Submission.Group.HallBasic.ExplicitCoordinatePackets

/-!
# Exact scaled coordinate packets for skew-symmetric Hall brackets

Swapping the children of a Hall-tree bracket negates its explicit reduction
coordinates.  Negating the external scaling exponent compensates for that
sign, so the two canonically ordered coordinate packets agree literally.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/-- Negating coordinates is the same as negating the external scale. -/
theorem coordinate_scaled_neg
    {r : ℕ}
    (coordinates : BasicIndex (α := α) r →₀ ℤ)
    (z : ℤ) :
    coordinateScaledProduct (-coordinates) z =
      coordinateScaledProduct coordinates (-z) := by
  simp [coordinateScaledProduct, coordinateScaledTerm]

/--
The scaled Hall-reduction packet of a bracket agrees exactly with the packet
of its reversed bracket after negating the scaling exponent.
-/
theorem scaled_swap_neg
    (u v : HallTree α)
    (z : ℤ) :
    basicReductionScaled (commutator u v) z =
      basicReductionScaled (commutator v u) (-z) := by
  have hweight :
      (commutator v u).weight = (commutator u v).weight := by
    simp only [weight_commutator]
    omega
  rw [← coordinate_scaled_coordinates
      (commutator u v) rfl,
    ← coordinate_scaled_coordinates
      (commutator v u) hweight,
    basic_coordinates_swap,
    coordinate_scaled_neg]

end HallTree
end Submission
