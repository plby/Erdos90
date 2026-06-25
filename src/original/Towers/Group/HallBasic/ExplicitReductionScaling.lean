import Towers.Group.HallBasic.ExplicitReductionCoordinates

/-!
# Scaling explicit Hall-tree reductions

The explicit Hall-tree reduction packet is an ordered product of powers of
basic Hall representatives.  Raising that product to an integer exponent is
not literally coordinatewise scaling in the free group.  It is
coordinatewise scaling in the associated-graded layer, so the discrepancy
lies in the next lower-central term.

This file records that precise residual statement.  It is intentionally not
imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The ordered basic-tree reduction packet with every extracted coordinate
scaled by an integer.
-/
noncomputable def basicScaledTerm
    (w : HallTree α)
    (z : ℤ) :
    Subgroup.lowerCentralSeries (FreeGroup α) (w.weight - 1) :=
  ((Finset.univ.sort
      fun i j : BasicIndex (α := α) w.weight => i ≤ j).map
    fun i =>
      indexedTreeRep i ^
        (basicReductionCoordinates w i * z)).prod

/-- Integer scaling distributes over products in a commutative group. -/
private theorem list_zpow_mul
    {G β : Type*}
    [CommGroup G]
    (g : β → G)
    (e : β → ℤ)
    (L : List β)
    (z : ℤ) :
    (L.map fun i => g i ^ (e i * z)).prod =
      (L.map fun i => g i ^ e i).prod ^ z := by
  induction L with
  | nil =>
      simp
  | cons i L ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih, zpow_mul, mul_zpow]

/--
The scaled packet has the same associated-graded class as the integer power
of the original packet.
-/
theorem lower_scaled_term
    (w : HallTree α)
    (z : ℤ) :
    TBluepr.lowerClassHom (w.weight - 1)
        (basicScaledTerm w z) =
      TBluepr.lowerClassHom (w.weight - 1)
        (basicReductionTerm w ^ z) := by
  rw [basicScaledTerm, basicReductionTerm,
    map_list_prod, map_zpow, map_list_prod, List.map_map, List.map_map]
  simpa only [Function.comp_apply, map_zpow] using
    list_zpow_mul
      (fun i : BasicIndex (α := α) w.weight =>
        TBluepr.lowerClassHom (w.weight - 1)
          (indexedTreeRep i))
      (basicReductionCoordinates w)
      (Finset.univ.sort fun i j : BasicIndex (α := α) w.weight => i ≤ j)
      z

/--
The coordinatewise-scaled packet differs from the powered reduction packet
only in the next lower-central term.
-/
theorem scaled_inv_next
    (w : HallTree α)
    (z : ℤ) :
    (basicScaledTerm w z)⁻¹ *
        basicReductionTerm w ^ z ∈
      (Subgroup.lowerCentralSeries (FreeGroup α) ((w.weight - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) (w.weight - 1)) := by
  apply (QuotientGroup.eq_one_iff
    (N :=
      (Subgroup.lowerCentralSeries (FreeGroup α) ((w.weight - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) (w.weight - 1)))
    ((basicScaledTerm w z)⁻¹ *
      basicReductionTerm w ^ z)).mp
  change
    TBluepr.lowerClassHom (w.weight - 1)
        ((basicScaledTerm w z)⁻¹ *
          basicReductionTerm w ^ z) =
      1
  rw [map_mul, map_inv,
    lower_scaled_term,
    inv_mul_cancel]

/-- Ambient free-group value of the coordinatewise-scaled reduction packet. -/
noncomputable def basicReductionScaled
    (w : HallTree α)
    (z : ℤ) :
    FreeGroup α :=
  basicScaledTerm w z

/--
Ambient-group form of the scaled-packet residual theorem.
-/
theorem scaled_zpow_series
    (w : HallTree α)
    (z : ℤ) :
    (basicReductionScaled w z)⁻¹ *
        basicReductionProduct w ^ z ∈
      Subgroup.lowerCentralSeries (FreeGroup α) w.weight := by
  simpa [basicReductionScaled, basicReductionProduct,
    Nat.sub_add_cancel w.weight_pos] using
      scaled_inv_next w z

end HallTree
end Towers
