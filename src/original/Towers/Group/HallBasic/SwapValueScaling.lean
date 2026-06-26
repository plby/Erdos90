import Towers.Group.HallBasic.JacobiValueScaling

/-!
# Scaled skew-symmetry residuals for Hall-tree values

Associated-graded skew-symmetry compares a Hall-tree bracket with the
negative of its reversed bracket.  This file lifts that equality through an
arbitrary integer power: the corresponding value residual lies one
lower-central stratum higher.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/-- Integer powers scale lower-central associated-graded classes. -/
private theorem lower_central_zpow
    {G : Type*} [Group G]
    (n : ℕ)
    (x : Subgroup.lowerCentralSeries G n)
    (z : ℤ) :
    lowerCentralClass n (x ^ z) = z • lowerCentralClass n x := by
  change
    Additive.ofMul (lowerClassHom n (x ^ z)) =
      z • Additive.ofMul (lowerClassHom n x)
  rw [map_zpow]
  rfl

/--
The powered skew-symmetry residual of two Hall trees lies in the next
lower-central term, represented inside their common source layer.
-/
theorem rep_swap_next
    (u v : HallTree α)
    (z : ℤ) :
    let r : ℕ := (commutator u v).weight
    let original : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
      freeRepWeight (commutator u v) rfl
    let reversed : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
      freeRepWeight (commutator v u) (by
        dsimp only [r]
        simp only [weight_commutator]
        omega)
    (original ^ z)⁻¹ * reversed ^ (-z) ∈
      (Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)) := by
  dsimp only
  apply (QuotientGroup.eq_one_iff
    (N :=
      (Subgroup.lowerCentralSeries (FreeGroup α)
          (((commutator u v).weight - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α)
          ((commutator u v).weight - 1)))
    (((freeRepWeight (commutator u v) rfl) ^ z)⁻¹ *
      (freeRepWeight (commutator v u) (by
        simp only [weight_commutator]
        omega)) ^ (-z))).mp
  apply Additive.ofMul.injective
  change
    lowerCentralClass ((commutator u v).weight - 1)
        (((freeRepWeight (commutator u v) rfl) ^ z)⁻¹ *
          (freeRepWeight (commutator v u) (by
            simp only [weight_commutator]
            omega)) ^ (-z)) =
      0
  rw [lower_class_mul, lower_class_inv,
    lower_central_zpow, lower_central_zpow,
    lower_rep_weight,
    lower_rep_weight,
    free_lower_swap]
  module

/--
Ambient free-group form of the powered skew-symmetry residual theorem.
-/
theorem swap_zpow_series
    (u v : HallTree α)
    (z : ℤ) :
    ((commutator u v).toCWord.eval FreeGroup.of ^ z)⁻¹ *
        (commutator v u).toCWord.eval FreeGroup.of ^ (-z) ∈
      Subgroup.lowerCentralSeries (FreeGroup α) (commutator u v).weight := by
  let r : ℕ := (commutator u v).weight
  let original : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
    freeRepWeight (commutator u v) rfl
  let reversed : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
    freeRepWeight (commutator v u) (by
      dsimp only [r]
      simp only [weight_commutator]
      omega)
  have hnext :
      (original ^ z)⁻¹ * reversed ^ (-z) ∈
        (Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1)).subgroupOf
          (Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)) := by
    simpa only [r, original, reversed] using
      rep_swap_next u v z
  have hambient :
      (((original ^ z)⁻¹ * reversed ^ (-z) :
          Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)) :
        FreeGroup α) ∈
      Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1) :=
    hnext
  change
    (((original : FreeGroup α) ^ z)⁻¹ *
      (reversed : FreeGroup α) ^ (-z)) ∈
        Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1) at hambient
  simpa only [original, reversed,
    coe_rep_weight, r,
    Nat.sub_add_cancel (commutator u v).weight_pos] using hambient

end HallTree
end Towers
