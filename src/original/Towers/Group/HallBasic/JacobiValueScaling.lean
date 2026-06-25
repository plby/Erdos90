import Towers.Group.HallBasic.ExplicitReductionCoordinates

/-!
# Scaled Jacobi residuals for Hall-tree values

The associated-graded Jacobi rewrite compares a nested Hall-tree commutator
with two permuted descendants.  This file lifts that equality through an
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
Reindexing a Hall-tree lower-central representative does not change its
ambient free-group value.
-/
@[simp]
theorem coe_rep_weight
    {r : ℕ}
    (tree : HallTree α)
    (hweight : tree.weight = r) :
    (freeRepWeight tree hweight : FreeGroup α) =
      tree.toCWord.eval FreeGroup.of := by
  unfold freeRepWeight
  exact
    coe_cast_family
      (fun k => Subgroup.lowerCentralSeries (FreeGroup α) (k - 1))
      hweight tree.freeCentralRep

/--
The powered Jacobi value residual of three Hall trees lies in the next
lower-central term, represented inside their common source layer.
-/
theorem rep_zpow_next
    (u v w : HallTree α)
    (z : ℤ) :
    let r : ℕ := (commutator (commutator u v) w).weight
    let original : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
      freeRepWeight
        (commutator (commutator u v) w) rfl
    let first : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
      freeRepWeight
        (commutator (commutator u w) v) (by
          dsimp only [r]
          simp only [weight_commutator]
          omega)
    let second : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
      freeRepWeight
        (commutator (commutator v w) u) (by
          dsimp only [r]
          simp only [weight_commutator]
          omega)
    (original ^ z)⁻¹ * (first ^ z * second ^ (-z)) ∈
      (Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)) := by
  dsimp only
  apply (QuotientGroup.eq_one_iff
    (N :=
      (Subgroup.lowerCentralSeries (FreeGroup α)
          (((commutator (commutator u v) w).weight - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α)
          ((commutator (commutator u v) w).weight - 1)))
    (((freeRepWeight
          (commutator (commutator u v) w) rfl) ^ z)⁻¹ *
      ((freeRepWeight
          (commutator (commutator u w) v) (by
            simp only [weight_commutator]
            omega)) ^ z *
        (freeRepWeight
          (commutator (commutator v w) u) (by
            simp only [weight_commutator]
            omega)) ^ (-z)))).mp
  apply Additive.ofMul.injective
  change
    lowerCentralClass
        ((commutator (commutator u v) w).weight - 1)
        (((freeRepWeight
            (commutator (commutator u v) w) rfl) ^ z)⁻¹ *
          ((freeRepWeight
              (commutator (commutator u w) v) (by
                simp only [weight_commutator]
                omega)) ^ z *
            (freeRepWeight
              (commutator (commutator v w) u) (by
                simp only [weight_commutator]
                omega)) ^ (-z))) =
      0
  rw [lower_class_mul, lower_class_inv,
    lower_central_zpow, lower_class_mul,
    lower_central_zpow, lower_central_zpow,
    lower_rep_weight,
    lower_rep_weight,
    lower_rep_weight,
    lower_jacobi_rewrite]
  module

/--
Ambient free-group form of the powered Jacobi value residual theorem.
-/
theorem jacobi_zpow_series
    (u v w : HallTree α)
    (z : ℤ) :
    ((commutator (commutator u v) w).toCWord.eval FreeGroup.of ^ z)⁻¹ *
        ((commutator (commutator u w) v).toCWord.eval FreeGroup.of ^ z *
          (commutator (commutator v w) u).toCWord.eval FreeGroup.of ^
            (-z)) ∈
      Subgroup.lowerCentralSeries (FreeGroup α)
        (commutator (commutator u v) w).weight := by
  let r : ℕ := (commutator (commutator u v) w).weight
  let original : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
    freeRepWeight
      (commutator (commutator u v) w) rfl
  let first : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
    freeRepWeight
      (commutator (commutator u w) v) (by
        dsimp only [r]
        simp only [weight_commutator]
        omega)
  let second : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
    freeRepWeight
      (commutator (commutator v w) u) (by
        dsimp only [r]
        simp only [weight_commutator]
        omega)
  have hnext :
      (original ^ z)⁻¹ * (first ^ z * second ^ (-z)) ∈
        (Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1)).subgroupOf
          (Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)) := by
    simpa only [r, original, first, second] using
      rep_zpow_next u v w z
  have hambient :
      (((original ^ z)⁻¹ * (first ^ z * second ^ (-z)) :
          Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)) :
        FreeGroup α) ∈
      Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1) :=
    hnext
  change
    (((original : FreeGroup α) ^ z)⁻¹ *
      ((first : FreeGroup α) ^ z * (second : FreeGroup α) ^ (-z))) ∈
        Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1) at hambient
  simpa only [original, first, second,
    coe_rep_weight, r,
    Nat.sub_add_cancel (commutator (commutator u v) w).weight_pos] using
      hambient

end HallTree
end Towers
