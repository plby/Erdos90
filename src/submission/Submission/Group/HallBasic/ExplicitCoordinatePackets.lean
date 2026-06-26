import Submission.Group.HallBasic.ExplicitCoordinateIdentities
import Submission.Group.HallBasic.ExplicitReductionScaling

/-!
# Fixed-weight packets from explicit Hall coordinates

The explicit Hall reducer produces finitely supported integer coordinates in
one lower-central associated-graded layer.  This file turns an arbitrary
fixed-weight coordinate vector into its canonical ordered free-group packet.

Subtraction of coordinate vectors is exact only in the associated-graded
quotient.  In the free group, dividing the subtraction packet by the two
constituent packets leaves a residual in the next lower-central term.  The
Jacobi coordinate identity therefore yields a concrete finite next-stratum
packet.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/-- Canonically ordered packet for a fixed-weight Hall coordinate vector. -/
noncomputable def coordinateScaledTerm
    {r : ℕ}
    (coordinates : BasicIndex (α := α) r →₀ ℤ)
    (z : ℤ) :
    Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
  ((Finset.univ.sort
      fun i j : BasicIndex (α := α) r => i ≤ j).map
    fun i =>
      indexedTreeRep i ^
        (coordinates i * z)).prod

/-- Ambient free-group value of a fixed-weight Hall coordinate packet. -/
noncomputable def coordinateScaledProduct
    {r : ℕ}
    (coordinates : BasicIndex (α := α) r →₀ ℤ)
    (z : ℤ) :
    FreeGroup α :=
  coordinateScaledTerm coordinates z

/--
The packet for reindexed explicit coordinates is the ordinary scaled
reduction packet.
-/
@[simp]
theorem coordinate_scaled_coordinates
    (w : HallTree α)
    {r : ℕ}
    (hweight : w.weight = r)
    (z : ℤ) :
    coordinateScaledProduct
        (basicCoordinatesWeight w hweight) z =
      basicReductionScaled w z := by
  subst r
  rfl

/--
Finite products in a commutative target can be read from the canonical
ordered list without changing their value.
-/
private theorem sort_univ_fintype
    {G : Type*} [CommMonoid G]
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → G) :
    ((Finset.univ.sort fun i j : ι => i ≤ j).map f).prod =
      ∏ i, f i := by
  rw [← List.prod_toFinset]
  · simp
  · exact Finset.sort_nodup _ _

/--
The associated-graded class of a fixed-weight packet is its coordinate
linear combination.
-/
theorem coordinate_scaled_term
    {r : ℕ}
    (coordinates : BasicIndex (α := α) r →₀ ℤ)
    (z : ℤ) :
    lowerClassHom (r - 1)
        (coordinateScaledTerm coordinates z) =
      Additive.toMul
        (coordinates.sum
          (fun i coefficient =>
            (coefficient * z) •
              (indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i))) := by
  have hsum :
      coordinates.sum
          (fun i coefficient =>
            (coefficient * z) •
              (indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i)) =
        ∑ i,
          (coordinates i * z) •
            (indexedBasicTree i).freeLowerWeight
              (indexed_tree_weight i) :=
    Finsupp.sum_fintype coordinates
      (fun i coefficient =>
        (coefficient * z) •
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i))
      (fun i =>
        by
          simp)
  rw [coordinateScaledTerm, map_list_prod, List.map_map,
    show
      (List.map
          (lowerClassHom (r - 1) ∘
            fun i =>
              indexedTreeRep i ^
                (coordinates i * z))
          (Finset.univ.sort fun i j : BasicIndex (α := α) r =>
            i ≤ j)).prod =
        ∏ i,
          lowerClassHom (r - 1)
            (indexedTreeRep i ^
              (coordinates i * z)) by
        simpa only [Function.comp_apply] using
          sort_univ_fintype
            (fun i : BasicIndex (α := α) r =>
              lowerClassHom (r - 1)
                (indexedTreeRep i ^
                  (coordinates i * z))),
    hsum, toMul_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [map_zpow, toMul_zsmul]
  congr 1
  exact
    congrArg Additive.toMul
      (lower_indexed_rep i)

/-- Pull integer scaling outside a coordinate linear combination. -/
private theorem coordinate_sum_smul
    {r : ℕ}
    (coordinates : BasicIndex (α := α) r →₀ ℤ)
    (z : ℤ) :
    coordinates.sum
        (fun i coefficient =>
          (coefficient * z) •
            (indexedBasicTree i).freeLowerWeight
              (indexed_tree_weight i)) =
      z •
        Finsupp.linearCombination ℤ
          (fun i : BasicIndex (α := α) r =>
            (indexedBasicTree i).freeLowerWeight
              (indexed_tree_weight i))
          coordinates := by
  rw [Finsupp.linearCombination_apply, Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro i _hi
  rw [smul_smul, mul_comm]

/--
Subtracting coordinate vectors corresponds in the associated-graded quotient
to multiplying the first packet by the inverse-scaled second packet.
-/
theorem
    scaled_term_sub
    {r : ℕ}
    (left right : BasicIndex (α := α) r →₀ ℤ)
    (z : ℤ) :
    lowerCentralClass (r - 1)
        (coordinateScaledTerm (left - right) z) =
      lowerCentralClass (r - 1)
        (coordinateScaledTerm left z *
          coordinateScaledTerm right (-z)) := by
  change
    Additive.ofMul
        (lowerClassHom (r - 1)
          (coordinateScaledTerm (left - right) z)) =
      Additive.ofMul
        (lowerClassHom (r - 1)
          (coordinateScaledTerm left z *
            coordinateScaledTerm right (-z)))
  rw [map_mul,
    coordinate_scaled_term,
    coordinate_scaled_term,
    coordinate_scaled_term]
  change
    (left - right).sum
        (fun i coefficient =>
          (coefficient * z) •
            (indexedBasicTree i).freeLowerWeight
              (indexed_tree_weight i)) =
      left.sum
          (fun i coefficient =>
            (coefficient * z) •
              (indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i)) +
        right.sum
          (fun i coefficient =>
            (coefficient * -z) •
              (indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i))
  rw [coordinate_sum_smul, coordinate_sum_smul,
    coordinate_sum_smul, map_sub, smul_sub]
  rw [sub_eq_add_neg, neg_smul]

/--
Multiplicative quotient form of coordinate-vector subtraction.
-/
theorem
    lower_scaled_sub
    {r : ℕ}
    (left right : BasicIndex (α := α) r →₀ ℤ)
    (z : ℤ) :
    lowerClassHom (r - 1)
        (coordinateScaledTerm (left - right) z) =
      lowerClassHom (r - 1)
        (coordinateScaledTerm left z *
          coordinateScaledTerm right (-z)) := by
  apply Additive.ofMul.injective
  exact
    scaled_term_sub left right z

/--
The free-group residual between a subtraction packet and its two constituent
packets lies in the next lower-central term.
-/
theorem scaled_products_series
    {r : ℕ}
    (hr : 0 < r)
    (left right : BasicIndex (α := α) r →₀ ℤ)
    (z : ℤ) :
    (coordinateScaledProduct (left - right) z)⁻¹ *
        (coordinateScaledProduct left z *
          coordinateScaledProduct right (-z)) ∈
      Subgroup.lowerCentralSeries (FreeGroup α) r := by
  have hnext :
      ((coordinateScaledTerm (left - right) z)⁻¹ *
        (coordinateScaledTerm left z *
          coordinateScaledTerm right (-z)) :
      Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)) ∈
        (Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1)).subgroupOf
          (Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)) := by
    apply (QuotientGroup.eq_one_iff
      (N :=
        (Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1)).subgroupOf
          (Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)))
      ((coordinateScaledTerm (left - right) z)⁻¹ *
        (coordinateScaledTerm left z *
          coordinateScaledTerm right (-z)))).mp
    change
      lowerClassHom (r - 1)
        ((coordinateScaledTerm (left - right) z)⁻¹ *
          (coordinateScaledTerm left z *
            coordinateScaledTerm right (-z))) =
        1
    rw [map_mul, map_inv,
      ← lower_scaled_sub,
      inv_mul_cancel]
  simpa [coordinateScaledProduct, Nat.sub_add_cancel hr] using hnext

/--
The coordinate packet produced by the graded Jacobi rewrite differs from its
two descendant packets only by a next-stratum free-group residual.
-/
theorem coordinate_scaled_series
    (u v w : HallTree α)
    (z : ℤ) :
    let r : ℕ := (commutator (commutator u v) w).weight
    let original : BasicIndex (α := α) r →₀ ℤ :=
      basicCoordinatesWeight
        (commutator (commutator u v) w) rfl
    let first : BasicIndex (α := α) r →₀ ℤ :=
      basicCoordinatesWeight
        (commutator (commutator u w) v) (by
          dsimp only [r]
          simp only [weight_commutator]
          omega)
    let second : BasicIndex (α := α) r →₀ ℤ :=
      basicCoordinatesWeight
        (commutator (commutator v w) u) (by
          dsimp only [r]
          simp only [weight_commutator]
          omega)
    (coordinateScaledProduct original z)⁻¹ *
        (coordinateScaledProduct first z *
          coordinateScaledProduct second (-z)) ∈
      Subgroup.lowerCentralSeries (FreeGroup α) r := by
  dsimp only
  rw [
    coordinates_jacobi_rewrite
      u v w rfl]
  exact
    scaled_products_series
      (commutator (commutator u v) w).weight_pos _ _ z

/--
The scaled explicit reduction packet of a Jacobi bracket differs from the
two descendant reduction packets only by a next-stratum residual.
-/
theorem scaled_jacobi_series
    (u v w : HallTree α)
    (z : ℤ) :
    (basicReductionScaled (commutator (commutator u v) w) z)⁻¹ *
        (basicReductionScaled (commutator (commutator u w) v) z *
          basicReductionScaled (commutator (commutator v w) u)
            (-z)) ∈
      Subgroup.lowerCentralSeries (FreeGroup α)
        (commutator (commutator u v) w).weight := by
  simpa only [coordinate_scaled_coordinates] using
    coordinate_scaled_series u v w z

end HallTree
end Submission
