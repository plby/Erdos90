import Submission.Group.HallBasic.InnerOuterCoordinates
import Submission.Group.HallBasic.JacobiValueScaling


/-!
# Scaled full outer-child packets from inner Hall reduction

Reducing an inner Hall tree first produces a finite packet of basic trees.
Bracketing those trees with one fixed right tree yields full outer children
of the same total weight as the original outer bracket.  This file packages
their ordered powered free-group product and proves that its quotient from
the powered original bracket lies in the next lower-central term.

Unlike a temporary lower-weight inner factor, every child here retains the
full outer weight.  The construction therefore lifts cleanly to bounded
symbolic repeated-power recipes.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/-- The original outer bracket represented in its explicit total-weight layer. -/
def innerReductionRep
    (inner right : HallTree α) :
    Subgroup.lowerCentralSeries (FreeGroup α) (inner.weight + right.weight - 1) :=
  freeRepWeight (commutator inner right) (by
    simp only [weight_commutator])

omit [Fintype α] [DecidableEq α] [Encodable α] in
/-- The original outer representative has its expected graded class. -/
theorem lower_inner_rep
    (inner right : HallTree α) :
    lowerCentralClass (inner.weight + right.weight - 1)
        (innerReductionRep inner right) =
      (commutator inner right).freeLowerWeight (by
        simp only [weight_commutator]) :=
  lower_rep_weight
    (commutator inner right) (by
      simp only [weight_commutator])

/-- A full outer-child representative in the common total-weight layer. -/
def indexedInnerRep
    (inner right : HallTree α)
    (i : BasicIndex (α := α) inner.weight) :
    Subgroup.lowerCentralSeries (FreeGroup α) (inner.weight + right.weight - 1) :=
  freeRepWeight
    (commutator (indexedBasicTree i) right) (by
      simp only [weight_commutator, indexed_tree_weight])

/-- The full outer-child representative has its expected graded class. -/
theorem indexed_inner_rep
    (inner right : HallTree α)
    (i : BasicIndex (α := α) inner.weight) :
    lowerCentralClass (inner.weight + right.weight - 1)
        (indexedInnerRep inner right i) =
      (commutator (indexedBasicTree i) right).freeLowerWeight
        (by
          simp only [weight_commutator, indexed_tree_weight]) :=
  lower_rep_weight
    (commutator (indexedBasicTree i) right) (by
      simp only [weight_commutator, indexed_tree_weight])

/-- Ordered product of the powered full outer children of an inner reduction. -/
noncomputable def innerScaledTerm
    (inner right : HallTree α)
    (z : ℤ) :
    Subgroup.lowerCentralSeries (FreeGroup α) (inner.weight + right.weight - 1) :=
  ((Finset.univ.sort
      fun i j : BasicIndex (α := α) inner.weight => i ≤ j).map
    fun i =>
      indexedInnerRep inner right i ^
        (basicReductionCoordinates inner i * z)).prod

/-- Finite ordered products agree with `Fintype` products in a commutative target. -/
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
The graded class of the ordered outer-child packet is the scaled class of
the original full outer bracket.
-/
theorem outer_scaled_term
    (inner right : HallTree α)
    (z : ℤ) :
    lowerClassHom (inner.weight + right.weight - 1)
        (innerScaledTerm inner right z) =
      Additive.toMul
        (z • (commutator inner right).freeLowerWeight rfl) := by
  have hsum :
      (basicReductionCoordinates inner).sum
          (fun i coefficient =>
            (coefficient * z) •
              (commutator (indexedBasicTree i) right).freeLowerWeight
                (show
                  (commutator (indexedBasicTree i) right).weight =
                    inner.weight + right.weight by
                  simp only [weight_commutator, indexed_tree_weight])) =
        ∑ i,
          (basicReductionCoordinates inner i * z) •
            (commutator (indexedBasicTree i) right).freeLowerWeight
              (show
                (commutator (indexedBasicTree i) right).weight =
                  inner.weight + right.weight by
                simp only [weight_commutator, indexed_tree_weight]) :=
    Finsupp.sum_fintype _ _ (fun _ => by simp)
  rw [← inner_reduction_smul inner right z]
  rw [innerScaledTerm, map_list_prod, List.map_map,
    show
      (List.map
          (lowerClassHom (inner.weight + right.weight - 1) ∘
            fun i =>
              indexedInnerRep inner right i ^
                (basicReductionCoordinates inner i * z))
          (Finset.univ.sort
            fun i j : BasicIndex (α := α) inner.weight => i ≤ j)).prod =
        ∏ i,
          lowerClassHom (inner.weight + right.weight - 1)
            (indexedInnerRep inner right i ^
              (basicReductionCoordinates inner i * z)) by
        simpa only [Function.comp_apply] using
          sort_univ_fintype
            (fun i : BasicIndex (α := α) inner.weight =>
              lowerClassHom (inner.weight + right.weight - 1)
                (indexedInnerRep inner right i ^
                  (basicReductionCoordinates inner i * z))),
    ]
  calc
    _ =
        Additive.toMul
          (∑ i,
            (basicReductionCoordinates inner i * z) •
              (commutator (indexedBasicTree i) right).freeLowerWeight
                (show
                  (commutator (indexedBasicTree i) right).weight =
                    inner.weight + right.weight by
                  simp only [weight_commutator, indexed_tree_weight])) := by
      rw [toMul_sum]
      apply Finset.prod_congr rfl
      intro i _hi
      rw [map_zpow, toMul_zsmul]
      congr 1
      exact
        congrArg Additive.toMul
          (indexed_inner_rep
            inner right i)
    _ =
        Additive.toMul
          ((basicReductionCoordinates inner).sum
            (fun i coefficient =>
              (coefficient * z) •
                (commutator (indexedBasicTree i) right).freeLowerWeight
                  (by
                    simp only [weight_commutator, indexed_tree_weight]))) := by
      exact congrArg Additive.toMul hsum.symm

/--
The ordered outer-child packet and the powered original bracket have the
same associated-graded class.
-/
theorem inner_scaled_term
    (inner right : HallTree α)
    (z : ℤ) :
    lowerClassHom (inner.weight + right.weight - 1)
        (innerScaledTerm inner right z) =
      lowerClassHom (inner.weight + right.weight - 1)
        ((innerReductionRep inner right) ^ z) := by
  rw [outer_scaled_term,
    map_zpow]
  change
    Additive.toMul
        (z •
          (commutator inner right).freeLowerWeight rfl) =
      Additive.toMul
          (lowerCentralClass (inner.weight + right.weight - 1)
            (innerReductionRep inner right)) ^ z
  rw [← toMul_zsmul]
  exact
    congrArg Additive.toMul
      (congrArg (z • ·)
        (lower_inner_rep
          inner right).symm)

/--
Dividing the powered original outer bracket by its ordered full outer-child
packet leaves a residual in the next lower-central term.
-/
theorem scaled_zpow_next
    (inner right : HallTree α)
    (z : ℤ) :
    (innerScaledTerm inner right z)⁻¹ *
        (innerReductionRep inner right) ^ z ∈
      (Subgroup.lowerCentralSeries (FreeGroup α)
          ((inner.weight + right.weight - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α)
          (inner.weight + right.weight - 1)) := by
  apply (QuotientGroup.eq_one_iff
    (N :=
      (Subgroup.lowerCentralSeries (FreeGroup α)
          ((inner.weight + right.weight - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α)
          (inner.weight + right.weight - 1)))
    ((innerScaledTerm inner right z)⁻¹ *
      (innerReductionRep inner right) ^ z)).mp
  change
    lowerClassHom (inner.weight + right.weight - 1)
        ((innerScaledTerm inner right z)⁻¹ *
          (innerReductionRep inner right) ^ z) =
      1
  rw [map_mul, map_inv,
    inner_scaled_term,
    inv_mul_cancel]

/-- Ambient free-group value of the ordered full outer-child packet. -/
noncomputable def innerOuterScaled
    (inner right : HallTree α)
    (z : ℤ) :
    FreeGroup α :=
  innerScaledTerm inner right z

/-- Ambient free-group form of the full outer-child residual theorem. -/
theorem inner_scaled_zpow
    (inner right : HallTree α)
    (z : ℤ) :
    (innerOuterScaled inner right z)⁻¹ *
        (commutator inner right).toCWord.eval FreeGroup.of ^ z ∈
      Subgroup.lowerCentralSeries (FreeGroup α) (inner.weight + right.weight) := by
  have htotalPos : 0 < inner.weight + right.weight := by
    have hinner := inner.weight_pos
    omega
  have hnext :
      (innerScaledTerm inner right z)⁻¹ *
          (innerReductionRep inner right) ^ z ∈
        (Subgroup.lowerCentralSeries (FreeGroup α)
            ((inner.weight + right.weight - 1) + 1)).subgroupOf
          (Subgroup.lowerCentralSeries (FreeGroup α)
            (inner.weight + right.weight - 1)) :=
    scaled_zpow_next
      inner right z
  have hambient :
      (((innerScaledTerm inner right z)⁻¹ *
          (innerReductionRep inner right) ^ z :
            Subgroup.lowerCentralSeries (FreeGroup α)
              (inner.weight + right.weight - 1)) :
          FreeGroup α) ∈
        Subgroup.lowerCentralSeries (FreeGroup α)
          ((inner.weight + right.weight - 1) + 1) :=
    hnext
  change
    (((innerScaledTerm inner right z :
          Subgroup.lowerCentralSeries (FreeGroup α)
            (inner.weight + right.weight - 1)) :
        FreeGroup α)⁻¹ *
      ((innerReductionRep inner right :
          Subgroup.lowerCentralSeries (FreeGroup α)
            (inner.weight + right.weight - 1)) :
        FreeGroup α) ^ z) ∈
      Subgroup.lowerCentralSeries (FreeGroup α)
        ((inner.weight + right.weight - 1) + 1) at hambient
  simpa only [innerOuterScaled,
    innerReductionRep,
    coe_rep_weight,
    Nat.sub_add_cancel htotalPos] using hambient

end HallTree
end Submission
