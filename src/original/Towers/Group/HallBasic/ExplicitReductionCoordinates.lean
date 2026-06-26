import Towers.Group.HallBasic.AssociatedGradedSpanning

/-!
# Explicit coordinates from Hall-tree reduction

The recursive Hall-tree reducer proves that every free-group lower-central
class belongs to the span of the indexed basic Hall classes.  This file
extracts one finite integer coefficient packet from that theorem.  The packet
is intentionally noncomputable: its role is to expose the finite coordinate
data that a later group-level collector must lift through the next
lower-central stratum.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
One finitely supported integer coordinate packet expressing a Hall-tree class
as a linear combination of indexed basic Hall classes in the same weight.
-/
noncomputable def basicReductionCoordinates
    (w : HallTree α) :
    BasicIndex (α := α) w.weight →₀ ℤ :=
  Classical.choose
    (Finsupp.mem_span_range_iff_exists_finsupp.mp
      (show
        w.freeCentralLayer ∈
          Submodule.span ℤ
            (Set.range fun i : BasicIndex (α := α) w.weight =>
              (indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i)) by
        simpa only [basicTreeSpan] using
          basic_tree_span w))

/--
The extracted coordinate packet reconstructs the original Hall-tree class in
the free-group lower-central associated-graded layer.
-/
theorem basic_coordinates_sum
    (w : HallTree α) :
    (basicReductionCoordinates w).sum
        (fun i coefficient =>
          coefficient •
            (indexedBasicTree i).freeLowerWeight
              (indexed_tree_weight i)) =
      w.freeCentralLayer :=
  Classical.choose_spec
    (Finsupp.mem_span_range_iff_exists_finsupp.mp
      (show
        w.freeCentralLayer ∈
          Submodule.span ℤ
            (Set.range fun i : BasicIndex (α := α) w.weight =>
              (indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i)) by
        simpa only [basicTreeSpan] using
          basic_tree_span w))

/--
The same reconstruction statement phrased through
`Finsupp.linearCombination`.
-/
theorem reduction_coordinates_combination
    (w : HallTree α) :
    Finsupp.linearCombination ℤ
        (fun i : BasicIndex (α := α) w.weight =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i))
        (basicReductionCoordinates w) =
      w.freeCentralLayer := by
  simpa only [Finsupp.linearCombination_apply] using
    basic_coordinates_sum w

/--
A Hall-tree representative reindexed into an explicitly chosen lower-central
term.
-/
def freeRepWeight
    {r : ℕ}
    (w : HallTree α)
    (hweight : w.weight = r) :
    Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
  cast
    (congrArg
      (fun k => ↥(Subgroup.lowerCentralSeries (FreeGroup α) (k - 1)))
      hweight)
    w.freeCentralRep

section Reindexing

variable {β : Type u}

/-- Reindexing a representative and then taking its class gives the reindexed class. -/
theorem lower_rep_weight
    {r : ℕ}
    (w : HallTree β)
    (hweight : w.weight = r) :
    TBluepr.lowerCentralClass (r - 1)
        (freeRepWeight w hweight) =
      w.freeLowerWeight hweight := by
  subst r
  simp [freeRepWeight, TBluepr.lowerCentralClass,
    TBluepr.lowerClassHom, freeLowerWeight,
    freeCentralLayer, freeCentralRep]

end Reindexing

/-- The fixed-weight lower-central representative of one indexed basic tree. -/
def indexedTreeRep
    {r : ℕ}
    (i : BasicIndex (α := α) r) :
    Subgroup.lowerCentralSeries (FreeGroup α) (r - 1) :=
  freeRepWeight
    (indexedBasicTree i) (indexed_tree_weight i)

/--
The indexed representative has the expected indexed associated-graded class.
-/
theorem lower_indexed_rep
    {r : ℕ}
    (i : BasicIndex (α := α) r) :
    TBluepr.lowerCentralClass (r - 1)
        (indexedTreeRep i) =
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) :=
  lower_rep_weight
    (indexedBasicTree i) (indexed_tree_weight i)

/--
The ordered free-group lower-central product encoded by the extracted integer
coordinates.
-/
noncomputable def basicReductionTerm
    (w : HallTree α) :
    Subgroup.lowerCentralSeries (FreeGroup α) (w.weight - 1) :=
  ((Finset.univ.sort
      fun i j : BasicIndex (α := α) w.weight => i ≤ j).map
    fun i =>
      indexedTreeRep i ^
        basicReductionCoordinates w i).prod

/--
Finite products in a commutative target can be read from the canonical ordered
list without changing their value.
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
The quotient class of the ordered lower-central product is the finite linear
combination encoded by the extracted coordinates.
-/
theorem basic_reduction_term
    (w : HallTree α) :
    TBluepr.lowerClassHom (w.weight - 1)
        (basicReductionTerm w) =
      Additive.toMul
        ((basicReductionCoordinates w).sum
          (fun i coefficient =>
            coefficient •
              (indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i))) := by
  have hsum :
      (basicReductionCoordinates w).sum
          (fun i coefficient =>
            coefficient •
              (indexedBasicTree i).freeLowerWeight
                (indexed_tree_weight i)) =
        ∑ i,
          basicReductionCoordinates w i •
            (indexedBasicTree i).freeLowerWeight
              (indexed_tree_weight i) :=
    Finsupp.sum_fintype _ _ (fun _ => zero_smul ℤ _)
  rw [basicReductionTerm, map_list_prod, List.map_map,
    show
      (List.map
          (TBluepr.lowerClassHom (w.weight - 1) ∘
            fun i =>
              indexedTreeRep i ^
                basicReductionCoordinates w i)
          (Finset.univ.sort fun i j : BasicIndex (α := α) w.weight =>
            i ≤ j)).prod =
        ∏ i,
          TBluepr.lowerClassHom (w.weight - 1)
            (indexedTreeRep i ^
              basicReductionCoordinates w i) by
        simpa only [Function.comp_apply] using
          sort_univ_fintype
            (fun i : BasicIndex (α := α) w.weight =>
              TBluepr.lowerClassHom (w.weight - 1)
                (indexedTreeRep i ^
                  basicReductionCoordinates w i)),
    hsum, toMul_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [map_zpow, toMul_zsmul]
  congr 1
  exact
    congrArg Additive.toMul
      (lower_indexed_rep i)

/--
The ordered lower-central product and the original Hall tree have the same
associated-graded class.
-/
theorem lower_reduction_term
    (w : HallTree α) :
    TBluepr.lowerClassHom (w.weight - 1)
        (basicReductionTerm w) =
      TBluepr.lowerClassHom (w.weight - 1)
        w.freeCentralRep := by
  rw [basic_reduction_term]
  exact congrArg Additive.toMul (basic_coordinates_sum w)

/--
Dividing a Hall tree by its ordered basic-tree compression leaves a residual
in the next lower-central term.
-/
theorem basic_inv_next
    (w : HallTree α) :
    (basicReductionTerm w)⁻¹ * w.freeCentralRep ∈
      (Subgroup.lowerCentralSeries (FreeGroup α) ((w.weight - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) (w.weight - 1)) := by
  apply (QuotientGroup.eq_one_iff
    (N :=
      (Subgroup.lowerCentralSeries (FreeGroup α) ((w.weight - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) (w.weight - 1)))
    ((basicReductionTerm w)⁻¹ *
      w.freeCentralRep)).mp
  change
    TBluepr.lowerClassHom (w.weight - 1)
        ((basicReductionTerm w)⁻¹ *
          w.freeCentralRep) =
      1
  rw [map_mul, map_inv,
    lower_reduction_term,
    inv_mul_cancel]

/-- The ambient free-group value of the ordered basic-tree compression. -/
noncomputable def basicReductionProduct
    (w : HallTree α) :
    FreeGroup α :=
  basicReductionTerm w

/--
Ambient-group form of the next-stratum residual theorem.
-/
theorem basic_reduction_series
    (w : HallTree α) :
    (basicReductionProduct w)⁻¹ *
        w.toCWord.eval FreeGroup.of ∈
      Subgroup.lowerCentralSeries (FreeGroup α) w.weight :=
  by
    simpa [basicReductionProduct, Nat.sub_add_cancel w.weight_pos] using
      basic_inv_next w

end HallTree
end Towers
