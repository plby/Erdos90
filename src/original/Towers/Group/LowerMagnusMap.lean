import Towers.Group.CommutatorLeadingTerm

namespace Towers
namespace TBluepr

open scoped IsMulCommutative

/--
The zero-based lower-central associated-graded layer
`γ_(n+1)(G) / γ_(n+2)(G)`.
-/
abbrev LowerGradedLayer
    (G : Type*) [Group G]
    (n : ℕ) :
    Type _ :=
  (Subgroup.lowerCentralSeries G n) ⧸
    ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf (Subgroup.lowerCentralSeries G n))

/-- The self-commutator of one lower-central term lands in the next term. -/
theorem lower_self_based
    (G : Type*) [Group G]
    (n : ℕ) :
    ⁅Subgroup.lowerCentralSeries G n, Subgroup.lowerCentralSeries G n⁆ ≤
      Subgroup.lowerCentralSeries G (n + 1) := by
  have hcomm :
      ⁅Subgroup.lowerCentralSeries G n, Subgroup.lowerCentralSeries G 0⁆ ≤
        Subgroup.lowerCentralSeries G (n + 0 + 1) :=
    lower_commutator_succ n 0
  simpa using
    (Subgroup.commutator_mono le_rfl
      (show Subgroup.lowerCentralSeries G n ≤ Subgroup.lowerCentralSeries G 0 by simp)).trans
      hcomm

instance lower_graded_commutative
    (G : Type*) [Group G]
    (n : ℕ) :
    IsMulCommutative (LowerGradedLayer G n) := by
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  let A : Subgroup G := Subgroup.lowerCentralSeries G n
  let B : Subgroup G := Subgroup.lowerCentralSeries G (n + 1)
  change _root_.commutator A ≤ B.comap A.subtype
  rw [← Subgroup.map_le_iff_le_comap]
  rw [_root_.commutator_def, Subgroup.map_commutator]
  rw [← MonoidHom.range_eq_map, A.range_subtype]
  exact lower_self_based G n

instance lower_graded_comm
    (G : Type*) [Group G] (n : ℕ) :
    CommGroup (LowerGradedLayer G n) :=
  { (inferInstance : Group (LowerGradedLayer G n)) with
    mul_comm := mul_comm' }

/-- A lower-central element represented by its augmentation difference in the
corresponding augmentation power. -/
noncomputable def lowerDifferenceRep
    (R G : Type*) [CommRing R] [Group G]
    (n : ℕ)
    (x : Subgroup.lowerCentralSeries G n) :
    GroupAlgebra.augmentationPowerSubmodule R G (n + 1) := by
  refine ⟨augmentationDifference R G x, ?_⟩
  have hx :=
    GShafar.lower_series_succ
      (R := R) (G := G) n x.property
  simpa [GroupAlgebra.augmentationPower,
    ← golod_shafarevich_algebra,
    GShafar.augmentationPowerSubgroup,
    augmentationDifference] using hx

/-- Before quotienting the lower-central source, `g ↦ g - 1` is a
multiplicative map into the multiplicative form of the augmentation layer. -/
noncomputable def lowerMagnusHom
    (R G : Type*) [CommRing R] [Group G]
    (n : ℕ) :
    Subgroup.lowerCentralSeries G n →*
      Multiplicative (GroupAlgebra.augmentationLayer R G (n + 1)) where
  toFun x :=
    Multiplicative.ofAdd
      (Submodule.Quotient.mk
        (lowerDifferenceRep R G n x))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change
      Submodule.Quotient.mk
          (lowerDifferenceRep R G n 1) =
        0
    rw [Submodule.Quotient.mk_eq_zero]
    change
      augmentationDifference R G (1 : G) ∈
        GroupAlgebra.augmentationPower R G ((n + 1) + 1)
    simp [augmentationDifference, MonoidAlgebra.one_def]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul]
    change
      Submodule.Quotient.mk
          (lowerDifferenceRep R G n (x * y)) =
        Submodule.Quotient.mk
            (lowerDifferenceRep R G n x) +
          Submodule.Quotient.mk
            (lowerDifferenceRep R G n y)
    rw [← Submodule.Quotient.mk_add]
    apply
      (Submodule.Quotient.eq
        (GroupAlgebra.augmentationLayerDenom R G (n + 1))).mpr
    change
      (MonoidAlgebra.of R G ((x : G) * (y : G)) - 1) -
          ((MonoidAlgebra.of R G x - 1) +
            (MonoidAlgebra.of R G y - 1)) ∈
        GroupAlgebra.augmentationPower R G ((n + 1) + 1)
    have hprod :=
      GroupAlgebra.mul_augmentation_add
        (R := R) (G := G)
        (lowerDifferenceRep R G n x).property
        (lowerDifferenceRep R G n y).property
    have hdown :
        augmentationDifference R G x * augmentationDifference R G y ∈
          GroupAlgebra.augmentationPower R G ((n + 1) + 1) :=
      GroupAlgebra.augmentationPower_antitone R G (by omega) hprod
    rw [GShafar.of_sub_eq]
    simpa [augmentationDifference, add_assoc] using hdown

/-- The pre-quotient Magnus homomorphism kills the next lower-central term. -/
theorem lower_magnus_succ
    (R G : Type*) [CommRing R] [Group G]
    (n : ℕ)
    (x : Subgroup.lowerCentralSeries G n)
    (hx : (x : G) ∈ Subgroup.lowerCentralSeries G (n + 1)) :
    lowerMagnusHom R G n x = 1 := by
  apply Multiplicative.toAdd.injective
  change
    Submodule.Quotient.mk
        (lowerDifferenceRep R G n x) =
      0
  rw [Submodule.Quotient.mk_eq_zero]
  change
    augmentationDifference R G x ∈
      GroupAlgebra.augmentationPower R G ((n + 1) + 1)
  have hnext :=
    GShafar.lower_series_succ
      (R := R) (G := G) (n + 1) hx
  simpa [GroupAlgebra.augmentationPower,
    ← golod_shafarevich_algebra,
    GShafar.augmentationPowerSubgroup,
    augmentationDifference] using hnext

/--
The Magnus map from the lower-central associated-graded layer to the
corresponding augmentation layer.
-/
noncomputable def associatedGradedHom
    (R G : Type*) [CommRing R] [Group G]
    (n : ℕ) :
    LowerGradedLayer G n →*
      Multiplicative (GroupAlgebra.augmentationLayer R G (n + 1)) :=
  QuotientGroup.lift
    ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf (Subgroup.lowerCentralSeries G n))
    (lowerMagnusHom R G n)
    (by
      intro x hx
      apply lower_magnus_succ R G n x
      exact hx)

@[simp]
theorem associated_magnus_mk
    (R G : Type*) [CommRing R] [Group G]
    (n : ℕ)
    (x : Subgroup.lowerCentralSeries G n) :
    associatedGradedHom R G n
        (QuotientGroup.mk'
          ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf
            (Subgroup.lowerCentralSeries G n)) x) =
      Multiplicative.ofAdd
        (Submodule.Quotient.mk
          (lowerDifferenceRep R G n x)) := by
  change
    (QuotientGroup.lift
      ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf (Subgroup.lowerCentralSeries G n))
      (lowerMagnusHom R G n) _)
        (QuotientGroup.mk'
          ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf
            (Subgroup.lowerCentralSeries G n)) x) =
      lowerMagnusHom R G n x
  rfl

/-- Additive form of the Magnus map. -/
noncomputable def lowerAssociatedGraded
    (R G : Type*) [CommRing R] [Group G]
    (n : ℕ) :
    Additive (LowerGradedLayer G n) →+
      GroupAlgebra.augmentationLayer R G (n + 1) where
  toFun x :=
    (associatedGradedHom R G n x.toMul).toAdd
  map_zero' := by
    simp
  map_add' x y := by
    simp

@[simp]
theorem graded_magnus_mk
    (R G : Type*) [CommRing R] [Group G]
    (n : ℕ)
    (x : Subgroup.lowerCentralSeries G n) :
    lowerAssociatedGraded R G n
        (Additive.ofMul
          (QuotientGroup.mk'
            ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf
              (Subgroup.lowerCentralSeries G n)) x)) =
      Submodule.Quotient.mk
        (lowerDifferenceRep R G n x) := by
  change
    (associatedGradedHom R G n
      (QuotientGroup.mk'
        ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf
          (Subgroup.lowerCentralSeries G n)) x)).toAdd =
      Submodule.Quotient.mk
        (lowerDifferenceRep R G n x)
  rw [associated_magnus_mk]
  rfl

/-- Integer-linear form of the Magnus map, matching the coefficient ring of
the classical lower-central basic-commutator theorem. -/
noncomputable def associatedGradedMagnus
    (G : Type*) [Group G]
    (n : ℕ) :
    Additive (LowerGradedLayer G n) →ₗ[ℤ]
      GroupAlgebra.augmentationLayer ℤ G (n + 1) :=
  (lowerAssociatedGraded ℤ G n).toIntLinearMap

@[simp]
theorem associated_graded_mk
    (G : Type*) [Group G]
    (n : ℕ)
    (x : Subgroup.lowerCentralSeries G n) :
    associatedGradedMagnus G n
        (Additive.ofMul
          (QuotientGroup.mk'
            ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf
              (Subgroup.lowerCentralSeries G n)) x)) =
      Submodule.Quotient.mk
        (lowerDifferenceRep ℤ G n x) := by
  change
    lowerAssociatedGraded ℤ G n
        (Additive.ofMul
          (QuotientGroup.mk'
            ((Subgroup.lowerCentralSeries G (n + 1)).subgroupOf
              (Subgroup.lowerCentralSeries G n)) x)) =
      (Submodule.Quotient.mk
        (lowerDifferenceRep ℤ G n x) :
          GroupAlgebra.augmentationLayer ℤ G (n + 1))
  exact graded_magnus_mk ℤ G n x

/-- A binary commutator word evaluated in the free group, represented in its
expected lower-central term. -/
def freeLowerRep
    (α : Type*)
    (w : CWord α) :
    Subgroup.lowerCentralSeries (FreeGroup α) ((w.weight fun _ => 1) - 1) :=
  ⟨w.eval FreeGroup.of,
    CWord.eval_lower_series
      FreeGroup.of
      (fun _ : α => 1)
      (fun _ => by simp)
      (fun _ => by simp)
      w⟩

/-- The lower-central associated-graded class represented by a binary
commutator word in free generators. -/
def freeLowerLayer
    (α : Type*)
    (w : CWord α) :
    Additive
      (LowerGradedLayer (FreeGroup α)
        ((w.weight fun _ => 1) - 1)) :=
  Additive.ofMul
    (QuotientGroup.mk'
      ((Subgroup.lowerCentralSeries (FreeGroup α) (((w.weight fun _ => 1) - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) ((w.weight fun _ => 1) - 1)))
      (freeLowerRep α w))

/--
For a binary commutator word in free generators, the Magnus map sends its
lower-central class to its recursively defined associative leading polynomial.
-/
theorem associated_graded_layer
    (R α : Type*) [CommRing R]
    (w : CWord α) :
    GroupAlgebra.augmentationLayerReindex R (FreeGroup α)
        (Nat.sub_add_cancel
          (CWord.weight_pos
            (fun _ : α => 1) (fun _ => by simp) w))
        (lowerAssociatedGraded R (FreeGroup α)
          ((w.weight fun _ => 1) - 1)
          (freeLowerLayer α w)) =
      freeLeadingLayer R α w := by
  rw [freeLowerLayer,
    graded_magnus_mk,
    GroupAlgebra.augmentation_reindex_mk]
  rw [← free_difference_leading
    R α w]
  rfl

end TBluepr
end Towers
