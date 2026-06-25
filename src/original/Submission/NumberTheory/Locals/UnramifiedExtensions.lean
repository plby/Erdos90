import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.IsAdjoinRoot
import Submission.NumberTheory.Locals.UnramifiedResidueLift


/-!
# Unramified extensions and residue-field degree

This file records the ramification-theoretic parts of Milne's Proposition
7.50 and Corollaries 7.51--7.52.  The construction from a finite separable
residue extension, and the resulting unramified/totally ramified
decomposition, are proved in `UnramifiedResidueLift` and
`LocalUnramifiedDecomposition`.
-/

namespace Submission.NumberTheory.Milne

open IsLocalRing Polynomial
open scoped Pointwise TensorProduct

noncomputable section

attribute [local instance] Ideal.Quotient.field

/-- The compositum of two formally unramified subalgebras is formally
unramified.  It is the image of their tensor product under multiplication;
formal unramifiedness is preserved by base change, composition, and passage
to a surjective image.  This is the missing compositum step in Milne's proof
of Proposition 7.50. -/
theorem formally_sup_subalgebra
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (U V : Subalgebra R S)
    [Algebra.FormallyUnramified R U]
    [Algebra.FormallyUnramified R V] :
    Algebra.FormallyUnramified R (U ⊔ V : Subalgebra R S) := by
  let T := U ⊗[R] V
  let f : T →ₐ[R] S := Subalgebra.mulMap U V
  have hrange : f.range = U ⊔ V := by
    simpa [f, Subalgebra.mulMap, Subalgebra.range_val] using
      Algebra.TensorProduct.productMap_range U.val V.val
  let g : T →ₐ[R] (U ⊔ V : Subalgebra R S) :=
    f.codRestrict (U ⊔ V) fun x ↦ by
      rw [← hrange]
      exact ⟨x, rfl⟩
  have hg : Function.Surjective g := by
    intro y
    have hy : (y : S) ∈ f.range := by
      rw [hrange]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  letI : Algebra.FormallyUnramified U T := by
    dsimp only [T]
    infer_instance
  letI : Algebra.FormallyUnramified R T :=
    Algebra.FormallyUnramified.comp R U T
  exact Algebra.FormallyUnramified.of_surjective g hg

/-- Milne, Proposition 7.50, footnote: for an essentially finite-type map of
local rings, unramifiedness is equivalent to separability of the residue-field
extension together with equality of the extended maximal ideal.  This is the
criterion that remains valid without assuming the residue field perfect. -/
theorem formally_separable_maximal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] :
    Algebra.FormallyUnramified R S ↔
      Algebra.IsSeparable (ResidueField R) (ResidueField S) ∧
        (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
  Algebra.FormallyUnramified.iff_map_maximalIdeal_eq

/-- The uniqueness mechanism in Milne's Proposition 7.50.  A finite
formally unramified local algebra with no residue-field enlargement is already
the base ring: its algebra map is bijective.

In Milne's application, this is applied after passing to the compositum of
two finite unramified subextensions having the same residue field. -/
theorem bijective_formally_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Finite R S] [Algebra.FormallyUnramified R S]
    [FaithfulSMul R S]
    (H : Function.Surjective
      (algebraMap (ResidueField R) (ResidueField S))) :
    Function.Bijective (algebraMap R S) := by
  refine ⟨FaithfulSMul.algebraMap_injective R S, ?_⟩
  change Function.Surjective (Algebra.linearMap R S)
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
    Module.Finite.fg_top (maximalIdeal_le_jacobson _)
  rw [Ideal.smul_top_eq_map, Algebra.FormallyUnramified.map_maximalIdeal]
  rintro x -
  obtain ⟨a, ha⟩ := H (algebraMap _ _ x)
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply _ S, ResidueField.algebraMap_eq,
    ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at ha
  rw [← sub_sub_self (algebraMap _ _ a) x]
  exact sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩)
    (Submodule.mem_sup_right ha)

/-- Equivalence form of the uniqueness mechanism in Proposition 7.50. -/
noncomputable def algFormallySurjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Finite R S] [Algebra.FormallyUnramified R S]
    [FaithfulSMul R S]
    (H : Function.Surjective
      (algebraMap (ResidueField R) (ResidueField S))) :
    R ≃ₐ[R] S :=
  AlgEquiv.ofBijective (Algebra.ofId R S)
    (bijective_formally_surjective H)

section ResidueCorrespondence

variable (A B : Type*) [CommRing A] [CommRing B]
  [HenselianLocalRing A] [HenselianLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

omit [HenselianLocalRing A] [IsLocalHom (algebraMap A B)] in
/-- An integral subalgebra of a local ring is local.  Its unique maximal
ideal is the contraction of the ambient maximal ideal. -/
theorem subalgebra_ring_integral
    [Algebra.IsIntegral A B] (U : Subalgebra A B) : IsLocalRing U := by
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  let P := (maximalIdeal B).under U
  have hP : P.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B)
  refine IsLocalRing.of_unique_max_ideal ⟨P, hP, ?_⟩
  intro M hM
  letI : M.IsMaximal := hM
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) M
  have hQ : Q = maximalIdeal B := IsLocalRing.eq_maximalIdeal hQmax
  rw [hQ] at hQover
  exact hQover.over

/-- The residue image of an integral local subalgebra, bundled as an
intermediate field of the ambient residue extension.  It is the field range
of the map on residue fields induced by the inclusion `U -> B`. -/
noncomputable def residueIntermediateField
    [FaithfulSMul A B] [Algebra.IsIntegral A B] (U : Subalgebra A B) :
    IntermediateField (ResidueField A) (ResidueField B) := by
  letI : IsLocalRing U := subalgebra_ring_integral A B U
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : Algebra.IsIntegral A U :=
    Algebra.IsIntegral.of_injective U.val Subtype.val_injective
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Algebra U B := U.val.toRingHom.toAlgebra
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsScalarTower A U B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : IsLocalHom (algebraMap U B) :=
    (algebraMap_isIntegral_iff.mpr
      (inferInstance : Algebra.IsIntegral U B)).isLocalHom
        Subtype.val_injective
  exact (IsScalarTower.toAlgHom (ResidueField A)
    (ResidueField U) (ResidueField B)).fieldRange

/-- The bundled residue intermediate field has the same underlying
subalgebra as `residueImage`. -/
theorem residue_intermediate_subalgebra
    [FaithfulSMul A B] [Algebra.IsIntegral A B] (U : Subalgebra A B) :
    (residueIntermediateField A B U).toSubalgebra =
      residueImage A B U := by
  letI : IsLocalRing U := subalgebra_ring_integral A B U
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : Algebra.IsIntegral A U :=
    Algebra.IsIntegral.of_injective U.val Subtype.val_injective
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Algebra U B := U.val.toRingHom.toAlgebra
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsScalarTower A U B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : IsLocalHom (algebraMap U B) :=
    (algebraMap_isIntegral_iff.mpr
      (inferInstance : Algebra.IsIntegral U B)).isLocalHom
        Subtype.val_injective
  apply SetLike.ext
  intro x
  change
    x ∈ (IsScalarTower.toAlgHom (ResidueField A)
      (ResidueField U) (ResidueField B)).fieldRange ↔
      x ∈ residueImage A B U
  rw [AlgHom.mem_fieldRange]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := residue_surjective y
    refine ⟨u, u.property, ?_⟩
    exact IsLocalRing.ResidueField.algebraMap_residue u
  · rintro ⟨b, hb, rfl⟩
    let u : U := ⟨b, hb⟩
    refine ⟨residue U u, ?_⟩
    exact IsLocalRing.ResidueField.algebraMap_residue u

/-- The residue intermediate field of a finite formally unramified
subalgebra is finite over the base residue field. -/
theorem residue_intermediate_field
    [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (U : Subalgebra A B) [Module.Finite A U]
    [Algebra.FormallyUnramified A U] :
    Module.Finite (ResidueField A) (residueIntermediateField A B U) := by
  letI : IsLocalRing U := subalgebra_ring_integral A B U
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : Algebra.IsIntegral A U :=
    Algebra.IsIntegral.of_injective U.val Subtype.val_injective
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Algebra U B := U.val.toRingHom.toAlgebra
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsScalarTower A U B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : IsLocalHom (algebraMap U B) :=
    (algebraMap_isIntegral_iff.mpr
      (inferInstance : Algebra.IsIntegral U B)).isLocalHom
        Subtype.val_injective
  let f := IsScalarTower.toAlgHom (ResidueField A)
    (ResidueField U) (ResidueField B)
  change Module.Finite (ResidueField A) f.fieldRange
  exact f.toLinearMap.finiteDimensional_range

/-- The residue intermediate field of a finite formally unramified
subalgebra is separable over the base residue field. -/
theorem residue_intermediate_separable
    [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (U : Subalgebra A B) [Module.Finite A U]
    [Algebra.FormallyUnramified A U] :
    Algebra.IsSeparable (ResidueField A)
      (residueIntermediateField A B U) := by
  letI : IsLocalRing U := subalgebra_ring_integral A B U
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : Algebra.IsIntegral A U :=
    Algebra.IsIntegral.of_injective U.val Subtype.val_injective
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Algebra U B := U.val.toRingHom.toAlgebra
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsScalarTower A U B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : IsLocalHom (algebraMap U B) :=
    (algebraMap_isIntegral_iff.mpr
      (inferInstance : Algebra.IsIntegral U B)).isLocalHom
        Subtype.val_injective
  let f := IsScalarTower.toAlgHom (ResidueField A)
    (ResidueField U) (ResidueField B)
  change Algebra.IsSeparable (ResidueField A) f.fieldRange
  exact AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)

/-- If nested integral subalgebras have the same image in the ambient
residue field, their induced residue-field map is surjective. -/
theorem residue_surjective_image
    [Algebra.IsIntegral A B] (U W : Subalgebra A B) (hUW : U ≤ W)
    (hres : residueImage A B U = residueImage A B W) :
    letI : IsLocalRing U := subalgebra_ring_integral A B U
    letI : IsLocalRing W := subalgebra_ring_integral A B W
    letI : Algebra U W := (Subalgebra.inclusion hUW).toRingHom.toAlgebra
    letI : IsScalarTower A U W := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.IsIntegral A W :=
      Algebra.IsIntegral.of_injective W.val Subtype.val_injective
    letI : Algebra.IsIntegral U W := Algebra.IsIntegral.tower_top A
    letI : FaithfulSMul U W :=
      (faithfulSMul_iff_algebraMap_injective U W).mpr
        (Subalgebra.inclusion_injective hUW)
    letI : IsLocalHom (algebraMap U W) := Algebra.IsIntegral.isLocalHom U W
    Function.Surjective (algebraMap (ResidueField U) (ResidueField W)) := by
  letI : IsLocalRing U := subalgebra_ring_integral A B U
  letI : IsLocalRing W := subalgebra_ring_integral A B W
  letI : Algebra U W := (Subalgebra.inclusion hUW).toRingHom.toAlgebra
  letI : IsScalarTower A U W := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsIntegral A W :=
    Algebra.IsIntegral.of_injective W.val Subtype.val_injective
  letI : Algebra.IsIntegral U W := Algebra.IsIntegral.tower_top A
  letI : FaithfulSMul U W :=
    (faithfulSMul_iff_algebraMap_injective U W).mpr
      (Subalgebra.inclusion_injective hUW)
  letI : IsLocalHom (algebraMap U W) := Algebra.IsIntegral.isLocalHom U W
  intro y
  obtain ⟨w, rfl⟩ := residue_surjective y
  have hw : residue B (w : B) ∈ residueImage A B W :=
    ⟨w, w.property, rfl⟩
  rw [← hres] at hw
  obtain ⟨u, hu, hures⟩ := hw
  let uU : U := ⟨u, hu⟩
  refine ⟨residue U uU, ?_⟩
  rw [IsLocalRing.ResidueField.algebraMap_residue]
  letI : Algebra.IsIntegral W B := Algebra.IsIntegral.tower_top A
  letI : IsLocalHom (algebraMap W B) := Algebra.IsIntegral.isLocalHom W B
  apply (algebraMap (ResidueField W) (ResidueField B)).injective
  rw [IsLocalRing.ResidueField.algebraMap_residue,
    IsLocalRing.ResidueField.algebraMap_residue]
  exact hures

/-- A finite formally unramified subalgebra cannot be enlarged without
enlarging its residue image.  This is the uniqueness step of Proposition
7.50. -/
theorem formally_unramified_image
    [Algebra.IsIntegral A B] (U W : Subalgebra A B) (hUW : U ≤ W)
    [Module.Finite A W] [Algebra.FormallyUnramified A W]
    (hres : residueImage A B U = residueImage A B W) : U = W := by
  letI : IsLocalRing U := subalgebra_ring_integral A B U
  letI : IsLocalRing W := subalgebra_ring_integral A B W
  letI : Algebra U W := (Subalgebra.inclusion hUW).toRingHom.toAlgebra
  letI : IsScalarTower A U W := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsIntegral A W :=
    Algebra.IsIntegral.of_injective W.val Subtype.val_injective
  letI : Algebra.IsIntegral U W := Algebra.IsIntegral.tower_top A
  letI : FaithfulSMul U W :=
    (faithfulSMul_iff_algebraMap_injective U W).mpr
      (Subalgebra.inclusion_injective hUW)
  letI : IsLocalHom (algebraMap U W) := Algebra.IsIntegral.isLocalHom U W
  letI : Module.Finite U W := Module.Finite.of_restrictScalars_finite A U W
  letI : Algebra.FormallyUnramified U W :=
    Algebra.FormallyUnramified.of_restrictScalars A U W
  have hsurj : Function.Surjective
      (algebraMap (ResidueField U) (ResidueField W)) :=
    residue_surjective_image A B U W hUW hres
  have hbij : Function.Bijective (algebraMap U W) :=
    bijective_formally_surjective hsurj
  apply le_antisymm hUW
  intro w hw
  obtain ⟨u, hu⟩ := hbij.2 ⟨w, hw⟩
  have huv : (u : B) = w := congrArg Subtype.val hu
  exact huv ▸ u.property

/-- For finite formally unramified subalgebras, containment is detected
exactly after reduction to the ambient residue field. -/
theorem formally_unramified_subalgebra
    [Algebra.IsIntegral A B]
    (U V : Subalgebra A B)
    [Module.Finite A U] [Module.Finite A V]
    [Algebra.FormallyUnramified A U]
    [Algebra.FormallyUnramified A V] :
    U ≤ V ↔ residueImage A B U ≤ residueImage A B V := by
  constructor
  · intro hUV
    exact residueImage_mono A B hUV
  · intro hres
    let W := U ⊔ V
    letI : Module.Finite A W := Subalgebra.finite_sup U V
    letI : Algebra.FormallyUnramified A W :=
      formally_sup_subalgebra U V
    have hVW : V ≤ W := le_sup_right
    have hresEq : residueImage A B V = residueImage A B W := by
      rw [residueImage_sup]
      exact (sup_eq_right.mpr hres).symm
    have hVWEq : V = W :=
      formally_unramified_image A B V W hVW hresEq
    rw [hVWEq]
    exact le_sup_left

/-- Equality of finite formally unramified subalgebras is equivalent to
equality of their residue images. -/
theorem formally_subalgebra_image
    [Algebra.IsIntegral A B]
    (U V : Subalgebra A B)
    [Module.Finite A U] [Module.Finite A V]
    [Algebra.FormallyUnramified A U]
    [Algebra.FormallyUnramified A V] :
    U = V ↔ residueImage A B U = residueImage A B V := by
  rw [le_antisymm_iff, le_antisymm_iff]
  exact and_congr
    (formally_unramified_subalgebra A B U V)
    (formally_unramified_subalgebra A B V U)

/-- A finite formally unramified local algebra is generated by any integral
element whose residue generates the full residue-field extension. -/
theorem adjoin_formally_residue
    [Module.Finite A B] [Algebra.IsIntegral A B]
    [Algebra.FormallyUnramified A B]
    (a : B) (ha : IsIntegral A a)
    [Algebra.FormallyUnramified A (Algebra.adjoin A ({a} : Set B))]
    (hresidue : Algebra.adjoin (ResidueField A) {residue B a} = ⊤) :
    Algebra.adjoin A ({a} : Set B) = ⊤ := by
  let U := Algebra.adjoin A ({a} : Set B)
  let T : Subalgebra A B := ⊤
  letI : Module.Finite A U :=
    Algebra.finite_adjoin_simple_of_isIntegral ha
  letI : Module.Finite A T :=
    Module.Finite.equiv
      (Subalgebra.topEquiv (R := A) (A := B)).symm.toLinearEquiv
  letI : Algebra.FormallyUnramified A T :=
    Algebra.FormallyUnramified.of_equiv
      (Subalgebra.topEquiv (R := A) (A := B)).symm
  apply (formally_subalgebra_image A B U T).2
  rw [show U = Algebra.adjoin A ({a} : Set B) from rfl,
    residue_adjoin_singleton, hresidue, show T = ⊤ from rfl,
    residueImage_top]

end ResidueCorrespondence

/-- The chosen lift in Proposition 7.50 respects containment of finite
separable intermediate residue fields. -/
theorem adjoin_intermediate_mono
    {A B : Type*} [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E F : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E]
    [FiniteDimensional (ResidueField A) F]
    [Algebra.IsSeparable (ResidueField A) F]
    (hEF : E ≤ F) :
    unramifiedAdjoinIntermediate A B E ≤
      unramifiedAdjoinIntermediate A B F := by
  let UE := unramifiedAdjoinIntermediate A B E
  let UF := unramifiedAdjoinIntermediate A B F
  letI : Module.Finite A UE :=
    unramified_adjoin_residue A B E
  letI : Module.Finite A UF :=
    unramified_adjoin_residue A B F
  letI : Algebra.FormallyUnramified A UE :=
    adjoin_intermediate_formally A B E
  letI : Algebra.FormallyUnramified A UF :=
    adjoin_intermediate_formally A B F
  apply (formally_unramified_subalgebra A B UE UF).2
  change
    residueImageAdjoin A B
        (unramifiedIntermediateLift A B E).generator ≤
      residueImageAdjoin A B
        (unramifiedIntermediateLift A B F).generator
  rw [unramified_adjoin_image A B E,
    unramified_adjoin_image A B F]
  exact hEF

/-- Proposition 7.50(a), for the chosen Hensel lifts: containment of finite
separable residue extensions is equivalent to containment of their lifted
unramified subalgebras. -/
theorem adjoin_intermediate_field
    {A B : Type*} [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E F : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E]
    [FiniteDimensional (ResidueField A) F]
    [Algebra.IsSeparable (ResidueField A) F] :
    unramifiedAdjoinIntermediate A B E ≤
        unramifiedAdjoinIntermediate A B F ↔
      E ≤ F := by
  constructor
  · intro hEF
    have hres := residueImage_mono A B hEF
    change
      residueImageAdjoin A B
          (unramifiedIntermediateLift A B E).generator ≤
        residueImageAdjoin A B
          (unramifiedIntermediateLift A B F).generator at hres
    rw [unramified_adjoin_image A B E,
      unramified_adjoin_image A B F] at hres
    exact hres
  · exact adjoin_intermediate_mono E F

/-- Equality version of the order correspondence in Proposition 7.50. -/
theorem adjoin_residue_intermediate
    {A B : Type*} [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E F : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E]
    [FiniteDimensional (ResidueField A) F]
    [Algebra.IsSeparable (ResidueField A) F] :
    unramifiedAdjoinIntermediate A B E =
        unramifiedAdjoinIntermediate A B F ↔
      E = F := by
  rw [le_antisymm_iff, le_antisymm_iff]
  exact and_congr
    (adjoin_intermediate_field E F)
    (adjoin_intermediate_field F E)

/-- Reducing the chosen Hensel lift recovers the original finite separable
residue intermediate field.  This is one inverse law in the correspondence
of Proposition 7.50. -/
theorem residue_intermediate_adjoin
    {A B : Type*} [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    residueIntermediateField A B
        (unramifiedAdjoinIntermediate A B E) = E := by
  apply IntermediateField.toSubalgebra_injective
  rw [residue_intermediate_subalgebra]
  change
    residueImageAdjoin A B
      (unramifiedIntermediateLift A B E).generator =
        E.toSubalgebra
  exact unramified_adjoin_image A B E

/-- Proposition 7.50, uniqueness: a finite formally unramified subalgebra
with prescribed finite separable residue image is the chosen Hensel lift of
that image. -/
theorem adjoin_intermediate_image
    {A B : Type*} [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (U : Subalgebra A B) [Module.Finite A U]
    [Algebra.FormallyUnramified A U]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E]
    (hres : residueImage A B U = E.toSubalgebra) :
    U = unramifiedAdjoinIntermediate A B E := by
  let UE := unramifiedAdjoinIntermediate A B E
  letI : Module.Finite A UE :=
    unramified_adjoin_residue A B E
  letI : Algebra.FormallyUnramified A UE :=
    adjoin_intermediate_formally A B E
  apply (formally_subalgebra_image A B U UE).2
  rw [hres]
  change E.toSubalgebra = residueImageAdjoin A B
    (unramifiedIntermediateLift A B E).generator
  exact (unramified_adjoin_image A B E).symm

/-- Lifting the bundled residue intermediate field of a finite formally
unramified subalgebra recovers that subalgebra.  Together with
`residue_intermediate_adjoin`, this
is the second inverse law in Proposition 7.50's correspondence. -/
theorem unramified_adjoin_intermediate
    {A B : Type*} [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (U : Subalgebra A B) [Module.Finite A U]
    [Algebra.FormallyUnramified A U] :
    let E := residueIntermediateField A B U
    letI : Module.Finite (ResidueField A) E :=
      residue_intermediate_field A B U
    letI : Algebra.IsSeparable (ResidueField A) E :=
      residue_intermediate_separable A B U
    unramifiedAdjoinIntermediate A B E = U := by
  let E := residueIntermediateField A B U
  letI : Module.Finite (ResidueField A) E :=
    residue_intermediate_field A B U
  letI : Algebra.IsSeparable (ResidueField A) E :=
    residue_intermediate_separable A B U
  change unramifiedAdjoinIntermediate A B E = U
  symm
  apply adjoin_intermediate_image U E
  exact (residue_intermediate_subalgebra A B U).symm

/-- Finite formally unramified subalgebras in a fixed ambient local
integral algebra. -/
def FiniteFormallySubalgebra
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :=
  {U : Subalgebra A B //
    Module.Finite A U ∧ Algebra.FormallyUnramified A U}

/-- Finite separable intermediate fields of a fixed residue-field
extension. -/
def SeparableResidueIntermediate
    (A B : Type*) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] :=
  {E : IntermediateField (ResidueField A) (ResidueField B) //
    Module.Finite (ResidueField A) E ∧
      Algebra.IsSeparable (ResidueField A) E}

instance formallyUnramifiedSubalgebra
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    LE (FiniteFormallySubalgebra A B) :=
  ⟨fun U V ↦ U.1 ≤ V.1⟩

instance separableResidueIntermediate
    (A B : Type*) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] :
    LE (SeparableResidueIntermediate A B) :=
  ⟨fun E F ↦ E.1 ≤ F.1⟩

/-- Proposition 7.50 as an actual equivalence: finite formally unramified
valuation subalgebras in the fixed ambient extension correspond to finite
separable intermediate residue fields.  The two functions are reduction and
the chosen Hensel lift, and the inverse laws above make the result independent
of the choices used in the lift. -/
noncomputable def unramifiedSubalgebraIntermediate
    (A B : Type*) [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B] :
    FiniteFormallySubalgebra A B ≃
      SeparableResidueIntermediate A B where
  toFun U := by
    letI : Module.Finite A U.1 := U.2.1
    letI : Algebra.FormallyUnramified A U.1 := U.2.2
    exact ⟨residueIntermediateField A B U.1,
      residue_intermediate_field A B U.1,
      residue_intermediate_separable A B U.1⟩
  invFun E := by
    letI : Module.Finite (ResidueField A) E.1 := E.2.1
    letI : Algebra.IsSeparable (ResidueField A) E.1 := E.2.2
    exact ⟨unramifiedAdjoinIntermediate A B E.1,
      unramified_adjoin_residue A B E.1,
      adjoin_intermediate_formally A B E.1⟩
  left_inv U := by
    apply Subtype.ext
    letI : Module.Finite A U.1 := U.2.1
    letI : Algebra.FormallyUnramified A U.1 := U.2.2
    exact
      unramified_adjoin_intermediate U.1
  right_inv E := by
    apply Subtype.ext
    letI : Module.Finite (ResidueField A) E.1 := E.2.1
    letI : Algebra.IsSeparable (ResidueField A) E.1 := E.2.2
    exact
      residue_intermediate_adjoin E.1

/-- Order-isomorphism form of Proposition 7.50(a): the residue
correspondence preserves and reflects containment. -/
noncomputable def subalgebraIsoIntermediate
    (A B : Type*) [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B] :
    FiniteFormallySubalgebra A B ≃o
      SeparableResidueIntermediate A B where
  toEquiv := unramifiedSubalgebraIntermediate A B
  map_rel_iff' := by
    intro U V
    letI : Module.Finite A U.1 := U.2.1
    letI : Algebra.FormallyUnramified A U.1 := U.2.2
    letI : Module.Finite A V.1 := V.2.1
    letI : Algebra.FormallyUnramified A V.1 := V.2.2
    change residueIntermediateField A B U.1 ≤
        residueIntermediateField A B V.1 ↔ U.1 ≤ V.1
    constructor
    · intro hres
      apply (formally_unramified_subalgebra
        A B U.1 V.1).2
      rw [← residue_intermediate_subalgebra A B U.1,
        ← residue_intermediate_subalgebra A B V.1]
      exact hres
    · intro hUV x hx
      have hxU : x ∈ residueImage A B U.1 := by
        rw [← residue_intermediate_subalgebra A B U.1]
        exact hx
      have hxV := residueImage_mono A B hUV hxU
      rw [← residue_intermediate_subalgebra A B V.1] at hxV
      exact hxV

/-- Milne, Proposition 7.50, existence-and-uniqueness form: every finite
separable intermediate field of the ambient residue extension is realized by
a unique finite formally unramified subalgebra. -/
theorem unique_formally_subalgebra
    {A B : Type*} [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    ∃! U : Subalgebra A B,
      Module.Finite A U ∧ Algebra.FormallyUnramified A U ∧
        residueImage A B U = E.toSubalgebra := by
  refine ⟨unramifiedAdjoinIntermediate A B E,
    ⟨unramified_adjoin_residue A B E,
      adjoin_intermediate_formally A B E,
      ?_⟩, ?_⟩
  · simpa [residueImageAdjoin] using
      (unramified_adjoin_image A B E)
  · intro U hU
    letI : Module.Finite A U := hU.1
    letI : Algebra.FormallyUnramified A U := hU.2.1
    exact
      adjoin_intermediate_image
        U E hU.2.2

/-- Milne, Proposition 7.50(b), uniqueness up to isomorphism: finite
formally unramified Henselian DVR extensions with isomorphic residue-field
extensions are isomorphic over the base DVR. -/
theorem nonempty_alg_formally
    (A S T : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    [HenselianLocalRing A] [HenselianLocalRing S] [HenselianLocalRing T]
    [Algebra A S] [Algebra A T]
    [IsLocalHom (algebraMap A S)] [IsLocalHom (algebraMap A T)]
    [Module.Finite A S] [Module.Finite A T]
    [Module.IsTorsionFree A S] [Module.IsTorsionFree A T]
    [Algebra.IsIntegral A S] [Algebra.IsIntegral A T]
    [Algebra.FormallyUnramified A S]
    [Algebra.FormallyUnramified A T]
    [FiniteDimensional (ResidueField A) (ResidueField S)]
    [FiniteDimensional (ResidueField A) (ResidueField T)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField S)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField T)]
    (e : ResidueField S ≃ₐ[ResidueField A] ResidueField T) :
    Nonempty (S ≃ₐ[A] T) := by
  let ES : IntermediateField (ResidueField A) (ResidueField S) := ⊤
  let d := unramifiedIntermediateLift A S ES
  let f : A[X] := d.polynomial
  let a : S := d.generator
  have hadjoinS : Algebra.adjoin A ({a} : Set S) = ⊤ := by
    letI : Algebra.FormallyUnramified A (Algebra.adjoin A ({a} : Set S)) :=
      d.adjoin_formallyUnramified
    apply adjoin_formally_residue
      A S a d.generator_integral
    change Algebra.adjoin (ResidueField A) {residue S d.generator} = ⊤
    rw [d.generator_residue]
    simpa [ES] using d.residue_adjoin_eq
  let a₀ : ResidueField T := e d.residueGenerator
  have ha₀root : ((f.map (residue A)).map
      (algebraMap (ResidueField A) (ResidueField T))).IsRoot a₀ := by
    rw [show f = d.polynomial from rfl, d.polynomial_reduction]
    have h := Polynomial.IsRoot.map (f := e.toRingHom)
      d.residue_generator_root
    have hcomp : e.toRingHom.comp
        (algebraMap (ResidueField A) (ResidueField S)) =
        algebraMap (ResidueField A) (ResidueField T) := by
      ext x
      exact e.commutes x
    rw [← hcomp, ← Polynomial.map_map]
    exact h
  have hfsep : (f.map (residue A)).Separable := by
    rw [show f = d.polynomial from rfl, d.polynomial_reduction]
    exact d.residuePolynomial_separable
  obtain ⟨b, hbroot, hbresidue⟩ :=
    monic_separable_reduction A T f
      d.polynomial_monic hfsep a₀ ha₀root
  have hbeval : aeval b f = 0 := by
    simpa [Polynomial.IsRoot.def, aeval_def] using hbroot
  have hbIntegral : IsIntegral A b := ⟨f, d.polynomial_monic, hbeval⟩
  have hfirr : Irreducible f := by
    change Irreducible d.polynomial
    rw [← d.generator_minpoly]
    exact minpoly.irreducible d.generator_integral
  have hbminpoly : minpoly A b = f := by
    have hdvd : minpoly A b ∣ f :=
      minpoly.isIntegrallyClosed_dvd hbIntegral hbeval
    exact Polynomial.eq_of_monic_of_associated
      (minpoly.monic hbIntegral) d.polynomial_monic
      ((minpoly.irreducible hbIntegral).associated_of_dvd hfirr hdvd)
  have ha₀adjoin :
      Algebra.adjoin (ResidueField A) {a₀} = ⊤ := by
    have hmapped := congrArg
      (fun U : Subalgebra (ResidueField A) (ResidueField S) ↦
        U.map e.toAlgHom) d.residue_adjoin_eq
    have hrange : e.toAlgHom.range = ⊤ :=
      (AlgHom.range_eq_top e.toAlgHom).2 e.surjective
    change (Algebra.adjoin (ResidueField A) {d.residueGenerator}).map
        e.toAlgHom = ES.toSubalgebra.map e.toAlgHom at hmapped
    have hES : ES.toSubalgebra = ⊤ := by simp [ES]
    rw [AlgHom.map_adjoin_singleton, hES, Algebra.map_top, hrange] at hmapped
    simpa [a₀] using hmapped
  have hadjoinT : Algebra.adjoin A ({b} : Set T) = ⊤ := by
    have hfred : Irreducible (f.map (residue A)) := by
      rw [show f = d.polynomial from rfl, d.polynomial_reduction]
      exact d.residuePolynomial_irreducible
    letI : Algebra.FormallyUnramified A (Algebra.adjoin A ({b} : Set T)) :=
      adjoin_separable_minpoly
        A T f b d.polynomial_monic hfred hfsep hbIntegral hbminpoly
    apply adjoin_formally_residue
      A T b hbIntegral
    rwa [hbresidue]
  let hS : IsAdjoinRoot S f := by
    change IsAdjoinRoot S d.polynomial
    rw [← d.generator_minpoly]
    exact IsAdjoinRoot.mkOfAdjoinEqTop d.generator_integral hadjoinS
  let hT : IsAdjoinRoot T f := by
    change IsAdjoinRoot T d.polynomial
    rw [← show minpoly A b = d.polynomial from hbminpoly]
    exact IsAdjoinRoot.mkOfAdjoinEqTop hbIntegral hadjoinT
  exact ⟨hS.algEquiv hT⟩

/-- Over a finite residue field, equality of residue degrees is enough for
the uniqueness statement in Proposition 7.50: finite fields of the same
degree are isomorphic over the base residue field. -/
theorem nonempty_formally_finrank
    (A S T : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    [HenselianLocalRing A] [HenselianLocalRing S] [HenselianLocalRing T]
    [Algebra A S] [Algebra A T]
    [IsLocalHom (algebraMap A S)] [IsLocalHom (algebraMap A T)]
    [Module.Finite A S] [Module.Finite A T]
    [Module.IsTorsionFree A S] [Module.IsTorsionFree A T]
    [Algebra.IsIntegral A S] [Algebra.IsIntegral A T]
    [Algebra.FormallyUnramified A S]
    [Algebra.FormallyUnramified A T]
    [FiniteDimensional (ResidueField A) (ResidueField S)]
    [FiniteDimensional (ResidueField A) (ResidueField T)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField S)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField T)]
    [Finite (ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hdegree : Module.finrank (ResidueField A) (ResidueField S) =
      Module.finrank (ResidueField A) (ResidueField T)) :
    Nonempty (S ≃ₐ[A] T) := by
  let n := Module.finrank (ResidueField A) (ResidueField S)
  letI : NeZero n := ⟨Module.finrank_pos.ne'⟩
  let eS := FiniteField.algEquivExtension (ResidueField A) p n
    (ResidueField S) rfl
  let eT := FiniteField.algEquivExtension (ResidueField A) p n
    (ResidueField T) hdegree.symm
  exact nonempty_alg_formally
    A S T (eS.trans eT.symm)

/-- Proposition 7.50(b) on fraction fields: an isomorphism of the finite
unramified valuation rings extends to an isomorphism of their local fields. -/
theorem nonempty_fraction_formally
    (A S T K L M : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    [HenselianLocalRing A] [HenselianLocalRing S] [HenselianLocalRing T]
    [Algebra A S] [Algebra A T]
    [IsLocalHom (algebraMap A S)] [IsLocalHom (algebraMap A T)]
    [Module.Finite A S] [Module.Finite A T]
    [Module.IsTorsionFree A S] [Module.IsTorsionFree A T]
    [Algebra.IsIntegral A S] [Algebra.IsIntegral A T]
    [Algebra.FormallyUnramified A S]
    [Algebra.FormallyUnramified A T]
    [FiniteDimensional (ResidueField A) (ResidueField S)]
    [FiniteDimensional (ResidueField A) (ResidueField T)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField S)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField T)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Field M] [Algebra T M] [IsFractionRing T M]
    [Algebra A L] [Algebra A M]
    [IsScalarTower A S L] [IsScalarTower A T M]
    [Algebra K L] [Algebra K M]
    [IsScalarTower A K L] [IsScalarTower A K M]
    (e : ResidueField S ≃ₐ[ResidueField A] ResidueField T) :
    Nonempty (L ≃ₐ[K] M) := by
  obtain ⟨eST⟩ :=
    nonempty_alg_formally
      A S T e
  exact ⟨IsFractionRing.fieldEquivOfAlgEquiv K L M eST⟩

/-- Milne, Proposition 7.50(b), converse direction: if the residue extension
of a finite formally unramified local extension is Galois, then the extension
of fraction fields is Galois. -/
theorem fraction_formally_residue
    (A S K L : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing S] [IsDomain S]
    [HenselianLocalRing A] [HenselianLocalRing S]
    [Algebra A S] [IsLocalHom (algebraMap A S)]
    [Module.Finite A S] [Module.IsTorsionFree A S]
    [Algebra.IsIntegral A S] [Algebra.FormallyUnramified A S]
    [FiniteDimensional (ResidueField A) (ResidueField S)]
    [IsGalois (ResidueField A) (ResidueField S)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra A L] [Algebra K L]
    [IsScalarTower A S L] [IsScalarTower A K L] :
    IsGalois K L := by
  classical
  let E : IntermediateField (ResidueField A) (ResidueField S) := ⊤
  let d := unramifiedIntermediateLift A S E
  let f : A[X] := d.polynomial
  let a : S := d.generator
  have hadjoinS : Algebra.adjoin A ({a} : Set S) = ⊤ := by
    letI : Algebra.FormallyUnramified A (Algebra.adjoin A ({a} : Set S)) :=
      d.adjoin_formallyUnramified
    apply adjoin_formally_residue
      A S a d.generator_integral
    change Algebra.adjoin (ResidueField A) {residue S d.generator} = ⊤
    rw [d.generator_residue]
    simpa [E] using d.residue_adjoin_eq
  let hS : IsAdjoinRoot S f := by
    change IsAdjoinRoot S d.polynomial
    rw [← d.generator_minpoly]
    exact IsAdjoinRoot.mkOfAdjoinEqTop d.generator_integral hadjoinS
  let hSmonic : IsAdjoinRootMonic S f :=
    { __ := hS
      monic := d.polynomial_monic }
  have hfsep : (f.map (residue A)).Separable := by
    change (d.polynomial.map (residue A)).Separable
    rw [d.polynomial_reduction]
    exact d.residuePolynomial_separable
  have hfred : Irreducible (f.map (residue A)) := by
    change Irreducible (d.polynomial.map (residue A))
    rw [d.polynomial_reduction]
    exact d.residuePolynomial_irreducible
  have hfirr : Irreducible f :=
    d.polynomial_monic.irreducible_of_irreducible_map (residue A) f hfred
  have hresMinpoly :
      d.residuePolynomial = minpoly (ResidueField A) d.residueGenerator := by
    exact minpoly.eq_of_irreducible_of_monic
      d.residuePolynomial_irreducible (by
        simpa [Polynomial.IsRoot.def, aeval_def] using
          d.residue_generator_root)
        d.residuePolynomial_monic
  have hresSplits :
      ((f.map (residue A)).map
        (algebraMap (ResidueField A) (ResidueField S))).Splits := by
    rw [show f.map (residue A) = d.residuePolynomial from d.polynomial_reduction,
      hresMinpoly]
    exact IsGalois.splits (ResidueField A) d.residueGenerator
  let Rts := (f.map (residue A)).rootSet (ResidueField S)
  have root_isRoot (y : Rts) :
      ((f.map (residue A)).map
        (algebraMap (ResidueField A) (ResidueField S))).IsRoot y := by
    rw [Polynomial.IsRoot.def, eval_map]
    simpa [aeval_def] using (Polynomial.mem_rootSet'.mp y.property).2
  choose beta hbetaRoot hbetaResidue using fun y : Rts ↦
    monic_separable_reduction A S f
      d.polynomial_monic hfsep y (root_isRoot y)
  have hbetaInjective : Function.Injective beta := by
    intro y z hyz
    apply Subtype.ext
    have hres := congrArg (residue S) hyz
    rw [hbetaResidue y, hbetaResidue z] at hres
    exact hres
  let roots : Finset S := Finset.univ.image beta
  have hrootsCard : roots.card = f.natDegree := by
    calc
      roots.card = Fintype.card Rts := by
        rw [Finset.card_image_of_injective _ hbetaInjective,
          Finset.card_univ]
      _ = (f.map (residue A)).natDegree :=
        Polynomial.card_rootSet_eq_natDegree hfsep hresSplits
      _ = f.natDegree := d.polynomial_monic.natDegree_map (residue A)
  let fS : S[X] := f.map (algebraMap A S)
  have hrootsSub : roots ⊆ fS.roots.toFinset := by
    intro x hx
    dsimp only [roots] at hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [Multiset.mem_toFinset,
      Polynomial.mem_roots (d.polynomial_monic.map (algebraMap A S)).ne_zero]
    exact hbetaRoot y
  have hrootsLower : f.natDegree ≤ fS.roots.card := by
    calc
      f.natDegree = roots.card := hrootsCard.symm
      _ ≤ fS.roots.toFinset.card := Finset.card_le_card hrootsSub
      _ ≤ fS.roots.card := Multiset.toFinset_card_le _
  have hfSsplits : fS.Splits := by
    have hdegFS : fS.natDegree = f.natDegree := by
      exact d.polynomial_monic.natDegree_map (algebraMap A S)
    rw [Polynomial.splits_iff_card_roots]
    apply Nat.le_antisymm (Polynomial.card_roots' fS)
    rw [hdegFS]
    exact hrootsLower
  letI : Module.Finite K L :=
    Module.Finite.of_isLocalization A S (nonZeroDivisors A)
  letI : Algebra.FormallyUnramified S L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors S)
  letI : Algebra.FormallyUnramified A L :=
    Algebra.FormallyUnramified.comp A S L
  letI : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_restrictScalars A K L
  letI : Algebra.IsSeparable K L :=
    Algebra.FormallyUnramified.isSeparable K L
  have hLdegree : Module.finrank K L = f.natDegree := by
    calc
      Module.finrank K L = Module.finrank A S :=
        Algebra.IsAlgebraic.finrank_of_isFractionRing A K S L
      _ = f.natDegree := hSmonic.finrank
  let fK : K[X] := f.map (algebraMap A K)
  have hfKirred : Irreducible fK :=
    (d.polynomial_monic.irreducible_iff_irreducible_map_fraction_map).mp hfirr
  let alphaL : L := algebraMap S L a
  have halphaRoot : (f.map (algebraMap A S)).IsRoot a :=
    d.generator_isRoot
  have hmaps :
      (algebraMap K L).comp (algebraMap A K) =
        (algebraMap S L).comp (algebraMap A S) :=
    (IsScalarTower.algebraMap_eq A K L).symm.trans
      (IsScalarTower.algebraMap_eq A S L)
  have halphaLRoot : aeval alphaL fK = 0 := by
    rw [Polynomial.IsRoot.def, eval_map] at halphaRoot
    have hx := congrArg (algebraMap S L) halphaRoot
    rw [map_zero] at hx
    simpa [fK, alphaL] using
      (map_aeval_eq_aeval_map hmaps f a).symm.trans hx
  have hminpoly : minpoly K alphaL = fK :=
    (minpoly.eq_of_irreducible_of_monic hfKirred halphaLRoot
      (d.polynomial_monic.map (algebraMap A K))).symm
  have hprimitive : IntermediateField.adjoin K ({alphaL} : Set L) = ⊤ := by
    apply (Field.primitive_element_iff_minpoly_natDegree_eq K alphaL).mpr
    rw [hminpoly, show fK.natDegree = f.natDegree by
      exact d.polynomial_monic.natDegree_map (algebraMap A K), hLdegree]
  have hsplit : (fK.map (algebraMap K L)).Splits := by
    rw [map_map, hmaps]
    simpa [fS, fK, map_map] using hfSsplits.map (algebraMap S L)
  have hnormal : Normal K L := by
    rw [normal_iff]
    intro x
    refine ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
    apply IntermediateField.splits_of_mem_adjoin
      (F := K) (K := L) (L := L) (S := ({alphaL} : Set L))
    · intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨Algebra.IsIntegral.isIntegral alphaL, by
        simpa [hminpoly] using hsplit⟩
    · rw [hprimitive]
      exact IntermediateField.mem_top
  exact isGalois_iff.mpr ⟨inferInstance, hnormal⟩

/-- Milne, Proposition 7.50, unramifiedness criterion in the arithmetic
Dedekind-domain setting: a prime is unramified exactly when its ramification
index is one. -/
theorem unramified_ramification_idx
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S]
    (p : Ideal R) (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hP : P ≠ ⊥) :
    Algebra.IsUnramifiedAt R P ↔ p.ramificationIdx P = 1 := by
  rw [Ideal.LiesOver.over (p := p) (P := P)]
  exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain
    (R := R) (S := S) (p := P) hP

/-- An unramified prime induces a finite separable extension of residue
fields.  This is one direction of the residue-field correspondence in
Milne's Proposition 7.50. -/
theorem residue_separable_unramified
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S]
    (p : Ideal R) (P : Ideal S) [p.IsPrime] [P.IsPrime] [P.LiesOver p]
    [Algebra.IsUnramifiedAt R P] :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Module.Finite p.ResidueField P.ResidueField ∧
      Algebra.IsSeparable p.ResidueField P.ResidueField := by
  exact ⟨inferInstance, inferInstance⟩

/-- Milne, Proposition 7.50, degree identity: for an unramified finite local
extension, the field degree equals the inertia degree. -/
theorem finrank_inertia_deg
    {R S K L : Type*} [CommRing R] [CommRing S]
    [Field K] [Field L] [Algebra R S]
    [IsDedekindDomain R] [IsDedekindDomain S] [IsLocalRing S]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [Algebra.EssFiniteType R S]
    (p : Ideal R) [p.IsMaximal]
    [(maximalIdeal S).LiesOver p]
    [Algebra.IsUnramifiedAt R (maximalIdeal S)]
    (hp : p ≠ ⊥) (hP : maximalIdeal S ≠ ⊥) :
    Module.finrank K L = p.inertiaDeg (maximalIdeal S) := by
  have he : p.ramificationIdx (maximalIdeal S) = 1 := by
    rw [Ideal.LiesOver.over (p := p) (P := maximalIdeal S)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      (R := R) (S := S) hP
  have hef :=
    Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
      (R := R) S K L hp
  rw [he, one_mul] at hef
  exact hef.symm

/-- Milne, Proposition 7.50, the numerical heart of the correspondence:
the degree of an unramified finite local extension equals the degree of the
induced residue-field extension. -/
theorem finrank_unramified_local
    {R S K L : Type*} [CommRing R] [CommRing S]
    [Field K] [Field L] [Algebra R S]
    [IsDedekindDomain R] [IsDedekindDomain S] [IsLocalRing S]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [Algebra.EssFiniteType R S]
    (p : Ideal R) [p.IsMaximal]
    [(maximalIdeal S).LiesOver p]
    [Algebra.IsUnramifiedAt R (maximalIdeal S)]
    (hp : p ≠ ⊥) (hP : maximalIdeal S ≠ ⊥) :
    Module.finrank K L =
      Module.finrank (R ⧸ p) (S ⧸ maximalIdeal S) := by
  rw [← Ideal.inertiaDeg_algebraMap]
  exact finrank_inertia_deg p hp hP

/-- In a local extension the unique prime above the maximal ideal is fixed by
the whole Galois group.  This is the decomposition-group part of Milne,
Proposition 7.50(b). -/
theorem stabilizer_maximal_top
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain S] [IsLocalRing S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsMaximal] [(maximalIdeal S).LiesOver p]
    (hp : p ≠ ⊥) :
    MulAction.stabilizer G (maximalIdeal S) = ⊤ := by
  apply top_unique
  intro σ _
  rw [MulAction.mem_stabilizer_iff]
  let P : p.primesOver S :=
    ⟨maximalIdeal S, inferInstance, inferInstance⟩
  have hmem : σ • (maximalIdeal S) ∈ p.primesOver S := by
    simpa only [Ideal.coe_smul_primesOver] using (σ • P).property
  rw [IsLocalRing.primesOver_eq S hp] at hmem
  exact Set.mem_singleton_iff.mp hmem

/-- For an unramified local Galois extension, the inertia subgroup is
trivial. -/
theorem inertia_maximal_unramified
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain R] [IsDedekindDomain S]
    [IsLocalRing S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsMaximal] [(maximalIdeal S).LiesOver p]
    [Algebra.IsUnramifiedAt R (maximalIdeal S)]
    (hp : p ≠ ⊥) (hP : maximalIdeal S ≠ ⊥) :
    (maximalIdeal S).inertia G = ⊥ := by
  letI := Localization.AtPrime.algebraOfLiesOver p (maximalIdeal S)
  have he : p.ramificationIdx (maximalIdeal S) = 1 :=
    by
      rw [Ideal.LiesOver.over (p := p) (P := maximalIdeal S)]
      exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
        (R := R) (S := S) hP
  apply Subgroup.card_eq_one.mp
  rw [Ideal.card_inertia_eq_ramificationIdxIn p hp (maximalIdeal S),
    Ideal.ramificationIdxIn_eq_ramificationIdx p (maximalIdeal S) G]
  exact he

/-- Milne, Proposition 7.50(b), forward direction: the residue-field
extension of a finite unramified local Galois extension is Galois. -/
theorem residue_unramified_local
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain R] [IsDedekindDomain S]
    [IsLocalRing S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsMaximal] [(maximalIdeal S).LiesOver p]
    [Algebra.IsUnramifiedAt R (maximalIdeal S)] :
    IsGalois (R ⧸ p) (S ⧸ maximalIdeal S) := by
  letI := Localization.AtPrime.algebraOfLiesOver p (maximalIdeal S)
  letI : Algebra.IsSeparable (R ⧸ p) (S ⧸ maximalIdeal S) := inferInstance
  exact { __ := Ideal.Quotient.normal (A := R) G p (maximalIdeal S) }

/-- Milne, Proposition 7.50(b): for a finite unramified local Galois
extension, reduction induces the canonical isomorphism from its Galois group
to the Galois group of the residue-field extension. -/
noncomputable def galois_unramified_local
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain R] [IsDedekindDomain S]
    [IsLocalRing S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsMaximal] [(maximalIdeal S).LiesOver p]
    [Algebra.IsUnramifiedAt R (maximalIdeal S)]
    (hp : p ≠ ⊥) (hP : maximalIdeal S ≠ ⊥) :
    G ≃* Gal((S ⧸ maximalIdeal S)/(R ⧸ p)) := by
  let P := maximalIdeal S
  have hD : MulAction.stabilizer G P = ⊤ :=
    stabilizer_maximal_top p hp
  have hI : P.inertia G = ⊥ :=
    inertia_maximal_unramified p hp hP
  let decompositionEquiv : G ≃* MulAction.stabilizer G P :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hD.symm)
  have hN :
      (⊥ : Subgroup (MulAction.stabilizer G P)) =
        (P.inertia G).subgroupOf (MulAction.stabilizer G P) := by
    simp [hI]
  exact decompositionEquiv.trans <|
    QuotientGroup.quotientBot.symm |>.trans <|
      (QuotientGroup.quotientMulEquivOfEq hN).trans <|
        Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P

/-- Milne, Proposition 7.50(a), forward containment direction: a prime in a
larger ring lying over an intermediate prime induces the canonical embedding
of their residue fields. -/
noncomputable def fieldTowerEmbedding
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (P : Ideal S) (Q : Ideal T) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    P.ResidueField →ₐ[R] Q.ResidueField :=
  Ideal.ResidueField.mapₐ P Q (IsScalarTower.toAlgHom R S T)
    (Ideal.LiesOver.over (p := P) (P := Q))

/-- The residue-field map induced by containment in a tower is injective. -/
theorem residue_tower_injective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (P : Ideal S) (Q : Ideal T) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    Function.Injective (fieldTowerEmbedding (R := R) P Q) :=
  RingHom.injective _

/-- The quotient presentation of the residue-field embedding in a tower.
Unlike `fieldTowerEmbedding`, this map visibly respects scalars from
the residue field at the bottom of the tower. -/
noncomputable def residueTowerEmbedding
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) (P : Ideal S) (Q : Ideal T)
    [p.IsPrime] [P.IsPrime] [Q.IsPrime] [P.IsMaximal] [Q.IsMaximal]
    [P.LiesOver p] [Q.LiesOver P] [Q.LiesOver p] :
    S ⧸ P →ₐ[R ⧸ p] T ⧸ Q :=
  { Ideal.quotientMap Q (algebraMap S T)
      (Ideal.LiesOver.over (p := P) (P := Q)).le with
    commutes' := by
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [Ideal.Quotient.algebraMap_mk_of_liesOver]
      change Ideal.Quotient.mk Q (algebraMap S T (algebraMap R S r)) =
        Ideal.Quotient.mk Q (algebraMap R T r)
      rw [IsScalarTower.algebraMap_apply R S T] }

/-- The quotient-level residue-field map induced by a tower is injective. -/
theorem tower_embedding_injective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) (P : Ideal S) (Q : Ideal T)
    [p.IsPrime] [P.IsPrime] [Q.IsPrime] [P.IsMaximal] [Q.IsMaximal]
    [P.LiesOver p] [Q.LiesOver P] [Q.LiesOver p] :
    Function.Injective (residueTowerEmbedding p P Q) :=
  RingHom.injective _

/-- In a finite tower of fields, equality of the two degrees over the bottom
field forces the upper algebra map to be surjective. -/
theorem algebra_surjective_finrank
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [FiniteDimensional L M]
    (h : Module.finrank K L = Module.finrank K M) :
    Function.Surjective (algebraMap L M) := by
  have htower := Module.finrank_mul_finrank K L M
  have hmul : Module.finrank K L * Module.finrank L M =
      Module.finrank K L * 1 := by
    rw [mul_one, htower, h]
  have hLM : Module.finrank L M = 1 :=
    Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := K) (M := L)) hmul
  intro x
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (K := L) (1 : M) one_ne_zero).mp hLM x
  refine ⟨c, ?_⟩
  simpa [Algebra.smul_def] using hc

/-- Milne, Proposition 7.50(a), containment-reflection direction.  Suppose
two finite unramified local extensions are nested.  If the induced embedding
of their residue fields is onto, then the extension of fraction fields
between them has degree one, hence its algebra map is onto.

This proves the injectivity part of the residue-field correspondence for
nested extensions. -/
theorem algebra_unramified_residue
    {R S T K L M : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Field K] [Field L] [Field M]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsDedekindDomain R] [IsDedekindDomain S] [IsDedekindDomain T]
    [IsLocalRing S] [IsLocalRing T]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra T M] [IsFractionRing T M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra R L] [Algebra R M]
    [IsScalarTower R S L] [IsScalarTower R T M]
    [IsScalarTower R K L] [IsScalarTower R K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [Module.Finite R S] [Module.Finite R T]
    [Algebra.EssFiniteType R S] [Algebra.EssFiniteType R T]
    (p : Ideal R) [p.IsMaximal]
    [(maximalIdeal S).LiesOver p]
    [(maximalIdeal T).LiesOver p]
    [(maximalIdeal T).LiesOver (maximalIdeal S)]
    [Algebra.IsUnramifiedAt R (maximalIdeal S)]
    [Algebra.IsUnramifiedAt R (maximalIdeal T)]
    (hp : p ≠ ⊥) (hS : maximalIdeal S ≠ ⊥)
    (hT : maximalIdeal T ≠ ⊥)
    (hres : Function.Surjective
      (residueTowerEmbedding p (maximalIdeal S) (maximalIdeal T))) :
    Function.Surjective (algebraMap L M) := by
  have hSdeg := finrank_unramified_local
    (R := R) (S := S) (K := K) (L := L) p hp hS
  have hTdeg := finrank_unramified_local
    (R := R) (S := T) (K := K) (L := M) p hp hT
  let f := residueTowerEmbedding p (maximalIdeal S) (maximalIdeal T)
  let e : (S ⧸ maximalIdeal S) ≃ₗ[R ⧸ p] (T ⧸ maximalIdeal T) :=
    LinearEquiv.ofBijective f.toLinearMap
      ⟨tower_embedding_injective p (maximalIdeal S)
        (maximalIdeal T), hres⟩
  have hfields : Module.finrank K L = Module.finrank K M := by
    rw [hSdeg, hTdeg]
    exact e.finrank_eq
  exact algebra_surjective_finrank hfields

/-- Unramifiedness descends from an extension to an intermediate Dedekind
domain.  This is the algebraic containment direction used in Milne's
Corollaries 7.51 and 7.52. -/
theorem unramified_intermediate
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.EssFiniteType R S] [Algebra.EssFiniteType R T]
    [IsDedekindDomain S] [IsDomain T] [Module.IsTorsionFree S T]
    (p : Ideal S) (P : Ideal T) [p.IsPrime] [P.IsPrime] [P.LiesOver p]
    [Algebra.IsUnramifiedAt R P] :
    Algebra.IsUnramifiedAt R p :=
  Algebra.IsUnramifiedAt.of_liesOver R p P

/-- The order-theoretic construction underlying Milne, Corollary 7.51.
Given a property of finite subextensions, take the compositum of every
finitely generated subextension having that property.  For local fields the
property is "unramified over the base field". -/
def maximalPropertyExtension
    {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]
    (P : IntermediateField K Omega -> Prop) : IntermediateField K Omega :=
  ⨆ E : {E : IntermediateField K Omega // E.FG ∧ P E}, E.1

/-- Every finite subextension having `P` is contained in the corresponding
maximal extension. -/
theorem maximal_property_extension
    {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]
    {P : IntermediateField K Omega -> Prop}
    (E : IntermediateField K Omega) (hEfg : E.FG) (hEP : P E) :
    E ≤ maximalPropertyExtension P :=
  le_iSup (fun F : {F : IntermediateField K Omega // F.FG ∧ P F} => F.1)
    ⟨E, hEfg, hEP⟩

/-- Corollary 7.51, finite-subextension characterization.  If `P` contains
the base field, is stable under composita, and descends to finite
subextensions, then the finitely generated subfields of the maximal
`P`-extension are exactly those satisfying `P`.

The key point is compactness: a finitely generated intermediate field lying
in the supremum of all `P`-fields already lies in the supremum of finitely
many of them. -/
theorem fg_property_extension
    {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]
    {P : IntermediateField K Omega -> Prop}
    (hbot : P ⊥)
    (hsup : ∀ {E F : IntermediateField K Omega}, P E -> P F -> P (E ⊔ F))
    (hdown : ∀ {E F : IntermediateField K Omega}, F ≤ E -> F.FG -> P E -> P F)
    (F : IntermediateField K Omega) (hFfg : F.FG) :
    F ≤ maximalPropertyExtension P ↔ P F := by
  constructor
  · intro hF
    obtain ⟨t, rfl⟩ := hFfg
    have hcompact : IsCompactElement (IntermediateField.adjoin K (t : Set Omega)) :=
      IntermediateField.adjoin_finite_isCompactElement t.finite_toSet
    obtain ⟨s, hs⟩ :=
      CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
        (α := IntermediateField K Omega) hcompact
        (fun E : {E : IntermediateField K Omega // E.FG ∧ P E} => E.1) hF
    classical
    have hfamily : ∀ u : Finset {E : IntermediateField K Omega // E.FG ∧ P E},
        P (⨆ E ∈ u, E.1) := by
      intro u
      induction u using Finset.induction_on with
      | empty => simpa using hbot
      | @insert E u hEu ih =>
          rw [Finset.iSup_insert]
          exact hsup E.property.2 ih
    exact hdown hs (IntermediateField.fg_adjoin_finset t) (hfamily s)
  · intro hF
    exact maximal_property_extension F hFfg hF

/-- Corollary 7.51 in its infinite-extension form: the maximal `P`-extension
contains an intermediate field exactly when every finitely generated
subextension of that field has property `P`. -/
theorem maximal_property_fg
    {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]
    {P : IntermediateField K Omega -> Prop}
    (hbot : P ⊥)
    (hsup : ∀ {E F : IntermediateField K Omega}, P E -> P F -> P (E ⊔ F))
    (hdown : ∀ {E F : IntermediateField K Omega}, F ≤ E -> F.FG -> P E -> P F)
    (E : IntermediateField K Omega) :
    E ≤ maximalPropertyExtension P ↔
      ∀ F : IntermediateField K Omega, F ≤ E -> F.FG -> P F := by
  constructor
  · intro hE F hFE hFfg
    exact (fg_property_extension hbot hsup hdown F hFfg).1
      (hFE.trans hE)
  · intro hlocal x hx
    let F : IntermediateField K Omega := IntermediateField.adjoin K {x}
    have hFfg : F.FG :=
      IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x)
    have hFle : F ≤ E := by
      apply IntermediateField.adjoin_le_iff.mpr
      simpa only [Set.singleton_subset_iff] using hx
    have hFP : P F := hlocal F hFle hFfg
    have hFmax : F ≤ maximalPropertyExtension P :=
      maximal_property_extension F hFfg hFP
    exact hFmax
      (IntermediateField.subset_adjoin K ({x} : Set Omega) (Set.mem_singleton x))

/-- The supremum construction is the greatest intermediate field whose
finitely generated subextensions all satisfy `P`. -/
theorem maximal_property_greatest
    {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]
    {P : IntermediateField K Omega -> Prop}
    (hbot : P ⊥)
    (hsup : ∀ {E F : IntermediateField K Omega}, P E -> P F -> P (E ⊔ F))
    (hdown : ∀ {E F : IntermediateField K Omega}, F ≤ E -> F.FG -> P E -> P F) :
    IsGreatest
      {E : IntermediateField K Omega |
        ∀ F : IntermediateField K Omega, F ≤ E -> F.FG -> P F}
      (maximalPropertyExtension P) := by
  constructor
  · exact (maximal_property_fg hbot hsup hdown
      (maximalPropertyExtension P)).1 le_rfl
  · intro E hE
    exact (maximal_property_fg hbot hsup hdown E).2 hE

/-- For a finite extension, membership in the maximal `P`-extension is
equivalent simply to property `P`. -/
theorem dimensional_maximal_property
    {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]
    {P : IntermediateField K Omega -> Prop}
    (hbot : P ⊥)
    (hsup : ∀ {E F : IntermediateField K Omega}, P E -> P F -> P (E ⊔ F))
    (hdown : ∀ {E F : IntermediateField K Omega}, F ≤ E -> F.FG -> P E -> P F)
    (F : IntermediateField K Omega) [FiniteDimensional K F] :
    F ≤ maximalPropertyExtension P ↔ P F :=
  fg_property_extension hbot hsup hdown F
    (IntermediateField.essFiniteType_iff.mp inferInstance)

/-- Milne, Corollary 7.52, the final algebraic-closure argument.  An
algebraic field extension in which every polynomial over the base splits is
an algebraic closure of the base.  Milne applies this after showing that
every residue polynomial lifts to a polynomial splitting in the algebraic
closure of the local field. -/
theorem algebraic_polynomials_split
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l]
    (hsplit : ∀ f : Polynomial k, (f.map (algebraMap k l)).Splits) :
    IsAlgClosure k l := by
  apply IsAlgClosure.of_splits
  intro f _ _
  exact hsplit f

end

end Submission.NumberTheory.Milne
