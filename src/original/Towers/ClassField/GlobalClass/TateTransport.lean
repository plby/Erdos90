import Towers.ClassField.GlobalClass.IdeleClassSmall
import Towers.ClassField.GlobalClass.CorestrictionSquare
import Towers.ClassField.GlobalClass.GaloisClosure
import Mathlib.Algebra.Module.Shrink

/-!
# Tate's degree-minus-two shift for the actual idèle-class representation

The implementation of Theorem II.3.11 is Type-0.  This file proves that a
small representation over `ULift ℤ` can be transported to a Type-0 integral
representation, transports `H¹`, `H²`, and Tate degree zero explicitly, and
applies the result to the idèle-class representation in Theorem VIII.4.8.
-/

namespace Towers.CField.GClass

open AddSubgroup CategoryTheory CategoryTheory.Limits Representation
open NumberField
open Towers.CField.Shifting
open Towers.CField.Ideles
open Towers.CField.CIdeles
open groupCohomology
open scoped BigOperators

noncomputable section

universe u

variable {G₀ : Type} {G : Type u}
  [Group G₀] [Group G]
  (A₀ : Rep ℤ G₀) (A : Rep (ULift.{u} ℤ) G)
  (eG : G₀ ≃* G) (eC : A₀ ≃+ A)
  (hρ : ∀ (g : G₀) (x : A₀),
    eC (A₀.ρ g x) = A.ρ (eG g) (eC x))

include hρ in
private theorem action_symm (g : G) (x : A) :
    eC.symm (A.ρ g x) = A₀.ρ (eG.symm g) (eC.symm x) := by
  apply eC.injective
  rw [eC.apply_symm_apply, hρ, eG.apply_symm_apply, eC.apply_symm_apply]

include hρ in
private def cocyclesOneForward
    (z : cocycles₁ A₀) : cocycles₁ A := by
  refine ⟨fun g ↦ eC (z (eG.symm g)), ?_⟩
  rw [mem_cocycles₁_iff]
  intro g h
  rw [eG.symm.map_mul, (mem_cocycles₁_iff z).1 z.2,
    map_add, hρ, eG.apply_symm_apply]

include hρ in
private def cocyclesOneBackward
    (z : cocycles₁ A) : cocycles₁ A₀ := by
  refine ⟨fun g ↦ eC.symm (z (eG g)), ?_⟩
  rw [mem_cocycles₁_iff]
  intro g h
  rw [eG.map_mul, (mem_cocycles₁_iff z).1 z.2,
    map_add, action_symm (A₀ := A₀) (A := A) eG eC hρ,
    eG.symm_apply_apply]

include hρ in
private noncomputable def cocyclesAddEquiv :
    cocycles₁ A₀ ≃+ cocycles₁ A where
  toFun := cocyclesOneForward A₀ A eG eC hρ
  invFun := cocyclesOneBackward A₀ A eG eC hρ
  left_inv z := by
    apply cocycles₁_ext
    intro g
    simp [cocyclesOneForward, cocyclesOneBackward]
  right_inv z := by
    apply cocycles₁_ext
    intro g
    simp [cocyclesOneForward, cocyclesOneBackward]
  map_add' x y := by
    apply cocycles₁_ext
    intro g
    exact eC.map_add _ _

include hρ in
private theorem cocycles_add_boundary
    (z : cocycles₁ A₀) :
    ⇑(cocyclesAddEquiv A₀ A eG eC hρ z) ∈ coboundaries₁ A ↔
      ⇑z ∈ coboundaries₁ A₀ := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨eC.symm x, ?_⟩
    apply funext
    intro g
    apply eC.injective
    have hg := congrFun hx (eG g)
    simpa [cocyclesAddEquiv, cocyclesOneForward, hρ] using hg
  · rintro ⟨x, hx⟩
    refine ⟨eC x, ?_⟩
    apply funext
    intro g
    have hg := congrFun hx (eG.symm g)
    simpa [cocyclesAddEquiv, cocyclesOneForward, hρ] using
      congrArg eC hg

private theorem H1π_surjective (B : Rep (ULift.{u} ℤ) G) :
    Function.Surjective (H1π B) :=
  (ModuleCat.epi_iff_surjective (H1π B)).1 inferInstance

private theorem H1π_surjective_zero (B : Rep ℤ G₀) :
    Function.Surjective (H1π B) :=
  (ModuleCat.epi_iff_surjective (H1π B)).1 inferInstance

private noncomputable def cohomologyOneForward : H1 A₀ → H1 A :=
  fun x ↦ H1π A
    (cocyclesAddEquiv A₀ A eG eC hρ
      (Function.surjInv (H1π_surjective_zero A₀) x))

private noncomputable def cohomologyOneBackward : H1 A → H1 A₀ :=
  fun x ↦ H1π A₀
    ((cocyclesAddEquiv A₀ A eG eC hρ).symm
      (Function.surjInv (H1π_surjective A) x))

include hρ in
private theorem cohomology_forward_1π (z : cocycles₁ A₀) :
    cohomologyOneForward A₀ A eG eC hρ (H1π A₀ z) =
      H1π A (cocyclesAddEquiv A₀ A eG eC hρ z) := by
  unfold cohomologyOneForward
  rw [H1π_eq_iff]
  suffices h : ⇑(cocyclesAddEquiv A₀ A eG eC hρ
      (Function.surjInv (H1π_surjective_zero A₀) (H1π A₀ z) - z)) ∈
        coboundaries₁ A by
    simpa only [map_sub, cocycles₁.val_eq_coe] using h
  · apply (cocycles_add_boundary A₀ A eG eC hρ _).2
    apply (H1π_eq_iff _ _).1
    simp [Function.surjInv_eq]

include hρ in
private theorem cohomology_backward_1π (z : cocycles₁ A) :
    cohomologyOneBackward A₀ A eG eC hρ (H1π A z) =
      H1π A₀ ((cocyclesAddEquiv A₀ A eG eC hρ).symm z) := by
  unfold cohomologyOneBackward
  rw [H1π_eq_iff]
  suffices h : ⇑((cocyclesAddEquiv A₀ A eG eC hρ).symm
      (Function.surjInv (H1π_surjective A) (H1π A z) - z)) ∈
        coboundaries₁ A₀ by
    simpa only [map_sub, cocycles₁.val_eq_coe] using h
  · apply (cocycles_add_boundary A₀ A eG eC hρ _).1
    simpa only [AddEquiv.apply_symm_apply] using
      (H1π_eq_iff
        (Function.surjInv (H1π_surjective A) (H1π A z)) z).1
        (by simp [Function.surjInv_eq])

include hρ in
private noncomputable def cohomologyAddEquiv : H1 A₀ ≃+ H1 A := by
  let f : H1 A₀ →+ H1 A :=
    { toFun := cohomologyOneForward A₀ A eG eC hρ
      map_zero' := by
        simpa using cohomology_forward_1π A₀ A eG eC hρ
          (0 : cocycles₁ A₀)
      map_add' := by
        intro x y
        induction x using H1_induction_on with
        | _ x =>
          induction y using H1_induction_on with
          | _ y =>
            rw [cohomology_forward_1π A₀ A eG eC hρ x,
              cohomology_forward_1π A₀ A eG eC hρ y]
            simpa only [map_add] using
              cohomology_forward_1π A₀ A eG eC hρ (x + y) }
  let g : H1 A →+ H1 A₀ :=
    { toFun := cohomologyOneBackward A₀ A eG eC hρ
      map_zero' := by
        simpa using cohomology_backward_1π A₀ A eG eC hρ
          (0 : cocycles₁ A)
      map_add' := by
        intro x y
        induction x using H1_induction_on with
        | _ x =>
          induction y using H1_induction_on with
          | _ y =>
            rw [cohomology_backward_1π A₀ A eG eC hρ x,
              cohomology_backward_1π A₀ A eG eC hρ y]
            simpa only [map_add] using
              cohomology_backward_1π A₀ A eG eC hρ (x + y) }
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        induction x using H1_induction_on with
        | _ x =>
          rw [show f (H1π A₀ x) = H1π A
              (cocyclesAddEquiv A₀ A eG eC hρ x) by
                exact cohomology_forward_1π A₀ A eG eC hρ x,
            show g (H1π A
              (cocyclesAddEquiv A₀ A eG eC hρ x)) = H1π A₀ x by
                simpa using cohomology_backward_1π A₀ A eG eC hρ
                  (cocyclesAddEquiv A₀ A eG eC hρ x)]
      right_inv := by
        intro x
        induction x using H1_induction_on with
        | _ x =>
          rw [show g (H1π A x) = H1π A₀
              ((cocyclesAddEquiv A₀ A eG eC hρ).symm x) by
                exact cohomology_backward_1π A₀ A eG eC hρ x,
            show f (H1π A₀
              ((cocyclesAddEquiv A₀ A eG eC hρ).symm x)) = H1π A x by
                simpa using cohomology_forward_1π A₀ A eG eC hρ
                  ((cocyclesAddEquiv A₀ A eG eC hρ).symm x)]
      map_add' := f.map_add }

include hρ in
private def cocyclesTwoForward
    (z : cocycles₂ A₀) : cocycles₂ A := by
  refine ⟨fun gh ↦ eC (z (eG.symm gh.1, eG.symm gh.2)), ?_⟩
  rw [mem_cocycles₂_iff]
  intro g h j
  change eC (z (eG.symm (g * h), eG.symm j)) +
      eC (z (eG.symm g, eG.symm h)) =
    A.ρ g (eC (z (eG.symm h, eG.symm j))) +
      eC (z (eG.symm g, eG.symm (h * j)))
  rw [eG.symm.map_mul, eG.symm.map_mul]
  have hz := (mem_cocycles₂_iff z).1 z.2
    (eG.symm g) (eG.symm h) (eG.symm j)
  simpa only [map_add, hρ, eG.apply_symm_apply] using congrArg eC hz

include hρ in
private def cocyclesTwoBackward
    (z : cocycles₂ A) : cocycles₂ A₀ := by
  refine ⟨fun gh ↦ eC.symm (z (eG gh.1, eG gh.2)), ?_⟩
  rw [mem_cocycles₂_iff]
  intro g h j
  change eC.symm (z (eG (g * h), eG j)) +
      eC.symm (z (eG g, eG h)) =
    A₀.ρ g (eC.symm (z (eG h, eG j))) +
      eC.symm (z (eG g, eG (h * j)))
  rw [eG.map_mul, eG.map_mul]
  have hz := (mem_cocycles₂_iff z).1 z.2 (eG g) (eG h) (eG j)
  simpa only [map_add,
    action_symm (A₀ := A₀) (A := A) eG eC hρ,
    eG.symm_apply_apply] using congrArg eC.symm hz

include hρ in
private noncomputable def cocyclesTwoAdd :
    cocycles₂ A₀ ≃+ cocycles₂ A where
  toFun := cocyclesTwoForward A₀ A eG eC hρ
  invFun := cocyclesTwoBackward A₀ A eG eC hρ
  left_inv z := by
    apply cocycles₂_ext
    intro g h
    simp [cocyclesTwoForward, cocyclesTwoBackward]
  right_inv z := by
    apply cocycles₂_ext
    intro g h
    simp [cocyclesTwoForward, cocyclesTwoBackward]
  map_add' x y := by
    apply cocycles₂_ext
    intro g h
    exact eC.map_add _ _

include hρ in
private theorem cocycles_two_boundary
    (z : cocycles₂ A₀) :
    ⇑(cocyclesTwoAdd A₀ A eG eC hρ z) ∈ coboundaries₂ A ↔
      ⇑z ∈ coboundaries₂ A₀ := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun g ↦ eC.symm (x (eG g)), ?_⟩
    apply funext
    rintro ⟨g, h⟩
    apply eC.injective
    have hgh := congrFun hx (eG g, eG h)
    simpa [cocyclesTwoAdd, cocyclesTwoForward, hρ] using hgh
  · rintro ⟨x, hx⟩
    refine ⟨fun g ↦ eC (x (eG.symm g)), ?_⟩
    apply funext
    rintro ⟨g, h⟩
    have hgh := congrFun hx (eG.symm g, eG.symm h)
    simpa [cocyclesTwoAdd, cocyclesTwoForward, hρ] using
      congrArg eC hgh

private theorem H2π_surjective (B : Rep (ULift.{u} ℤ) G) :
    Function.Surjective (H2π B) :=
  (ModuleCat.epi_iff_surjective (H2π B)).1 inferInstance

private theorem H2π_surjective_zero (B : Rep ℤ G₀) :
    Function.Surjective (H2π B) :=
  (ModuleCat.epi_iff_surjective (H2π B)).1 inferInstance

private noncomputable def cohomologyTwoForward : H2 A₀ → H2 A :=
  fun x ↦ H2π A
    (cocyclesTwoAdd A₀ A eG eC hρ
      (Function.surjInv (H2π_surjective_zero A₀) x))

private noncomputable def cohomologyTwoBackward : H2 A → H2 A₀ :=
  fun x ↦ H2π A₀
    ((cocyclesTwoAdd A₀ A eG eC hρ).symm
      (Function.surjInv (H2π_surjective A) x))

include hρ in
private theorem cohomology_forward_2π (z : cocycles₂ A₀) :
    cohomologyTwoForward A₀ A eG eC hρ (H2π A₀ z) =
      H2π A (cocyclesTwoAdd A₀ A eG eC hρ z) := by
  unfold cohomologyTwoForward
  rw [H2π_eq_iff]
  suffices h : ⇑(cocyclesTwoAdd A₀ A eG eC hρ
      (Function.surjInv (H2π_surjective_zero A₀) (H2π A₀ z) - z)) ∈
        coboundaries₂ A by
    simpa only [map_sub, cocycles₂.val_eq_coe] using h
  · apply (cocycles_two_boundary A₀ A eG eC hρ _).2
    apply (H2π_eq_iff _ _).1
    simp [Function.surjInv_eq]

include hρ in
private theorem cohomology_backward_2π (z : cocycles₂ A) :
    cohomologyTwoBackward A₀ A eG eC hρ (H2π A z) =
      H2π A₀ ((cocyclesTwoAdd A₀ A eG eC hρ).symm z) := by
  unfold cohomologyTwoBackward
  rw [H2π_eq_iff]
  suffices h : ⇑((cocyclesTwoAdd A₀ A eG eC hρ).symm
      (Function.surjInv (H2π_surjective A) (H2π A z) - z)) ∈
        coboundaries₂ A₀ by
    simpa only [map_sub, cocycles₂.val_eq_coe] using h
  · apply (cocycles_two_boundary A₀ A eG eC hρ _).1
    simpa only [AddEquiv.apply_symm_apply] using
      (H2π_eq_iff
        (Function.surjInv (H2π_surjective A) (H2π A z)) z).1
        (by simp [Function.surjInv_eq])

include hρ in
private noncomputable def cohomologyTwoAdd : H2 A₀ ≃+ H2 A := by
  let f : H2 A₀ →+ H2 A :=
    { toFun := cohomologyTwoForward A₀ A eG eC hρ
      map_zero' := by
        simpa using cohomology_forward_2π A₀ A eG eC hρ
          (0 : cocycles₂ A₀)
      map_add' := by
        intro x y
        induction x using H2_induction_on with
        | _ x =>
          induction y using H2_induction_on with
          | _ y =>
            rw [cohomology_forward_2π A₀ A eG eC hρ x,
              cohomology_forward_2π A₀ A eG eC hρ y]
            simpa only [map_add] using
              cohomology_forward_2π A₀ A eG eC hρ (x + y) }
  let g : H2 A →+ H2 A₀ :=
    { toFun := cohomologyTwoBackward A₀ A eG eC hρ
      map_zero' := by
        simpa using cohomology_backward_2π A₀ A eG eC hρ
          (0 : cocycles₂ A)
      map_add' := by
        intro x y
        induction x using H2_induction_on with
        | _ x =>
          induction y using H2_induction_on with
          | _ y =>
            rw [cohomology_backward_2π A₀ A eG eC hρ x,
              cohomology_backward_2π A₀ A eG eC hρ y]
            simpa only [map_add] using
              cohomology_backward_2π A₀ A eG eC hρ (x + y) }
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        induction x using H2_induction_on with
        | _ x =>
          rw [show f (H2π A₀ x) = H2π A
              (cocyclesTwoAdd A₀ A eG eC hρ x) by
                exact cohomology_forward_2π A₀ A eG eC hρ x,
            show g (H2π A
              (cocyclesTwoAdd A₀ A eG eC hρ x)) = H2π A₀ x by
                simpa using cohomology_backward_2π A₀ A eG eC hρ
                  (cocyclesTwoAdd A₀ A eG eC hρ x)]
      right_inv := by
        intro x
        induction x using H2_induction_on with
        | _ x =>
          rw [show g (H2π A x) = H2π A₀
              ((cocyclesTwoAdd A₀ A eG eC hρ).symm x) by
                exact cohomology_backward_2π A₀ A eG eC hρ x,
            show f (H2π A₀
              ((cocyclesTwoAdd A₀ A eG eC hρ).symm x)) = H2π A x by
                simpa using cohomology_forward_2π A₀ A eG eC hρ
                  ((cocyclesTwoAdd A₀ A eG eC hρ).symm x)]
      map_add' := f.map_add }

include hρ in
private noncomputable def invariantsAddEquiv :
    letI : Module ℤ A₀ := A₀.hV2
    letI : Module (ULift.{u} ℤ) A := A.hV2
    A₀.ρ.invariants ≃+ A.ρ.invariants := by
  letI : Module ℤ A₀ := A₀.hV2
  letI : Module (ULift.{u} ℤ) A := A.hV2
  exact
    { toFun := fun x ↦ ⟨eC x.1, fun g ↦ by
        obtain ⟨g, rfl⟩ := eG.surjective g
        rw [← hρ, x.2]⟩
      invFun := fun x ↦ ⟨eC.symm x.1, fun g ↦ by
        apply eC.injective
        rw [hρ, eC.apply_symm_apply]
        exact x.2 (eG g)⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        exact eC.symm_apply_apply x.1
      right_inv := fun x ↦ by
        apply Subtype.ext
        exact eC.apply_symm_apply x.1
      map_add' := fun x y ↦ by
        apply Subtype.ext
        exact eC.map_add x.1 y.1 }

include hρ in
private theorem norm_commutes [Fintype G₀] [Fintype G] (x : A₀) :
    letI : Module ℤ A₀ := A₀.hV2
    letI : Module (ULift.{u} ℤ) A := A.hV2
    eC (A₀.ρ.norm x) = A.ρ.norm (eC x) := by
  letI : Module ℤ A₀ := A₀.hV2
  letI : Module (ULift.{u} ℤ) A := A.hV2
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  rw [← eG.sum_comp (fun g : G ↦ A.ρ g (eC x))]
  apply Fintype.sum_congr
  intro g
  exact hρ g x

include hρ in
private theorem invariants_maps_range
    [Fintype G₀] [Fintype G] :
    letI : Module ℤ A₀ := A₀.hV2
    letI : Module (ULift.{u} ℤ) A := A.hV2
    (normCoinvariantsInvariants A₀).toAddMonoidHom.range ≤
      (normCoinvariantsInvariants A).toAddMonoidHom.range.comap
        (invariantsAddEquiv A₀ A eG eC hρ).toAddMonoidHom := by
  letI : Module ℤ A₀ := A₀.hV2
  letI : Module (ULift.{u} ℤ) A := A.hV2
  rintro z ⟨q, rfl⟩
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective A₀.ρ q
  refine ⟨Coinvariants.mk A.ρ (eC x), ?_⟩
  apply Subtype.ext
  change A.ρ.norm (eC x) = eC (A₀.ρ.norm x)
  exact (norm_commutes A₀ A eG eC hρ x).symm

include hρ in
private theorem invariants_symm_range
    [Fintype G₀] [Fintype G] :
    letI : Module ℤ A₀ := A₀.hV2
    letI : Module (ULift.{u} ℤ) A := A.hV2
    (normCoinvariantsInvariants A).toAddMonoidHom.range ≤
      (normCoinvariantsInvariants A₀).toAddMonoidHom.range.comap
        (invariantsAddEquiv A₀ A eG eC hρ).symm.toAddMonoidHom := by
  letI : Module ℤ A₀ := A₀.hV2
  letI : Module (ULift.{u} ℤ) A := A.hV2
  rintro z ⟨q, rfl⟩
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective A.ρ q
  refine ⟨Coinvariants.mk A₀.ρ (eC.symm x), ?_⟩
  apply Subtype.ext
  change A₀.ρ.norm (eC.symm x) = eC.symm (A.ρ.norm x)
  apply eC.injective
  rw [norm_commutes A₀ A eG eC hρ]
  rw [eC.apply_symm_apply, eC.apply_symm_apply]

include hρ in
private noncomputable def tateCohomologyEquiv
    [Fintype G₀] [Fintype G] :
    letI : Module ℤ A₀ := A₀.hV2
    letI : Module (ULift.{u} ℤ) A := A.hV2
    tateCohomologyZero A₀ ≃+ tateCohomologyZero A := by
  letI : Module ℤ A₀ := A₀.hV2
  letI : Module (ULift.{u} ℤ) A := A.hV2
  let e := invariantsAddEquiv A₀ A eG eC hρ
  let f := QuotientAddGroup.map
    (normCoinvariantsInvariants A₀).toAddMonoidHom.range
    (normCoinvariantsInvariants A).toAddMonoidHom.range
    e.toAddMonoidHom
    (invariants_maps_range A₀ A eG eC hρ)
  let g := QuotientAddGroup.map
    (normCoinvariantsInvariants A).toAddMonoidHom.range
    (normCoinvariantsInvariants A₀).toAddMonoidHom.range
    e.symm.toAddMonoidHom
    (invariants_symm_range A₀ A eG eC hρ)
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
          (normCoinvariantsInvariants A₀).toAddMonoidHom.range x
        simp [f, g, e]
      right_inv := by
        intro x
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
          (normCoinvariantsInvariants A).toAddMonoidHom.range x
        simp [f, g, e]
      map_add' := f.map_add }

section ShrinkModel

variable {G : Type u} [Group G] [Small.{0} G]
  (A : Rep (ULift.{u} ℤ) G) [Small.{0} A]

/-- The transported Type-0 integral representation underlying a small
`ULift ℤ`-representation. -/
private noncomputable def shrunkIntegralRepresentation :
    Rep ℤ (Shrink.{0} G) := by
  letI : Module ℤ A := AddCommGroup.toIntModule A
  let eG : Shrink.{0} G ≃* G := Shrink.mulEquiv
  let eC : Shrink.{0} A ≃+ A := Shrink.addEquiv
  let rho : Representation ℤ (Shrink.{0} G) (Shrink.{0} A) :=
    { toFun := fun g ↦
        { toFun := fun x ↦ eC.symm (A.ρ (eG g) (eC x))
          map_add' := by
            intro x y
            apply eC.injective
            simp
          map_smul' := by
            intro r x
            apply eC.injective
            simp only [eC.apply_symm_apply, map_zsmul]
            rfl }
      map_one' := by
        ext x
        simp [eG, eC]
      map_mul' := by
        intro g h
        ext x
        simp [eG, eC, map_mul, Module.End.mul_apply] }
  exact Rep.of rho

private theorem shrunk_representation_action
    (g : Shrink.{0} G) (x : shrunkIntegralRepresentation A) :
    (Shrink.addEquiv : Shrink.{0} A ≃+ A)
        ((shrunkIntegralRepresentation A).ρ g x) =
      A.ρ ((Shrink.mulEquiv : Shrink.{0} G ≃* G) g)
        ((Shrink.addEquiv : Shrink.{0} A ≃+ A) x) := by
  change (Shrink.addEquiv : Shrink.{0} A ≃+ A)
      ((Shrink.addEquiv : Shrink.{0} A ≃+ A).symm
        (A.ρ ((Shrink.mulEquiv : Shrink.{0} G ≃* G) g)
          ((Shrink.addEquiv : Shrink.{0} A ≃+ A) x))) = _
  exact (Shrink.addEquiv : Shrink.{0} A ≃+ A).apply_symm_apply _

end ShrinkModel

/-- The degree-minus-two consequence of Tate's theorem for a representation
whose carrier has a Type-0 model. -/
theorem tate_neg_small
    {G : Type u} [Group G] [Fintype G]
    (C : Rep (ULift.{u} ℤ) G) [Small.{0} C]
    (gamma : H2 C)
    (hgamma : ∀ x : H2 C, x ∈ zmultiples gamma)
    (hC1 : ∀ H : Subgroup G,
      IsZero (H1 (Rep.res H.subtype C)))
    (hcardH : ∀ H : Subgroup G,
      Nat.card (H2 (Rep.res H.subtype C)) = Nat.card H) :
    Nonempty (Additive (Abelianization G) ≃+ tateCohomologyZero C) := by
  letI : Small.{0} G :=
    small_of_injective (Fintype.equivFin G).injective
  let G₀ := Shrink.{0} G
  let C₀ : Rep ℤ G₀ := shrunkIntegralRepresentation C
  let eG : G₀ ≃* G :=
    (Shrink.mulEquiv : Shrink.{0} G ≃* G)
  let eC : C₀ ≃+ C :=
    (Shrink.addEquiv : Shrink.{0} C ≃+ C)
  have hρ (g : G₀) (x : C₀) :
      eC (C₀.ρ g x) = C.ρ (eG g) (eC x) :=
    shrunk_representation_action C g x
  let eH2 : H2 C₀ ≃+ H2 C :=
    cohomologyTwoAdd C₀ C eG eC hρ
  let gamma₀ : H2 C₀ := eH2.symm gamma
  have hgamma₀ : ∀ x : H2 C₀, x ∈ zmultiples gamma₀ := by
    intro x
    rw [AddSubgroup.mem_zmultiples_iff]
    obtain ⟨z, hz⟩ := (AddSubgroup.mem_zmultiples_iff.mp (hgamma (eH2 x)))
    refine ⟨z, ?_⟩
    apply eH2.injective
    rw [map_zsmul, eH2.apply_symm_apply]
    exact hz
  have hC1₀ : ∀ H₀ : Subgroup G₀,
      IsZero (H1 (Rep.res H₀.subtype C₀)) := by
    intro H₀
    let H : Subgroup G := H₀.map eG.toMonoidHom
    let eH : H₀ ≃* H := eG.subgroupMap H₀
    have hρH (g : H₀) (x : C₀) :
        eC ((Rep.res H₀.subtype C₀).ρ g x) =
          (Rep.res H.subtype C).ρ (eH g) (eC x) := by
      exact hρ g x
    let e1 : H1 (Rep.res H₀.subtype C₀) ≃+
        H1 (Rep.res H.subtype C) :=
      cohomologyAddEquiv
        (Rep.res H₀.subtype C₀) (Rep.res H.subtype C) eH eC hρH
    letI : Subsingleton (H1 (Rep.res H.subtype C)) :=
      ModuleCat.subsingleton_of_isZero (hC1 H)
    letI : Subsingleton (H1 (Rep.res H₀.subtype C₀)) :=
      e1.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hcardH₀ : ∀ H₀ : Subgroup G₀,
      Nat.card (H2 (Rep.res H₀.subtype C₀)) = Nat.card H₀ := by
    intro H₀
    let H : Subgroup G := H₀.map eG.toMonoidHom
    let eH : H₀ ≃* H := eG.subgroupMap H₀
    have hρH (g : H₀) (x : C₀) :
        eC ((Rep.res H₀.subtype C₀).ρ g x) =
          (Rep.res H.subtype C).ρ (eH g) (eC x) := by
      exact hρ g x
    let e2 : H2 (Rep.res H₀.subtype C₀) ≃+
        H2 (Rep.res H.subtype C) :=
      cohomologyTwoAdd
        (Rep.res H₀.subtype C₀) (Rep.res H.subtype C) eH eC hρH
    calc
      Nat.card (H2 (Rep.res H₀.subtype C₀)) =
          Nat.card (H2 (Rep.res H.subtype C)) :=
        Nat.card_congr e2.toEquiv
      _ = Nat.card H := hcardH H
      _ = Nat.card H₀ := Nat.card_congr eH.symm.toEquiv
  let shift : TateTwoShift C₀ :=
    restrictedShiftStatement C₀ gamma₀ hgamma₀ hC1₀ hcardH₀
  let eAb : Additive (Abelianization G₀) ≃+
      Additive (Abelianization G) := eG.abelianizationCongr.toAdditive
  let eBase : Additive (Abelianization G₀) ≃+
      tateCohomologyZero C₀ :=
    (TCohomo.homology1Abelianization G₀).symm.trans
      shift.negTwo
  let eTate : tateCohomologyZero C₀ ≃+ tateCohomologyZero C :=
    tateCohomologyEquiv C₀ C eG eC hρ
  exact ⟨eAb.symm.trans (eBase.trans eTate)⟩

/-- The actual idèle-class representation satisfies the smallness condition,
so Theorems VII.5.1 and VIII.4.7 give the Tate isomorphism without an
additional universe-polymorphic bridge hypothesis. -/
theorem isomorphism_previous_small
    (h51 : IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u}) :
    GaloisTateIsomorphism.{u} := by
  intro K L _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  let C := ideleCohomologyRepresentation K L
  letI : Small.{0} C :=
    cohomologyRepresentationSmall K L
  obtain ⟨inv, _, _⟩ := h47 K L
  let gamma : H2 C := fundamentalClassInvariant inv
  apply tate_neg_small C gamma
  · intro x
    exact zmultiples_fundamental_invariant inv x
  · intro H
    let E := IntermediateField.fixedField H
    have hzero : IsZero (H1
        (ideleCohomologyRepresentation E L)) :=
      (h51 E L).2.1
    let e := restrictedIdeleCohomology K L H 1
    letI : Subsingleton (H1
        (ideleCohomologyRepresentation E L)) :=
      ModuleCat.subsingleton_of_isZero hzero
    letI : Subsingleton (H1
        (Rep.res H.subtype C)) :=
      e.symm.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · intro H
    let E := IntermediateField.fixedField H
    obtain ⟨invH, _, _⟩ := h47 E L
    calc
      Nat.card (H2 (Rep.res H.subtype C)) =
          Nat.card (H2
            (ideleCohomologyRepresentation E L)) :=
        (Nat.card_congr
          (restrictedIdeleCohomology K L H 2).toEquiv).symm
      _ = Module.finrank E L := nat_card_invariant invH
      _ = Nat.card H := IntermediateField.finrank_fixedField_eq_card H

/-- The Galois norm-index formula, with Tate's theorem transported through
the Type-0 model of the actual idèle-class representation. -/
theorem previous_results_small
    (h51 : IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u}) :
    GaloisIndexFormula.{u} :=
  galois_formula_isomorphism
    (isomorphism_previous_small h51 h47)

/-- Fixed-field norm limitation with the universe transport discharged
internally; only the source's corestriction square remains as an input. -/
theorem fixed_previous_small
    (h51 : IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hcore : CorestrictionCokernelBridge.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    (canonicalIdeleNorm (K := K)
        (L := IntermediateField.fixedField H)).range =
      (canonicalIdeleNorm (K := K)
        (L := maximalSubfieldInside K L H)).range := by
  apply norm_maximal_abelian hcore _ K L H
  exact previous_results_small h51 h47

/-- Fixed-field norm limitation in the literal form of Milne's proof: the
only remaining cohomological input is commutativity of the displayed
fundamental-class/corestriction square. -/
theorem fixed_corestriction_square
    (h51 : IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hsquare : CorestrictionSquareBridge.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    (canonicalIdeleNorm (K := K)
        (L := IntermediateField.fixedField H)).range =
      (canonicalIdeleNorm (K := K)
        (L := maximalSubfieldInside K L H)).range :=
  fixed_previous_small h51 h47
    (corestriction_cokernel_square hsquare) K L H

/-- The existential consequence used in Chapter VII, with Tate's theorem
transported internally and the printed corestriction square left as the
sole VIII.4.8 compatibility input. -/
theorem existential_limitation_square
    (h51 : IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hsquare : CorestrictionSquareBridge.{u}) :
    ExistentialNormLimitation.{u} :=
  existential_limitation_corestriction
    (corestriction_cokernel_square hsquare)
    (previous_results_small h51 h47)

end

end Towers.CField.GClass
