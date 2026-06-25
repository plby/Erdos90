import Towers.ClassField.LocalBrauer.LinearlyDisjointChange

/-!
# The Galois package on a field-valued tensor product

When `U ⊗[K] F` is a field and is Galois over `F`, the action on the left
factor identifies `Gal(U/K)` with `Gal((U ⊗[K] F)/F)`.  This file builds
that equivalence, proves its coefficient equivariance, and applies the
linearly-disjoint carry base-change theorem with tautologically compatible
cyclic coordinates.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (K U F : Type u) [Field K] [Field U] [Field F]
  [Algebra K U] [FiniteDimensional K U] [IsGalois K U]
  [Algebra K F]

private abbrev TensorCompositum := U ⊗[K] F

local instance tensorCompositumModuleFinite :
    Module.Finite F (TensorCompositum K U F) := by
  letI : Module.Finite F (F ⊗[K] U) := Module.Finite.base_change K F U
  exact Module.Finite.equiv
    (Algebra.TensorProduct.commRight K F U).toLinearEquiv

/-- The `F`-algebra automorphism of `U ⊗[K] F` acting through `sigma` on
the left factor and trivially on the right factor. -/
noncomputable def tensorCompositumAlg
    (sigma : Gal(U/K)) :
    TensorCompositum K U F ≃ₐ[F] TensorCompositum K U F := by
  let leftHom : F ⊗[K] U →ₐ[F] F ⊗[K] U :=
    Algebra.TensorProduct.map (AlgHom.id F F) sigma.toAlgHom
  let leftInv : F ⊗[K] U →ₐ[F] F ⊗[K] U :=
    Algebra.TensorProduct.map (AlgHom.id F F) sigma.symm.toAlgHom
  let leftEquiv : F ⊗[K] U ≃ₐ[F] F ⊗[K] U := by
    apply AlgEquiv.ofAlgHom leftHom leftInv
    · apply AlgHom.ext
      intro x
      induction x with
      | zero => simp [leftHom, leftInv]
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul a b => simp [leftHom, leftInv]
    · apply AlgHom.ext
      intro x
      induction x with
      | zero => simp [leftHom, leftInv]
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul a b => simp [leftHom, leftInv]
  exact (Algebra.TensorProduct.commRight K F U).symm.trans
    (leftEquiv.trans (Algebra.TensorProduct.commRight K F U))

omit [FiniteDimensional K U] [IsGalois K U] in
@[simp]
theorem tensor_compositum_tmul
    (sigma : Gal(U/K)) (a : U) (b : F) :
    tensorCompositumAlg K U F sigma (a ⊗ₜ[K] b) =
      sigma a ⊗ₜ[K] b := by
  rfl

omit [FiniteDimensional K U] [IsGalois K U] in
@[simp]
theorem tensor_compositum_one :
    tensorCompositumAlg K U F (1 : Gal(U/K)) =
      AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (fun a b ↦ a + b) hx hy
  | tmul a b => simp

omit [FiniteDimensional K U] [IsGalois K U] in
theorem tensor_compositum_alg
    (sigma tau : Gal(U/K)) :
    tensorCompositumAlg K U F (sigma * tau) =
      (tensorCompositumAlg K U F tau).trans
        (tensorCompositumAlg K U F sigma) := by
  apply AlgEquiv.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (fun a b ↦ a + b) hx hy
  | tmul a b => simp

/-- The left-factor Galois action as a homomorphism into the Galois group of
the tensor compositum over `F`. -/
noncomputable def tensorCompositumHom :
    Gal(U/K) →* Gal(TensorCompositum K U F/F) where
  toFun := tensorCompositumAlg K U F
  map_one' := tensor_compositum_one K U F
  map_mul' := tensor_compositum_alg K U F

omit [IsGalois K U] in
theorem tensor_compositum_injective :
    Function.Injective (tensorCompositumHom K U F) := by
  intro sigma tau h
  apply AlgEquiv.ext
  intro a
  have ha := congrArg
    (fun e : Gal(TensorCompositum K U F/F) ↦ e (a ⊗ₜ[K] (1 : F))) h
  change sigma a ⊗ₜ[K] (1 : F) = tau a ⊗ₜ[K] (1 : F) at ha
  exact (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := U) (B := F)).injective ha

theorem tensor_compositum_bijective
    (hTensorCompositum : IsField (TensorCompositum K U F)) :
    Function.Bijective (tensorCompositumHom K U F) := by
  letI : Field (TensorCompositum K U F) := hTensorCompositum.toField
  have hinj := tensor_compositum_injective K U F
  refine (Nat.bijective_iff_injective_and_card
    (tensorCompositumHom K U F)).2 ⟨hinj, ?_⟩
  apply le_antisymm
  · exact Nat.card_le_card_of_injective _ hinj
  · calc
      Nat.card Gal(TensorCompositum K U F/F) =
          Nat.card (TensorCompositum K U F →ₐ[F] TensorCompositum K U F) :=
        Nat.card_congr (algEquivEquivAlgHom F (TensorCompositum K U F))
      _ ≤ Module.finrank F (TensorCompositum K U F) :=
        card_algHom_le_finrank F (TensorCompositum K U F)
          (TensorCompositum K U F)
      _ = Module.finrank F (F ⊗[K] U) :=
        (Algebra.TensorProduct.commRight K F U).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K U :=
        Module.finrank_baseChange (R := F) (S := K) (M' := U)
      _ = Nat.card Gal(U/K) :=
        (IsGalois.card_aut_eq_finrank K U).symm

/-- A field-valued scalar extension of a finite Galois extension is Galois.
The proof constructs enough automorphisms by acting on the left tensor
factor, and compares their cardinality with the base-changed dimension. -/
theorem tensor_compositum
    (hTensorCompositum : IsField (TensorCompositum K U F)) :
    letI : Field (TensorCompositum K U F) := hTensorCompositum.toField
    IsGalois F (TensorCompositum K U F) := by
  letI : Field (TensorCompositum K U F) := hTensorCompositum.toField
  apply IsGalois.of_card_aut_eq_finrank
  calc
    Nat.card Gal(TensorCompositum K U F/F) = Nat.card Gal(U/K) :=
      (Nat.card_congr <| Equiv.ofBijective
        (tensorCompositumHom K U F)
        (tensor_compositum_bijective K U F hTensorCompositum)).symm
    _ = Module.finrank K U :=
      IsGalois.card_aut_eq_finrank K U
    _ = Module.finrank F (F ⊗[K] U) :=
      (Module.finrank_baseChange (R := F) (S := K) (M' := U)).symm
    _ = Module.finrank F (TensorCompositum K U F) :=
      (Algebra.TensorProduct.commRight K F U).toLinearEquiv.finrank_eq

/-- The canonical Galois equivalence produced by the left-factor action. -/
noncomputable def tensorCompositumGalois
    (hTensorCompositum : IsField (TensorCompositum K U F)) :
    Gal(U/K) ≃* Gal(TensorCompositum K U F/F) :=
  MulEquiv.ofBijective (tensorCompositumHom K U F)
    (tensor_compositum_bijective K U F hTensorCompositum)

@[simp]
theorem tensor_compositum_galois
    (hTensorCompositum : IsField (TensorCompositum K U F))
    (sigma : Gal(U/K)) :
    tensorCompositumGalois K U F hTensorCompositum sigma =
      tensorCompositumAlg K U F sigma :=
  rfl

@[simp]
theorem tensor_include_equivariant
    (hTensorCompositum : IsField (TensorCompositum K U F))
    (sigma : Gal(U/K)) (a : U) :
    Algebra.TensorProduct.includeLeftRingHom
        (R := K) (A := U) (B := F) (sigma a) =
      tensorCompositumGalois K U F hTensorCompositum sigma
        (Algebra.TensorProduct.includeLeftRingHom
          (R := K) (A := U) (B := F) a) := by
  change sigma a ⊗ₜ[K] (1 : F) =
    tensorCompositumAlg K U F sigma (a ⊗ₜ[K] (1 : F))
  rw [tensor_compositum_tmul]

variable {n : ℕ} [NeZero n]

/-- Base change of a carry class to a field-valued tensor product.  All
Galois-coordinate compatibility is supplied canonically by the left-factor
action. -/
theorem brauer_carry_compositum
    (hTensorCompositum : IsField (TensorCompositum K U F))
    (eK : Multiplicative (ZMod n) ≃* Gal(U/K)) (a : Kˣ) :
    letI : Field (TensorCompositum K U F) := hTensorCompositum.toField
    letI : IsGalois F (TensorCompositum K U F) :=
      tensor_compositum K U F hTensorCompositum
    brauerBaseChange K F
        (CProduc.brauerClass K U (galoisCarryCocycle K eK a)) =
      CProduc.brauerClass F (TensorCompositum K U F)
        (galoisCarryCocycle F
          (eK.trans (tensorCompositumGalois K U F hTensorCompositum))
          (Units.map (algebraMap K F) a)) := by
  letI : Field (TensorCompositum K U F) := hTensorCompositum.toField
  letI : IsGalois F (TensorCompositum K U F) :=
    tensor_compositum K U F hTensorCompositum
  let i : U →+* TensorCompositum K U F :=
    Algebra.TensorProduct.includeLeftRingHom
  let g := tensorCompositumGalois K U F hTensorCompositum
  refine brauer_base_carry i g
    (tensor_include_equivariant K U F hTensorCompositum)
    ?_ AlgEquiv.refl ?_ eK
    (eK.trans (tensorCompositumGalois K U F hTensorCompositum))
    ?_ a
  · intro x
    change algebraMap K U x ⊗ₜ[K] (1 : F) =
      (1 : U) ⊗ₜ[K] algebraMap K F x
    rw [← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply']
  · intro x y
    change x ⊗ₜ[K] y = (x ⊗ₜ[K] (1 : F)) * ((1 : U) ⊗ₜ[K] y)
    simp
  · intro z
    rfl

end

end Towers.CField.LBrauer
