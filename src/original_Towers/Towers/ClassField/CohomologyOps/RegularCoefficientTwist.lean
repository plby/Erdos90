import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Milne, Class Field Theory, Remark II.1.4

For a `G`-representation `A`, the tensor product of the left regular
representation with the underlying trivial representation of `A` is
isomorphic to the diagonal tensor product with `A`.  On pure basis tensors
the isomorphism sends

`g ⊗ a ↦ g ⊗ g • a`.
-/

namespace Towers.CField.COps

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G]

section

variable (A : Rep k G)

/-- Twist the coefficient at `g` by the action of `g`. -/
noncomputable def regularCoefficientTwist :
    (G →₀ A) →ₗ[k] G →₀ A :=
  Finsupp.lsum k fun g ↦ (Finsupp.lsingle g).comp (A.ρ g)

/-- The inverse coefficient twist. -/
noncomputable def regularCoefficientUntwist :
    (G →₀ A) →ₗ[k] G →₀ A :=
  Finsupp.lsum k fun g ↦ (Finsupp.lsingle g).comp (A.ρ g⁻¹)

@[simp]
lemma regular_coefficient_twist (g : G) (a : A) :
    regularCoefficientTwist A (Finsupp.single g a) =
      Finsupp.single g (A.ρ g a) := by
  simp [regularCoefficientTwist]

@[simp]
lemma regular_untwist_single (g : G) (a : A) :
    regularCoefficientUntwist A (Finsupp.single g a) =
      Finsupp.single g (A.ρ g⁻¹ a) := by
  simp [regularCoefficientUntwist]

lemma regular_twist_untwist :
    (regularCoefficientUntwist A).comp (regularCoefficientTwist A) =
      (LinearMap.id : (G →₀ A) →ₗ[k] G →₀ A) := by
  apply Finsupp.lhom_ext'
  intro g
  apply LinearMap.ext
  intro a
  simp [← Module.End.mul_apply, ← map_mul]

lemma regular_untwist_twist :
    (regularCoefficientTwist A).comp (regularCoefficientUntwist A) =
      (LinearMap.id : (G →₀ A) →ₗ[k] G →₀ A) := by
  apply Finsupp.lhom_ext'
  intro g
  apply LinearMap.ext
  intro a
  simp [← Module.End.mul_apply, ← map_mul]

/-- Pointwise coefficient twisting is a linear equivalence. -/
noncomputable def regularTwistEquiv :
    (G →₀ A) ≃ₗ[k] G →₀ A :=
  LinearEquiv.ofLinear (regularCoefficientTwist A) (regularCoefficientUntwist A)
    (regular_untwist_twist A)
    (regular_twist_untwist A)

/-- The underlying linear equivalence in Remark II.1.4. -/
noncomputable def regularTensorTwist :
    TensorProduct k (G →₀ k) A ≃ₗ[k] TensorProduct k (G →₀ k) A := by
  classical
  exact (TensorProduct.finsuppScalarLeft k A G).trans <|
    (regularTwistEquiv A).trans
      (TensorProduct.finsuppScalarLeft k A G).symm

@[simp]
theorem regular_tensor_twist (g : G) (a : A) :
    regularTensorTwist A (Finsupp.single g 1 ⊗ₜ[k] a) =
      Finsupp.single g 1 ⊗ₜ[k] A.ρ g a := by
  classical
  simp only [regularTensorTwist, LinearEquiv.trans_apply]
  rw [TensorProduct.finsuppScalarLeft_apply_tmul]
  have hs : (Finsupp.single g (1 : k)).sum
      (fun i m ↦ Finsupp.single i (m • a)) = Finsupp.single g a := by
    simp
  rw [hs]
  rw [
    show regularTwistEquiv A (Finsupp.single g a) =
      Finsupp.single g (A.ρ g a) from regular_coefficient_twist A g a,
    TensorProduct.finsuppScalarLeft_symm_apply_single]

@[simp]
theorem regular_twist_smul
    (g : G) (r : k) (a : A) :
    regularTensorTwist A (Finsupp.single g r ⊗ₜ[k] a) =
      Finsupp.single g r ⊗ₜ[k] A.ρ g a := by
  rw [show Finsupp.single g r = r • Finsupp.single g 1 by simp,
    ← TensorProduct.smul_tmul', map_smul,
    regular_tensor_twist, TensorProduct.smul_tmul']

@[simp]
theorem regular_twist_single (g : G) (a : A) :
    (regularTensorTwist A).symm (Finsupp.single g 1 ⊗ₜ[k] a) =
      Finsupp.single g 1 ⊗ₜ[k] A.ρ g⁻¹ a := by
  apply (regularTensorTwist A).injective
  rw [LinearEquiv.apply_symm_apply, regular_tensor_twist]
  simp [← Module.End.mul_apply, ← map_mul]

/-- **Remark II.1.4.** Twisting the second tensor factor by its regular-basis
index identifies the trivial and diagonal tensor-product actions. -/
noncomputable def regularIsoDiagonal :
    (Rep.leftRegular k G ⊗ Rep.trivial k G A) ≅ (Rep.leftRegular k G ⊗ A) :=
  Rep.mkIso {
    toLinearEquiv := regularTensorTwist A
    isIntertwining' := fun h ↦ by
      apply TensorProduct.ext
      apply Finsupp.lhom_ext'
      intro g
      apply LinearMap.ext
      intro r
      apply LinearMap.ext
      intro a
      simp [regular_twist_smul,
        ← Module.End.mul_apply, ← map_mul] }

@[simp]
theorem regular_diagonal_single (g : G) (a : A) :
    (regularIsoDiagonal A).hom (Finsupp.single g 1 ⊗ₜ[k] a) =
      Finsupp.single g 1 ⊗ₜ[k] A.ρ g a := by
  exact regular_tensor_twist A g a

@[simp]
theorem regular_trivial_single (g : G) (a : A) :
    (regularIsoDiagonal A).inv (Finsupp.single g 1 ⊗ₜ[k] a) =
      Finsupp.single g 1 ⊗ₜ[k] A.ρ g⁻¹ a := by
  exact regular_twist_single A g a

end

end Towers.CField.COps
