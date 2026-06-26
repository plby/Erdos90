import Submission.NumberTheory.Completions.TensorDecomposition
import Submission.ClassField.IdeleCohomology.CompletionProductAction

/-!
# The tensor-product Galois action before Lemma VII.2.1

Milne constructs the action on `\prod_{w \mid v} L_w` by first letting
`Gal(L/K)` act on the `L` factor of `L \otimes_K K_v`, and then transporting
that action across the canonical equivalence

`L \otimes_K K_v \simeq \prod_{w \mid v} L_w`.

This file formalizes the first half of that construction.  In particular,
`tensorGaloisAlg v sigma` is the `K_v`-algebra automorphism
sending `a \otimes b` to `sigma(a) \otimes b`, and these automorphisms form a
genuine action of `Gal(L/K)`.
-/

namespace Submission.CField.ICohomo

open AbsoluteValue
open Submission.NumberTheory.Milne
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

set_option backward.isDefEq.respectTransparency false in
local instance tensorProductActionBaseAlgebra (v : AbsoluteValue K ℝ) :
    Algebra K v.Completion :=
  completionBaseAlgebra v

local instance tensorProductActionBaseSMul (v : AbsoluteValue K ℝ) :
    SMul K v.Completion :=
  (tensorProductActionBaseAlgebra v).toSMul

local instance tensorProductActionBaseModule (v : AbsoluteValue K ℝ) :
    Module K v.Completion :=
  Algebra.toModule

/-- The action of `sigma` on `K_v \otimes_K L`: it fixes the completed-base
factor and applies `sigma` to the global-field factor. -/
def tensorAlgHom
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K)) :
    (v.Completion ⊗[K] L) →ₐ[v.Completion] (v.Completion ⊗[K] L) :=
  Algebra.TensorProduct.map (AlgHom.id v.Completion v.Completion) sigma.toAlgHom

@[simp]
theorem left_tensor_tmul
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K))
    (b : v.Completion) (a : L) :
    tensorAlgHom v sigma (b ⊗ₜ[K] a) =
      b ⊗ₜ[K] sigma a := by
  rw [tensorAlgHom, Algebra.TensorProduct.map_tmul]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Tensor-product algebra homomorphisms require a deep additive-map instance search.
/-- The inverse pair of tensor-product homomorphisms, packaged as an algebra
equivalence. -/
def leftTensorAlg
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K)) :
    (v.Completion ⊗[K] L) ≃ₐ[v.Completion] (v.Completion ⊗[K] L) := by
  apply AlgEquiv.ofAlgHom
    (tensorAlgHom v sigma)
    (tensorAlgHom v sigma⁻¹)
  · apply AlgHom.ext
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro b a
      simp
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  · apply AlgHom.ext
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro b a
      simp
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]

@[simp]
theorem tensor_alg_tmul
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K))
    (b : v.Completion) (a : L) :
    leftTensorAlg v sigma (b ⊗ₜ[K] a) =
      b ⊗ₜ[K] sigma a := by
  change tensorAlgHom v sigma (b ⊗ₜ[K] a) = _
  exact left_tensor_tmul v sigma b a

/-- The action through the `L` factor, written on Milne's tensor ordering
`L \otimes_K K_v`. -/
def tensorGaloisAlg
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K)) :
    (L ⊗[K] v.Completion) ≃ₐ[v.Completion] (L ⊗[K] v.Completion) :=
  (Algebra.TensorProduct.commRight K v.Completion L).symm.trans
    ((leftTensorAlg v sigma).trans
      (Algebra.TensorProduct.commRight K v.Completion L))

/-- On pure tensors the tensor-product action is exactly
`a \otimes b ↦ sigma(a) \otimes b`. -/
@[simp]
theorem tensor_galois_tmul
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K))
    (a : L) (b : v.Completion) :
    tensorGaloisAlg v sigma (a ⊗ₜ[K] b) =
      sigma a ⊗ₜ[K] b := by
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Tensor induction synthesizes the completed-base module on the tensor product.
/-- The identity Galois automorphism acts trivially on the tensor product. -/
theorem tensor_alg_one (v : AbsoluteValue K ℝ) :
    tensorGaloisAlg v (1 : Gal(L/K)) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a b
    simp
  · intro x y hx hy
    simpa using congrArg₂ (· + ·) hx hy

set_option synthInstance.maxHeartbeats 200000 in
-- Tensor induction synthesizes the completed-base module on the tensor product.
/-- Acting by a product is composition of the two tensor-product actions. -/
theorem tensor_galois_alg
    (v : AbsoluteValue K ℝ) (sigma tau : Gal(L/K)) :
    tensorGaloisAlg v (sigma * tau) =
      (tensorGaloisAlg v tau).trans
        (tensorGaloisAlg v sigma) := by
  apply AlgEquiv.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a b
    simp
  · intro x y hx hy
    simpa using congrArg₂ (· + ·) hx hy

set_option synthInstance.maxHeartbeats 200000 in
-- Packaging the action synthesizes the completed-base tensor-product module.
/-- The Galois action on `L \otimes_K K_v` used in Milne's construction. -/
@[reducible]
def tensorSemiringAction (v : AbsoluteValue K ℝ) :
    MulSemiringAction Gal(L/K) (L ⊗[K] v.Completion) where
  smul sigma x := tensorGaloisAlg v sigma x
  one_smul x := by
    change tensorGaloisAlg v (1 : Gal(L/K)) x = x
    rw [tensor_alg_one]
    rfl
  mul_smul sigma tau x := by
    change tensorGaloisAlg v (sigma * tau) x =
      tensorGaloisAlg v sigma (tensorGaloisAlg v tau x)
    rw [tensor_galois_alg]
    rfl
  smul_zero sigma := map_zero (tensorGaloisAlg v sigma)
  smul_add sigma := map_add (tensorGaloisAlg v sigma)
  smul_one sigma := map_one (tensorGaloisAlg v sigma)
  smul_mul sigma := map_mul (tensorGaloisAlg v sigma)

end

end Submission.CField.ICohomo
