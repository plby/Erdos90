import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# Milne, Chapter 1, Remark 1.16

The matrix of a tensor product of linear maps is the Kronecker product of
their matrices.
-/

namespace Towers.NumberTheory.Milne

open Matrix Module LinearMap
open scoped Kronecker

/-- Milne, Remark 1.16: in tensor-product bases, the matrix of `f ⊗ g` is
the Kronecker product of the matrices of `f` and `g`. -/
theorem matrix_tensor_kronecker
    {R M N M' N' : Type*} {ι κ ι' κ' : Type*}
    [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    [Fintype ι] [Fintype κ] [Finite ι'] [Finite κ']
    [DecidableEq ι] [DecidableEq κ]
    (bM : Basis ι R M) (bN : Basis κ R N)
    (bM' : Basis ι' R M') (bN' : Basis κ' R N')
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    toMatrix (bM.tensorProduct bN) (bM'.tensorProduct bN')
        (TensorProduct.map f g) =
      toMatrix bM bM' f ⊗ₖ toMatrix bN bN' g :=
  TensorProduct.toMatrix_map bM bN bM' bN' f g

end Towers.NumberTheory.Milne
