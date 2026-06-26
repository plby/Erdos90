import Mathlib.RingTheory.MatrixAlgebra

/-!
# Milne, Class Field Theory, Example IV.2.1

Tensoring with a full matrix algebra produces the corresponding matrix algebra
over the tensor product of coefficient algebras.
-/

namespace Towers.CField.BGroups

universe u v w

open Algebra.TensorProduct

variable (k : Type u) [Field k]

/-- **Example IV.2.1.** `A ⊗ M_n(k)` is canonically isomorphic to `M_n(A)`. -/
noncomputable def tensorMatrixBase
    (A : Type v) [Ring A] [Algebra k A] (n : Type w)
    [Fintype n] [DecidableEq n] :
    TensorProduct k A (Matrix n n k) ≃ₐ[k] Matrix n n A :=
  (matrixEquivTensor n k A).symm

/-- The general form stated after Example IV.2.1:
`A ⊗ M_n(A') ≃ M_n(A ⊗ A')`. -/
noncomputable def tensorMatrixCoefficients
    (A : Type v) (A' : Type w) [Ring A] [Ring A']
    [Algebra k A] [Algebra k A'] (n : Type*)
    [Fintype n] [DecidableEq n] :
    TensorProduct k A (Matrix n n A') ≃ₐ[k]
      Matrix n n (TensorProduct k A A') :=
  (Algebra.TensorProduct.congr AlgEquiv.refl
      (matrixEquivTensor n k A')).trans <|
    (Algebra.TensorProduct.assoc k k k A A' (Matrix n n k)).symm.trans <|
      (matrixEquivTensor n k (TensorProduct k A A')).symm

end Towers.CField.BGroups
