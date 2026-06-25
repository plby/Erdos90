import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Milne, Class Field Theory, Example IV.2.2

The tensor product of two full matrix algebras is a full matrix algebra whose
size is the product of the two sizes.
-/

namespace Submission.CField.BGroups

universe u

variable (k : Type u) [Field k]

/-- **Example IV.2.2.** `M_m(k) ⊗ M_n(k) ≃ M_(mn)(k)`. -/
noncomputable def matrixTensorAlg (m n : ℕ) :
    TensorProduct k (Matrix (Fin m) (Fin m) k)
      (Matrix (Fin n) (Fin n) k) ≃ₐ[k]
      Matrix (Fin (m * n)) (Fin (m * n)) k :=
  (Matrix.kroneckerAlgEquiv (Fin m) (Fin n) k).trans <|
    Matrix.reindexAlgEquiv k k finProdFinEquiv

end Submission.CField.BGroups
