import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Submission.ClassField.BrauerGroups.ScalarExtensionCentral

/-!
# Chapter IV, Corollary 2.16

The dimension of a finite-dimensional central simple algebra over its center
is a square.
-/

namespace Submission.CField.BGroups

open scoped TensorProduct

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Milne, Corollary IV.2.16: `[A : k]` is a square. -/
theorem finrank_simple_square :
    ∃ n : ℕ, Module.finrank k A = n ^ 2 := by
  let K := AlgebraicClosure k
  have hCSA := scalar_extension_simple k K A
  letI : IsSimpleRing (A ⊗[k] K) := hCSA.1
  letI : Algebra.IsCentral K (A ⊗[k] K) := hCSA.2
  letI : Module.Finite K (K ⊗[k] A) := Module.Finite.base_change k K A
  letI : Module.Finite K (A ⊗[k] K) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight k K A).toLinearEquiv
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K (A ⊗[k] K)
  refine ⟨n, ?_⟩
  calc
    Module.finrank k A = Module.finrank K (K ⊗[k] A) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank K (A ⊗[k] K) :=
      (Algebra.TensorProduct.commRight k K A).toLinearEquiv.finrank_eq
    _ = Module.finrank K (Matrix (Fin n) (Fin n) K) :=
      e.toLinearEquiv.finrank_eq
    _ = n ^ 2 := by simp [Module.finrank_matrix, pow_two]

end Submission.CField.BGroups
