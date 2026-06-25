import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Submission.ClassField.BrauerGroups.CentralizerInfCentralizers
import Submission.ClassField.BrauerGroups.CentralMatrix

/-!
# Chapter IV, Corollary 2.8

The tensor product of two finite-dimensional central simple algebras is again
central simple.
-/

namespace Submission.CField.BGroups

open scoped TensorProduct

universe u v

variable (k : Type v) (A B : Type u) [Field k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]

/-- The center of a tensor product of central algebras over a field consists
only of scalars. -/
theorem tensor_product_central [Algebra.IsCentral k A] [Algebra.IsCentral k B] :
    Algebra.IsCentral k (A ⊗[k] B) := by
  constructor
  have h := centralizer_tensorProduct k A B (⊤ : Subalgebra k A) (⊤ : Subalgebra k B)
  have htop :
      (Algebra.TensorProduct.map (⊤ : Subalgebra k A).val
        (⊤ : Subalgebra k B).val).range = ⊤ := by
    rw [AlgHom.range_eq_top]
    apply Algebra.TensorProduct.map_surjective
    · exact fun a ↦ ⟨⟨a, trivial⟩, rfl⟩
    · exact fun b ↦ ⟨⟨b, trivial⟩, rfl⟩
  rw [htop] at h
  have hT :
      Subalgebra.centralizer k ((⊤ : Subalgebra k (A ⊗[k] B)) : Set (A ⊗[k] B)) =
        Subalgebra.center k (A ⊗[k] B) := by
    simpa only [Algebra.coe_top] using
      (Subalgebra.centralizer_univ (R := k) (A := A ⊗[k] B))
  have hA : Subalgebra.centralizer k ((⊤ : Subalgebra k A) : Set A) =
      Subalgebra.center k A := by
    simpa only [Algebra.coe_top] using
      (Subalgebra.centralizer_univ (R := k) (A := A))
  have hB : Subalgebra.centralizer k ((⊤ : Subalgebra k B) : Set B) =
      Subalgebra.center k B := by
    simpa only [Algebra.coe_top] using
      (Subalgebra.centralizer_univ (R := k) (A := B))
  rw [hT, hA, hB] at h
  rw [Algebra.IsCentral.center_eq_bot k A,
    Algebra.IsCentral.center_eq_bot k B] at h
  have hbot :
      (Algebra.TensorProduct.map (⊥ : Subalgebra k A).val
        (⊥ : Subalgebra k B).val).range = ⊥ := by
    rw [Algebra.TensorProduct.map_range,
      Subalgebra.range_comp_val, Subalgebra.range_comp_val]
    simp
  rw [hbot] at h
  exact h.le

/-- Milne, Corollary IV.2.8. -/
theorem tensor_central_simple
    [IsSimpleRing A] [IsSimpleRing B]
    [Algebra.IsCentral k A] [Algebra.IsCentral k B]
    [Module.Finite k A] :
    IsSimpleRing (A ⊗[k] B) ∧ Algebra.IsCentral k (A ⊗[k] B) := by
  letI : IsSimpleRing (A ⊗[k] B) :=
    tensor_simple_ring k A B
  letI : Algebra.IsCentral k (A ⊗[k] B) := tensor_product_central k A B
  exact ⟨inferInstance, inferInstance⟩

/-- Alias using the shorter naming introduced by the universe-generalized
Proposition 2.6 development. -/
theorem tensor_isCentral [Algebra.IsCentral k A] [Algebra.IsCentral k B] :
    Algebra.IsCentral k (A ⊗[k] B) :=
  tensor_product_central k A B

/-- Alias for the combined central-simple conclusion. -/
theorem tensor_simple
    [IsSimpleRing A] [IsSimpleRing B]
    [Algebra.IsCentral k A] [Algebra.IsCentral k B]
    [Module.Finite k A] :
    IsSimpleRing (A ⊗[k] B) ∧ Algebra.IsCentral k (A ⊗[k] B) :=
  tensor_central_simple k A B

end Submission.CField.BGroups
