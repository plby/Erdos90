import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Central.TensorProduct
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import Submission.ClassField.BrauerGroups.CentralTensor

/-!
# Chapter IV, Proposition 2.6

The tensor product of two finite-dimensional simple algebras over a field is simple if at least
one factor is central.
-/

namespace Submission.CField.BGroups

open scoped TensorProduct

universe u v w

variable {k : Type v} {A : Type u} {B : Type w} [Field k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]

private theorem central_matrix
    {D : Type w} [DivisionRing D] [Algebra k D]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (h : Algebra.IsCentral k (Matrix n n D)) : Algebra.IsCentral k D := by
  letI : Algebra.IsCentral k (Matrix n n D) := h
  constructor
  intro z hz
  have hz' : Matrix.scalar n z ∈ Subalgebra.center k (Matrix n n D) := by
    rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map]
    exact ⟨z, hz, rfl⟩
  have hzbot := Algebra.IsCentral.out hz'
  rw [Algebra.mem_bot] at hzbot ⊢
  obtain ⟨c, hc⟩ := hzbot
  refine ⟨c, ?_⟩
  let i : n := Classical.arbitrary n
  have hii := congrFun (congrFun hc i) i
  change (if i = i then algebraMap k D c else 0) = (if i = i then z else 0) at hii
  simpa using hii

/-- The matrix/tensor rearrangement used in Milne's proof of Proposition 2.6. -/
noncomputable def tensorMatrixEquiv
    {D : Type w} [Ring D] [Algebra k D] (n : Type*) [Fintype n] [DecidableEq n] :
    A ⊗[k] Matrix n n D ≃ₐ[k] Matrix n n (A ⊗[k] D) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (matrixEquivTensor n k D)).trans <|
    (Algebra.TensorProduct.assoc k k k A D (Matrix n n k)).symm.trans <|
      (matrixEquivTensor n k (A ⊗[k] D)).symm

/-- Milne, Chapter IV, Proposition 2.6, with the central factor on the right. -/
theorem tensor_simple_right
    [IsSimpleRing A] [IsSimpleRing B] [Module.Finite k B]
    [Algebra.IsCentral k B] : IsSimpleRing (A ⊗[k] B) := by
  letI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn, D, hDdiv, hDalg, hDfin, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B
  letI : DivisionRing D := hDdiv
  letI : Algebra k D := hDalg
  letI : Module.Finite k D := hDfin
  letI : NeZero n := hn
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv k B (Matrix (Fin n) (Fin n) D) e
  letI : Algebra.IsCentral k D :=
    central_matrix (k := k) (D := D)
      (n := Fin n) (inferInstance : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D))
  letI : IsSimpleRing (D ⊗[k] A) := division_simple_ring
  have hAD : IsSimpleRing (A ⊗[k] D) :=
    IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k D A).toRingEquiv inferInstance
  letI : IsSimpleRing (A ⊗[k] D) := hAD
  letI : IsSimpleRing (Matrix (Fin n) (Fin n) (A ⊗[k] D)) := inferInstance
  let E : A ⊗[k] B ≃ₐ[k] Matrix (Fin n) (Fin n) (A ⊗[k] D) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans
      (tensorMatrixEquiv (k := k) (A := A) (D := D) (Fin n))
  exact IsSimpleRing.of_ringEquiv E.symm.toRingEquiv inferInstance

/-- Milne, Chapter IV, Proposition 2.6. -/
theorem simple_ring_central
    [IsSimpleRing A] [IsSimpleRing B] [Module.Finite k A] [Module.Finite k B]
    (h : Algebra.IsCentral k A ∨ Algebra.IsCentral k B) : IsSimpleRing (A ⊗[k] B) := by
  rcases h with hA | hB
  · letI : Algebra.IsCentral k A := hA
    have hBA : IsSimpleRing (B ⊗[k] A) := tensor_simple_right
    exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k B A).toRingEquiv hBA
  · letI : Algebra.IsCentral k B := hB
    exact tensor_simple_right

/-- Compatibility form of Proposition IV.2.6 with the central factor on the
right. -/
theorem tensor_simple_central
    (k : Type v) (A : Type u) (B : Type w) [Field k] [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] [IsSimpleRing A] [IsSimpleRing B]
    [Algebra.IsCentral k B] [Module.Finite k B] :
    IsSimpleRing (A ⊗[k] B) :=
  tensor_simple_right

/-- Compatibility form of Proposition IV.2.6 with the central factor on the
left. -/
theorem tensor_simple_ring
    (k : Type v) (A : Type u) (B : Type w) [Field k] [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] [IsSimpleRing A] [IsSimpleRing B]
    [Algebra.IsCentral k A] [Module.Finite k A] :
    IsSimpleRing (A ⊗[k] B) := by
  have hBA : IsSimpleRing (B ⊗[k] A) :=
    tensor_simple_right
  exact IsSimpleRing.of_ringEquiv
    (Algebra.TensorProduct.comm k B A).toRingEquiv hBA

end Submission.CField.BGroups
