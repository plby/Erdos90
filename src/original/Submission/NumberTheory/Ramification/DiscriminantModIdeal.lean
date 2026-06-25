import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Discriminants modulo an ideal

This file formalizes Milne's Lemma 3.36: reducing a finite free algebra and a basis modulo an
ideal reduces the discriminant by the same ideal.
-/

namespace Submission.NumberTheory.Milne

open Module

universe u v w z

/-- Discriminants commute with extension of scalars. -/
theorem discr_baseChange
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Basis ι A B) :
    Algebra.discr C (b.baseChange C) = algebraMap A C (Algebra.discr A b) := by
  letI : Module.Free A B := Module.Free.of_basis b
  letI : Module.Finite A B := Module.Finite.of_basis b
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, Basis.baseChange_apply]
  have hmul :
      (Algebra.lmul A B (b i * b j)).baseChange C =
        Algebra.lmul C (TensorProduct A C B) (1 ⊗ₜ[A] (b i * b j)) :=
    Algebra.baseChange_lmul (b i * b j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.trace_apply, ← hmul,
    LinearMap.trace_baseChange, Algebra.trace_apply]

/-- The basis of the quotient algebra obtained by reducing a basis modulo an ideal. -/
noncomputable def basisModIdeal
    (A : Type u) {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type z} (b : Basis ι A B) (I : Ideal A) :
    Basis ι (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  (b.baseChange (A ⧸ I)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv

@[simp]
theorem basis_mod_ideal
    (A : Type u) {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type z} (b : Basis ι A B) (I : Ideal A) (i : ι) :
    basisModIdeal A b I i = Ideal.Quotient.mk (I.map (algebraMap A B)) (b i) := by
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective
  simp [basisModIdeal]

set_option maxRecDepth 4000 in
/-- **Milne, Lemma 3.36.** The discriminant of the basis induced modulo an ideal is the
reduction modulo that ideal of the original discriminant. -/
theorem discr_modIdeal
    (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Basis ι A B) (I : Ideal A) :
    Algebra.discr (A ⧸ I) (basisModIdeal A b I) =
      Ideal.Quotient.mk I (Algebra.discr A b) := by
  rw [Algebra.discr_eq_discr_of_algEquiv (basisModIdeal A b I)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)]
  have hbasis :
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I :
          (B ⧸ I.map (algebraMap A B)) → TensorProduct A (A ⧸ I) B) ∘
          (basisModIdeal A b I : ι → B ⧸ I.map (algebraMap A B)) =
        (b.baseChange (A ⧸ I) : ι → TensorProduct A (A ⧸ I) B) := by
    funext i
    rw [Function.comp_apply, basisModIdeal, Basis.map_apply]
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).apply_symm_apply _
  rw [hbasis]
  exact discr_baseChange A B (A ⧸ I) b

end Submission.NumberTheory.Milne
