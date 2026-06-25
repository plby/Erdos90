import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Discriminant

/-!
# Discriminants of product algebras

Milne's Lemma 3.37: the discriminant of a finite product of finite free algebras is the
product of their discriminants.
-/

namespace Towers.NumberTheory.Milne

open Matrix Module

variable (A B C : Type*)
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]
variable [Module.Free A B] [Module.Free A C]
variable [Module.Finite A B] [Module.Finite A C]

private def sigmaFiberEquiv {ι : Type*} (κ : ι → Type*) (i : ι) :
    {x : Σ j, κ j // x.1 = i} ≃ κ i where
  toFun x := cast (congrArg κ x.property) x.1.2
  invFun x := ⟨⟨i, x⟩, rfl⟩
  left_inv x := by
    rcases x with ⟨⟨j, x⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

/-- The determinant of a block-diagonal matrix whose blocks may have different finite sizes. -/
private theorem det_blockDiagonal'
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : ∀ i, Matrix (κ i) (κ i) A) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  have htri := Matrix.blockTriangular_blockDiagonal' M
  calc
    (Matrix.blockDiagonal' M).det =
        ∏ i ∈ Finset.univ.image Sigma.fst,
          ((Matrix.blockDiagonal' M).toSquareBlock Sigma.fst i).det := htri.det
    _ = ∏ i ∈ Finset.univ,
          ((Matrix.blockDiagonal' M).toSquareBlock Sigma.fst i).det := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro i _ hi
      letI : IsEmpty (κ i) :=
        ⟨fun x ↦ hi (Finset.mem_image.mpr ⟨⟨i, x⟩, Finset.mem_univ _, rfl⟩)⟩
      letI : IsEmpty {x : Σ j, κ j // x.1 = i} :=
        ⟨fun x ↦ isEmptyElim (cast (congrArg κ x.property) x.1.2)⟩
      exact Matrix.det_isEmpty
    _ = ∏ i, (M i).det := by
      apply Finset.prod_congr rfl
      intro i _
      let e := sigmaFiberEquiv κ i
      rw [← Matrix.det_submatrix_equiv_self e (M i)]
      congr 1
      ext x y
      rcases x with ⟨⟨j, x⟩, hx⟩
      rcases y with ⟨⟨k, y⟩, hy⟩
      cases hx
      cases hy
      simp [Matrix.toSquareBlock_def, e, sigmaFiberEquiv]

/-- The trace of an element of a finite product algebra is the sum of its component traces. -/
private theorem trace_pi_apply
    {ι : Type*} [Fintype ι]
    {D : ι → Type*} [∀ i, CommRing (D i)] [∀ i, Algebra A (D i)]
    {κ : ι → Type*} [∀ i, Finite (κ i)]
    (b : ∀ i, Basis (κ i) A (D i)) (x : ∀ i, D i) :
    Algebra.trace A (∀ i, D i) x = ∑ i, Algebra.trace A (D i) (x i) := by
  classical
  letI (i : ι) : Fintype (κ i) := Fintype.ofFinite (κ i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  simp_rw [Algebra.trace_eq_matrix_trace (b _), Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]

/-- The binary case of Milne's Lemma 3.37.  The product basis makes the trace matrix
block diagonal, so its determinant is the product of the two discriminants. -/
theorem discr_prod
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι A B) (c : Basis κ A C) :
    Algebra.discr A (b.prod c) = Algebra.discr A b * Algebra.discr A c := by
  rw [Algebra.discr_def, Algebra.discr_def, Algebra.discr_def]
  have hmatrix : Algebra.traceMatrix A (b.prod c) =
      Matrix.fromBlocks (Algebra.traceMatrix A b) 0 0 (Algebra.traceMatrix A c) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        Algebra.trace_prod_apply]
  rw [hmatrix, Matrix.det_fromBlocks_zero₂₁]

/-- Milne's Lemma 3.37: for the basis obtained by adjoining the bases of a finite family of
finite free algebras, the discriminant of the product is the product of the discriminants. -/
theorem discr_pi
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {D : ι → Type*} [∀ i, CommRing (D i)] [∀ i, Algebra A (D i)]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Basis (κ i) A (D i)) :
    Algebra.discr A (Pi.basis b) = ∏ i, Algebra.discr A (b i) := by
  classical
  rw [Algebra.discr_def]
  have hmatrix : Algebra.traceMatrix A (Pi.basis b) =
      Matrix.blockDiagonal' (fun i ↦ Algebra.traceMatrix A (b i)) := by
    ext x y
    rcases x with ⟨i, x⟩
    rcases y with ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Pi.basis_apply]
      rw [trace_pi_apply A b]
      simp only [Pi.mul_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        rw [Pi.single_eq_of_ne hki, zero_mul, map_zero]
      · simp
    · simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Pi.basis_apply]
      rw [trace_pi_apply A b]
      simp only [Pi.mul_apply]
      have hsum :
          ∑ k, Algebra.trace A (D k)
            (Pi.single i ((b i) x) k * Pi.single j ((b j) y) k) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        by_cases hki : k = i
        · subst k
          rw [Pi.single_eq_of_ne hij, mul_zero, map_zero]
        · rw [Pi.single_eq_of_ne hki, zero_mul, map_zero]
      rw [hsum]
      simp [Matrix.blockDiagonal'_apply, hij]
  rw [hmatrix, det_blockDiagonal']
  simp only [Algebra.discr_def]

end Towers.NumberTheory.Milne
