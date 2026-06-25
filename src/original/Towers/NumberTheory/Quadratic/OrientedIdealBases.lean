import Towers.NumberTheory.Quadratic.IdealNormForms

/-!
# Milne, Algebraic Number Theory, Theorem 4.29: oriented ideal bases

An ordered basis of an integral ideal is positively oriented relative to an ordered basis of the
ring of integers when the determinant of its coordinate matrix is positive.  Since the transition
matrix between two integral bases is unimodular, two positively oriented bases differ by an
element of `SL(2, Z)`.  Consequently, the proper-equivalence class of the normalized ideal norm
form does not depend on the chosen positively oriented basis.
-/

namespace Towers.NumberTheory.Milne

open scoped MatrixGroups NumberField
open Module

noncomputable section

namespace INForm

variable {K : Type*} [Field K] [NumberField K]

/-- The coordinate matrix of an ordered ideal basis relative to an ordered basis of the ring of
integers.  Its columns are the two ideal-basis vectors. -/
def basisCoordinateMatrix (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)}
    (b : Basis (Fin 2) ℤ I) : Matrix (Fin 2) (Fin 2) ℤ :=
  B.toMatrix fun i => (b i : 𝓞 K)

/-- An ordered basis of an integral ideal is positively oriented when its coordinate determinant
relative to the fixed ring-of-integers basis is positive. -/
def IsPositivelyOriented (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)}
    (b : Basis (Fin 2) ℤ I) : Prop :=
  0 < (basisCoordinateMatrix B b).det

/-- Ordered ideal bases carrying the positive orientation induced by `B`. -/
abbrev PositivelyOrientedBasis (B : Basis (Fin 2) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) :=
  {b : Basis (Fin 2) ℤ I // IsPositivelyOriented B b}

omit [NumberField K] in
/-- Coordinate matrices compose with the change-of-basis matrix. -/
theorem basis_matrix_change (B : Basis (Fin 2) ℤ (𝓞 K))
    {I : Ideal (𝓞 K)} (b b' : Basis (Fin 2) ℤ I) :
    basisCoordinateMatrix B b' = basisCoordinateMatrix B b * b.toMatrix b' := by
  ext i j
  have h := b.sum_toMatrix_smul_self b' j
  have h' := congrArg (fun x : I ↦ B.repr (x : 𝓞 K) i) h
  simpa only [basisCoordinateMatrix, Matrix.mul_apply, Basis.toMatrix_apply,
    map_sum, Submodule.coe_sum, map_smul, Submodule.coe_smul_of_tower, smul_eq_mul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, mul_comm] using h'.symm

omit [NumberField K] in
/-- The transition matrix between two positively oriented ideal bases has determinant one. -/
theorem matrix_positively_oriented
    (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)}
    (b b' : Basis (Fin 2) ℤ I) (hb : IsPositivelyOriented B b)
    (hb' : IsPositivelyOriented B b') :
    (b.toMatrix b').det = 1 := by
  let M := b.toMatrix b'
  have hmatrix := basis_matrix_change B b b'
  have hdet : (basisCoordinateMatrix B b').det =
      (basisCoordinateMatrix B b).det * M.det := by
    rw [hmatrix, Matrix.det_mul]
  have hMpos : 0 < M.det := by
    apply pos_of_mul_pos_right (a := (basisCoordinateMatrix B b).det)
    · rw [← hdet]
      exact hb'
    · exact hb.le
  letI := Basis.invertibleToMatrix b b'
  have hunit : IsUnit M.det := Matrix.isUnit_det_of_invertible M
  rcases Int.isUnit_eq_one_or hunit with h | h
  · exact h
  · rw [h] at hMpos
    norm_num at hMpos

/-- The determinant-one transition matrix between two positively oriented bases. -/
def orientedTransition (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)}
    (b b' : PositivelyOrientedBasis B I) : SL(2, ℤ) :=
  ⟨b.1.toMatrix b'.1,
    matrix_positively_oriented B b.1 b'.1 b.2 b'.2⟩

omit [NumberField K] in
@[simp]
theorem orientedTransition_apply (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)}
    (b b' : PositivelyOrientedBasis B I) (i j : Fin 2) :
    orientedTransition B b b' i j = b.1.toMatrix b'.1 i j :=
  rfl

omit [NumberField K] in
/-- The columns of the oriented transition matrix express the second basis in the first. -/
theorem orientedTransition_smul (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)}
    (b b' : PositivelyOrientedBasis B I) (j : Fin 2) :
    (b'.1 j : 𝓞 K) =
      orientedTransition B b b' 0 j • (b.1 0 : 𝓞 K) +
        orientedTransition B b b' 1 j • (b.1 1 : 𝓞 K) := by
  have h := b.1.sum_toMatrix_smul_self b'.1 j
  rw [Fin.sum_univ_two] at h
  have h' := congrArg (fun x : I ↦ (x : 𝓞 K)) h
  rw [orientedTransition_apply, orientedTransition_apply]
  simpa only [Submodule.coe_add, Submodule.coe_smul_of_tower] using h'.symm

/-- **Theorem 4.29 (oriented-basis independence).**  Positively oriented bases of the same
nonzero integral ideal produce properly equivalent normalized norm forms. -/
theorem positi_orien_equiv
    (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (b b' : PositivelyOrientedBasis B I) :
    (formOfBasis I b.1).Equivalent (formOfBasis I b'.1) := by
  apply form_equivalent B hI b.1 b'.1 (orientedTransition B b b')
  · exact orientedTransition_smul B b b' 0
  · exact orientedTransition_smul B b b' 1

/-- Hence the proper-equivalence quotient class of the ideal norm form is independent of the
chosen positively oriented basis. -/
theorem form_positively_oriented
    (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (b b' : PositivelyOrientedBasis B I) :
    (Quotient.mk _ (formOfBasis I b.1) : BQForm.Class) =
      Quotient.mk _ (formOfBasis I b'.1) := by
  apply Quotient.sound
  exact positi_orien_equiv B hI b b'

end INForm

end

end Towers.NumberTheory.Milne
