import Mathlib.Data.Matrix.Basis

/-!
# Chapter IV, Example 1.13

This file records the three elementary centralizer computations for full matrix algebras:
scalar matrices commute with every matrix, the center consists of the scalar matrices, and
the centralizer of the diagonal matrices is the diagonal subalgebra.
-/

namespace Towers.CField.SAlgebr

open Matrix

variable {k ι : Type*} [CommSemiring k] [Fintype ι] [DecidableEq ι]

/-- Example IV.1.13(a): every scalar matrix commutes with every matrix. -/
theorem scalarMatrix_commutes (a : k) (M : Matrix ι ι k) :
    Commute (Matrix.scalar ι a) M :=
  Matrix.scalar_commute a (fun _ ↦ mul_comm a _) M

/-- Example IV.1.13(b): the center of a full matrix algebra over a commutative semiring is
exactly the set of scalar matrices. -/
theorem matrix_center_scalar {M : Matrix ι ι k} :
    M ∈ Set.center (Matrix ι ι k) ↔ ∃ a : k, Matrix.scalar ι a = M := by
  rw [Matrix.center_eq_range]
  rfl

omit [Fintype ι] in
/-- A matrix is diagonal precisely when all of its off-diagonal entries vanish. -/
theorem exists_eq_iff {M : Matrix ι ι k} :
    (∃ d : ι → k, M = Matrix.diagonal d) ↔ ∀ i j, i ≠ j → M i j = 0 := by
  constructor
  · rintro ⟨d, rfl⟩ i j hij
    exact Matrix.diagonal_apply_ne d hij
  · intro hM
    refine ⟨Matrix.diag M, Matrix.ext fun i j ↦ ?_⟩
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, hM i j hij]

/-- Example IV.1.13(c): a matrix commutes with every diagonal matrix if and only if it is
diagonal. -/
theorem commutes_every_diagonal {M : Matrix ι ι k} :
    (∀ d : ι → k, Commute M (Matrix.diagonal d)) ↔
      ∃ d : ι → k, M = Matrix.diagonal d := by
  constructor
  · intro hM
    rw [exists_eq_iff]
    intro i j hij
    have hentry := congrFun (congrFun (hM (Pi.single i 1)).eq i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.single_apply, hij,
      Ne.symm hij] using hentry.symm
  · rintro ⟨d, rfl⟩ e
    exact Matrix.commute_diagonal d e

end Towers.CField.SAlgebr
