import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# The natural module of a full matrix algebra

This is the last assertion of Example IV.1.1, in the slightly more general form used by
Example IV.1.11: a full matrix algebra over a division ring acts simply on column vectors.
-/

namespace Submission.CField.SAlgebr

open scoped Matrix.Module

variable {D ι : Type*} [DivisionRing D] [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- A full matrix algebra can carry any fixed nonzero column vector to any target vector. -/
theorem matrix_smul (v : ι -> D) (hv : v ≠ 0) (w : ι -> D) :
    ∃ A : Matrix ι ι D, A • v = w := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv
    ext i
    exact not_ne_iff.mp (not_exists.mp h i)
  let A : Matrix ι ι D := fun i j' => if j' = j then w i * (v j)⁻¹ else 0
  refine ⟨A, ?_⟩
  ext i
  simp [Matrix.Module.smul_apply, A, hj]

/-- The natural column-vector module over a full matrix algebra is simple. -/
theorem natural_matrix_simple : IsSimpleModule (Matrix ι ι D) (ι -> D) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, ?_⟩
  intro v hv w
  obtain ⟨A, hA⟩ := matrix_smul v hv w
  exact ⟨A, hA⟩

omit [DecidableEq ι] in
/-- **Example IV.1.11.** A full matrix algebra over a division algebra is a
simple ring. -/
theorem full_matrix_simple : IsSimpleRing (Matrix ι ι D) :=
  inferInstance

end Submission.CField.SAlgebr
