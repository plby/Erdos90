import Mathlib

/-!
# Milne, Algebraic Number Theory, Exercise 2-3

The discriminant of an inseparable finite field extension is zero.
-/

namespace Towers.NumberTheory.Milne

/-- If a finite field extension is not separable, the discriminant of every basis is zero. -/
theorem discr_zero_separable
    (K L ι : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (hsep : ¬ Algebra.IsSeparable K L) :
    Algebra.discr K b = 0 := by
  have htrace : Algebra.trace K L = 0 :=
    Algebra.trace_eq_zero_of_not_isSeparable hsep
  rw [Algebra.discr_def]
  have hmatrix : Algebra.traceMatrix K b = 0 := by
    ext i j
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, htrace]
  rw [hmatrix, Matrix.det_zero b.index_nonempty]

end Towers.NumberTheory.Milne
