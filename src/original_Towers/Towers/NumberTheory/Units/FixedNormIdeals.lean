import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Milne, Algebraic Number Theory, ideals of fixed norm

In the discussion of finding fundamental units, Milne uses that only finitely many integral
ideals have a prescribed absolute norm.
-/

namespace Towers.NumberTheory.Milne

open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- There are only finitely many ideals of the ring of integers having norm `m`. -/
theorem finite_ideals_abs (m : ℕ) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = m}.Finite :=
  Ideal.finite_setOf_absNorm_eq m

end Towers.NumberTheory.Milne
