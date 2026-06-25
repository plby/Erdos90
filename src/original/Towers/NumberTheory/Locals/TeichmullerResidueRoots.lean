import Mathlib.FieldTheory.Finite.Basic

/-!
# The residue roots used for Teichmuller representatives

Milne's Remark 7.36 starts from the fact that over a finite residue field
every element is a distinct root of `X ^ q - X`, where `q` is the field's
cardinality.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

section

variable (k : Type*) [Field k] [Fintype k]

/-- Every element of a finite field occurs, with multiplicity one, among the
roots of `X ^ q - X`. -/
theorem roots_x_univ :
    roots (X ^ Fintype.card k - X : k[X]) = Finset.univ.val :=
  FiniteField.roots_X_pow_card_sub_X k

/-- The derivative of `X ^ q - X` over the field with `q` elements is `-1`. -/
theorem derivative_x_sub :
    derivative (X ^ Fintype.card k - X : k[X]) = -1 := by
  rw [derivative_sub, derivative_X, derivative_X_pow,
    Nat.cast_card_eq_zero k, C_0, zero_mul, zero_sub]

/-- Thus every residue element is a simple root of `X ^ q - X`. -/
theorem simple_x_sub (a : k) :
    (X ^ Fintype.card k - X : k[X]).IsRoot a ∧
      (derivative (X ^ Fintype.card k - X : k[X])).eval a ≠ 0 := by
  constructor
  · simp [Polynomial.IsRoot.def, FiniteField.pow_card]
  · rw [derivative_x_sub]
    simp

end

end Towers.NumberTheory.Milne
