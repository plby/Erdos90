import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The product formula for the rational numbers

Milne's Theorem 7.13 is the rational-number case of Mathlib's product formula for
number fields.  The finite product below ranges over the normalized finite places and
the ordinary product ranges over the normalized infinite places.
-/

namespace Submission.NumberTheory.Milne

/-- Milne, Theorem 7.13: the product of all normalized absolute values of a nonzero
rational number is one. -/
theorem rational_productFormula {x : ℚ} (hx : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace ℚ, w x ^ w.mult) *
        ∏ᶠ w : NumberField.FinitePlace ℚ, w x = 1 :=
  NumberField.prod_abs_eq_one hx

end Submission.NumberTheory.Milne
