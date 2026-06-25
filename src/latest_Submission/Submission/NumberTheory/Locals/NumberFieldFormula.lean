import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The product formula for number fields

This file records Milne's Theorem 7.15 using Mathlib's normalized finite and
infinite places.  At a complex infinite place the factor occurs with
multiplicity two, exactly as in Milne's normalization `|sigma x| ^ 2`.
-/

namespace Submission.NumberTheory.Milne

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Milne, Theorem 7.15: the product of all normalized place values of a
nonzero element of a number field is one. -/
theorem number_product_formula {x : K} (hx : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) *
        ∏ᶠ w : FinitePlace K, w x = 1 :=
  NumberField.prod_abs_eq_one hx

end Submission.NumberTheory.Milne
