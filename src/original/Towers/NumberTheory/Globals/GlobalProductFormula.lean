import Towers.NumberTheory.Locals.NumberFieldFormula

/-!
# Milne, Chapter 8, Theorem 8.8

Milne restates the normalized product formula here after deriving it from the
completion decomposition and the norm formula.  The result was already
recorded in Chapter 7, so this file exposes it at its Chapter 8 location.
-/

namespace Towers.NumberTheory.Milne

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Milne, Theorem 8.8: the product of all normalized place values of a
nonzero element of a number field is one. -/
theorem global_number_formula {x : K} (hx : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) *
        ∏ᶠ w : FinitePlace K, w x = 1 :=
  number_product_formula hx

end Towers.NumberTheory.Milne
