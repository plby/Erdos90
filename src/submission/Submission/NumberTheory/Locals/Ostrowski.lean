import Submission.NumberTheory.Locals.NonarchimedeanCriterion
import Mathlib.NumberTheory.Ostrowski

/-!
# Ostrowski's theorem for the rational numbers

This file records Milne's Theorem 7.12.  Mathlib proves the full classification of
nontrivial real-valued absolute values on `ℚ`; the two declarations below separate its
archimedean and nonarchimedean clauses in Milne's form.
-/

namespace Submission.NumberTheory.Milne

/-- Milne, Theorem 7.12(a): every nontrivial archimedean absolute value on `ℚ` is
equivalent to the usual real absolute value. -/
theorem ostrowski_archimedean (v : AbsoluteValue ℚ ℝ) (_hv : v.IsNontrivial)
    (harch : ¬ IsNonarchimedean v) :
    v.IsEquiv Rat.AbsoluteValue.real := by
  apply Rat.AbsoluteValue.equiv_real_of_unbounded
  intro hbounded
  exact harch ((nonarchimedean_nat_cast v).2 hbounded)

/-- Milne, Theorem 7.12(b): every nontrivial nonarchimedean absolute value on `ℚ` is
equivalent to the `p`-adic absolute value for a unique prime `p`. -/
theorem ostrowski_nonarchimedean (v : AbsoluteValue ℚ ℝ) (hv : v.IsNontrivial)
    (hnonarch : IsNonarchimedean v) :
    ∃! p : ℕ, ∃ (_ : Fact p.Prime), v.IsEquiv (Rat.AbsoluteValue.padic p) := by
  exact Rat.AbsoluteValue.equiv_padic_of_bounded hv
    ((nonarchimedean_nat_cast v).1 hnonarch)

/-- The combined classification form of Ostrowski's theorem. -/
theorem ostrowski (v : AbsoluteValue ℚ ℝ) (hv : v.IsNontrivial) :
    v.IsEquiv Rat.AbsoluteValue.real ∨
      ∃! p : ℕ, ∃ (_ : Fact p.Prime), v.IsEquiv (Rat.AbsoluteValue.padic p) :=
  Rat.AbsoluteValue.equiv_real_or_padic v hv

end Submission.NumberTheory.Milne
