import Mathlib

/-!
# Milne, Algebraic Number Theory, two-hour examination

This file begins the nonduplicative material in the appendix following the solutions to the
exercises.  Question 1(a), on source PDF page 162 (`ANT.tex`, line 6772), asks whether
`(1 + i) / √2` is an algebraic integer.  It is: its square is `i`, so it is a root of the
monic polynomial `X ^ 4 + 1` over `ℤ`.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

/-- The complex number in Question 1(a) of Milne's two-hour examination. -/
noncomputable def examinationOneA : ℂ :=
  (1 + Complex.I) / (Real.sqrt 2 : ℂ)

lemma examination_one_sq : examinationOneA ^ 2 = Complex.I := by
  rw [examinationOneA, div_pow]
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by positivity)
  rw [show ((Real.sqrt 2 : ℂ) ^ 2) = 2 by exact_mod_cast hsqrt_sq]
  apply (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  calc
    (1 + Complex.I) ^ 2 = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
    _ = Complex.I * 2 := by rw [Complex.I_sq]; ring

lemma examination_one_fourth : examinationOneA ^ 4 = -1 := by
  calc
    examinationOneA ^ 4 = (examinationOneA ^ 2) ^ 2 := by ring
    _ = Complex.I ^ 2 := by rw [examination_one_sq]
    _ = -1 := Complex.I_sq

/-- Examination 1(a): `(1 + i) / √2` is an algebraic integer. -/
theorem examination_one_integral : IsIntegral ℤ examinationOneA := by
  refine ⟨X ^ 4 + C 1, monic_X_pow_add_C 1 (by norm_num), ?_⟩
  simp [examination_one_fourth]

end Towers.NumberTheory.Milne
