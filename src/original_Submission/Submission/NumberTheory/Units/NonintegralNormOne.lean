import Submission.NumberTheory.Quadratic.IntegralElements

/-!
# Milne, Algebraic Number Theory, Remark 5.7 and Exercise 5-3

Milne's element `(3 + 4i) / 5` has norm one but is not an algebraic integer.  It therefore
shows both that the integrality hypothesis in Corollary 5.6 is essential and that norm `±1`
alone does not imply membership in the unit group of the ring of integers.
-/

namespace Submission.NumberTheory.Milne

open Submission.NumberTheory

/-- Milne's counterexample as an explicit complex number. -/
noncomputable def nonintegralCirclePoint : ℂ :=
  (3 + 4 * Complex.I) / 5

@[simp]
theorem norm_nonintegral_circle : ‖nonintegralCirclePoint‖ = 1 := by
  norm_num [nonintegralCirclePoint, Complex.norm_def, Complex.normSq_apply]

@[simp]
theorem nonintegral_circle_point :
    ‖star nonintegralCirclePoint‖ = 1 := by
  simp [norm_nonintegral_circle]

/-- The element `(3 + 4i) / 5` in the rational Gaussian field. -/
def nonintegralNormOne : QFModel (-1) :=
  ⟨3 / 5, 4 / 5⟩

@[simp]
theorem nonintegral_norm_one : nonintegralNormOne.norm = 1 := by
  norm_num [nonintegralNormOne, QuadraticAlgebra.norm_def]

theorem nonintegral_not_integral : ¬IsIntegral ℤ nonintegralNormOne := by
  rw [QFModel.gaussian_integer_coordinates]
  rintro ⟨a, b, ha, hb⟩
  dsimp [nonintegralNormOne] at ha hb
  have ha' : (3 : ℤ) = 5 * a := by
    exact_mod_cast (by linarith : (3 : ℚ) = 5 * a)
  omega

theorem nonintegral_pow_ne (n : ℕ) (hn : 0 < n) :
    nonintegralNormOne ^ n ≠ 1 := by
  intro hpow
  apply nonintegral_not_integral
  apply IsIntegral.of_pow hn
  rw [hpow]
  exact isIntegral_one

end Submission.NumberTheory.Milne
