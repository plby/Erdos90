import Towers.NumberTheory.Quadratic.IntegralElements

/-!
# Milne, Algebraic Number Theory, Example 2.41

The algebraic integers in a quadratic field have integral coordinates when the square-free
radicand is `2` or `3` modulo four, and half-integral coordinates when it is `1` modulo four.
-/

namespace Towers.NumberTheory.Milne

open Towers.NumberTheory

/-- The first case of Example 2.41: for a square-free radicand congruent to `2` or `3`
modulo four, the algebraic integers are precisely the elements with integer coordinates. -/
theorem quadratic_integer_coordinates
    (m : ℤ) (hm : Squarefree m) (hm23 : m % 4 = 2 ∨ m % 4 = 3)
    (x : QFModel m) :
    IsIntegral ℤ x ↔
      ∃ a b : ℤ, x.re = (a : ℚ) ∧ x.im = (b : ℚ) := by
  apply QFModel.integral_integer_coordinates m hm
  omega

/-- The second case of Example 2.41: for a square-free radicand congruent to `1` modulo
four, the algebraic integers are precisely the elements with half-integral coordinates. -/
theorem quadratic_half_coordinates
    (m : ℤ) (hm : Squarefree m) (hm1 : m % 4 = 1)
    (x : QFModel m) :
    IsIntegral ℤ x ↔
      ∃ a b : ℤ,
        x.re = (a : ℚ) + (b : ℚ) / 2 ∧
        x.im = (b : ℚ) / 2 := by
  exact QFModel.integral_half_coordinates m hm hm1 x

end Towers.NumberTheory.Milne
