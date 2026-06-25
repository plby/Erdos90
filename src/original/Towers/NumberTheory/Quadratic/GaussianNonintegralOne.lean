import Towers.NumberTheory.Quadratic.IntegralElements

attribute [-instance] DivisionRing.toRatAlgebra
attribute [-instance] QuadraticAlgebra.instAddMonoid
attribute [-instance] QuadraticAlgebra.instAddCommMonoid
attribute [-instance] QuadraticAlgebra.instAddGroup
attribute [-instance] QuadraticAlgebra.instAddCommGroup
attribute [-instance] QuadraticAlgebra.instAddCommMonoidWithOne
attribute [-instance] QuadraticAlgebra.instAddCommGroupWithOne
attribute [-instance] QuadraticAlgebra.instNonUnitalNonAssocSemiring
attribute [-instance] QuadraticAlgebra.instNonAssocSemiring
attribute [-instance] QuadraticAlgebra.instCommSemiring
attribute [-instance] QuadraticAlgebra.instModule
attribute [-instance] LieAlgebra.ofAssociativeAlgebra

/-!
# Milne, Algebraic Number Theory, Exercise 5-3

The condition that a field element have norm `1` or `-1` does not by itself make the element
an algebraic integer.  We record Milne's Gaussian-rational counterexample.
-/

namespace Towers.NumberTheory.Milne

open Towers.NumberTheory

/-- The Gaussian rational `(2+i)/(2-i) = (3+4i)/5`. -/
def gaussianNonIntegral : QFModel (-1) :=
  ⟨3 / 5, 4 / 5⟩

theorem gaussian_non_integral :
    Algebra.norm ℚ gaussianNonIntegral = 1 := by
  have hmat : Algebra.leftMulMatrix (QuadraticAlgebra.basis (-1 : ℚ) 0)
      gaussianNonIntegral = !![3 / 5, -(4 / 5); 4 / 5, 3 / 5] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [gaussianNonIntegral, Algebra.leftMulMatrix_eq_repr_mul,
        QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple,
        QuadraticAlgebra.equivProd, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  calc
    Algebra.norm ℚ gaussianNonIntegral =
        Matrix.det (Algebra.leftMulMatrix (QuadraticAlgebra.basis (-1 : ℚ) 0)
          gaussianNonIntegral) :=
      Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis (-1 : ℚ) 0)
        gaussianNonIntegral
    _ = 1 := by rw [hmat, Matrix.det_fin_two_of]; norm_num

theorem gaussian_non_not :
    ¬IsIntegral ℤ gaussianNonIntegral := by
  rw [QFModel.gaussian_integer_coordinates]
  rintro ⟨a, b, ha, hb⟩
  have ha' : (3 : ℚ) = 5 * a := by
    change (3 : ℚ) / 5 = (a : ℚ) at ha
    linarith
  have haInt : (3 : ℤ) = 5 * a := by exact_mod_cast ha'
  omega

/-- **Milne, Exercise 5-3.** There is an element of a number field with norm one that is not
an algebraic integer, hence is not a unit of its ring of integers. -/
theorem norm_not_integral :
    ∃ x : QFModel (-1), Algebra.norm ℚ x = 1 ∧ ¬IsIntegral ℤ x :=
  ⟨gaussianNonIntegral, gaussian_non_integral,
    gaussian_non_not⟩

end Towers.NumberTheory.Milne
