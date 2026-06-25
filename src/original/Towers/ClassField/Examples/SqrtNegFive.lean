import Towers.NumberTheory.Quadratic.PrimeFactorization
import Towers.NumberTheory.Quadratic.ClassGroups

/-!
# Class Field Theory, Introduction: the field Q(sqrt(-5))

This file collects the concrete `Q(sqrt(-5))` facts used in the introduction:
the rational primes `2` and `5` ramify, the standard ideal above `2` is
nonprincipal but has principal square, and the class number is two.
-/

namespace Towers.CField.Examples

open Ideal
open Towers.NumberTheory

/-- The prime `2` ramifies in the integral quadratic order `Z[sqrt(-5)]`. -/
theorem sqrt_neg_ramifies :
    (QOrd.rootIdeal (-5) 0 2 (-1)).IsPrime ∧
      QOrd.rootIdeal (-5) 0 2 (-1) *
          QOrd.rootIdeal (-5) 0 2 (-1) =
        span {(2 : QOrd (-5) 0)} := by
  simpa using QOrd.ramifies_four_three (-2)

/-- The prime `5` ramifies in the integral quadratic order `Z[sqrt(-5)]`. -/
theorem sqrt_five_ramifies :
    (QOrd.rootIdeal (-5) 0 5 0).IsPrime ∧
      QOrd.rootIdeal (-5) 0 5 0 *
          QOrd.rootIdeal (-5) 0 5 0 =
        span {(5 : QOrd (-5) 0)} := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact
    Towers.NumberTheory.Milne.ramifies_quadratic_radical
      (-5) (by
        rw [← Int.squarefree_natAbs]
        norm_num
        exact Nat.prime_five.squarefree) 5 (by norm_num)

/-- The explicit ideal `(2, 1 + sqrt(-5))` is not principal. -/
theorem sqrt_five_principal :
    ¬ SNFive.primeIdealTwo.IsPrincipal :=
  Towers.NumberTheory.Milne.sqrt_five_principal

/-- The square of `(2, 1 + sqrt(-5))` is the principal ideal `(2)`. -/
theorem sqrt_five_sq :
    SNFive.primeIdealTwo ^ 2 =
      span {(2 : Towers.NumberTheory.SNFive)} :=
  Towers.NumberTheory.Milne.sqrt_sq_principal

/-- The field `Q(sqrt(-5))` has class number two. -/
theorem sqrt_five_number :
    CNOne.negativeQuadraticNumber (-5) (by norm_num) = 2 :=
  Towers.NumberTheory.Milne.negative_quadratic_five

/-- The concrete ideal class group of `Z[sqrt(-5)]` has two elements. -/
theorem sqrt_five_two :
    Nat.card (ClassGroup Towers.NumberTheory.SNFive) = 2 :=
  Towers.NumberTheory.Milne.sqrt_five_two

end Towers.CField.Examples
