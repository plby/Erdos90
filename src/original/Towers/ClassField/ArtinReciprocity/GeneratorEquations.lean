import Towers.NumberTheory.Quadratic.SqrtFiveBiquadratic
import Towers.ClassField.Examples.SqrtNegFive

/-!
# Chapter V, Section 3, Example 3.9

The Towers ANT development models `Q(i, sqrt(5))`, proves the displayed
generator equations and integrality facts, and packages the numerical and
unramified characterization needed for it to be the Hilbert class field of
`Q(sqrt(-5))`.  Mathlib does not yet define Hilbert class fields as objects,
so the final statement remains in that characterization form.
-/

namespace Towers.CField.ARecip

open Towers.NumberTheory
open Towers.NumberTheory.Milne

/-- The concrete characterization of the Hilbert-class-field claim used in
Example 3.9: an abelian, everywhere-unramified quadratic extension over a
base field of class number two. -/
def SqrtNegFiveIsHilbertClassField
    (k E : Type*) [Field k] [Field E] [NumberField k] [NumberField E]
    [Algebra k E] : Prop :=
  IsAbelianGalois k E ∧
    NumberField.classNumber k = 2 ∧
    Module.finrank k E = 2 ∧
    EverywhereUnramified k E

/-- The two generators in the model of `Q(i, sqrt(5))` satisfy the expected
quadratic equations. -/
theorem generator_equations :
    sqrt_biquadratic_i ^ 2 = -1 ∧ sqrtNegBiquadraticsqrt ^ 2 = 5 :=
  ⟨sqrt_biquadratici_sq, five_biquadraticsqrt_sq⟩

/-- The displayed generators are algebraic integers. -/
theorem generators_integral :
    IsIntegral ℤ sqrt_biquadratic_i ∧ IsIntegral ℤ sqrtFiveBiquadraticgamma :=
  sqrt_biqua_integ

/-- The class-number computation underlying Example 3.9. -/
theorem equations_sqrt_five :
    CNOne.negativeQuadraticNumber (-5) (by norm_num) = 2 :=
  sqrt_five_biquadraticsqrt

/-- The tower calculation used in Example 3.9: if the lower and total
ramification indices are both two, the upper quadratic step is unramified. -/
theorem top_ramification_idx
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P.IsMaximal] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hbase : p.ramificationIdx P = 2) (htotal : p.ramificationIdx Q = 2) :
    P.ramificationIdx Q = 1 :=
  sqrt_five_biquadratictop p P Q hbase htotal

/-- The abstract characterization used for the Hilbert-class-field claim in
Example 3.9. -/
theorem hilbert_degree_unramified
    {k E : Type*} [Field k] [Field E] [NumberField k] [NumberField E]
    [Algebra k E] [IsScalarTower ℚ k E]
    (habelian : IsAbelianGalois k E)
    (hclass : NumberField.classNumber k = 2)
    (hdegree : Module.finrank k E = 2)
    (hunramified : EverywhereUnramified k E) :
    SqrtNegFiveIsHilbertClassField k E :=
  ⟨habelian, hclass, hdegree, hunramified⟩

end Towers.CField.ARecip
