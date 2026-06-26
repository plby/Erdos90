import Towers.NumberTheory.Quadratic.ClassGroups
import Towers.NumberTheory.Quadratic.TwentyOneIdeals

/-!
# Principal products among the ideals in Milne's factorization of 21

Milne observes in the introduction that the four prime nonprincipal ideals
`(3, 1 ± √-5)` and `(7, 3 ± √-5)` all represent the unique nontrivial ideal class.
Consequently, the product of any two of them is principal.
-/

namespace Towers.NumberTheory.SNFive

open Ideal

/-- The four ideals displayed before Milne's three factorizations of `21`. -/
def TwentyPrimeIdeal (I : Ideal SNFive) : Prop :=
  I = primeIdealPlus ∨ I = primeIdealMinus ∨
    I = primeSevenPlus ∨ I = primeSevenMinus

private theorem twenty_ne_bot (I : Ideal SNFive)
    (hI : TwentyPrimeIdeal I) : I ≠ ⊥ := by
  rcases hI with rfl | rfl | rfl | rfl
  · intro h
    have : (3 : SNFive) ∈ primeIdealPlus := by
      rw [plus_span_pair]
      exact Ideal.subset_span (by simp)
    rw [h] at this
    norm_num at this
  · intro h
    have : (3 : SNFive) ∈ primeIdealMinus := by
      rw [minus_span_pair]
      exact Ideal.subset_span (by simp)
    rw [h] at this
    norm_num at this
  · intro h
    have : (7 : SNFive) ∈ primeSevenPlus := by
      rw [seven_plus_pair]
      exact Ideal.subset_span (by simp)
    rw [h] at this
    norm_num at this
  · intro h
    have : (7 : SNFive) ∈ primeSevenMinus := by
      rw [seven_minus_pair]
      exact Ideal.subset_span (by simp)
    rw [h] at this
    norm_num at this

private theorem twenty_not_principal (I : Ideal SNFive)
    (hI : TwentyPrimeIdeal I) : ¬ I.IsPrincipal := by
  rcases hI with rfl | rfl | rfl | rfl
  · exact plus_not_principal
  · exact minus_not_principal
  · exact seven_plus_principal
  · exact seven_minus_principal

/-- Milne, Introduction, page 13: the product of any two of the four displayed prime
nonprincipal ideals is principal. -/
theorem twenty_ideal_principal
    {I J : Ideal SNFive} (hI : TwentyPrimeIdeal I)
    (hJ : TwentyPrimeIdeal J) :
    (I * J).IsPrincipal :=
  Milne.sqrt_five_not
    (twenty_ne_bot I hI) (twenty_ne_bot J hJ)
    (twenty_not_principal I hI)
    (twenty_not_principal J hJ)

end Towers.NumberTheory.SNFive
