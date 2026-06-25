import Submission.Group.NilpotentProducts.CommutatorIdentities
import Submission.Group.Zassenhaus.PolynomialBracketRecipes

/-!
# Theorem H1 in standard Hall coordinates through cutoff four

The complete symbolic collector through nilpotence class three applies
directly to Struik's standard Hall family.  This gives multiplication and
inverse coordinate formulas in the same coordinates as
`normalForm`, without choosing a separate canonical basis.
-/

namespace Struik
namespace P1960

open Submission
open Submission.TCTex

universe u

/-- Through cutoff four, every finite product of standard Hall normal forms
recollects with weighted-binomial polynomial coordinates. -/
theorem standard_data_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (e : List (StandardExponentFamily.{u} d)) :
    CollectedCoordinateData
      (n := n) (standardHallFamily.{u} d) e :=
  collected_data_four
    hn hn4 (standardHallFamily.{u} d)
      (fun r hr hrn =>
        standard_forms_associated d n r hr hrn)
      e

/-- The standard Hall coordinate of a product of two normal forms is an
integer linear combination of weighted Hall binomial monomials in their
input coordinates.  This is Struik's polynomial multiplication clause in
the same standard coordinates as his normal-form clause, through cutoff
four. -/
theorem standard_multiplication_four
    {d n s : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (e f : StandardExponentFamily.{u} d)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (standardHallFamily.{u} d s).index) :
    ICMonomi
      (ι := Fin 2) (standardHallFamily.{u} d) s
      (fun j : Fin 2 => [e, f].get j)
      (standardHallCoordinates d n hn
        (standardHallProduct d n e * standardHallProduct d n f) s i) := by
  have hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (standardHallFamily.{u} d r).FormsAssocGradedbasis (n := n) :=
    fun r hr hrn =>
      standard_forms_associated d n r hr hrn
  have hcoordinate :=
    products_combination_monomials
      hn (standardHallFamily.{u} d) hH [e, f]
        (standard_data_four
          hn hn4 [e, f])
        hs hsn i
  simpa [hallCoordinate, standardHallCoordinates, collectedHallProducts,
    standardHallProduct] using hcoordinate

/-- Through cutoff four, the inverse of a standard Hall normal form
recollects with weighted-binomial polynomial coordinates. -/
theorem standard_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (e : StandardExponentFamily.{u} d) :
    CollectedInverseData
      (n := n) (standardHallFamily.{u} d) e :=
  data_n_four
    hn hn4 (standardHallFamily.{u} d)
      (fun r hr hrn =>
        standard_forms_associated d n r hr hrn)
      e

/-- Each standard Hall coordinate of an inverse is an integer linear
combination of weighted Hall binomial monomials in the negated input
coordinates, through cutoff four. -/
theorem standard_inverse_four
    {d n s : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (e : StandardExponentFamily.{u} d)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (standardHallFamily.{u} d s).index) :
    ICMonomi
      (ι := Fin 1) (standardHallFamily.{u} d) s
      (fun _ : Fin 1 => negExponentFamily e)
      (standardHallCoordinates d n hn (standardHallProduct d n e)⁻¹ s i) := by
  have hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (standardHallFamily.{u} d r).FormsAssocGradedbasis (n := n) :=
    fun r hr hrn =>
      standard_forms_associated d n r hr hrn
  have hcoordinate :=
    weighted_binomial_combination
      hn (standardHallFamily.{u} d) hH e
        (standard_n_four
          hn hn4 e)
        hs hsn i
  simpa [hallCoordinate, standardHallCoordinates, standardHallProduct] using
    hcoordinate

end P1960
end Struik
