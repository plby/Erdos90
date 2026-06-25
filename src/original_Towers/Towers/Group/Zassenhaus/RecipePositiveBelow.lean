import Towers.Group.Zassenhaus.RecipeAutomaticCollection
import Towers.Group.Zassenhaus.OneSourcedInput

/-!
# Positive Hall-power collection from retained class-three recipes

Through cutoff four, the retained recipe packet handles the explicit
weight-one class-three source.  Every larger positive input weight lies in the
semantic class-two tail range.  Together these supply Claim 5 and its
Hall-coordinate degree consequence.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace TSInput

/--
The explicit weight-one class-three source is collected automa by the
retained recipe packet.
-/
theorem coordinate_recipe_source
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H} :
    CollectedPolynomialData (n := n) H e 1 :=
  (classThreeSource hn4 e)
    |>.recipeAutomaticCollection
      hn hn4 H hH
      (word_least_source hn4 e) (by
        omega)

end TSInput

open TSInput

/--
Through cutoff four, retained recipes supply Claim 5 power-coordinate
polynomials at every positive input weight.
-/
theorem
    collected_recipe_four
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    {e : HEFam H} :
    CollectedPolynomialData
      (n := n) H e inputWeight := by
  by_cases hOne : inputWeight = 1
  · subst inputWeight
    exact
      coordinate_recipe_source
        hn hn4 H hH
  · exact
      collected_semantic_below
        hn H hH hinputWeight (by omega)

/--
Through cutoff four, retained recipes supply the quantified Claim 5 input.
-/
theorem
    forall_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  intro e inputWeight hinputWeight
  exact
    collected_recipe_four
      hn hn4 H hH hinputWeight

/--
Through cutoff four, retained recipes yield the polynomial degree bound for
every Hall coordinate of a power.
-/
theorem coordinate_n_four
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    IVMost
      (fun q : ℕ => hallCoordinate hn H hH (u ^ q) i)
      (s / r) := by
  exact
    integer_valued_most
      hn H hH
        (forall_n_four
          hn hn4 H hH)
        u hu hr hs hsn i

end TCTex
end Towers
