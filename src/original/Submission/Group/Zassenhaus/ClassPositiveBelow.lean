import Submission.Group.Zassenhaus.OneSourcedInput

/-!
# Positive-below Hall-power collection through class three

At cutoff at most four, the explicit finite class-three source handles input
weight one.  Every larger positive input weight lies in the semantic
class-two tail range.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
Claim 5 power-coordinate polynomials exist at every positive input weight
through cutoff four.
-/
theorem collected_coordinate_four
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
      TSInput.coordinate_data_source
        hn hn4 H hH
  · have hTwo : 2 ≤ inputWeight := by
      omega
    exact
      collected_semantic_below
        hn H hH hinputWeight (by omega)

end TCTex
end Submission
