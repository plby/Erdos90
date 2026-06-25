import Towers.Group.Zassenhaus.PolynomialBracketSupport
import Towers.Group.Zassenhaus.ClassPositiveBelow

/-!
# Free lower-central truncation collection bounds through class three

The canonical finite Hall families form associated-graded bases.  Through
cutoff four, the explicit weight-one source and semantic higher-weight tail
supply Claim 5, while automatic signed collection supplies global product
and inverse coordinate polynomials.

This file combines those packages with the existing Hall-data reduction and
fully discharges the free-truncation collection bound through nilpotence class
three.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The canonical Hall families satisfy the free-truncation collection bound at
every cutoff at most four.
-/
theorem
    commutators_truncation_four
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4) :
    TruncationCollectionBound.{u}
      p d n
        (commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n) := by
  apply free_truncation_data
    hn (concreteCommutatorsWeight.{u} d)
      (fun s hs hsn =>
        concrete_forms_associated
          d n s hs hsn)
  · intro e inputWeight hinputWeight
    exact
      collected_coordinate_four
        hn hn4 (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          hinputWeight
  · intro e
    exact
      collected_data_four
        hn hn4 (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e
  · intro e
    exact
      data_n_four
        hn hn4 (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e

/--
At every cutoff at most four, a concrete finite free-truncation collection
bound exists.
-/
theorem free_n_four
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  ⟨commutatorCountBelow
      (concreteCommutatorsWeight.{u} d) n,
    commutators_truncation_four
      hn hn4⟩

end TCTex
end Towers
