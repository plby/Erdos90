import Towers.Group.Zassenhaus.PolynomialBracketSupport
import Towers.Group.Zassenhaus.ClassTwo

/-!
# Free lower-central truncation collection bounds through class two

The canonical finite Hall families form associated-graded bases.  Through
cutoff three, the semantic class-two power tail supplies Claim 5 for every
positive input weight, while automatic signed collection supplies global
product and inverse coordinate polynomials.

This file combines those packages with the existing Hall-data reduction and
fully discharges the free-truncation collection bound through nilpotence class
two.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The canonical Hall families satisfy the free-truncation collection bound at
every cutoff at most three.
-/
theorem
    concrete_commutators_n
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hn3 : n ≤ 3) :
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
      collected_semantic_below
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          hinputWeight (by omega)
  · intro e
    exact
      collected_data_four
        hn (by omega) (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e
  · intro e
    exact
      data_n_four
        hn (by omega) (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e

/--
At every cutoff at most three, a concrete finite free-truncation collection
bound exists.
-/
theorem truncation_collection_n
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hn3 : n ≤ 3) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  ⟨commutatorCountBelow
      (concreteCommutatorsWeight.{u} d) n,
    concrete_commutators_n
      hn hn3⟩

end TCTex
end Towers
