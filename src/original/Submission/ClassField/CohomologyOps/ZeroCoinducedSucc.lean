import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Class Field Theory, Chapter II, Corollary 1.12

Shapiro's lemma reduces the cohomology of a module coinduced from the trivial
subgroup to the cohomology of that subgroup, which vanishes in positive
degrees.
-/

namespace Submission.CField.COps

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- **Corollary II.1.12.** Positive group cohomology of a module coinduced
from the trivial subgroup vanishes. -/
theorem cohomology_coinduced_succ
    (A : Rep.{u} k (⊥ : Subgroup G)) (n : ℕ) :
    Limits.IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype A) (n + 1)) := by
  have hA : Limits.IsZero (groupCohomology A (n + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton A n
  exact Limits.IsZero.of_iso hA (groupCohomology.coindIso A (n + 1))

/-- Positive-degree formulation of Corollary II.1.12. -/
theorem zero_cohomology_coinduced
    (A : Rep.{u} k (⊥ : Subgroup G)) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype A) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact cohomology_coinduced_succ A m

end Submission.CField.COps
