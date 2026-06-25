import Submission.NumberTheory.TameDiscriminant


open Filter

noncomputable section

namespace Submission

/--
The black-box tower input: a nested sequence of totally real number fields with
unbounded degree, uniformly bounded root discriminant, and infinitely many
rational primes that split completely throughout the tower.
-/
structure SplitTotallyTower where
  fields : ℕ → Type*
  instField : ∀ j : ℕ, Field (fields j)
  instNumberField : ∀ j : ℕ, NumberField (fields j)
  inclusions : ∀ j : ℕ, fields j ↪ fields (j + 1)
  totallyReal : ∀ j : ℕ, NumberField.IsTotallyReal (fields j)
  degree_tendsto_top : Tendsto (fun j : ℕ ↦ Module.finrank ℚ (fields j)) atTop atTop
  rootDiscriminant_bounded : ∃ ρ : ℝ, ∀ j : ℕ, rootDiscriminant (fields j) ≤ ρ
  splitPrimes : Set ℕ
  splitPrimes_infinite : splitPrimes.Infinite
  splitPrimes_spec :
    ∀ {p : ℕ}, p ∈ splitPrimes →
      Nat.Prime p ∧ p % 4 = 1 ∧ ∀ j : ℕ, splitsCompletely (fields j) p

attribute [instance] SplitTotallyTower.instField SplitTotallyTower.instNumberField

end Submission
