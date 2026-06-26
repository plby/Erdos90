import Mathlib.Analysis.AbsoluteValue.Equivalence

/-!
# Equivalent absolute values

This file records Milne's Proposition 7.8.  For a nontrivial real-valued absolute value,
equality of the induced topologies, preservation of the condition `|x| < 1`, and being a
positive real power of one another are equivalent.
-/

namespace Submission.NumberTheory.Milne

section

variable {K : Type*} [Field K]

/-- Milne, Proposition 7.8(a) `(a) ↔ (b)`: two absolute values define the same topology if
and only if `v x < 1` implies `w x < 1`, provided `v` is nontrivial.

The topology clause is expressed by the identity ring equivalence between the two copies of
`K` carrying the metric structures induced by `v` and `w` being a homeomorphism. -/
theorem values_topology_imp
    {v w : AbsoluteValue K ℝ} (hv : v.IsNontrivial) :
    IsHomeomorph (WithAbs.congr v w (.refl K)) ↔
      ∀ x : K, v x < 1 → w x < 1 := by
  rw [← AbsoluteValue.isEquiv_iff_isHomeomorph]
  exact ⟨fun h x hx ↦ h.lt_one_iff.mp hx,
    fun h ↦ AbsoluteValue.isEquiv_of_lt_one_imp hv h⟩

/-- Milne, Proposition 7.8(a) `(a) ↔ (c)`: two real-valued absolute values define the same
topology exactly when the second is a positive real power of the first. -/
theorem values_topology_rpow
    (v w : AbsoluteValue K ℝ) :
    IsHomeomorph (WithAbs.congr v w (.refl K)) ↔
      ∃ c : ℝ, 0 < c ∧ (v · ^ c) = w := by
  rw [← AbsoluteValue.isEquiv_iff_isHomeomorph]
  exact AbsoluteValue.isEquiv_iff_exists_rpow_eq

/-- Milne, Proposition 7.8(b) `(b) ↔ (c)`: for a nontrivial `v`, the one-sided implication
`v x < 1 → w x < 1` already forces `w` to be a positive real power of `v`. -/
theorem values_imp_rpow
    {v w : AbsoluteValue K ℝ} (hv : v.IsNontrivial) :
    (∀ x : K, v x < 1 → w x < 1) ↔
      ∃ c : ℝ, 0 < c ∧ (v · ^ c) = w := by
  rw [← values_topology_imp hv]
  exact values_topology_rpow v w

end

end Submission.NumberTheory.Milne
