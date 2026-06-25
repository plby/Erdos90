import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Milne, Algebraic Number Theory, Proposition 5.5 and Corollary 5.6

Finiteness of algebraic integers with bounded conjugates and Kronecker's theorem.
-/

namespace Submission.NumberTheory.Milne

open NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **Milne, Proposition 5.5.** In a fixed number field, the algebraic integers of degree
at most `m` whose complex conjugates all have norm less than `M` form a finite set. -/
theorem integral_degree_conjugates (m : ℕ) (M : ℝ) :
    {x : K | IsIntegral ℤ x ∧ (minpoly ℚ x).natDegree ≤ m ∧
      ∀ φ : K →+* ℂ, ‖φ x‖ < M}.Finite := by
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ M).subset ?_
  rintro x ⟨hxi, -, hx⟩
  exact ⟨hxi, fun φ ↦ (hx φ).le⟩

/-- A useful degree-free form of Proposition 5.5: bounded conjugates alone give finiteness
inside a fixed number field. -/
theorem finite_integral_conjugates (M : ℝ) :
    {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ M}.Finite :=
  NumberField.Embeddings.finite_of_norm_le K ℂ M

/-- **Milne, Corollary 5.6 (Kronecker).** An algebraic integer all of whose complex
conjugates have absolute value one is a root of unity. -/
theorem integral_all_conjugates {x : K}
    (hxi : IsIntegral ℤ x) (hx : ∀ φ : K →+* ℂ, ‖φ x‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  obtain ⟨n, hn, hxn⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hxi hx
  exact ⟨n, hn, hxn⟩

end Submission.NumberTheory.Milne
