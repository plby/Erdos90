import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Milne, Algebraic Number Theory, real-field roots of unity

Milne observes after Lemma 5.2 that a field admitting a real embedding has no roots of unity
other than `1` and `-1`.
-/

namespace Submission.NumberTheory.Milne

/-- Every finite-order element of a field with a real embedding is `1` or `-1`. -/
theorem or_real_embedding
    {K : Type*} [Field K] (σ : K →+* ℝ) {ζ : K} (hζ : IsOfFinOrder ζ) :
    ζ = 1 ∨ ζ = -1 := by
  obtain ⟨n, hn, hpow⟩ := hζ.exists_pow_eq_one
  have hσpow : (σ ζ) ^ n = 1 := by
    rw [← σ.map_pow, hpow, σ.map_one]
  rcases (pow_eq_one_iff_of_ne_zero hn.ne').mp hσpow with hσ | ⟨hσ, -⟩
  · exact Or.inl (σ.injective (by simpa using hσ))
  · exact Or.inr (σ.injective (by simpa using hσ))

end Submission.NumberTheory.Milne
