import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# Bounded absolute values are nonarchimedean

This file formalizes Proposition 7.2 of Milne's *Algebraic Number Theory* notes: an absolute
value is nonarchimedean if and only if it is bounded on the integer multiples of `1`.
-/

namespace Submission.NumberTheory.Milne

open Filter

section

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- A real-valued absolute value on a field is nonarchimedean exactly when every natural
multiple of `1` has absolute value at most `1`. -/
theorem nonarchimedean_nat_cast :
    IsNonarchimedean v ↔ ∀ n : ℕ, v (n : K) ≤ 1 := by
  constructor
  · intro hv n
    exact hv.apply_natCast_le_one
  · intro h
    have hnorm : ∀ n : ℕ, ‖(n : WithAbs v)‖ ≤ 1 := by
      intro n
      change v (n : K) ≤ 1
      exact h n
    letI : IsUltrametricDist (WithAbs v) :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hnorm
    intro x y
    have hxy := IsUltrametricDist.norm_add_le_max (WithAbs.toAbs v x) (WithAbs.toAbs v y)
    change v (x + y) ≤ max (v x) (v y)
    exact hxy

/-- If the values of an absolute value on integer multiples of `1` have any common upper bound,
then all its values on natural multiples of `1` are at most `1`. -/
private theorem nat_cast_int
    (h : ∃ C : ℝ, ∀ m : ℤ, v (m : K) ≤ C) :
    ∀ n : ℕ, v (n : K) ≤ 1 := by
  obtain ⟨C, hC⟩ := h
  intro n
  by_contra hn
  have hone : 1 < v (n : K) := lt_of_not_ge hn
  obtain ⟨k, hk⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hone).eventually_gt_atTop C).exists
  have hbound : v (n : K) ^ k ≤ C := by
    simpa only [Int.cast_pow, Int.cast_natCast, map_pow] using hC ((n : ℤ) ^ k)
  exact (not_lt_of_ge hbound) hk

/-- Milne, Proposition 7.2, in explicit upper-bound form: an absolute value is nonarchimedean if
and only if its values on the integer multiples of `1` are bounded above. -/
theorem nonarchimedean_int_cast :
    IsNonarchimedean v ↔ ∃ C : ℝ, ∀ m : ℤ, v (m : K) ≤ C := by
  constructor
  · intro hv
    exact ⟨1, fun _ ↦ hv.apply_intCast_le_one⟩
  · intro h
    exact (nonarchimedean_nat_cast v).2
      (nat_cast_int v h)

/-- Milne, Proposition 7.2, stated literally using boundedness of the range on integer multiples
of `1`. -/
theorem nonarchimedean_bdd_cast :
    IsNonarchimedean v ↔ BddAbove (Set.range fun m : ℤ ↦ v (m : K)) := by
  rw [nonarchimedean_int_cast v]
  simp only [bddAbove_def, Set.forall_mem_range]

end

end Submission.NumberTheory.Milne
