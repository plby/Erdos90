import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniformizer series

The convergence part of Milne's Proposition 7.26 is a geometric-series
estimate: bounded coefficients multiplied by successive powers of an element
of norm less than one form a summable series.
-/

namespace Towers.NumberTheory.Milne

section

variable {K : Type*} [NormedField K] [CompleteSpace K]

/-- The convergence assertion in Milne, Proposition 7.26. -/
theorem summable_norm_one
    (a : ℕ → K) (pi : K) (ha : ∀ n, ‖a n‖ ≤ 1) (hpi : ‖pi‖ < 1) :
    Summable (fun n ↦ a n * pi ^ n) := by
  refine (summable_geometric_of_lt_one (norm_nonneg pi) hpi).of_norm_bounded
    (fun n ↦ ?_)
  rw [norm_mul, norm_pow]
  calc
    ‖a n‖ * ‖pi‖ ^ n ≤ 1 * ‖pi‖ ^ n :=
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (norm_nonneg pi) n)
    _ = ‖pi‖ ^ n := one_mul _

/-- Consequently the partial sums of a uniformizer expansion converge to its
sum in the complete field. -/
theorem sum_norm_one
    (a : ℕ → K) (pi : K) (ha : ∀ n, ‖a n‖ ≤ 1) (hpi : ‖pi‖ < 1) :
    HasSum (fun n ↦ a n * pi ^ n) (∑' n, a n * pi ^ n) :=
  (summable_norm_one a pi ha hpi).hasSum

/-- The partial sums in Milne's uniformizer expansion form a Cauchy sequence. -/
theorem cauchy_seq_range
    (a : ℕ → K) (pi : K) (ha : ∀ n, ‖a n‖ ≤ 1) (hpi : ‖pi‖ < 1) :
    CauchySeq (fun N ↦ ∑ n ∈ Finset.range N, a n * pi ^ n) :=
  (sum_norm_one a pi ha hpi).tendsto_sum_nat.cauchySeq

end


end Towers.NumberTheory.Milne
