import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A 5-adic Cauchy sequence

Milne's Example 7.22: the sequence `4, 34, 334, 3334, ...` converges
5-adically to `2 / 3`.
-/

namespace Submission.NumberTheory.Milne

open scoped Topology

noncomputable section

open Filter
open scoped Topology

local instance fivePrimeFactCauchyExample : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The sequence `4, 34, 334, 3334, ...`, indexed from zero. -/
def fiveCauchyExample (n : ℕ) : ℚ_[5] :=
  ((10 : ℚ_[5]) ^ (n + 1) + 2) / 3

@[simp] theorem cauchy_example_zero : fiveCauchyExample 0 = 4 := by
  norm_num [fiveCauchyExample]

@[simp] theorem cauchy_example_one : fiveCauchyExample 1 = 34 := by
  norm_num [fiveCauchyExample]

@[simp] theorem cauchy_example_two : fiveCauchyExample 2 = 334 := by
  norm_num [fiveCauchyExample]

@[simp] theorem adic_cauchy_example : fiveCauchyExample 3 = 3334 := by
  norm_num [fiveCauchyExample]

/-- The elementary identity used by Milne to identify the limit. -/
theorem five_cauchy_example (n : ℕ) :
    3 * fiveCauchyExample n - 2 = (10 : ℚ_[5]) ^ (n + 1) := by
  rw [fiveCauchyExample]
  have hthree : (3 : ℚ_[5]) ≠ 0 := by norm_num
  rw [mul_div_cancel₀ _ hthree]
  ring

/-- Milne, Example 7.22: the displayed sequence converges to `2 / 3` in
`ℚ₅`. -/
theorem cauchy_example_tendsto :
    Filter.Tendsto fiveCauchyExample Filter.atTop (𝓝 (2 / 3 : ℚ_[5])) := by
  have h10 : ‖((10 : ℕ) : ℚ_[5])‖ < 1 :=
    (Padic.norm_natCast_lt_one_iff (p := 5)).mpr (by norm_num)
  have hpow : Filter.Tendsto (fun n : ℕ ↦ (10 : ℚ_[5]) ^ n)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one h10
  have hpow' : Filter.Tendsto (fun n : ℕ ↦ (10 : ℚ_[5]) ^ (n + 1))
      Filter.atTop (𝓝 0) :=
    hpow.comp (Filter.tendsto_add_atTop_nat 1)
  simpa [fiveCauchyExample] using
    (hpow'.add_const (2 : ℚ_[5])).div_const (3 : ℚ_[5])

/-- In particular the sequence is Cauchy for the 5-adic metric. -/
theorem cauchy_example_seq :
    CauchySeq fiveCauchyExample :=
  cauchy_example_tendsto.cauchySeq

end

end Submission.NumberTheory.Milne
