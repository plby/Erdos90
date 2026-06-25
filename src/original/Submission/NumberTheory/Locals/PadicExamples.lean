import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Small p-adic examples

Examples 7.27 and 7.28 from Milne's *Algebraic Number Theory*.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

noncomputable section

local instance twoPrimeFactPadicExamples : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance fivePrimeFactPadicExamples : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Milne, Example 7.27: `1 + 2 + 2^2 + ...` converges to `-1` in `ℚ₂`. -/
theorem adic_geometric_sum :
    HasSum (fun n : ℕ ↦ (2 : ℚ_[2]) ^ n) (-1) := by
  convert hasSum_geometric_of_norm_lt_one (Padic.norm_p_lt_one (p := 2)) using 1
  norm_num

/-- Milne, Example 7.28: `-1` is a square in `ℚ₅`. -/
theorem five_adic_sq :
    ∃ x : ℚ_[5], x ^ 2 = -1 := by
  let F : ℤ[X] := X ^ 2 + 1
  let a : ℤ_[5] := 2
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    have hFa : F.aeval a = (5 : ℤ_[5]) := by norm_num [F, a]
    have hFda : F.derivative.aeval a = (4 : ℤ_[5]) := by
      simp [F, a, aeval_def]
    have h4 : ‖(4 : ℤ_[5])‖ = 1 :=
      PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
    have h5 : ‖(5 : ℤ_[5])‖ = (5 : ℝ)⁻¹ := PadicInt.norm_p
    rw [hFa, hFda, h5, h4]
    norm_num
  obtain ⟨z, hz, -, -, -⟩ := hensels_lemma hnorm
  refine ⟨(z : ℚ_[5]), ?_⟩
  have hz0 : z ^ 2 + 1 = 0 := by
    simpa [F] using hz
  have hz' := congrArg (fun w : ℤ_[5] ↦ (w : ℚ_[5])) hz0
  norm_num at hz'
  linear_combination hz'

end

end Submission.NumberTheory.Milne
