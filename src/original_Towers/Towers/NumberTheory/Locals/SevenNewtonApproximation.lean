import Towers.NumberTheory.Locals.NewtonRootLifting

/-!
# Milne, Chapter 7, Exercise 7-4(b)

The polynomial `5X^3 - 7X^2 + 3X + 6` has a root in `ℤ_[7]`
congruent to `1` modulo `7`.  The first four base-seven digits supplied by
Newton lifting are `1, 5, 0, 1`, so `379 = 1 + 5 * 7 + 7^3` is an
approximation modulo `7^4`.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

local instance sevenPrimeFact_4b : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The polynomial appearing in Milne's Exercise 7-4(b). -/
def sevenNewtonApproximation : ℤ[X] :=
  5 * X ^ 3 - 7 * X ^ 2 + 3 * X + 6

/-- Milne, Exercise 7-4(b): the indicated cubic has a `7`-adic root
congruent to `1` modulo `7`, and `379` approximates it modulo `7^4`. -/
theorem seven4B :
    ∃ α : ℤ_[7],
      sevenNewtonApproximation.aeval α = 0 ∧
        ‖α - 1‖ < 1 ∧
          ‖α - ((379 : ℤ) : ℤ_[7])‖ ≤ (7 : ℝ) ^ (-4 : ℤ) := by
  let F : ℤ[X] := sevenNewtonApproximation
  have hF1 : F.aeval (1 : ℤ_[7]) = (7 : ℤ_[7]) := by
    norm_num [F, sevenNewtonApproximation, aeval_def]
  have hFd1 : F.derivative.aeval (1 : ℤ_[7]) = (4 : ℤ_[7]) := by
    norm_num [F, sevenNewtonApproximation, aeval_def]
  have h4 : ‖(4 : ℤ_[7])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have h7 : ‖(7 : ℤ_[7])‖ = (7 : ℝ)⁻¹ := PadicInt.norm_p
  have hnewton :
      ‖F.aeval (1 : ℤ_[7])‖ < ‖F.derivative.aeval (1 : ℤ_[7])‖ ^ 2 := by
    rw [hF1, hFd1, h7, h4]
    norm_num
  obtain ⟨α, hroot, hα1, -, -⟩ := padic_newton_root F 1 hnewton
  have hα1' : ‖α - 1‖ < 1 := by
    simpa [hFd1, h4] using hα1
  refine ⟨α, ?_, ?_, ?_⟩
  · simpa [F] using hroot
  · exact hα1'
  · let q : ℤ_[7] :=
      5 * (α ^ 2 + α * 379 + 379 ^ 2) - 7 * (α + 379) + 3
    let q0 : ℤ_[7] :=
      5 * (1 ^ 2 + 1 * 379 + 379 ^ 2) - 7 * (1 + 379) + 3
    have hq0 : q0 = (717448 : ℤ_[7]) := by
      norm_num [q0]
    have hq0norm : ‖q0‖ = 1 := by
      rw [hq0]
      change ‖((717448 : ℕ) : ℤ_[7])‖ = 1
      exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
    have hqsub : q - q0 =
        (α - 1) * (5 * (α + 1 + 379) - 7) := by
      dsimp [q, q0]
      ring
    have hqsub_lt : ‖q - q0‖ < 1 := by
      rw [hqsub, norm_mul]
      calc
        ‖α - 1‖ * ‖5 * (α + 1 + 379) - 7‖ ≤ ‖α - 1‖ * 1 := by
          gcongr
          exact PadicInt.norm_le_one _
        _ < 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    have hqnorm : ‖q‖ = 1 := by
      calc
        ‖q‖ = ‖-q0‖ := PadicInt.norm_eq_of_norm_add_lt_right (by
          simpa [sub_eq_add_neg, hq0norm] using hqsub_lt)
        _ = 1 := by simp [hq0norm]
    have hfactor :
        F.aeval α - F.aeval (379 : ℤ_[7]) = (α - 379) * q := by
      simp [F, sevenNewtonApproximation, aeval_def]
      dsimp [q]
      ring
    have hF379 : F.aeval (379 : ℤ_[7]) = (271195351 : ℤ_[7]) := by
      norm_num [F, sevenNewtonApproximation, aeval_def]
    have hnormeq : ‖α - (379 : ℤ_[7])‖ = ‖(271195351 : ℤ_[7])‖ := by
      have := congrArg norm hfactor
      rw [hroot, zero_sub, norm_neg, hF379, norm_mul, hqnorm, mul_one] at this
      exact this.symm
    have hbound :
        ‖α - (379 : ℤ_[7])‖ ≤ (7 : ℝ) ^ (-4 : ℤ) := by
      rw [hnormeq]
      change ‖((271195351 : ℤ) : ℤ_[7])‖ ≤ (7 : ℝ) ^ (-4 : ℤ)
      exact (PadicInt.norm_int_le_pow_iff_dvd
        (p := 7) (k := 271195351) (n := 4)).2 (by norm_num)
    simpa using hbound

end

end Towers.NumberTheory.Milne
