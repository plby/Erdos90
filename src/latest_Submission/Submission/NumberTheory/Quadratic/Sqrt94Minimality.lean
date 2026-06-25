import Submission.NumberTheory.Quadratic.Sqrt94Fraction
import Submission.NumberTheory.Quadratic.ContinuedFractionMinimality
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Pell
import Mathlib.Tactic.NormNum.IsSquare

/-!
# Milne, Algebraic Number Theory, fundamental Pell solution for sqrt(94)

This file connects Milne's exact Pell solution for `d = 94` with Mathlib's notion of a
fundamental Pell solution.
-/

namespace Submission.NumberTheory.Milne

open Pell

/-- The `y`-coordinate of a Pell solution divides the `y`-coordinate of each nonnegative
power. -/
theorem Pell.Solution₁.y_dvd_y_pow {d : ℤ} (a : Pell.Solution₁ d) (n : ℕ) :
    a.y ∣ (a ^ n).y := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨(a ^ n).x + k * a.x, ?_⟩
      rw [pow_succ, Pell.Solution₁.y_mul, hk]
      ring

/-- Milne's displayed solution, regarded as a solution of the positive Pell equation. -/
def sqrt94Pell : Pell.Solution₁ 94 :=
  Pell.Solution₁.mk 2143295 221064 sqrt_94_identity

@[simp] theorem sqrt_94_x : sqrt94Pell.x = 2143295 := rfl

@[simp] theorem sqrt_94_y : sqrt94Pell.y = 221064 := rfl

/-- The solution `2143295 + 221064 * √94` is the fundamental positive solution of
`x² - 94y² = 1`, as asserted in Milne's continued-fraction example. -/
theorem sqrt_94_fundamental : Pell.IsFundamental sqrt94Pell := by
  let M := integralContinuedMobius
    (completeIntBlock (Real.sqrt 94) 0 16)
  obtain ⟨hpell, hfund⟩ :=
    period_continuant_even
      (d := 94) (s := 16) (by norm_num) (by norm_num) (by norm_num)
      sqrt_94_least.1 sqrt_94_least.2
      ⟨8, by norm_num⟩
  change Pell.IsFundamental (Pell.Solution₁.mk M.a M.c hpell) at hfund
  have hqsPos :
      ∀ q ∈ completeIntBlock (Real.sqrt 94) 0 16, 0 < q :=
    complete_sqrt_pos (d := 94) (by norm_num) 16
  have hcPos : 0 < M.c := by
    change 0 <
      (integralContinuedMobius
        (⌊completeQuotient 0 (Real.sqrt 94)⌋ ::
          completeIntBlock (Real.sqrt 94) 1 15)).c
    apply continued_mobius_c
    simpa only [completeIntBlock] using hqsPos
  have hfirst :
      (GenContFract.of (Real.sqrt 94)).convs 15 =
        (M.a : ℝ) / M.c := by
    simpa only [M] using
      cont_convergent_column
        (quadratic_irrational_cast (d := 94) (by norm_num)).irrational 15
  have hrat :
      ((M.a : ℚ) / M.c) = (2143295 : ℚ) / 221064 := by
    exact_mod_cast hfirst.symm.trans sqrt_fifteenth_convergent
  have hMcop : IsCoprime M.a M.c := by
    dsimp only [M]
    exact continued_mobius_column
      (completeIntBlock (Real.sqrt 94) 0 16)
  have hMcopNat : Nat.Coprime M.a.natAbs M.c.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hMcop
  have hpq : IsCoprime (2143295 : ℤ) 221064 := by
    refine ⟨2143295, -94 * 221064, ?_⟩
    nlinarith [sqrt_94_identity]
  have hpqNat : Nat.Coprime (2143295 : ℤ).natAbs (221064 : ℤ).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hpq
  obtain ⟨hMa, hMc⟩ :=
    Rat.div_int_inj hcPos (by norm_num) hMcopNat hpqNat hrat
  have heq :
      Pell.Solution₁.mk M.a M.c hpell = sqrt94Pell := by
    apply Pell.Solution₁.ext
    · simpa [sqrt94Pell] using hMa
    · simpa [sqrt94Pell] using hMc
  rwa [heq] at hfund

/-- Every positive Pell solution for `d = 94` is a natural power of Milne's solution. -/
theorem sqrt_94_nonneg {a : Pell.Solution₁ 94} (hx : 0 < a.x) (hy : 0 ≤ a.y) :
    ∃ n : ℕ, a = sqrt94Pell ^ n :=
  sqrt_94_fundamental.eq_pow_of_nonneg hx hy

/-- The negative Pell equation for `d = 94` has no integral solutions.  Modulo
`47` it would assert that `-1` is a square, while `47 ≡ 3 (mod 4)`. -/
theorem sqrt_94_impossible (x y : ℤ) :
    x ^ 2 - 94 * y ^ 2 ≠ -1 := by
  letI : Fact (Nat.Prime 47) := ⟨by decide⟩
  intro h
  have hz : (x : ZMod 47) ^ 2 = -1 := by
    have hz' := congrArg (fun z : ℤ ↦ (z : ZMod 47)) h
    have h94 : (94 : ZMod 47) = 0 := by decide
    simpa [h94] using hz'
  have hmod := ZMod.mod_four_ne_three_of_sq_eq_neg_one hz
  norm_num at hmod

/-- Every unit of `ℤ√94` is, up to sign, an integral power of Milne's
fundamental unit.  This is the full unit-group form of the page 93 claim. -/
theorem sqrt_94_pell (z : ℤ√94) (hz : IsUnit z) :
    ∃ m : ℤ,
      z = ((sqrt94Pell ^ m : Pell.Solution₁ 94) : ℤ√94) ∨
      z = -((sqrt94Pell ^ m : Pell.Solution₁ 94) : ℤ√94) := by
  have hnorm : z.re ^ 2 - 94 * z.im ^ 2 = 1 := by
    rw [zsqrtd_pell_equation] at hz
    rcases hz with hplus | hminus
    · exact hplus
    · exact (sqrt_94_impossible z.re z.im hminus).elim
  let a : Pell.Solution₁ 94 := Pell.Solution₁.mk z.re z.im hnorm
  obtain ⟨m, h | h⟩ := sqrt_94_fundamental.eq_zpow_or_neg_zpow a
  · refine ⟨m, Or.inl ?_⟩
    simpa [a] using congrArg (fun w : Pell.Solution₁ 94 ↦ (w : ℤ√94)) h
  · refine ⟨m, Or.inr ?_⟩
    simpa [a] using congrArg (fun w : Pell.Solution₁ 94 ↦ (w : ℤ√94)) h

end Submission.NumberTheory.Milne
