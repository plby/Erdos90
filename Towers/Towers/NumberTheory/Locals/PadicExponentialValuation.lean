import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The factorial valuation in the p-adic exponential example

Milne's Example 7.29 uses Legendre's formula for the p-adic valuation of a
factorial, both as a sum of quotients and in terms of the base-`p` digits.  We
also prove the resulting exact convergence criterion for the terms of the
`p`-adic exponential and deduce convergence of the series from the complete
nonarchimedean summability criterion.
-/

namespace Towers.NumberTheory.Milne

open Filter Real Topology

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- Milne, Example 7.29: Legendre's formula, with any bound beyond the last
nonzero base-`p` digit. -/
theorem padic_val_factorial {n b : ℕ} (hnb : Nat.log p n < b) :
    padicValNat p n.factorial = ∑ i ∈ Finset.Ico 1 b, n / p ^ i :=
  padicValNat_factorial hnb

/-- The digit-sum form of the factorial valuation used in Example 7.29. -/
theorem val_factorial_digit (n : ℕ) :
    (p - 1) * padicValNat p n.factorial = n - (p.digits n).sum :=
  sub_one_mul_padicValNat_factorial n

/-- The `n`th term `x ^ n / n!` of the `p`-adic exponential series. -/
def padicExponentialTerm (x : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  x ^ n / (n.factorial : ℚ_[p])

/-- The valuation formula for an individual nonzero term of the `p`-adic exponential. -/
@[simp]
theorem padic_exponential_valuation {x : ℚ_[p]} (hx : x ≠ 0) (n : ℕ) :
    (padicExponentialTerm x n).valuation =
      (n : ℤ) * x.valuation - (padicValNat p n.factorial : ℤ) := by
  rw [padicExponentialTerm, div_eq_mul_inv,
    Padic.valuation_mul (pow_ne_zero n hx)
      (inv_ne_zero (Nat.cast_ne_zero.mpr n.factorial_ne_zero))]
  simp [sub_eq_add_neg]

/-- Milne's displayed valuation formula, cleared of its denominator `p - 1`. -/
theorem scaled_exponential_valuation {x : ℚ_[p]} (hx : x ≠ 0) (n : ℕ) :
    ((p - 1 : ℕ) : ℤ) * (padicExponentialTerm x n).valuation =
      (n : ℤ) * (((p - 1 : ℕ) : ℤ) * x.valuation - 1) +
        ((p.digits n).sum : ℤ) := by
  rw [padic_exponential_valuation hx]
  have hfac := val_factorial_digit (p := p) n
  have hdigit : (p.digits n).sum ≤ n := Nat.digit_sum_le p n
  have hfacZ :
      (((p - 1) * padicValNat p n.factorial : ℕ) : ℤ) =
        (n : ℤ) - ((p.digits n).sum : ℤ) := by
    calc
      _ = ((n - (p.digits n).sum : ℕ) : ℤ) :=
        congrArg (fun k : ℕ ↦ (k : ℤ)) hfac
      _ = _ := Nat.cast_sub hdigit
  rw [mul_sub, ← Nat.cast_mul, hfacZ]
  ring

/-- The rational inequality in Milne is equivalent to an integral inequality.
This formulation avoids any ambiguity at the prime `2`: there it says exactly
that `1 < x.valuation`. -/
theorem padic_exponential_threshold (x : ℚ_[p]) :
    (1 : ℚ) / (p - 1 : ℕ) < (x.valuation : ℚ) ↔
      (1 : ℤ) < ((p - 1 : ℕ) : ℤ) * x.valuation := by
  have hm : 0 < (p - 1 : ℕ) :=
    Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  rw [div_lt_iff₀ (by exact_mod_cast hm)]
  norm_cast
  simp [mul_comm]

/-- Above Milne's convergence threshold, the exponential terms tend to zero. -/
theorem exponential_tendsto_threshold
    {x : ℚ_[p]} (hx : x ≠ 0)
    (hthreshold : (1 : ℚ) / (p - 1 : ℕ) < (x.valuation : ℚ)) :
    Tendsto (padicExponentialTerm x) atTop (nhds 0) := by
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hmNat : 0 < (p - 1 : ℕ) := Nat.sub_pos_of_lt hp1
  have hmReal : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast hmNat
  have hscaledX : (1 : ℤ) < ((p - 1 : ℕ) : ℤ) * x.valuation :=
    (padic_exponential_threshold x).mp hthreshold
  have hvalLower (n : ℕ) :
      (n : ℝ) / (p - 1 : ℕ) ≤ ((padicExponentialTerm x n).valuation : ℝ) := by
    have hd : (1 : ℤ) ≤ ((p - 1 : ℕ) : ℤ) * x.valuation - 1 := by omega
    have hs := scaled_exponential_valuation (p := p) hx n
    have hdigits : (0 : ℤ) ≤ ((p.digits n).sum : ℤ) := by positivity
    have hn : (n : ℤ) ≤
        ((p - 1 : ℕ) : ℤ) * (padicExponentialTerm x n).valuation := by
      rw [hs]
      nlinarith
    rw [div_le_iff₀ hmReal]
    have hn' : (n : ℝ) ≤
        (((p - 1 : ℕ) : ℤ) * (padicExponentialTerm x n).valuation : ℤ) := by
      exact_mod_cast hn
    simpa [mul_comm] using hn'
  have hnorm_le (n : ℕ) :
      ‖padicExponentialTerm x n‖ ≤
        (p : ℝ) ^ (-((n : ℝ) / (p - 1 : ℕ))) := by
    have ht0 : padicExponentialTerm x n ≠ 0 := by
      exact div_ne_zero (pow_ne_zero n hx) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    rw [Padic.norm_eq_zpow_neg_valuation ht0, ← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp1.le)
    simpa only [Int.cast_neg] using neg_le_neg (hvalLower n)
  have hbound : Tendsto
      (fun n : ℕ ↦ (p : ℝ) ^ (-((n : ℝ) / (p - 1 : ℕ)))) atTop (nhds 0) := by
    let r : ℝ := (p : ℝ) ^ (-(1 / ((p - 1 : ℕ) : ℝ)))
    have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
    have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp1) (neg_neg_of_pos (one_div_pos.mpr hmReal))
    have hrpow : Tendsto (fun n : ℕ ↦ r ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    convert hrpow using 1
    funext n
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (p : ℝ))]
    congr 1
    field_simp
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun n ↦ norm_nonneg (padicExponentialTerm x n)) hnorm_le hbound

/-- A prime power has digit sum one in its own base. -/
theorem digits_sum_pow (k : ℕ) : (p.digits (p ^ k)).sum = 1 := by
  rw [show p ^ k = p ^ k * 1 by simp,
    Nat.digits_base_pow_mul (Fact.out : Nat.Prime p).one_lt zero_lt_one]
  rw [Nat.digits_def' (Fact.out : Nat.Prime p).one_lt (by omega)]
  rw [Nat.div_eq_of_lt (Fact.out : Nat.Prime p).one_lt,
    Nat.mod_eq_of_lt (Fact.out : Nat.Prime p).one_lt]
  simp

/-- If the exponential terms tend to zero, Milne's strict valuation threshold holds.
The subsequence indexed by `p ^ k` handles the boundary case, including `p = 2`. -/
theorem exponential_threshold_tendsto
    {x : ℚ_[p]} (hx : x ≠ 0)
    (htendsto : Tendsto (padicExponentialTerm x) atTop (nhds 0)) :
    (1 : ℚ) / (p - 1 : ℕ) < (x.valuation : ℚ) := by
  by_contra hnot
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hmNat : 0 < (p - 1 : ℕ) := Nat.sub_pos_of_lt hp1
  have hmInt : (0 : ℤ) < (p - 1 : ℕ) := by exact_mod_cast hmNat
  have hscaledX : ((p - 1 : ℕ) : ℤ) * x.valuation ≤ 1 := by
    exact le_of_not_gt (fun h ↦ hnot ((padic_exponential_threshold x).mpr h))
  have hval_le (k : ℕ) : (padicExponentialTerm x (p ^ k)).valuation ≤ 1 := by
    have hs := scaled_exponential_valuation (p := p) hx (p ^ k)
    rw [digits_sum_pow (p := p) k] at hs
    have hscaledTerm :
        ((p - 1 : ℕ) : ℤ) * (padicExponentialTerm x (p ^ k)).valuation ≤ 1 := by
      rw [hs]
      have hpow : (0 : ℤ) ≤ ((p ^ k : ℕ) : ℤ) := by positivity
      have hd : ((p - 1 : ℕ) : ℤ) * x.valuation - 1 ≤ 0 := sub_nonpos.mpr hscaledX
      have hmul : ((p ^ k : ℕ) : ℤ) *
          (((p - 1 : ℕ) : ℤ) * x.valuation - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpow hd
      simpa using add_le_add_right hmul 1
    nlinarith
  have hnorm_lower (k : ℕ) :
      (p : ℝ)⁻¹ ≤ ‖padicExponentialTerm x (p ^ k)‖ := by
    have ht0 : padicExponentialTerm x (p ^ k) ≠ 0 := by
      exact div_ne_zero (pow_ne_zero _ hx)
        (Nat.cast_ne_zero.mpr (p ^ k).factorial_ne_zero)
    rw [Padic.norm_eq_zpow_neg_valuation ht0, ← zpow_neg_one]
    exact (zpow_right_strictMono₀ (by exact_mod_cast hp1)).monotone
      (neg_le_neg (hval_le k))
  have hcomp : Tendsto (fun k : ℕ ↦ padicExponentialTerm x (p ^ k)) atTop (nhds 0) :=
    htendsto.comp (tendsto_pow_atTop_atTop_of_one_lt hp1)
  have hnorm : Tendsto (fun k : ℕ ↦ ‖padicExponentialTerm x (p ^ k)‖) atTop (nhds 0) := by
    simpa using tendsto_norm.comp hcomp
  have hpInv : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by positivity)
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hnorm).2 _ hpInv).exists
  exact (not_lt_of_ge (hnorm_lower k)) hk

/-- **Milne, Example 7.29.** For nonzero `x : ℚ_[p]`, the terms `x ^ n / n!`
tend to zero exactly when `ord_p(x) > 1 / (p - 1)`. -/
theorem exponential_term_tendsto {x : ℚ_[p]} (hx : x ≠ 0) :
    Tendsto (padicExponentialTerm x) atTop (nhds 0) ↔
      (1 : ℚ) / (p - 1 : ℕ) < (x.valuation : ℚ) :=
  ⟨exponential_threshold_tendsto hx,
    exponential_tendsto_threshold hx⟩

/-- At `x = 0` the first exponential term is one and all later terms vanish. -/
theorem exponential_zero_tendsto :
    Tendsto (padicExponentialTerm (0 : ℚ_[p])) atTop (nhds 0) := by
  apply (tendsto_congr' (show ∀ᶠ n in atTop, padicExponentialTerm (0 : ℚ_[p]) n = 0 by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [padicExponentialTerm, Nat.ne_zero_of_lt hn])).2
  exact tendsto_const_nhds

/-- The exact all-elements version, accounting for Mathlib's convention `valuation 0 = 0`. -/
theorem padic_exponential_tendsto (x : ℚ_[p]) :
    Tendsto (padicExponentialTerm x) atTop (nhds 0) ↔
      x = 0 ∨ (1 : ℚ) / (p - 1 : ℕ) < (x.valuation : ℚ) := by
  by_cases hx : x = 0
  · subst x
    simp only [true_or, iff_true]
    exact exponential_zero_tendsto
  · rw [exponential_term_tendsto hx]
    simp [hx]

/-- The complete nonarchimedean summability criterion, specialized to `ℚ_[p]`. -/
private theorem padic_summable_tendsto (f : ℕ → ℚ_[p]) :
    Summable f ↔ Tendsto f atTop (nhds 0) := by
  letI : IsUltrametricDist ℚ_[p] := Padic.instIsUltrametricDist p
  letI huniform : IsUniformAddGroup ℚ_[p] := SeminormedAddCommGroup.to_isUniformAddGroup
  letI hnonarch : NonarchimedeanAddGroup ℚ_[p] := IsUltrametricDist.nonarchimedeanAddGroup
  have hcrit : Summable f ↔ Tendsto f cofinite (nhds 0) :=
    @NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero ℕ ℚ_[p]
      inferInstance inferInstance huniform hnonarch inferInstance f
  simpa only [Nat.cofinite_eq_atTop] using hcrit

/-- **Milne, Example 7.29.** The `p`-adic exponential series converges exactly on
the open disk `x = 0` or `ord_p(x) > 1 / (p - 1)`. -/
theorem padic_exponential_summable (x : ℚ_[p]) :
    Summable (padicExponentialTerm x) ↔
      x = 0 ∨ (1 : ℚ) / (p - 1 : ℕ) < (x.valuation : ℚ) := by
  rw [padic_summable_tendsto, padic_exponential_tendsto]

/-- At `p = 2`, strictness excludes valuation one: the terms tend to zero exactly
when the valuation is at least two. -/
theorem adic_exponential_tendsto {x : ℚ_[2]} (hx : x ≠ 0) :
    Tendsto (padicExponentialTerm x) atTop (nhds 0) ↔ 1 < x.valuation := by
  rw [exponential_term_tendsto hx]
  norm_num
  constructor <;> intro h <;> exact_mod_cast h

/-- The corresponding explicit summability criterion at the boundary prime `2`. -/
theorem adic_exponential_summable (x : ℚ_[2]) :
    Summable (padicExponentialTerm x) ↔ x = 0 ∨ 1 < x.valuation := by
  rw [padic_exponential_summable]
  norm_num
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by exact_mod_cast h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by exact_mod_cast h)

end

end Towers.NumberTheory.Milne
