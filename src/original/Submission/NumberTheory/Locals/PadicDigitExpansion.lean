import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Canonical p-adic digit expansions

This file makes the concrete `p`-adic instance of Milne's Proposition 7.26
explicit.  Mathlib's `PadicInt.appr x n` is the unique natural representative
of `x` modulo `p ^ n`; its successive differences therefore determine the
base-`p` digits of `x`.
-/

namespace Submission.NumberTheory.Milne

open Filter Metric
open scoped Topology

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The canonical representatives of a p-adic integer modulo `p ^ n`
converge to that p-adic integer. -/
theorem padic_appr_tendsto (x : ℤ_[p]) :
    Tendsto (fun n ↦ (x.appr n : ℤ_[p])) atTop (nhds x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  apply lt_of_le_of_lt _ hN
  rw [PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [Ideal.mem_span_singleton] at ⊢
  exact (pow_dvd_pow (p : ℤ_[p]) hn).trans
    (Ideal.mem_span_singleton.mp (PadicInt.appr_spec n x))

/-- The `n`th canonical base-`p` digit of a p-adic integer. -/
def padicIntDigit (x : ℤ_[p]) (n : ℕ) : ℕ :=
  (x.appr (n + 1) - x.appr n) / p ^ n

/-- Successive canonical representatives are obtained by adjoining one
base-`p` digit. -/
theorem padic_appr_succ (x : ℤ_[p]) (n : ℕ) :
    x.appr (n + 1) = x.appr n + padicIntDigit p x n * p ^ n := by
  have hmono : x.appr n ≤ x.appr (n + 1) :=
    x.appr_mono (Nat.le_succ n)
  have hdvd : p ^ n ∣ x.appr (n + 1) - x.appr n :=
    PadicInt.dvd_appr_sub_appr x n (n + 1) (Nat.le_succ n)
  rw [padicIntDigit, Nat.div_mul_cancel hdvd]
  exact (Nat.add_sub_of_le hmono).symm

/-- Every canonical digit lies in the usual range `0, ..., p - 1`. -/
theorem padic_int_digit (x : ℤ_[p]) (n : ℕ) :
    padicIntDigit p x n < p := by
  have hpow : 0 < p ^ n := pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n
  have hdiff : x.appr (n + 1) - x.appr n < p ^ (n + 1) :=
    (Nat.sub_le _ _).trans_lt (x.appr_lt (n + 1))
  rw [padicIntDigit, Nat.div_lt_iff_lt_mul hpow]
  simpa [pow_succ, Nat.mul_comm] using hdiff

/-- The canonical representative modulo `p ^ n` is the finite base-`p`
expansion formed from the first `n` canonical digits. -/
theorem padic_appr_digits (x : ℤ_[p]) (n : ℕ) :
    x.appr n = ∑ i ∈ Finset.range n, padicIntDigit p x i * p ^ i := by
  induction n with
  | zero => simp [PadicInt.appr]
  | succ n ih =>
      rw [padic_appr_succ, ih, Finset.sum_range_succ]

/-- `PadicInt.appr x n` is the unique natural representative of `x` modulo
`p ^ n` lying in the standard range. -/
theorem padic_appr_unique (x : ℤ_[p]) (n a : ℕ)
    (ha : a < p ^ n)
    (hcongr : x - a ∈ Ideal.span {(p : ℤ_[p]) ^ n}) :
    a = x.appr n := by
  have hz : (a : ZMod (p ^ n)) = x.appr n :=
    PadicInt.zmod_congr_of_sub_mem_span n x a (x.appr n)
      hcongr (PadicInt.appr_spec n x)
  have hval := congrArg ZMod.val hz
  simpa [ZMod.val_natCast_of_lt ha,
    ZMod.val_natCast_of_lt (x.appr_lt n)] using hval

/-- Milne, Proposition 7.26 for `ℤ_p`: every p-adic integer is the limit of
the partial sums of a unique canonical sequence of digits in `0, ..., p-1`.
The uniqueness of every partial sum is `padic_appr_unique`. -/
theorem padic_digit_tendsto (x : ℤ_[p]) :
    Tendsto
      (fun n ↦
        (↑(∑ i ∈ Finset.range n, padicIntDigit p x i * p ^ i) : ℤ_[p]))
      atTop (nhds x) := by
  simpa only [← padic_appr_digits p x] using
    padic_appr_tendsto p x

end

end Submission.NumberTheory.Milne
