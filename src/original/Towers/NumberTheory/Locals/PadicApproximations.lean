import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Canonical approximations to a p-adic integer

After Proposition 7.26, Milne describes a p-adic integer by compatible
ordinary integers modulo successive powers of `p`.  Mathlib's
`PadicInt.appr` is exactly this canonical system of approximations.
-/

namespace Towers.NumberTheory.Milne

open Filter Topology

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- Every p-adic integer has a representative modulo `p ^ n` in the standard
range `0, ..., p ^ n - 1`. -/
theorem padic_int_approximation (x : ℤ_[p]) (n : ℕ) :
    ∃ a : ℕ, a < p ^ n ∧
      x - (a : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} :=
  ⟨x.appr n, x.appr_lt n, x.appr_spec n⟩

/-- The canonical representatives at two levels are compatible modulo the
smaller power of `p`. -/
theorem padic_approximations_compatible (x : ℤ_[p]) {m n : ℕ} (hmn : m ≤ n) :
    p ^ m ∣ x.appr n - x.appr m :=
  x.dvd_appr_sub_appr m n hmn

/-- The canonical ordinary-integer approximations converge to the p-adic
integer they represent. -/
theorem padic_tendsto_approximation (x : ℤ_[p]) :
    Tendsto (fun n ↦ (x.appr n : ℤ_[p])) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  calc
    ‖(x.appr n : ℤ_[p]) - x‖ = ‖x - (x.appr n : ℤ_[p])‖ := norm_sub_rev _ _
    _ ≤ (p : ℝ) ^ (-n : ℤ) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 (x.appr_spec n)
    _ ≤ (p : ℝ) ^ (-N : ℤ) := by
      apply zpow_le_zpow_right₀
      · exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le
      · exact neg_le_neg (by exact_mod_cast hn)
    _ < ε := hN

/-- In particular, the canonical representatives form a Cauchy sequence. -/
theorem cauchy_seq_approximation (x : ℤ_[p]) :
    CauchySeq (fun n ↦ (x.appr n : ℤ_[p])) :=
  (padic_tendsto_approximation x).cauchySeq

/-- Ordinary natural numbers are dense in the p-adic integers, the density
statement underlying the approximation construction. -/
theorem padic_cast_dense : DenseRange (Nat.cast : ℕ → ℤ_[p]) :=
  PadicInt.denseRange_natCast

end

end Towers.NumberTheory.Milne
