import Towers.ClassField.EulerProducts.CoefficientPartialSum
import Towers.ClassField.DirichletDensity.DirichletDensity
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Chapter VI, Section 4, Lemma 4.3

This is the logarithmic comparison for an Euler product with real local
norms `u_j >= 2`.  The hypothesis uses the same closed regions
`D(1,delta,epsilon)` defined for Proposition VI.2.1.
-/

namespace Towers.CField.DDensit

open Complex Filter Finset Set Topology
open Towers.CField.EProduc
open scoped BigOperators

noncomputable section

/-- The ordered finite Euler product through the first `N` factors. -/
def partialEulerProduct (u : ℕ → ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∏ j ∈ range N, (1 - (u j : ℂ) ^ (-s))⁻¹

/-- The infinite product value selected by the ordered partial products. -/
def eulerProduct (u : ℕ → ℝ) (s : ℂ) : ℂ :=
  limUnder atTop (fun N ↦ partialEulerProduct u N s)

/-- The first-order term in the logarithm of the Euler product, restricted
to real `s>1`. -/
def reciprocalPowerSum (u : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑' j, Real.rpow (u j) (-s)

/-- Literal conclusion `log f(s) ~ sum_j u_j^(-s)` as `s` decreases to
`1` through real values. -/
def PartialEulerConclusion (u : ℕ → ℝ) : Prop :=
  BoundedDifferenceNear
    (fun s ↦ (Complex.log (eulerProduct u (s : ℂ))).re)
    (reciprocalPowerSum u)

/-- The one analytic interface not supplied by the current ordered infinite
product API.  For positive real Euler factors, convergence of the ordered
products implies convergence of the first-order series, and the logarithm of
the product is the ordered sum of the local logarithms.

This bridge is deliberately restricted to the real line `s > 1`, which is
exactly what the conclusion of Lemma 4.3 uses. -/
def LogInfiniteBridge : Prop :=
  ∀ (u : ℕ → ℝ),
    (∀ j, 2 ≤ u j) →
    (∀ δ ε : ℝ, 0 < δ → 0 < ε →
      TendstoUniformlyOn (partialEulerProduct u)
        (eulerProduct u) atTop (dirichletRegion 1 δ ε)) →
    ∀ s : ℝ, 1 < s →
      Summable (fun j ↦ Real.rpow (u j) (-s)) ∧
      (Complex.log (eulerProduct u (s : ℂ))).re =
        ∑' j, (Complex.log
          (1 - (Real.rpow (u j) (-s) : ℂ))⁻¹).re

/-- For `u ≥ 2` and `s ≥ 1`, the local logarithmic remainder is bounded by
the square of its first-order term. -/
lemma log_remainder_bound
    {u s : ℝ} (hu : 2 ≤ u) (hs : 1 ≤ s) :
    |(Complex.log (1 - (Real.rpow u (-s) : ℂ))⁻¹).re -
        Real.rpow u (-s)| ≤
      (Real.rpow u (-s)) ^ 2 := by
  let x := Real.rpow u (-s)
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hx0 : 0 ≤ x := Real.rpow_nonneg hu0 _
  have hxhalf : x ≤ (1 / 2 : ℝ) := by
    have hxinv : x ≤ u⁻¹ := by
      simpa only [x, Real.rpow_neg_one] using
        Real.rpow_le_rpow_of_exponent_le hu1 (by linarith : -s ≤ (-1 : ℝ))
    have huinv : u⁻¹ ≤ (2 : ℝ)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 hu
    norm_num at huinv ⊢
    exact hxinv.trans huinv
  have hxlt : x < 1 := hxhalf.trans_lt (by norm_num)
  have hlog := Complex.norm_log_one_sub_inv_sub_self_le
    (z := (x : ℂ)) (by simpa [Complex.norm_real, abs_of_nonneg hx0] using hxlt)
  have hre :
      |(Complex.log (1 - (x : ℂ))⁻¹).re - x| ≤
        ‖Complex.log (1 - (x : ℂ))⁻¹ - (x : ℂ)‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re, Real.norm_eq_abs] using
      abs_re_le_norm (Complex.log (1 - (x : ℂ))⁻¹ - (x : ℂ))
  have hinv : (1 - x)⁻¹ ≤ 2 := by
    have h := (inv_le_inv₀ (by linarith [hxhalf]) (by norm_num : (0 : ℝ) < 1 / 2)).2
      (by linarith [hxhalf] : (1 / 2 : ℝ) ≤ 1 - x)
    norm_num at h ⊢
    exact h
  have htail : x ^ 2 * (1 - x)⁻¹ / 2 ≤ x ^ 2 := by
    have hxSq : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  have hlog' :
      ‖Complex.log (1 - (x : ℂ))⁻¹ - (x : ℂ)‖ ≤
        x ^ 2 * (1 - x)⁻¹ / 2 := by
    simpa [Complex.norm_real, abs_of_nonneg hx0] using hlog
  exact hre.trans (hlog'.trans htail)

/-- The square of `u⁻ˢ` is bounded by `u⁻²` uniformly for `s ≥ 1`. -/
lemma reciprocal_sq_two
    {u s : ℝ} (hu : 2 ≤ u) (hs : 1 ≤ s) :
    (Real.rpow u (-s)) ^ 2 ≤ Real.rpow u (-2) := by
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  calc
    (Real.rpow u (-s)) ^ 2 = Real.rpow u ((-s) * 2) := by
      exact (Real.rpow_mul_natCast hu0 (-s) 2).symm
    _ ≤ Real.rpow u (-2) :=
      Real.rpow_le_rpow_of_exponent_le
        (le_trans (by norm_num) hu) (by linarith)

/-- The narrow logarithm bridge implies the literal bounded-difference
conclusion of Lemma 4.3.  The bound is the convergent comparison series
`sum_j u_j⁻²`, independent of real `s` near `1`. -/
theorem partial_euler_bridge
    (hlogProduct : LogInfiniteBridge) :
    (∀ u : ℕ → ℝ,
          (∀ j, 2 ≤ u j) →
          (∀ δ ε : ℝ, 0 < δ → 0 < ε →
            TendstoUniformlyOn (partialEulerProduct u)
              (eulerProduct u) atTop (dirichletRegion 1 δ ε)) →
          PartialEulerConclusion u) := by
  intro u hu hconvergence
  have htwo := hlogProduct u hu hconvergence 2 (by norm_num)
  have hsummableTwo : Summable (fun j ↦ Real.rpow (u j) (-2)) := htwo.1
  refine ⟨1, by norm_num, ∑' j, Real.rpow (u j) (-2), ?_⟩
  intro s hs
  have hs1 : 1 < s := hs.1
  have hsat : 1 ≤ s := hs1.le
  obtain ⟨hsummableFirst, hlogEq⟩ :=
    hlogProduct u hu hconvergence s hs1
  let localLog : ℕ → ℝ := fun j ↦
    (Complex.log (1 - (Real.rpow (u j) (-s) : ℂ))⁻¹).re
  let remainder : ℕ → ℝ := fun j ↦
    localLog j - Real.rpow (u j) (-s)
  have hremainderBound (j : ℕ) :
      |remainder j| ≤ Real.rpow (u j) (-2) := by
    exact (log_remainder_bound (hu j) hsat).trans
      (reciprocal_sq_two (hu j) hsat)
  have hsummableRemainder : Summable remainder :=
    hsummableTwo.of_norm_bounded fun j ↦ by
      simpa only [Real.norm_eq_abs] using hremainderBound j
  have hsummableLocalLog : Summable localLog := by
    have hadd := hsummableFirst.add hsummableRemainder
    exact hadd.congr fun j ↦ by
      simp only [remainder, localLog]
      ring
  have htsumRemainder :
      (∑' j, localLog j) - (∑' j, Real.rpow (u j) (-s)) =
        ∑' j, remainder j := by
    rw [← hsummableLocalLog.tsum_sub hsummableFirst]
  change |(Complex.log (eulerProduct u (s : ℂ))).re -
      reciprocalPowerSum u s| ≤ ∑' j, Real.rpow (u j) (-2)
  change |(Complex.log (eulerProduct u (s : ℂ))).re -
      ∑' j, Real.rpow (u j) (-s)| ≤ ∑' j, Real.rpow (u j) (-2)
  rw [hlogEq]
  change |(∑' j, localLog j) - (∑' j, Real.rpow (u j) (-s))| ≤ _
  rw [htsumRemainder]
  exact (norm_tsum_le_tsum_norm hsummableRemainder.norm).trans <|
    hsummableRemainder.norm.tsum_le_tsum hremainderBound hsummableTwo

end

end Towers.CField.DDensit
