import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Chapter VI, Section 2: convergence of Dirichlet series

This file records the parts of Proposition 2.1 through Proposition 2.5 that
are directly supported by Mathlib's `LSeries` API.

There is an important interface distinction.  In Mathlib,
`LSeriesSummable f s` means *absolute* convergence.  Proposition 2.1 of the
text concerns ordinary convergence under a bound on the partial sums of the
coefficients.  `absolute_variant` therefore states the exact
absolute-convergence theorem available from the library, with a bound on the
partial sums of the coefficient norms; it does not silently identify the two
notions.  Likewise, `residue_mean_value` gives the residue
conclusion packaged by Mathlib, while the claimed meromorphic continuation
from a power-saving error term is not currently a packaged general theorem.
-/

namespace Submission.CField.EProduc

open Finset Filter Topology
open scoped LSeries.notation

/-- Proposition 2.1, absolute-convergence variant: polynomial growth of the
partial sums of coefficient norms gives absolute convergence to the right of
that exponent. -/
theorem absolute_variant {f : ℕ → ℂ} {b : ℝ} {s : ℂ}
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ b)
    (hb : 0 ≤ b) (hs : b < s.re) :
    LSeriesSummable f s :=
  LSeriesSummable_of_sum_norm_bigO hO hb hs

/-- Remark 2.2(a): the Dirichlet series defining the Riemann zeta function
converges absolutely exactly in the half-plane `Re(s) > 1`. -/
theorem riemann_zeta_summable {s : ℂ} :
    LSeriesSummable 1 s ↔ 1 < s.re :=
  LSeriesSummable_one_iff

/-- Remark 2.2(a), rational Dirichlet-character specialization: Dirichlet
`L`-series converge absolutely for `Re(s) > 1`. -/
theorem dirichlet_series_summable {N : ℕ}
    (chi : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (chi ·) s :=
  DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs

/-- Lemma 2.3, in the stronger global form supplied by Mathlib: the Riemann
zeta function is complex differentiable at every point other than `1`. -/
theorem riemann_zeta_differentiable {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/-- Lemma 2.4, residue form: the Riemann zeta function has residue `1` at its
simple pole at `1`. -/
theorem dirichlet_riemann_zeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s)
      (𝓝[≠] 1) (𝓝 1) :=
  riemannZeta_residue_one

/-- Lemma 2.4, regular-part form: subtracting `1 / (s - 1)` removes the pole,
and the limiting value is Euler's constant. -/
theorem riemann_regular_part :
    Tendsto (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1))
      (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
  tendsto_riemannZeta_sub_one_div

/-- Proposition 2.5, residue consequence in mean-value form.  If the
normalized coefficient sums tend to `a₀`, then the normalized `L`-series
tends to `a₀` from the right at `1`. -/
theorem residue_mean_value {f : ℕ → ℂ} {a₀ : ℂ}
    (hmean : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n)
      atTop (𝓝 a₀))
    (hsum : ∀ s : ℝ, 1 < s → LSeriesSummable f s) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s)
      (𝓝[>] 1) (𝓝 a₀) :=
  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div hmean hsum

/-- A convenient nonnegative real-coefficient form of Proposition 2.5.  In
this case Mathlib derives convergence for `s > 1` from nonnegativity and the
mean-value hypothesis. -/
theorem residue_mean_nonneg
    (f : ℕ → ℝ) {a₀ : ℝ}
    (hmean : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k) / n)
      atTop (𝓝 a₀))
    (hf : ∀ n, 0 ≤ f n) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ (f n : ℂ)) s)
      (𝓝[>] 1) (𝓝 (a₀ : ℂ)) :=
  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg f hmean hf

end Submission.CField.EProduc
