import Mathlib.Analysis.Meromorphic.Basic
import Towers.ClassField.EulerProducts.DirichletSeries

/-!
# Chapter VI, Section 2, Proposition 2.5

Milne subtracts `a₀ ζ(s)` from the given Dirichlet series.  The resulting
coefficients have partial sums `S(N) - a₀ N`, so Proposition 2.1 makes their
ordered Dirichlet series holomorphic on `Re(s) > b`.

Mathlib's `LSeriesSummable` deliberately means absolute convergence.  It
therefore cannot express the conditionally convergent series used here.  The
single predicate `OrdinaryConvergenceBridge` below is exactly the
ordinary-convergence-to-holomorphy implication needed from Abel summation.
The rest of the source proposition is proved here, including agreement with
the original ordered series, meromorphy, the regular-part expansion, and the
residue at `1`.
-/

namespace Towers.CField.EProduc

open Complex Filter Finset Set Topology

noncomputable section

/-- The ordinary coefficient sum `S(N) = ∑_{1 ≤ n ≤ N} a(n)`. -/
def orderedCoefficientPartial (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, a n

/-- The ordered finite Dirichlet sum through the first `N` natural indices. -/
def orderedPartialSum (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, LSeries.term a s n

/-- The value selected by the limit of the ordered Dirichlet partial sums. -/
def orderedValue (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  limUnder atTop (fun N ↦ orderedPartialSum a N s)

/-- The coefficients of `f(s) - a₀ ζ(s)`.  The artificial coefficient at
`0` is harmless because `LSeries.term` is zero there. -/
def residualCoefficients (a : ℕ → ℂ) (a₀ : ℂ) : ℕ → ℂ :=
  fun n ↦ a n - a₀

/-- The exact ordinary Abel-summation interface used in Proposition 2.5.
It says that a polynomial bound for ordinary coefficient partial sums gives
both ordinary convergence to `orderedDirichletValue` and holomorphy on the
open half-plane.  This is the non-absolute content of Proposition 2.1 that is
not represented by Mathlib's `LSeriesSummable` API. -/
def OrdinaryConvergenceBridge : Prop :=
  ∀ (d : ℕ → ℂ) (C b : ℝ),
    (∀ N : ℕ, ‖orderedCoefficientPartial d N‖ ≤
      C * (N : ℝ) ^ b) →
    DifferentiableOn ℂ (orderedValue d) {s : ℂ | b < s.re} ∧
    ∀ s : ℂ, b < s.re →
      Tendsto (fun N ↦ orderedPartialSum d N s) atTop
        (𝓝 (orderedValue d s))

/-- Riemann zeta with its pole removed and its removable value filled in by
Euler's constant. -/
def riemannRegularPart : ℂ → ℂ :=
  Function.update (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1)) 1
    (Real.eulerMascheroniConstant : ℂ)

/-- The holomorphic part in Milne's displayed expansion. -/
def holomorphicPart (a : ℕ → ℂ) (a₀ : ℂ) : ℂ → ℂ :=
  fun s ↦ a₀ * riemannRegularPart s +
    orderedValue (residualCoefficients a a₀) s

/-- The continuation furnished by Proposition 2.5. -/
def continuation (a : ℕ → ℂ) (a₀ : ℂ) : ℂ → ℂ :=
  fun s ↦ a₀ / (s - 1) + holomorphicPart a a₀ s

/-- Literal conclusion of Proposition VI.2.5.  The first clause says that the
new function extends the original *ordered* Dirichlet series on its initial
half-plane.  The second and third clauses state meromorphy and the displayed
simple-pole expansion; the last clause records the residue explicitly.

When `a₀ = 0`, the displayed expansion makes the singularity removable, as
it must; thus "simple pole with residue `a₀`" is read in the source's own
following `i.e.` sense as an at-most-simple pole with this regular part. -/
def OrderedPartialConclusion (a : ℕ → ℂ) (a₀ : ℂ) (b : ℝ) : Prop :=
  (∀ s : ℂ, 1 < s.re →
    continuation a a₀ s = orderedValue a s) ∧
  MeromorphicOn (continuation a a₀) {s : ℂ | b < s.re} ∧
  DifferentiableOn ℂ (holomorphicPart a a₀) {s : ℂ | b < s.re} ∧
  (∀ s : ℂ, continuation a a₀ s =
    a₀ / (s - 1) + holomorphicPart a a₀ s) ∧
  Tendsto (fun s : ℂ ↦ (s - 1) * continuation a a₀ s)
    (𝓝[≠] 1) (𝓝 a₀)

/-- Subtracting the constant coefficient `a₀` subtracts exactly `a₀ N`
from the first `N` coefficients. -/
lemma coefficient_partial_residual
    (a : ℕ → ℂ) (a₀ : ℂ) (N : ℕ) :
    orderedCoefficientPartial
        (residualCoefficients a a₀) N =
      orderedCoefficientPartial a N - a₀ * (N : ℂ) := by
  simp [orderedCoefficientPartial, residualCoefficients,
    sum_sub_distrib, mul_comm]

/-- The filled-in regular part of zeta is entire. -/
theorem differentiable_riemann_part :
    Differentiable ℂ riemannRegularPart := by
  intro s
  by_cases hs : s = 1
  · subst s
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (f := riemannRegularPart) ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hbase : DifferentiableAt ℂ
          (fun w : ℂ ↦ riemannZeta w - 1 / (w - 1)) z := by
        exact (differentiableAt_riemannZeta hz).sub
          ((differentiableAt_const (c := (1 : ℂ))).div
            (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ))))
            (sub_ne_zero.mpr hz))
      apply hbase.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [riemannRegularPart, hw]
    · rw [riemannRegularPart, continuousAt_update_same]
      exact tendsto_riemannZeta_sub_one_div
  · have hbase : DifferentiableAt ℂ
        (fun w : ℂ ↦ riemannZeta w - 1 / (w - 1)) s := by
      exact (differentiableAt_riemannZeta hs).sub
        ((differentiableAt_const (c := (1 : ℂ))).div
          (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ))))
          (sub_ne_zero.mpr hs))
    apply hbase.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hs] with w hw
    simp [riemannRegularPart, hw]

/-- Finite ordered sums respect the coefficient decomposition
`a = a₀ + (a - a₀)`. -/
lemma partial_constant_residual
    (a : ℕ → ℂ) (a₀ : ℂ) (N : ℕ) (s : ℂ) :
    orderedPartialSum a N s =
      a₀ * orderedPartialSum (fun _ : ℕ ↦ (1 : ℂ)) N s +
        orderedPartialSum
          (residualCoefficients a a₀) N s := by
  simp only [orderedPartialSum]
  calc
    ∑ n ∈ range N, LSeries.term a s n =
        ∑ n ∈ range N,
          (a₀ * LSeries.term (fun _ : ℕ ↦ (1 : ℂ)) s n +
            LSeries.term (residualCoefficients a a₀) s n) := by
      apply sum_congr rfl
      intro n hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · simp [LSeries.term_of_ne_zero hn0,
          residualCoefficients]
        ring
    _ = a₀ * ∑ n ∈ range N, LSeries.term (fun _ : ℕ ↦ (1 : ℂ)) s n +
          ∑ n ∈ range N,
            LSeries.term (residualCoefficients a a₀) s n := by
      rw [sum_add_distrib, mul_sum]

/-- The ordered partial sums with constant coefficient one converge to the
continued Riemann zeta function in its original half-plane. -/
lemma tendsto_ordered_partial {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun N ↦ orderedPartialSum (fun _ : ℕ ↦ (1 : ℂ)) N s)
      atTop (𝓝 (riemannZeta s)) := by
  have hsum : LSeriesSummable (fun _ : ℕ ↦ (1 : ℂ)) s :=
    LSeriesSummable_one_iff.mpr hs
  have h := hsum.hasSum.tendsto_sum_nat
  change Tendsto
    (fun N ↦ ∑ n ∈ range N, LSeries.term (fun _ : ℕ ↦ (1 : ℂ)) s n)
    atTop (𝓝 (LSeries (fun _ : ℕ ↦ (1 : ℂ)) s)) at h
  have hz : LSeries (fun _ : ℕ ↦ (1 : ℂ)) s = riemannZeta s := by
    simpa only using LSeries_one_eq_riemannZeta hs
  rw [hz] at h
  simpa [orderedPartialSum] using h

/-- Away from `1`, the continuation is precisely `a₀ ζ` plus the ordered
Dirichlet series of the residual coefficients. -/
lemma continuation_zeta_residual
    (a : ℕ → ℂ) (a₀ : ℂ) {s : ℂ} (hs : s ≠ 1) :
    continuation a a₀ s =
      a₀ * riemannZeta s +
        orderedValue (residualCoefficients a a₀) s := by
  simp only [continuation, holomorphicPart]
  simp [riemannRegularPart, hs]
  ring

/-- The bridge makes Milne's regular part holomorphic on `Re(s) > b`. -/
theorem differentiable_holomorphic
    (hOrdinary : OrdinaryConvergenceBridge)
    (a : ℕ → ℂ) (a₀ : ℂ) (C b : ℝ)
    (hgrowth : ∀ N : ℕ,
      ‖orderedCoefficientPartial a N - a₀ * (N : ℂ)‖ ≤
        C * (N : ℝ) ^ b) :
    DifferentiableOn ℂ (holomorphicPart a a₀)
      {s : ℂ | b < s.re} := by
  have hresGrowth : ∀ N : ℕ,
      ‖orderedCoefficientPartial
        (residualCoefficients a a₀) N‖ ≤ C * (N : ℝ) ^ b := by
    intro N
    rw [coefficient_partial_residual]
    exact hgrowth N
  have hres := (hOrdinary
    (residualCoefficients a a₀) C b hresGrowth).1
  intro s hs
  exact (((differentiable_riemann_part s).const_mul a₀).differentiableWithinAt).add
    (hres s hs)

/-- On `Re(s) > 1`, the continuation agrees with the original ordered
Dirichlet series. -/
theorem continuation_ordered_value
    (hOrdinary : OrdinaryConvergenceBridge)
    (a : ℕ → ℂ) (a₀ : ℂ) (C b : ℝ) (hb : b < 1)
    (hgrowth : ∀ N : ℕ,
      ‖orderedCoefficientPartial a N - a₀ * (N : ℂ)‖ ≤
        C * (N : ℝ) ^ b)
    (s : ℂ) (hs : 1 < s.re) :
    continuation a a₀ s = orderedValue a s := by
  have hresGrowth : ∀ N : ℕ,
      ‖orderedCoefficientPartial
        (residualCoefficients a a₀) N‖ ≤ C * (N : ℝ) ^ b := by
    intro N
    rw [coefficient_partial_residual]
    exact hgrowth N
  have hres := (hOrdinary
    (residualCoefficients a a₀) C b hresGrowth).2 s (hb.trans hs)
  have hone := tendsto_ordered_partial hs
  have hsum : Tendsto
      (fun N ↦ a₀ *
          orderedPartialSum (fun _ : ℕ ↦ (1 : ℂ)) N s +
        orderedPartialSum
          (residualCoefficients a a₀) N s)
      atTop
      (𝓝 (a₀ * riemannZeta s +
        orderedValue
          (residualCoefficients a a₀) s)) :=
    (hone.const_mul a₀).add hres
  have ha : Tendsto (fun N ↦ orderedPartialSum a N s) atTop
      (𝓝 (a₀ * riemannZeta s +
        orderedValue
          (residualCoefficients a a₀) s)) := by
    apply hsum.congr'
    exact Eventually.of_forall fun N ↦
      (partial_constant_residual a a₀ N s).symm
  rw [continuation_zeta_residual a a₀
    (ne_of_apply_ne re (by simpa using ne_of_gt hs))]
  exact ha.limUnder_eq.symm

/-- The displayed continuation is meromorphic on Milne's half-plane. -/
theorem meromorphicOn_Continuation
    (hOrdinary : OrdinaryConvergenceBridge)
    (a : ℕ → ℂ) (a₀ : ℂ) (C b : ℝ)
    (hgrowth : ∀ N : ℕ,
      ‖orderedCoefficientPartial a N - a₀ * (N : ℂ)‖ ≤
        C * (N : ℝ) ^ b) :
    MeromorphicOn (continuation a a₀) {s : ℂ | b < s.re} := by
  have hopen : IsOpen {s : ℂ | b < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hhol := differentiable_holomorphic
    hOrdinary a a₀ C b hgrowth
  intro s hs
  have hholAnalytic : AnalyticAt ℂ (holomorphicPart a a₀) s :=
    hhol.analyticAt (hopen.mem_nhds hs)
  have hpole : MeromorphicAt (fun z : ℂ ↦ a₀ / (z - 1)) s :=
    (MeromorphicAt.const a₀ s).div
      ((MeromorphicAt.id s).sub (MeromorphicAt.const 1 s))
  simpa only [continuation] using
    hpole.add hholAnalytic.meromorphicAt

/-- The continuation has residue `a₀` at its at-most-simple pole at `1`. -/
theorem continuation_residue
    (hOrdinary : OrdinaryConvergenceBridge)
    (a : ℕ → ℂ) (a₀ : ℂ) (C b : ℝ) (hb : b < 1)
    (hgrowth : ∀ N : ℕ,
      ‖orderedCoefficientPartial a N - a₀ * (N : ℂ)‖ ≤
        C * (N : ℝ) ^ b) :
    Tendsto (fun s : ℂ ↦ (s - 1) * continuation a a₀ s)
      (𝓝[≠] 1) (𝓝 a₀) := by
  have hopen : IsOpen {s : ℂ | b < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hhol := differentiable_holomorphic
    hOrdinary a a₀ C b hgrowth
  have honeMem : (1 : ℂ) ∈ {s : ℂ | b < s.re} := by
    simpa using hb
  have hholContinuous : ContinuousAt (holomorphicPart a a₀) 1 :=
    ((hhol 1 honeMem).differentiableAt (hopen.mem_nhds honeMem)).continuousAt
  have hzero : Tendsto
      (fun s : ℂ ↦ (s - 1) * holomorphicPart a a₀ s)
      (𝓝[≠] 1) (𝓝 0) := by
    have hsub : Tendsto (fun s : ℂ ↦ s - 1) (𝓝 1) (𝓝 0) :=
      by
        have hc : ContinuousAt (fun _ : ℂ ↦ (1 : ℂ)) 1 := continuousAt_const
        simpa using (continuousAt_id.sub hc).tendsto
    have hfull := hsub.mul hholContinuous.tendsto
    simpa using hfull.mono_left
      (show 𝓝[≠] (1 : ℂ) ≤ 𝓝 (1 : ℂ) from nhdsWithin_le_nhds)
  have hlimit : Tendsto
      (fun s : ℂ ↦ a₀ +
        (s - 1) * holomorphicPart a a₀ s)
      (𝓝[≠] 1) (𝓝 a₀) := by
    simpa using hzero.const_add a₀
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [continuation, mul_add]
  rw [mul_div_cancel₀ a₀ (sub_ne_zero.mpr hs)]

/-- Proposition VI.2.5 follows from the precise ordinary Abel-summation
interface, with no strengthening of Milne's hypotheses. -/
theorem partial_ordinary_convergence
    (hOrdinary : OrdinaryConvergenceBridge) :
    ∀ (a : ℕ → ℂ) (a₀ : ℂ) (C b : ℝ), b < 1 →
    (∀ N : ℕ,
      ‖orderedCoefficientPartial a N - a₀ * (N : ℂ)‖ ≤
        C * (N : ℝ) ^ b) →
    OrderedPartialConclusion a a₀ b
  := by
  intro a a₀ C b hb hgrowth
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact continuation_ordered_value
      hOrdinary a a₀ C b hb hgrowth s hs
  · exact meromorphicOn_Continuation
      hOrdinary a a₀ C b hgrowth
  · exact differentiable_holomorphic
      hOrdinary a a₀ C b hgrowth
  · intro s
    rfl
  · exact continuation_residue
      hOrdinary a a₀ C b hb hgrowth

end

end Towers.CField.EProduc
