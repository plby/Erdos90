import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.Deriv
import Submission.ClassField.DirichletSeries.DirichletSeries

/-!
# Chapter VI, Section 2, Proposition 2.1

Milne's proposition concerns ordinary convergence in the order `1, 2, ...`.
This is intentionally not expressed using `Summable` or `LSeriesSummable`:
for complex series indexed by `ℕ`, those predicates encode unconditional
(hence absolute) convergence.

The only input not currently packaged by Mathlib is the quantitative Abel
summation estimate used in the printed proof.  `AbelTailEstimate`
records exactly that estimate.  From it, this file proves uniform convergence
on every source region `D(b, δ, ε)`, constructs the ordered sum, and proves
that this sum is holomorphic on `Re(s) > b` by the locally uniform limit
theorem.
-/

namespace Submission.CField.EProduc

open Complex Filter Finset Set Topology

noncomputable section

/-- The coefficient sum `S(N) = ∑_{1 ≤ n ≤ N} a(n)`.  Since the real-valued
function `S(x)` in the source is constant between consecutive integers, its
eventual `O(x^b)` hypothesis is equivalently usable in this integer form. -/
def coefficientPartialSum (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, a n

/-- The source's real-variable step function
`S(x) = ∑_{n ≤ x} a(n)`. -/
def coefficientPartialReal (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  coefficientPartialSum a ⌊x⌋₊

@[simp]
theorem partial_real_cast (a : ℕ → ℂ) (N : ℕ) :
    coefficientPartialReal a (N : ℝ) = coefficientPartialSum a N := by
  simp [coefficientPartialReal]

/-- The ordered partial sum of `∑ a(n) / n^s`.  The artificial zeroth term of
`LSeries.term` is zero. -/
def dirichletPartialSum (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, LSeries.term a s n

/-- Milne's closed sector
`D(b, δ, ε) = {Re(s) ≥ b + δ, |arg(s-b)| ≤ π/2-ε}`. -/
def dirichletRegion (b δ ε : ℝ) : Set ℂ :=
  {s : ℂ | b + δ ≤ s.re ∧ |arg (s - b)| ≤ Real.pi / 2 - ε}

/-- The ordered value of the Dirichlet series.  At a point where the ordered
partial sums are Cauchy, completeness of `ℂ` proves that `limUnder` is their
limit. -/
def orderedDirichletValue (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  limUnder atTop (fun N ↦ dirichletPartialSum a N s)

/-- The quantitative tail estimate obtained by the summation-by-parts
calculation in Milne's proof.  Its hypotheses are exactly positivity of the
two source constants, eventual polynomial growth of `S(N)`, and positivity
of `δ, ε`.  The conclusion is the uniform `O(N^{-δ})` tail bound.

This is the narrow analytic bridge missing from the current L-series API;
the tracked theorem only treats partial sums of coefficient *norms* and hence
absolute convergence. -/
def AbelTailEstimate : Prop :=
  ∀ (a : ℕ → ℂ) (A b δ ε : ℝ),
    0 < A → 0 < b → 0 < δ → 0 < ε →
    (∀ᶠ N : ℕ in atTop,
      ‖coefficientPartialSum a N‖ ≤ A * (N : ℝ) ^ b) →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ m ≥ N, ∀ n ≥ N, ∀ s ∈ dirichletRegion b δ ε,
        dist (dirichletPartialSum a m s)
            (dirichletPartialSum a n s) ≤
          C * ((N : ℝ) + 1) ^ (-δ)

/-- Literal conclusion of Proposition VI.2.1 for fixed coefficients and
growth exponent: uniform convergence on every `D(b,δ,ε)`, to one and the
same function, and holomorphy of that function on `Re(s)>b`. -/
def CoefficientPartialConclusion (a : ℕ → ℂ) (b : ℝ) : Prop :=
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    TendstoUniformlyOn (dirichletPartialSum a)
      (orderedDirichletValue a) atTop (dirichletRegion b δ ε)) ∧
  AnalyticOnNhd ℂ (orderedDirichletValue a) {s : ℂ | b < s.re}

/-- The quantitative Abel estimate implies the uniform Cauchy criterion on
each source sector. -/
theorem uniform_cauchy_dirichlet
    (hAbel : AbelTailEstimate)
    (a : ℕ → ℂ) (A b δ ε : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hδ : 0 < δ) (hε : 0 < ε)
    (hgrowth : ∀ᶠ N : ℕ in atTop,
      ‖coefficientPartialSum a N‖ ≤ A * (N : ℝ) ^ b) :
    UniformCauchySeqOn (dirichletPartialSum a) atTop
      (dirichletRegion b δ ε) := by
  obtain ⟨C, hC, N₀, htail⟩ :=
    hAbel a A b δ ε hA hb hδ hε hgrowth
  have hbase : Tendsto (fun N : ℕ ↦ (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun N : ℕ ↦ C * ((N : ℝ) + 1) ^ (-δ))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hδ).comp hbase |>.const_mul C
  rw [Metric.uniformCauchySeqOn_iff]
  intro η hη
  have heventually : ∀ᶠ N : ℕ in atTop,
      C * ((N : ℝ) + 1) ^ (-δ) < η :=
    hbound.eventually (Iio_mem_nhds hη)
  rw [eventually_atTop] at heventually
  obtain ⟨N₁, hN₁⟩ := heventually
  refine ⟨max N₀ N₁, fun m hm n hn s hs ↦ ?_⟩
  exact lt_of_le_of_lt
    (htail (max N₀ N₁) (max_le_iff.mp le_rfl).1 m hm n hn s hs)
    (hN₁ _ ((le_max_right N₀ N₁).trans le_rfl))

/-- Hence the ordered partial sums converge uniformly to their canonical
`limUnder` value on `D(b,δ,ε)`. -/
theorem tendsto_uniformly_dirichlet
    (hAbel : AbelTailEstimate)
    (a : ℕ → ℂ) (A b δ ε : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hδ : 0 < δ) (hε : 0 < ε)
    (hgrowth : ∀ᶠ N : ℕ in atTop,
      ‖coefficientPartialSum a N‖ ≤ A * (N : ℝ) ^ b) :
    TendstoUniformlyOn (dirichletPartialSum a)
      (orderedDirichletValue a) atTop (dirichletRegion b δ ε) := by
  have hC := uniform_cauchy_dirichlet
    hAbel a A b δ ε hA hb hδ hε hgrowth
  apply hC.tendstoUniformlyOn_of_tendsto
  intro s hs
  exact (hC.cauchySeq hs).tendsto_limUnder

/-- Every point of the open half-plane `Re(s)>b` has one of Milne's closed
sectors as a neighbourhood.  This supplies the elementary geometry invoked
between the two sentences of the proposition. -/
theorem dirichlet_region_nhds
    {b : ℝ} {s : ℂ} (hs : b < s.re) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧ dirichletRegion b δ ε ∈ 𝓝 s := by
  have hwre : 0 < (s - (b : ℂ)).re := by
    simpa using sub_pos.mpr hs
  have harg : |arg (s - (b : ℂ))| < Real.pi / 2 := by
    rw [abs_arg_lt_pi_div_two_iff]
    exact Or.inl hwre
  let δ : ℝ := (s.re - b) / 2
  let ε : ℝ := (Real.pi / 2 - |arg (s - (b : ℂ))|) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hre : b + δ < s.re := by
    dsimp [δ]
    linarith
  have hangle : |arg (s - (b : ℂ))| < Real.pi / 2 - ε := by
    dsimp [ε]
    linarith
  have hwslit : s - (b : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    exact Or.inl hwre
  have hsub : ContinuousAt (fun z : ℂ ↦ z - (b : ℂ)) s :=
    continuousAt_id.sub continuousAt_const
  have hargContinuous :
      ContinuousAt (fun z : ℂ ↦ |arg (z - (b : ℂ))|) s :=
    by simpa only [Function.comp_apply] using
      (ContinuousAt.comp (f := fun z : ℂ ↦ z - (b : ℂ))
        (x := s) (g := arg)
        (continuousAt_arg (x := s - (b : ℂ)) hwslit) hsub).abs
  have hreEventually : ∀ᶠ z : ℂ in 𝓝 s, b + δ < z.re :=
    Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds hre)
  have hargEventually : ∀ᶠ z : ℂ in 𝓝 s,
      |arg (z - (b : ℂ))| < Real.pi / 2 - ε :=
    hargContinuous.eventually (Iio_mem_nhds hangle)
  refine ⟨δ, ε, hδ, hε, ?_⟩
  filter_upwards [hreEventually, hargEventually] with z hzre hzarg
  exact ⟨hzre.le, hzarg.le⟩

/-- Uniform convergence on all source sectors is locally uniform convergence
on the whole half-plane. -/
theorem tendsto_locally_uniformly
    (hAbel : AbelTailEstimate)
    (a : ℕ → ℂ) (A b : ℝ)
    (hA : 0 < A) (hb : 0 < b)
    (hgrowth : ∀ᶠ N : ℕ in atTop,
      ‖coefficientPartialSum a N‖ ≤ A * (N : ℝ) ^ b) :
    TendstoLocallyUniformlyOn (dirichletPartialSum a)
      (orderedDirichletValue a) atTop {s : ℂ | b < s.re} := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro s hs
  obtain ⟨δ, ε, hδ, hε, hregion⟩ :=
    dirichlet_region_nhds hs
  exact ⟨dirichletRegion b δ ε,
    mem_nhdsWithin_of_mem_nhds hregion,
    tendsto_uniformly_dirichlet
      hAbel a A b δ ε hA hb hδ hε hgrowth⟩

/-- Each finite ordered partial sum is an entire function of `s`. -/
theorem differentiable_dirichlet_partial
    (a : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (dirichletPartialSum a N) := by
  intro s
  unfold dirichletPartialSum
  exact DifferentiableAt.fun_sum fun n _ ↦
    (LSeries.hasDerivAt_term a n s).differentiableAt

/-- The common ordered sum is holomorphic on `Re(s)>b`. -/
theorem differentiable_dirichlet_value
    (hAbel : AbelTailEstimate)
    (a : ℕ → ℂ) (A b : ℝ)
    (hA : 0 < A) (hb : 0 < b)
    (hgrowth : ∀ᶠ N : ℕ in atTop,
      ‖coefficientPartialSum a N‖ ≤ A * (N : ℝ) ^ b) :
    DifferentiableOn ℂ (orderedDirichletValue a) {s : ℂ | b < s.re} := by
  apply (tendsto_locally_uniformly
    hAbel a A b hA hb hgrowth).differentiableOn
  · exact Eventually.of_forall fun N ↦
      (differentiable_dirichlet_partial a N).differentiableOn
  · exact isOpen_lt continuous_const Complex.continuous_re

/-- Analytic formulation of the source's final assertion. -/
theorem analytic_nhd_dirichlet
    (hAbel : AbelTailEstimate)
    (a : ℕ → ℂ) (A b : ℝ)
    (hA : 0 < A) (hb : 0 < b)
    (hgrowth : ∀ᶠ N : ℕ in atTop,
      ‖coefficientPartialSum a N‖ ≤ A * (N : ℝ) ^ b) :
    AnalyticOnNhd ℂ (orderedDirichletValue a) {s : ℂ | b < s.re} :=
  (differentiable_dirichlet_value
    hAbel a A b hA hb hgrowth).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)

/-- Proposition VI.2.1 follows in full from the single quantitative Abel
summation bridge. -/
theorem partial_abel_estimate
    (hAbel : AbelTailEstimate) :
    (∀ (a : ℕ → ℂ) (A b : ℝ),
          0 < A → 0 < b →
          (∀ᶠ x : ℝ in atTop,
            ‖coefficientPartialReal a x‖ ≤ A * x ^ b) →
          CoefficientPartialConclusion a b) := by
  intro a A b hA hb hgrowthReal
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      ‖coefficientPartialSum a N‖ ≤ A * (N : ℝ) ^ b := by
    simpa using tendsto_natCast_atTop_atTop.eventually hgrowthReal
  constructor
  · intro δ ε hδ hε
    exact tendsto_uniformly_dirichlet
      hAbel a A b δ ε hA hb hδ hε hgrowth
  · exact analytic_nhd_dirichlet
      hAbel a A b hA hb hgrowth

end

end Submission.CField.EProduc
