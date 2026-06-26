import Mathlib.Analysis.Complex.RemovableSingularity
import Towers.ClassField.Characters.ZetaRegularPart

/-!
# Chapter V, Section 2, Theorem 2.1: source-facing statements

This file packages the holomorphic regular part in clause (a), and records
ordered convergence of partial sums separately from Mathlib's
`LSeriesSummable`, which means absolute convergence.
-/

namespace Towers.CField.Charac

open Filter Set Topology
open scoped LSeries.notation

noncomputable section

/-- The removable regular part `φ` in the source, with its value at the
removed point chosen to be Euler's constant. -/
noncomputable def zetaRegularPart (s : ℂ) : ℂ :=
  Function.update
    (fun z : ℂ ↦ riemannZeta z - 1 / (z - 1))
    1 (Real.eulerMascheroniConstant : ℂ) s

@[simp]
theorem zeta_part_one :
    zetaRegularPart 1 = (Real.eulerMascheroniConstant : ℂ) := by
  simp [zetaRegularPart]

theorem zeta_part_ne {s : ℂ} (hs : s ≠ 1) :
    zetaRegularPart s = riemannZeta s - 1 / (s - 1) := by
  simp [zetaRegularPart, hs]

/-- The regular part is holomorphic on the full source half-plane
`Re(s) > 0`, including at the removed point `s = 1`. -/
theorem differentiable_regular_part :
    DifferentiableOn ℂ zetaRegularPart {s : ℂ | 0 < s.re} := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hU : U ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  apply (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hU).1
  constructor
  · intro s hs
    let g := fun z : ℂ ↦ riemannZeta z - 1 / (z - 1)
    have hg : DifferentiableAt ℂ g s := (differentiableAt_riemannZeta hs.2).sub
      ((differentiableAt_const (x := s) (1 : ℂ)).div
        (differentiableAt_id.sub (differentiableAt_const (x := s) (1 : ℂ)))
        (sub_ne_zero.mpr hs.2))
    have heq : zetaRegularPart =ᶠ[𝓝 s] g := by
      filter_upwards [isOpen_ne.mem_nhds hs.2] with z hz
      exact zeta_part_ne hz
    exact (hg.congr_of_eventuallyEq heq).differentiableWithinAt
  · change ContinuousAt
      (Function.update
        (fun z : ℂ ↦ riemannZeta z - 1 / (z - 1))
        1 (Real.eulerMascheroniConstant : ℂ)) 1
    rw [continuousAt_update_same]
    exact zeta_regular_part

/-- Analytic formulation of the holomorphy assertion for `φ`. -/
theorem analytic_nhd_part :
    AnalyticOnNhd ℂ zetaRegularPart {s : ℂ | 0 < s.re} :=
  differentiable_regular_part.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- On the punctured half-plane, the zeta function is its polar part plus
the holomorphic regular part, exactly as in clause (a). -/
theorem riemann_polar_part
    {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + zetaRegularPart s := by
  rw [zeta_part_ne hs]
  ring

/-- Ordered convergence of the naive Dirichlet series.  This uses the
ordinary sequence of partial sums and deliberately does not assert absolute
summability. -/
def OrderedDirichletConverges {m : ℕ} [NeZero m]
    (chi : DirichletCharacter ℂ m) (s : ℂ) : Prop :=
  ∃ a : ℂ, Tendsto
    (fun N : ℕ ↦ ∑ n ∈ Finset.range N, LSeries.term (chi ·) s n)
    atTop (𝓝 a)

/-- In the half-plane of absolute convergence, the ordered partial sums
converge to the analytic `LFunction`. -/
theorem tendsto_l_re
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.range N, LSeries.term (chi ·) s n)
      atTop (𝓝 (DirichletCharacter.LFunction chi s)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
  exact (ZMod.LSeriesSummable_of_one_lt_re chi hs).hasSum.tendsto_sum_nat

theorem dirichlet_converges_re
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m)
    {s : ℂ} (hs : 1 < s.re) :
    OrderedDirichletConverges chi s :=
  ⟨DirichletCharacter.LFunction chi s,
    tendsto_l_re chi hs⟩

/-- The nonvanishing clause, restated next to the source-facing ordered
convergence predicate. -/
theorem nonprincipal_l_function
    {m : ℕ} [NeZero m] {chi : DirichletCharacter ℂ m}
    (hchi : chi ≠ 1) :
    DirichletCharacter.LFunction chi 1 ≠ 0 :=
  l_function_ne hchi

end

end Towers.CField.Charac
