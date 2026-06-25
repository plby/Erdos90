import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Submission.ClassField.Characters.DirichletCharacters

/-!
# Chapter V, Section 2, Theorem 2.1

The removable regular part and residue statements below express the simple
pole of the Riemann zeta function at `1`.  For a nonprincipal Dirichlet
character, Mathlib supplies an everywhere differentiable continuation and
the classical nonvanishing theorem at `1`.

The text also states conditional convergence of the naive Dirichlet series
on `Re(s) > 0`.  Mathlib's `LSeriesSummable` API deliberately means absolute
convergence, so that particular assertion is not conflated here with the
analytic continuation `LFunction`.
-/

namespace Submission.CField.Charac

open Filter Topology

/-- Theorem 2.1(a): after subtracting its polar part at `1`, the Riemann zeta
function has a removable singularity, with value Euler's constant. -/
theorem zeta_regular_part :
    Tendsto (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1))
      (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
  tendsto_riemannZeta_sub_one_div

/-- Theorem 2.1(a), residue form: the residue of `ζ` at `1` is `1`. -/
theorem zeta_residue :
    Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s)
      (𝓝[≠] 1) (𝓝 1) :=
  riemannZeta_residue_one

/-- Theorem 2.1(b), analytic-continuation form: the `L`-function of a
nonprincipal Dirichlet character is differentiable everywhere. -/
theorem differentiable {m : ℕ} [NeZero m]
    {chi : DirichletCharacter ℂ m} (hchi : chi ≠ 1) :
    Differentiable ℂ (DirichletCharacter.LFunction chi) :=
  DirichletCharacter.differentiable_LFunction hchi

/-- Theorem 2.1(b): a nonprincipal Dirichlet `L`-function does not vanish at
`s = 1`. -/
theorem l_function_ne {m : ℕ} [NeZero m]
    {chi : DirichletCharacter ℂ m} (hchi : chi ≠ 1) :
    DirichletCharacter.LFunction chi 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hchi

end Submission.CField.Charac
