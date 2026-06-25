import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Meromorphic.NormalForm
import Submission.ClassField.PrimeDensities.SetEulerClauses

/-!
# Chapter VI, Section 3, Proposition 3.2

Milne proves that a set of finite primes containing no degree-one prime has
polar density zero.  The arithmetic decomposition by rational primes gives a
normally convergent Euler product near `s = 1`; the rest of the argument is
carried out here using Mathlib's locally uniform limit theorem.
-/

namespace Submission.CField.PDensit

open Complex Filter IsDedekindDomain NumberField Set Topology
open scoped BigOperators NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The exact source condition: none of the absolute norms occurring in `T`
is a prime number in `ℤ`. -/
def ContainsNoAbsolute
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) : Prop :=
  ∀ p ∈ T, ¬Nat.Prime p.asIdeal.absNorm

/-- The precise normal-convergence input supplied in the printed proof by
decomposing the prime ideals into at most `[K:ℚ]` products indexed by rational
primes.  Mathlib has the abstract uniform-product API, but not this
number-field estimate connecting residue degrees at least two to it.

Besides locally uniform multipliability on a right-half-plane neighborhood of `1`,
we retain summability of the deviations at `1`; this is exactly what ensures
that the limiting product is nonzero there. -/
def EulerConvergenceBridge : Prop :=
  ∀ T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ContainsNoAbsolute K T →
    ∃ U : Set ℂ,
      IsOpen U ∧ (1 : ℂ) ∈ U ∧ U ⊆ {s : ℂ | 0 < s.re} ∧
      MultipliableLocallyUniformlyOn
        (fun p : T ↦ fun s : ℂ ↦ setEulerClauses K s p.1) U ∧
      Summable (fun p : T ↦ ‖setEulerClauses K 1 p.1 - 1‖)

/-- Every local Euler factor is holomorphic on the right half-plane.  This is
the elementary local part of the Euler-product argument; no convergence
hypothesis is used. -/
private theorem differentiable_clauses_re
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K)) {s : ℂ}
    (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z ↦ setEulerClauses K z p) s := by
  have hN : 1 < p.asIdeal.absNorm :=
    NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hN0 : (p.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (zero_lt_one.trans hN))
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ ↦ (p.asIdeal.absNorm : ℂ) ^ (-z)) s := by
    simpa using (differentiable_id.neg.const_cpow (.inl hN0) s)
  have hnorm : ‖(p.asIdeal.absNorm : ℂ) ^ (-s)‖ < 1 := by
    rw [show (p.asIdeal.absNorm : ℂ) =
      ((p.asIdeal.absNorm : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by
        exact_mod_cast (zero_lt_one.trans hN))]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) (by simp [hs])
  have hden : (1 : ℂ) - (p.asIdeal.absNorm : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have heq : (p.asIdeal.absNorm : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    have := congrArg norm heq
    simpa [heq] using hnorm.ne
  exact ((differentiableAt_const (c := (1 : ℂ))).sub hpow).inv hden

/-- The bridge's normal convergence makes the Euler product holomorphic and
nonvanishing at `1`.  This is the analytic core of Milne's proof. -/
theorem euler_regular_convergence
    {T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))}
    {U : Set ℂ} (hUopen : IsOpen U) (hone : (1 : ℂ) ∈ U)
    (hUright : U ⊆ {s : ℂ | 0 < s.re})
    (hmult : MultipliableLocallyUniformlyOn
      (fun p : T ↦ fun s : ℂ ↦ setEulerClauses K s p.1) U)
    (hsum : Summable (fun p : T ↦ ‖setEulerClauses K 1 p.1 - 1‖)) :
    AnalyticAt ℂ (setEulerProduct K T) 1 ∧
      setEulerProduct K T 1 ≠ 0 := by
  have htend : TendstoLocallyUniformlyOn
      (fun F : Finset T ↦ fun s : ℂ ↦
        ∏ p ∈ F, setEulerClauses K s p.1)
      (setEulerProduct K T) atTop U := by
    simpa only [setEulerProduct] using
      hmult.hasProdLocallyUniformlyOn
  have hfinite : ∀ F : Finset T,
      DifferentiableOn ℂ
        (fun s : ℂ ↦ ∏ p ∈ F, setEulerClauses K s p.1) U := by
    intro F
    apply DifferentiableOn.fun_finsetProd
    intro p hp s hs
    exact (differentiable_clauses_re K p.1
      (hUright hs)).differentiableWithinAt
  have hdiff : DifferentiableOn ℂ (setEulerProduct K T) U :=
    htend.differentiableOn (Eventually.of_forall hfinite) hUopen
  have han : AnalyticAt ℂ (setEulerProduct K T) 1 :=
    hdiff.analyticAt (hUopen.mem_nhds hone)
  have hne : setEulerProduct K T 1 ≠ 0 := by
    unfold setEulerProduct
    simpa [add_sub_cancel] using
      tprod_one_add_ne_zero_of_summable
        (f := fun p : T ↦ setEulerClauses K 1 p.1 - 1)
        (fun p ↦ by
          have hN : 1 < p.1.asIdeal.absNorm :=
            NumberField.HeightOneSpectrum.one_lt_absNorm p.1
          have hN0 : (p.1.asIdeal.absNorm : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (zero_lt_one.trans hN))
          have hden : (1 : ℂ) - (p.1.asIdeal.absNorm : ℂ)⁻¹ ≠ 0 := by
            intro h
            have hinv : (p.1.asIdeal.absNorm : ℂ)⁻¹ = 1 :=
              (sub_eq_zero.mp h).symm
            have hi := congrArg Inv.inv hinv
            have hN1 : (p.1.asIdeal.absNorm : ℂ) ≠ 1 := by
              exact_mod_cast (ne_of_gt hN)
            exact hN1 (by simpa [hN0] using hi)
          simpa [add_sub_cancel, setEulerClauses,
            Complex.cpow_neg_one] using inv_ne_zero hden)
        hsum
  exact ⟨han, hne⟩

/-- A regular nonzero Euler product has polar density zero. -/
theorem polar_density_regular
    {T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (han : AnalyticAt ℂ (setEulerProduct K T) 1)
    (hne : setEulerProduct K T 1 ≠ 0) :
    PrimePolarDensity K T 0 := by
  refine ⟨1, 0, ?_, by norm_num⟩
  refine ⟨Nat.one_pos, setEulerProduct K T, han.meromorphicAt, ?_, ?_⟩
  · filter_upwards [] with x
    simp
  · rw [han.meromorphicOrderAt_eq,
      han.analyticOrderAt_eq_zero.mpr hne]
    simp

/-- The source proposition follows from precisely the normal-convergence
estimate furnished by Milne's rational-prime decomposition. -/
theorem contains_euler_convergence
    (hbridge : EulerConvergenceBridge K) :
    (∀ T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)),
          ContainsNoAbsolute K T → PrimePolarDensity K T 0) := by
  intro T hT
  obtain ⟨U, hUopen, hone, hUright, hmult, hsum⟩ := hbridge T hT
  obtain ⟨han, hne⟩ :=
    euler_regular_convergence K
      hUopen hone hUright hmult hsum
  exact polar_density_regular K han hne

end

end Submission.CField.PDensit
