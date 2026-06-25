import Submission.ClassField.PrimeDensities.SetEulerClauses
import Submission.ClassField.DirichletDensity.DirichletDensity
import Submission.ClassField.DirichletDensity.PartialEulerProduct

/-!
# Chapter VI, Section 4, Proposition 4.1

This file records the two comparison implications using the three literal
density notions in the text: polar density from §3, Dirichlet density from
the prime reciprocal-power sum, and natural density from prime counting.
-/

namespace Submission.CField.DDensit

open IsDedekindDomain NumberField Set
open Submission.CField.PDensit
open Submission.NumberTheory.Milne

noncomputable section

universe u

/-- Proposition VI.4.1(a): existence of polar density implies existence of
Dirichlet density, with the same value. -/
def PolarImpliesDirichlet : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (δ : ℝ),
    PrimePolarDensity K T δ → PrimeDirichletDensity K T δ

/-- Proposition VI.4.1(b): existence of natural density implies existence of
Dirichlet density, with the same value. -/
def DensityImpliesDirichlet : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (δ : ℝ),
    PNDensit K T δ → PrimeDirichletDensity K T δ

/-- **Proposition VI.4.1 (source statement).** -/
def PolarDirichletBridge : Prop :=
  PolarImpliesDirichlet.{u} ∧ DensityImpliesDirichlet.{u}

/-- The exact Euler-log step in the proof of part (a).  Starting from a
polar-density certificate with power `n` and pole order `m`, Lemma VI.4.3 and
the local meromorphic normal form show that the *weighted* prime sum differs
boundedly from `m log (1/(s-1))`.

This is kept at certificate level, rather than assuming the conclusion of
Proposition 4.1(a): the remaining division by the positive integer `n` is
proved below.  The missing ingredient is the specialization of Lemma 4.3
from an ordered sequence to the prime-ideal Euler product. -/
def PolarEulerLog : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (n m : ℕ),
    PolarDensityCertificate K T n m →
      BoundedDifferenceNear
        (fun s ↦ (n : ℝ) * primeReciprocalSum K T s)
        (fun s ↦ (m : ℝ) * Real.log (1 / (s - 1)))

/-- Goldstein's Abelian/Tauberian comparison used verbatim in part (b),
stated at the level of the two transforms rather than as a density
implication.  This is not currently present in Mathlib's prime-ideal density
API. -/
def NaturalDirichletBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (δ : ℝ),
    Filter.Tendsto
      (fun N : ℕ ↦
        (primeIdealCount K T N : ℝ) / primeIdealCount K Set.univ N)
      Filter.atTop (nhds δ) →
      BoundedDifferenceNear
        (primeReciprocalSum K T)
        (fun s ↦ δ * Real.log (1 / (s - 1)))

/-- Bounded-difference asymptotics may be divided by a positive integral
weight.  This is the algebraic step from `n Σ ~ m log` to
`Σ ~ (m/n) log`. -/
private theorem difference_div_nat
    (f g : ℝ → ℝ) (n m : ℕ) (hn : 0 < n)
    (h : BoundedDifferenceNear
      (fun s ↦ (n : ℝ) * f s) (fun s ↦ (m : ℝ) * g s)) :
    BoundedDifferenceNear f (fun s ↦ (m : ℝ) / n * g s) := by
  obtain ⟨ε, hε, B, hB⟩ := h
  refine ⟨ε, hε, |((n : ℝ)⁻¹)| * B, ?_⟩
  intro s hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    |f s - (m : ℝ) / n * g s| =
        |((n : ℝ)⁻¹) * ((n : ℝ) * f s - (m : ℝ) * g s)| := by
      congr 1
      field_simp
    _ = |((n : ℝ)⁻¹)| * |(n : ℝ) * f s - (m : ℝ) * g s| := abs_mul _ _
    _ ≤ |((n : ℝ)⁻¹)| * B :=
      mul_le_mul_of_nonneg_left (hB s hs) (abs_nonneg _)

/-- Part (a), with only the exact Euler-log bridge isolated. -/
theorem polar_euler_log
    (hlog : PolarEulerLog.{u}) :
    PolarImpliesDirichlet.{u} := by
  intro K _ _ T δ hpolar
  obtain ⟨n, m, hcert, rfl⟩ := hpolar
  exact difference_div_nat
    (primeReciprocalSum K T)
    (fun s ↦ Real.log (1 / (s - 1))) n m hcert.1
    (hlog K T n m hcert)

/-- Part (b), after unfolding natural and Dirichlet density, is precisely the
prime-ideal transform comparison isolated above. -/
theorem polar_euler_dirichlet
    (hTauberian : NaturalDirichletBridge.{u}) :
    DensityImpliesDirichlet.{u} := by
  intro K _ _ T δ hnatural
  exact hTauberian K T δ hnatural

/-- **Proposition VI.4.1**, reduced to the two narrow analytic inputs used in
the printed proof and with no extra hypotheses in the source statement. -/
theorem polar_euler_bridges
    (hlog : PolarEulerLog.{u})
    (hTauberian : NaturalDirichletBridge.{u}) :
    PolarDirichletBridge.{u} :=
  ⟨polar_euler_log hlog,
    polar_euler_dirichlet hTauberian⟩

end

end Submission.CField.DDensit
