import Mathlib.Analysis.Meromorphic.Basic
import Submission.ClassField.ArtinReciprocity.Statements
import Submission.ClassField.Characters.DedekindResidueFormula

/-!
# Chapter V, Section 2, Theorem 2.4 (source statements)

This file keeps the three analytic assertions in the source distinct:

* existence of a meromorphic continuation of the Dedekind zeta function;
* its class-number-formula asymptotic at `1`;
* ordered (not absolute) convergence and nonvanishing of a nonprincipal
  ray-class character series.

The class-number asymptotic follows from the existing Mathlib theorem.  The
continuation and general ray-class `L`-series assertions are recorded as
literal interfaces, but are not asserted as consequences of that real
asymptotic.
-/

namespace Submission.CField.Charac

open Filter IsDedekindDomain NumberField Set Topology
open scoped LSeries.notation
open scoped nonZeroDivisors

noncomputable section

universe u

/-- The literal meaning of “`ζ_K` extends meromorphically to `Re(s) > 0`”.
The continued function is required to agree with the defining Dirichlet
series in its original half-plane `Re(s) > 1`. -/
def DedekindMeromorphicContinuation
    (K : Type u) [Field K] [NumberField K] : Prop :=
  ∃ zetaContinuation : ℂ → ℂ,
    MeromorphicOn zetaContinuation {s : ℂ | 0 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        zetaContinuation s = NumberField.dedekindZeta K s

/-- The class-number-formula constant displayed in Theorem V.2.4(a). -/
def classNumberConstant
    (K : Type u) [Field K] [NumberField K] : ℝ :=
  (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      NumberField.Units.regulator K * NumberField.classNumber K) /
    (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|)

theorem number_constant_residue
    (K : Type u) [Field K] [NumberField K] :
    classNumberConstant K = NumberField.dedekindZeta_residue K := by
  rw [classNumberConstant,
    NumberField.dedekindZeta_residue_def]

theorem number_constant_pos
    (K : Type u) [Field K] [NumberField K] :
    0 < classNumberConstant K := by
  rw [number_constant_residue]
  exact NumberField.dedekindZeta_residue_pos K

/-- The literal ratio interpretation of
`ζ_K(s) ~ c_K / (s - 1)` as real `s ↓ 1`.  This is stronger than merely
naming `c_K` a residue, and follows from Mathlib's one-sided limit because
`c_K` is nonzero. -/
theorem dedekind_asymptotic_ratio
    (K : Type u) [Field K] [NumberField K] :
    Tendsto
      (fun s : ℝ ↦
        NumberField.dedekindZeta K s /
          ((classNumberConstant K : ℂ) / (s - 1)))
      (𝓝[>] 1) (𝓝 1) := by
  have hres : (classNumberConstant K : ℂ) ≠ 0 := by
    exact_mod_cast (number_constant_pos K).ne'
  have h :=
    (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).div_const
      (classNumberConstant K : ℂ)
  rw [← number_constant_residue] at h
  have heq : Filter.EventuallyEq (𝓝[>] 1)
      (fun s : ℝ ↦
        ((s - 1) * NumberField.dedekindZeta K s) /
          (classNumberConstant K : ℂ))
      (fun s : ℝ ↦
        NumberField.dedekindZeta K s /
          ((classNumberConstant K : ℂ) / (s - 1))) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (s : ℂ) - 1 ≠ 0 := by
      exact_mod_cast (sub_ne_zero.mpr hs.ne')
    field_simp
  simpa [div_self hres] using Filter.Tendsto.congr' heq h

/-- The literal conjunction in Theorem V.2.4(a).  Only its second component
is currently supplied by the Dedekind-zeta API. -/
def DedekindContinuationAsymptotic
    (K : Type u) [Field K] [NumberField K] : Prop :=
  DedekindMeromorphicContinuation K ∧
    Tendsto
      (fun s : ℝ ↦
        NumberField.dedekindZeta K s /
          ((classNumberConstant K : ℂ) / (s - 1)))
      (𝓝[>] 1) (𝓝 1)

/-- Since the class-number asymptotic is proved independently, the only
currently missing component of the literal clause (a) is meromorphic
continuation. -/
theorem analytic_consequences_meromorphic
    (K : Type u) [Field K] [NumberField K] :
    DedekindContinuationAsymptotic K ↔
      DedekindMeromorphicContinuation K := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, dedekind_asymptotic_ratio K⟩

theorem asymptotic_analytic_consequences
    (K : Type u) [Field K] [NumberField K]
    (h : DedekindContinuationAsymptotic K) :
    Tendsto
      (fun s : ℝ ↦
        NumberField.dedekindZeta K s /
          ((classNumberConstant K : ℂ) / (s - 1)))
      (𝓝[>] 1) (𝓝 1) :=
  h.2

open Submission.CField.RCGroups

/-- A nonzero integral ideal prime to the finite part of a modulus, the
indexing objects in the ray-class Dirichlet series. -/
structure IIPrime
    (K : Type u) [Field K] [NumberField K] (m : Modulus K) where
  ideal : Ideal (𝓞 K)
  ne_zero : ideal ≠ 0
  primeTo : ∀ p ∈ m.finiteSupport,
    FractionalIdeal.count K p
      (ideal : FractionalIdeal (𝓞 K)⁰ K) = 0

/-- The corresponding element of the group of fractional ideals away from
the modulus. -/
def IIPrime.idealsPrime
    {K : Type u} [Field K] [NumberField K] {m : Modulus K}
    (I : IIPrime K m) :
    IdealsPrimeTo (𝓞 K) K m.finiteSupport :=
  ⟨Units.mk0 (I.ideal : FractionalIdeal (𝓞 K)⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr I.ne_zero), I.primeTo⟩

/-- The ray class quotient `C_m = I^S / i(K_{m,1})`. -/
abbrev StatementsRayGroup
    (K : Type u) [Field K] [NumberField K] (m : Modulus K) :=
  IdealsPrimeTo (𝓞 K) K m.finiteSupport ⧸
    Submission.CField.ARecip.rayPrincipalSubgroup K m

/-- The ray class of a nonzero integral ideal prime to the modulus. -/
def rayIntegralIdeal
    {K : Type u} [Field K] [NumberField K] {m : Modulus K}
    (I : IIPrime K m) :
    StatementsRayGroup K m :=
  QuotientGroup.mk'
    (Submission.CField.ARecip.rayPrincipalSubgroup K m)
    I.idealsPrime

/-- A ray-class character in the sense of the source. -/
abbrev RayClassCharacter
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) :=
  StatementsRayGroup K m →* ℂˣ

/-- The contribution of all integral ideals of norm `n` to the ray-class
Dirichlet series.  The finite set is a norm shell; ideals not prime to the
finite part of the modulus contribute zero. -/
def rayLShell
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (chi : RayClassCharacter K m)
    (s : ℂ) (n : ℕ) : ℂ :=
  ∑ I ∈ (Ideal.finite_setOf_absNorm_eq n).toFinset,
    if hI : I ≠ 0 ∧
        ∀ p ∈ m.finiteSupport,
          FractionalIdeal.count K p
            (I : FractionalIdeal (𝓞 K)⁰ K) = 0 then
      (chi (rayIntegralIdeal
        { ideal := I, ne_zero := hI.1, primeTo := hI.2 }) : ℂ) *
          (n : ℂ) ^ (-s)
    else 0

/-- Partial sums ordered by increasing ideal norm.  This is the ordering
implicit in the source Dirichlet series. -/
def rayLPartial
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (chi : RayClassCharacter K m)
    (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, rayLShell K m chi s n

/-- Ordered convergence of the ray-class Dirichlet series.  This deliberately
uses convergence of the sequence of norm-ordered partial sums, rather than
`Summable` or `LSeriesSummable`, which encode unconditional/absolute
summability in this setting. -/
def RayLConverges
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (chi : RayClassCharacter K m) (s : ℂ) : Prop :=
  ∃ value : ℂ, Tendsto (rayLPartial K m chi s) atTop (𝓝 value)

/-- The ordered value at a point is nonzero, independently of how the unique
limit is named. -/
def RayLNonzero
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (chi : RayClassCharacter K m) (s : ℂ) : Prop :=
  ∀ value : ℂ,
    Tendsto (rayLPartial K m chi s) atTop (𝓝 value) → value ≠ 0

/-- Literal statement of Theorem V.2.4(b), with conditional convergence
expressed through norm-ordered partial sums. -/
def LConvergenceNonvanishing
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (chi : RayClassCharacter K m) : Prop :=
  chi ≠ 1 →
    (∀ s : ℂ, 0 < s.re → RayLConverges K m chi s) ∧
      RayLNonzero K m chi 1

theorem convergence_analytic_consequences
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (chi : RayClassCharacter K m)
    (h : LConvergenceNonvanishing K m chi) (hchi : chi ≠ 1) :
    ∀ s : ℂ, 0 < s.re → RayLConverges K m chi s :=
  (h hchi).1

theorem nonzero_analytic_consequences
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (chi : RayClassCharacter K m)
    (h : LConvergenceNonvanishing K m chi) (hchi : chi ≠ 1) :
    RayLNonzero K m chi 1 :=
  (h hchi).2

end

end Submission.CField.Charac
