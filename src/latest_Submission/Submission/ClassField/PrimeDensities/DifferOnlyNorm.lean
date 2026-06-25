import Submission.ClassField.PrimeDensities.SetEulerClauses
import Submission.ClassField.PrimeDensities.ContainsNoNorm

/-!
# Milne, Class Field Theory, Corollary VI.3.3

If two sets of finite primes differ only at primes whose absolute norm is not
a rational prime, Proposition 3.2 gives density zero to both set differences.
Proposition 3.1(c), applied first by subtraction and then by addition, shows
that either set has a polar density exactly when the other does, with the same
value.
-/

namespace Submission.CField.PDensit

open IsDedekindDomain NumberField Set

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The exact exceptional-prime condition in Corollary 3.3: every prime in
either one-sided set difference has absolute norm that is not prime in
`ℤ`. -/
def DifferNonAbsolute
    (S T : Set (HeightOneSpectrum (𝓞 K))) : Prop :=
  ContainsNoAbsolute K (S \ T) ∧
    ContainsNoAbsolute K (T \ S)

omit [NumberField K] in
/-- The elementary decomposition of `S` into its common part with `T` and
its one-sided difference. -/
theorem inter_diff_right
    (S T : Set (HeightOneSpectrum (𝓞 K))) :
    S = (S ∩ T) ∪ (S \ T) := by
  ext p
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
  tauto

omit [NumberField K] in
/-- The common part is disjoint from the part of `S` missing from `T`. -/
theorem disjoint_inter_diff
    (S T : Set (HeightOneSpectrum (𝓞 K))) :
    Disjoint (S ∩ T) (S \ T) := by
  rw [Set.disjoint_left]
  intro p hp hdiff
  exact hdiff.2 hp.2

/-- One direction of Corollary 3.3.  The density-zero exceptional part is
subtracted from `S`, and the other exceptional part is then added to obtain
`T`. -/
theorem differ_only_non
    (h31c : PolarDisjointLaws K)
    (h32 : ∀ T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ContainsNoAbsolute K T → PrimePolarDensity K T 0)
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hdiff : DifferNonAbsolute K S T)
    (hS : PrimePolarDensity K S δ) :
    PrimePolarDensity K T δ := by
  let A : Set (HeightOneSpectrum (𝓞 K)) := S ∩ T
  let DS : Set (HeightOneSpectrum (𝓞 K)) := S \ T
  let DT : Set (HeightOneSpectrum (𝓞 K)) := T \ S
  have hDS : PrimePolarDensity K DS 0 := h32 DS hdiff.1
  have hDT : PrimePolarDensity K DT 0 := h32 DT hdiff.2
  have hSdecomp : S = A ∪ DS := inter_diff_right K S T
  have hTdecomp : T = A ∪ DT := by
    simpa [A, DT, inter_comm] using inter_diff_right K T S
  have hdisjS : Disjoint A DS := disjoint_inter_diff K S T
  have hdisjT : Disjoint A DT := by
    simpa [A, DT, inter_comm] using disjoint_inter_diff K T S
  have hA_sub : PrimePolarDensity K A (δ - 0) :=
    ((h31c S A DS δ δ 0 hSdecomp hdisjS).2.2 ⟨hS, hDS⟩)
  have hA : PrimePolarDensity K A δ := by
    simpa using hA_sub
  have hT_add : PrimePolarDensity K T (δ + 0) :=
    (h31c T A DT δ δ 0 hTdecomp hdisjT).1 ⟨hA, hDT⟩
  simpa using hT_add

/-- Literal conclusion of Corollary VI.3.3: existence and value of polar
density are unchanged by modifying only primes of non-prime absolute norm. -/
def DifferNonConclusion
    (S T : Set (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ δ : ℝ,
    PrimePolarDensity K S δ ↔
      PrimePolarDensity K T δ

/-- **Corollary VI.3.3 (source statement).** -/
def DifferOnlyNon : Prop :=
  ∀ S T : Set (HeightOneSpectrum (𝓞 K)),
    DifferNonAbsolute K S T →
      DifferNonConclusion K S T

/-- Propositions 3.1(c) and 3.2 prove Corollary 3.3 with no additional
hypothesis. -/
theorem differ_non_clauses
    (h31 : EulerDensityLaws K)
    (h32 : (∀ T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)),
          ContainsNoAbsolute K T → PrimePolarDensity K T 0)) :
    DifferOnlyNon K := by
  intro S T hdiff δ
  have h31c : PolarDisjointLaws K := h31.2.2.1
  constructor
  · exact differ_only_non
      K h31c h32 hdiff
  · exact differ_only_non
      K h31c h32 ⟨hdiff.2, hdiff.1⟩

end

end Submission.CField.PDensit
