import Submission.Algebra.DenseGenerators.JenningsSeparation
import Submission.Group.ZassenhausTrivial


open Filter
open scoped Pointwise Topology

noncomputable section

universe u v

namespace Submission

section JenningsReductions

variable {p : ℕ} [Fact p.Prime]
variable {Q : Type u} [Group Q] [Finite Q]

omit [Fact (Nat.Prime p)] [Finite Q] in
/-- Immediate target reduction: once you have membership in `D_(n+1)`, `hbot` finishes. -/
theorem truncated_separation_d
    {n : ℕ}
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {q : Q}
    (hqDs : q ∈ zassenhausFiltration p Q (n + 1)) :
    q = 1 := by
  have hqbot : q ∈ (⊥ : Subgroup Q) := by
    simpa [hbot] using hqDs
  simpa using hqbot

omit [Finite Q] in
/-- Isolate the remaining hard step:
`q ∈ D_n` and `q - 1 ∈ I^(n+1)` imply `q ∈ D_(n+1)`. -/
theorem separation_d_bot
    {n : ℕ}
    (_hn : 0 < n)
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hqI : groupAlgebraSub p Q q ∈ augmentationIdealPower p Q (n + 1))
    (hstep : ∀ {r : Q},
      r ∈ zassenhausFiltration p Q n →
      groupAlgebraSub p Q r ∈ augmentationIdealPower p Q (n + 1) →
      r ∈ zassenhausFiltration p Q (n + 1)) :
    q = 1 := by
  exact truncated_separation_d
    (p := p) (Q := Q) (n := n) hbot (hstep hqD hqI)

/-- Formal bridge from the finite trivial-Zassenhaus upper theorem to the local target. -/
theorem separation_d_trivial
    {n : ℕ}
    (H : TUBound.{u} (p := p) (n + 1))
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {q : Q}
    (hqI : groupAlgebraSub p Q q ∈ augmentationIdealPower p Q (n + 1)) :
    q = 1 := by
  have hqI_ideal :
      groupAlgebraSub p Q q ∈
        denseGeneratorsIdeal p Q ^ (n + 1) := by
    exact
      (Submodule.restrictScalars_mem (ZMod p)
        (denseGeneratorsIdeal p Q ^ (n + 1))
        (groupAlgebraSub p Q q)).mp
        (by simpa [augmentationIdealPower] using hqI)
  have hqCongruence :
      dDCongru p Q (n + 1) q := by
    simpa [groupAlgebraSub, dDCongru]
      using hqI_ideal
  exact
    H.one_trivial_zassenhaus
      (Λ := Q) hbot q hqCongruence

omit [Fact (Nat.Prime p)] [Finite Q] in
/-- In a killed successor quotient, a nonidentity element cannot lie in the killed term. -/
lemma not_filtration_bot
    {n : ℕ}
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {q : Q}
    (hqne : q ≠ 1) :
    q ∉ zassenhausFiltration p Q (n + 1) := by
  intro hqsucc
  have hqbot : q ∈ (⊥ : Subgroup Q) := by
    simpa [hbot] using hqsucc
  exact hqne (Subgroup.mem_bot.mp hqbot)

omit [Finite Q] in
/-- Final reduction to the top-layer nonvanishing statement. -/
theorem separation_d_nonvanishing
    {n : ℕ}
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    (htop :
      ∀ {r : Q},
        r ∈ zassenhausFiltration p Q n →
        r ∉ zassenhausFiltration p Q (n + 1) →
          groupAlgebraSub p Q r ∉ augmentationIdealPower p Q (n + 1))
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hqI : groupAlgebraSub p Q q ∈ augmentationIdealPower p Q (n + 1)) :
    q = 1 := by
  by_contra hqne
  exact
    (htop hqD
      (not_filtration_bot
        (p := p) (Q := Q) hbot hqne)) hqI

omit [Finite Q] in
/-- A packaged positive dimension-subgroup bound gives the required top-layer nonvanishing. -/
theorem top_nonvanishing_bound
    {n : ℕ}
    (H : DDBound (p := p) Q n) :
    ∀ {r : Q},
      r ∈ zassenhausFiltration p Q n →
      r ∉ zassenhausFiltration p Q (n + 1) →
        groupAlgebraSub p Q r ∉ augmentationIdealPower p Q (n + 1) := by
  intro r hrD hrNot hrI
  have hrI_ideal :
      groupAlgebraSub p Q r ∈
        denseGeneratorsIdeal p Q ^ (n + 1) := by
    exact
      (Submodule.restrictScalars_mem (ZMod p)
        (denseGeneratorsIdeal p Q ^ (n + 1))
        (groupAlgebraSub p Q r)).mp
        (by simpa [augmentationIdealPower] using hrI)
  have hrCongruence :
      dDCongru p Q (n + 1) r := by
    simpa [groupAlgebraSub, dDCongru]
      using hrI_ideal
  have hrAug :
      r ∈ denseGeneratorsSubgroup p Q (n + 1) :=
    (dense_generators_subgroup
      (p := p) (Λ := Q) (m := n + 1) r).2 hrCongruence
  have hrKernel :
      r ∈ dGKern p Q n := by
    rw [dense_algebra_kernel]
    exact ⟨hrD, hrAug⟩
  exact hrNot (H.mem_succ hrKernel)

omit [Finite Q] in
/-- A packaged positive dimension-subgroup bound proves the local target directly. -/
theorem separation_d_bound
    {n : ℕ}
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    (H : DDBound (p := p) Q n)
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hqI : groupAlgebraSub p Q q ∈ augmentationIdealPower p Q (n + 1)) :
    q = 1 := by
  exact
    separation_d_nonvanishing
      (p := p) (Q := Q) hbot
      (top_nonvanishing_bound
        (p := p) (Q := Q) H)
      hqD hqI

end JenningsReductions

end Submission
