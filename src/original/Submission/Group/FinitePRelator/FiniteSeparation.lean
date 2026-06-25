import Submission.Group.FinitePRelator.FiniteQuotients


open scoped Topology

noncomputable section

namespace Submission
namespace PRSep

open PCShadow
open PRFact
open PRQuotie

universe u

variable
    {p : ℕ}
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    {ι : Type*}
    {relator : ι → F}

/-- A finite relator quotient detects every element of a displayed set. -/
def SeparatesSet
    (S : RQShadow p F relator)
    (s : Set F) :
    Prop :=
  ∀ x ∈ s, x ∉ S.map.ker

omit [IsTopologicalGroup F] in
lemma separatesSet_mono
    (S : RQShadow p F relator)
    {s t : Set F}
    (hst : s ⊆ t)
    (hsep : SeparatesSet S t) :
    SeparatesSet S s := by
  intro x hx
  exact hsep x (hst hx)

omit [IsTopologicalGroup F] in
lemma separates_set_singleton
    (S : RQShadow p F relator)
    (x : F) :
    SeparatesSet S {x} ↔ x ∉ S.map.ker := by
  simp [SeparatesSet]

variable
    {p : ℕ}
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    {ι : Type*}
    {relator : ι → F}
    {q : F →* G}
    {x : F}

omit [IsTopologicalGroup F] in
/--
The relator residual kernel can be tested using actual surjective finite
relator quotients, not merely arbitrary finite relator shadows.
-/
lemma relator_forall_shadows :
    x ∈ relatorKernel p relator ↔
      ∀ S : RQShadow p F relator, x ∈ S.map.ker := by
  constructor
  · intro hx S
    exact relator_kernel S.toRShadow hx
  · intro hx
    rw [mem_relator_iff]
    intro S
    simpa using hx (RQShadow.relatorShadowRange S)

omit [IsTopologicalGroup F] in
/--
An element outside the relator residual kernel is detected by one actual
surjective finite relator quotient.
-/
lemma not_relator_shadow :
    x ∉ relatorKernel p relator ↔
      ∃ S : RQShadow p F relator, x ∉ S.map.ker := by
  rw [relator_forall_shadows]
  simp

omit [IsTopologicalGroup F] in
/--
Finitely many elements outside the relator residual kernel can be detected
simultaneously by one finite relator quotient.
-/
lemma relator_shadow_separating
    [Fact p.Prime]
    (xs : List F)
    (hxs : ∀ x ∈ xs, x ∉ relatorKernel p relator) :
    ∃ S : RQShadow p F relator,
      ∀ x ∈ xs, x ∉ S.map.ker := by
  induction xs with
  | nil =>
      exact ⟨RQShadow.trivial, by simp⟩
  | cons x xs ih =>
      rcases (not_relator_shadow
          (p := p) (relator := relator) (x := x)).mp (hxs x (by simp)) with
        ⟨Sx, hxSx⟩
      rcases ih (fun y hy => hxs y (by simp [hy])) with ⟨Sxs, hSxs⟩
      refine ⟨RQShadow.inf Sx Sxs, ?_⟩
      intro y hy hyKernel
      rw [RQShadow.inf_kernel] at hyKernel
      simp only [List.mem_cons] at hy
      cases hy with
      | inl hyHead =>
          apply hxSx
          simpa [hyHead] using hyKernel.1
      | inr hyTail =>
          exact hSxs y hyTail hyKernel.2

omit [IsTopologicalGroup F] in
/--
A finite subset of the complement of the relator residual kernel has one
surjective finite relator quotient detecting all of its elements.
-/
lemma shadow_separating_finset
    [Fact p.Prime]
    (s : Finset F)
    (hs : ∀ x ∈ s, x ∉ relatorKernel p relator) :
    ∃ S : RQShadow p F relator,
      ∀ x ∈ s, x ∉ S.map.ker := by
  classical
  simpa only [Finset.mem_toList] using
    relator_shadow_separating
      (p := p)
      (relator := relator)
      s.toList
      (by simpa only [Finset.mem_toList] using hs)

omit [IsTopologicalGroup F] in
/--
For finite sets, avoiding the relator residual kernel is equivalent to being
simultaneously detected by a single finite relator quotient.
-/
lemma set_avoids_separating
    [Fact p.Prime]
    {s : Set F}
    (hsfinite : s.Finite) :
    (∀ x ∈ s, x ∉ relatorKernel p relator) ↔
      ∃ S : RQShadow p F relator, SeparatesSet S s := by
  constructor
  · intro hs
    classical
    rcases shadow_separating_finset
        (p := p)
        (relator := relator)
        hsfinite.toFinset
        (by simpa using hs) with
      ⟨S, hS⟩
    exact ⟨S, by simpa [SeparatesSet] using hS⟩
  · rintro ⟨S, hS⟩ x hx hxKernel
    exact hS x hx (relator_kernel S.toRShadow hxKernel)

omit [IsTopologicalGroup F] in
/--
Failure of finite quotient factorization is witnessed by one kernel element
and one actual surjective finite relator quotient.
-/
lemma not_property_counterexample :
    ¬ QuotientFactorizationProperty p relator q ↔
      ∃ S : RQShadow p F relator,
        ∃ x : F, x ∈ q.ker ∧ x ∉ S.map.ker := by
  rw [QuotientFactorizationProperty]
  simp only [not_forall, SetLike.not_le_iff_exists]

omit [IsTopologicalGroup F] in
/--
If the candidate kernel is not contained in the relator residual kernel, one
finite relator quotient already witnesses the obstruction.
-/
lemma counterexample_not_relator
    (hkernel : ¬ q.ker ≤ relatorKernel p relator) :
    ∃ S : RQShadow p F relator,
      ∃ x : F, x ∈ q.ker ∧ x ∉ S.map.ker := by
  rw [← not_property_counterexample]
  intro hfactor
  exact hkernel ((factorization_property_relator).mp hfactor)

end PRSep
end Submission
