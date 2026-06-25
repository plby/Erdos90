import Mathlib.LinearAlgebra.Span.Basic
import Submission.ClassField.ProfiniteCohom.Cochains

/-!
# Milne, Class Field Theory, Proposition II.4.4: cochain factorization

The image of a continuous cochain is finite.  If its coefficient module is a
directed union of submodules, that finite image is contained in one stage.
-/

namespace Submission.CField.PCohom

open Set

universe u v w

variable {R : Type u} [Semiring R]
  {M : Type v} [AddCommMonoid M] [Module R M]
  {ι : Type w} [Nonempty ι]

/-- A finite subset of a directed union of submodules is contained in a
single member of the family. -/
theorem subset_directed_submodules
    (S : ι → Submodule R M) (hS : Directed (· ≤ ·) S)
    (s : Set M) (hs : s.Finite)
    (hmem : ∀ x ∈ s, ∃ i, x ∈ S i) :
    ∃ i, s ⊆ S i := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      exact ⟨Classical.choice inferInstance, by simp⟩
  | @insert x s hxs hs ih =>
      obtain ⟨i, hi⟩ := hmem x (mem_insert x s)
      obtain ⟨j, hj⟩ := ih fun y hy ↦ hmem y (mem_insert_of_mem x hy)
      obtain ⟨k, hik, hjk⟩ := hS i j
      refine ⟨k, ?_⟩
      intro y hy
      rcases mem_insert_iff.mp hy with rfl | hy
      · exact hik hi
      · exact hjk (hj hy)

/-- The cochain-level compactness argument in Proposition II.4.4. -/
theorem contained_directed_submodule
    (S : ι → Submodule R M) (hS : Directed (· ≤ ·) S)
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace M] [DiscreteTopology M]
    (f : A → M) (hf : Continuous f)
    (hcover : ∀ x, ∃ i, x ∈ S i) :
    ∃ i, ∀ a, f a ∈ S i := by
  obtain ⟨i, hi⟩ := subset_directed_submodules S hS (range f)
    (continuous_compact_discrete hf)
    (fun x _ ↦ hcover x)
  exact ⟨i, fun a ↦ hi ⟨a, rfl⟩⟩

end Submission.CField.PCohom
