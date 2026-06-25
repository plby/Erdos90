import Towers.NumberTheory.Locals.WeakApproximation
import Towers.NumberTheory.Locals.CompletionUniversal

/-!
# Weak approximation in completed fields

Milne states Weak Approximation with targets in the completions attached to
the chosen absolute values.  This file obtains that form by composing the
dense diagonal map into the `WithAbs` fields with the coordinatewise dense
completion embeddings.
-/

namespace Towers.NumberTheory.Milne

open AbsoluteValue
open scoped Topology

variable {K : Type*} [Field K]
variable {ι : Type*} [Finite ι]

/-- Milne, Theorem 7.20, completion-valued form: the diagonal image of `K`
is dense in the finite product of the completions belonging to pairwise
inequivalent nontrivial absolute values. -/
theorem weak_approximation_range
    (v : ι → AbsoluteValue K ℝ)
    (hnt : ∀ i, (v i).IsNontrivial)
    (hpair : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) :
    DenseRange (fun x : K ↦ fun i ↦ completionEmbedding (v i) x) := by
  let complete : ((i : ι) → WithAbs (v i)) →
      ((i : ι) → (v i).Completion) :=
    fun z i ↦ (z i : (v i).Completion)
  have hdenseComplete : DenseRange complete :=
    DenseRange.piMap fun i ↦ UniformSpace.Completion.denseRange_coe
  have hcontinuousComplete : Continuous complete := by
    exact continuous_pi fun i ↦
      (UniformSpace.Completion.continuous_coe _).comp (continuous_apply i)
  have hcomp := hdenseComplete.comp
    (weak_approximation_dense v hnt hpair) hcontinuousComplete
  simpa [complete, Function.comp_def, completionEmbedding_apply] using hcomp

end Towers.NumberTheory.Milne
