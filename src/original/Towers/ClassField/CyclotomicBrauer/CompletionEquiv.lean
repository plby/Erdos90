import Towers.ClassField.CyclotomicBrauer.CompletionDegree
import Towers.NumberTheory.Locals.CompletionUniversal

/-!
# Lemma VII.7.3: completions transported by algebra equivalence

The common-ambient compositum replaces each abstract prime-power block by an
algebra-equivalent intermediate field.  This file proves that pulling a
place back along that equivalence produces an algebra-equivalent completion
over the same base completion, hence preserves the local degree.
-/

namespace Towers.CField.CBrauer

open AbsoluteValue UniformSpace NumberField
open Towers.NumberTheory.Milne

noncomputable section

universe u v w

variable {K : Type v} {L : Type w} {E : Type u}
  [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra K E]

/-- Pull an absolute value back along a field equivalence. -/
def pullbackAbsoluteValue
    (e : L ≃ₐ[K] E) (w : AbsoluteValue E ℝ) : AbsoluteValue L ℝ :=
  w.comp (f := e.toRingEquiv.toRingHom) e.injective

/-- Pullback preserves the lower place because an algebra equivalence
commutes with the base-field embeddings. -/
theorem pullback_absolute_lies
    (e : L ≃ₐ[K] E) (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue E ℝ) (hwv : AbsoluteValue.LiesOver w v) :
    AbsoluteValue.LiesOver (pullbackAbsoluteValue e w) v := by
  constructor
  ext x
  change w (e (algebraMap K L x)) = v x
  rw [e.commutes]
  exact DFunLike.congr_fun hwv.comp_eq x

/-- The ring equivalence between completions induced by a global algebra
equivalence. -/
def completionRingAlg
    (e : L ≃ₐ[K] E) (w : AbsoluteValue E ℝ) :
    (pullbackAbsoluteValue e w).Completion ≃+* w.Completion := by
  let u := pullbackAbsoluteValue e w
  let f : L →+* w.Completion :=
    (completionEmbedding w).comp e.toRingEquiv.toRingHom
  have hf : ∀ x, ‖f x‖ = u x := by
    intro x
    rw [show f x = completionEmbedding w (e x) by rfl,
      norm_completionEmbedding]
    rfl
  have hfdense : DenseRange f := by
    apply DenseRange.of_comp (g := e.symm)
    simpa [f, Function.comp_def] using dense_range_embedding w
  exact Classical.choose (completion_unique_equiv u f hf hfdense)

/-- The completion equivalence is an isometry. -/
theorem completion_alg_isometry
    (e : L ≃ₐ[K] E) (w : AbsoluteValue E ℝ) :
    Isometry (completionRingAlg e w) := by
  let u := pullbackAbsoluteValue e w
  let f : L →+* w.Completion :=
    (completionEmbedding w).comp e.toRingEquiv.toRingHom
  have hf : ∀ x, ‖f x‖ = u x := by
    intro x
    rw [show f x = completionEmbedding w (e x) by rfl,
      norm_completionEmbedding]
    rfl
  have hfdense : DenseRange f := by
    apply DenseRange.of_comp (g := e.symm)
    simpa [f, Function.comp_def] using dense_range_embedding w
  exact (Classical.choose_spec (completion_unique_equiv u f hf hfdense)).1.1

/-- The completion equivalence extends the original global equivalence. -/
@[simp]
theorem completion_alg_embedding
    (e : L ≃ₐ[K] E) (w : AbsoluteValue E ℝ) (x : L) :
    completionRingAlg e w
        (completionEmbedding (pullbackAbsoluteValue e w) x) =
      completionEmbedding w (e x) := by
  let u := pullbackAbsoluteValue e w
  let f : L →+* w.Completion :=
    (completionEmbedding w).comp e.toRingEquiv.toRingHom
  have hf : ∀ x, ‖f x‖ = u x := by
    intro y
    rw [show f y = completionEmbedding w (e y) by rfl,
      norm_completionEmbedding]
    rfl
  have hfdense : DenseRange f := by
    apply DenseRange.of_comp (g := e.symm)
    simpa [f, Function.comp_def] using dense_range_embedding w
  have hcomp :=
    (Classical.choose_spec (completion_unique_equiv u f hf hfdense)).1.2
  exact RingHom.congr_fun hcomp x

/-- The induced completion equivalence is an algebra equivalence over the
unchanged base completion. -/
def completionAlgEquiv
    (e : L ≃ₐ[K] E) (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue E ℝ) (hwv : AbsoluteValue.LiesOver w v) :
    let u := pullbackAbsoluteValue e w
    let huv := pullback_absolute_lies e v w hwv
    letI : Algebra v.Completion u.Completion :=
      (completionLies v u huv).toAlgebra
    letI : Algebra v.Completion w.Completion :=
      (completionLies v w hwv).toAlgebra
    u.Completion ≃ₐ[v.Completion] w.Completion := by
  let u := pullbackAbsoluteValue e w
  let huv := pullback_absolute_lies e v w hwv
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  apply AlgEquiv.ofRingEquiv
    (f := completionRingAlg e w)
  intro b
  have hfun :
      (fun c : v.Completion ↦
        completionRingAlg e w
          (completionLies v u huv c)) =
        fun c : v.Completion ↦ completionLies v w hwv c :=
    (dense_range_embedding v).equalizer
      ((completion_alg_isometry e w).continuous.comp
        (completion_lies_isometry v u huv).continuous)
      (completion_lies_isometry v w hwv).continuous
      (funext fun x ↦ by
        change completionRingAlg e w
            (completionLies v u huv (completionEmbedding v x)) =
          completionLies v w hwv (completionEmbedding v x)
        rw [show completionLies v u huv (completionEmbedding v x) =
            completionEmbedding u (algebraMap K L x) by
          exact RingHom.congr_fun (completion_lies_comp v u huv) x]
        rw [completion_alg_embedding]
        rw [e.commutes]
        exact (RingHom.congr_fun
          (completion_lies_comp v w hwv) x).symm)
  exact congrFun hfun b

/-- Local completion degree is invariant under replacing the global field
by an algebra-equivalent copy and pulling back the upper place. -/
theorem completion_finrank_alg
    (e : L ≃ₐ[K] E) (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue E ℝ) (hwv : AbsoluteValue.LiesOver w v) :
    let u := pullbackAbsoluteValue e w
    let huv := pullback_absolute_lies e v w hwv
    letI : Algebra v.Completion u.Completion :=
      (completionLies v u huv).toAlgebra
    letI : Algebra v.Completion w.Completion :=
      (completionLies v w hwv).toAlgebra
    Module.finrank v.Completion u.Completion =
      Module.finrank v.Completion w.Completion := by
  let u := pullbackAbsoluteValue e w
  let huv := pullback_absolute_lies e v w hwv
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  exact (completionAlgEquiv e v w hwv).toLinearEquiv.finrank_eq

end

end Towers.CField.CBrauer
