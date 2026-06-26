import Towers.NumberTheory.Locals.CompletionUniversal
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.FieldTheory.Galois.Notation

/-!
# Galois conjugation on absolute-value completions

This file constructs the completion-conjugation maps used in the construction
preceding Milne, Chapter VII, Lemma 2.1.  We use the standard left action

`(sigma * w)(x) = w(sigma^-1 x)`.

Thus `sigma` is an isometry from the field equipped with `w` to the field
equipped with `sigma * w`, and consequently extends to an isometric ring
equivalence between the corresponding completions.
-/

namespace Towers.CField.ICohomo

open AbsoluteValue UniformSpace
open Towers.NumberTheory.Milne

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Galois conjugation of an absolute value, with the left-action convention
`(sigma * w)(x) = w(sigma^-1 x)`. -/
def conjugateAbsoluteValue
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) : AbsoluteValue L ℝ :=
  w.comp (f := sigma.symm.toRingEquiv.toRingHom) sigma.symm.injective

/-- The standard Galois action on absolute values. -/
instance : MulAction Gal(L/K) (AbsoluteValue L ℝ) where
  smul := conjugateAbsoluteValue
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

@[simp]
theorem smul_absolute_value
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) (x : L) :
    (sigma • w) x = w (sigma.symm x) :=
  rfl

/-- The isometric Galois equivalence before taking completions. -/
def absGaloisRing
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    WithAbs w ≃+* WithAbs (sigma • w) :=
  WithAbs.congr w (sigma • w) sigma.toRingEquiv

@[simp]
theorem abs_galois_ring
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) (x : WithAbs w) :
    absGaloisRing sigma w x =
      WithAbs.toAbs (sigma • w) (sigma x.ofAbs) :=
  rfl

/-- Galois conjugation preserves the norms attached to the conjugate
absolute values. -/
theorem abs_galois_isometry
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    Isometry (absGaloisRing sigma w) :=
  AddMonoidHomClass.isometry_of_norm _ fun x => by
    change w (sigma.symm (sigma x.ofAbs)) = w x.ofAbs
    simp

/-- The isometric equivalence underlying Galois conjugation before
completion. -/
def absGaloisIsometry
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    WithAbs w ≃ᵢ WithAbs (sigma • w) where
  toEquiv := (absGaloisRing sigma w).toEquiv
  isometry_toFun := abs_galois_isometry sigma w

/-- The extension of a Galois automorphism to an equivalence between the
corresponding absolute-value completions. -/
def completionGaloisRing
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    w.Completion ≃+* (sigma • w).Completion := by
  let f : L →+* (sigma • w).Completion :=
    (completionEmbedding (sigma • w)).comp sigma.toRingEquiv.toRingHom
  have hf : ∀ x, ‖f x‖ = w x := by
    intro x
    rw [show f x = completionEmbedding (sigma • w) (sigma x) by rfl,
      norm_completionEmbedding]
    simp
  have hfdense : DenseRange f := by
    apply DenseRange.of_comp (g := sigma.symm)
    simpa [f, Function.comp_def] using dense_range_embedding (sigma • w)
  exact Classical.choose (completion_unique_equiv w f hf hfdense)

/-- The completion-conjugation equivalence is an isometry. -/
theorem completion_galois_isometry
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    Isometry (completionGaloisRing sigma w) := by
  let f : L →+* (sigma • w).Completion :=
    (completionEmbedding (sigma • w)).comp sigma.toRingEquiv.toRingHom
  have hf : ∀ x, ‖f x‖ = w x := by
    intro x
    rw [show f x = completionEmbedding (sigma • w) (sigma x) by rfl,
      norm_completionEmbedding]
    simp
  have hfdense : DenseRange f := by
    apply DenseRange.of_comp (g := sigma.symm)
    simpa [f, Function.comp_def] using dense_range_embedding (sigma • w)
  exact (Classical.choose_spec (completion_unique_equiv w f hf hfdense)).1.1

/-- Completion conjugation as an isometric equivalence. -/
def completionGaloisIsometry
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    w.Completion ≃ᵢ (sigma • w).Completion where
  toEquiv := (completionGaloisRing sigma w).toEquiv
  isometry_toFun := completion_galois_isometry sigma w

/-- Completion conjugation extends the original Galois automorphism. -/
@[simp]
theorem completion_galois_embedding
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) (x : L) :
    completionGaloisRing sigma w (completionEmbedding w x) =
      completionEmbedding (sigma • w) (sigma x) := by
  let f : L →+* (sigma • w).Completion :=
    (completionEmbedding (sigma • w)).comp sigma.toRingEquiv.toRingHom
  have hf : ∀ x, ‖f x‖ = w x := by
    intro y
    rw [show f y = completionEmbedding (sigma • w) (sigma y) by rfl,
      norm_completionEmbedding]
    simp
  have hfdense : DenseRange f := by
    apply DenseRange.of_comp (g := sigma.symm)
    simpa [f, Function.comp_def] using dense_range_embedding (sigma • w)
  have hcomp :=
    (Classical.choose_spec (completion_unique_equiv w f hf hfdense)).1.2
  exact RingHom.congr_fun hcomp x

/-- Conjugation by the identity is the identity on the completion. -/
@[simp]
theorem completion_galois_one (w : AbsoluteValue L ℝ) :
    completionGaloisRing (1 : Gal(L/K)) w = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro y
  have hfun :
      (completionGaloisRing (1 : Gal(L/K)) w : w.Completion → w.Completion) = id :=
    (dense_range_embedding w).equalizer
      (completion_galois_isometry (1 : Gal(L/K)) w).continuous
      continuous_id
      (funext fun x => by
        change completionGaloisRing (1 : Gal(L/K)) w
            (completionEmbedding w x) = completionEmbedding w x
        simpa using
          completion_galois_embedding
            (1 : Gal(L/K)) w x)
  exact congrFun hfun y

/-- Completion conjugation respects multiplication in the Galois group. -/
theorem completion_galois_ring
    (sigma tau : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    completionGaloisRing (sigma * tau) w =
      (completionGaloisRing tau w).trans
        (completionGaloisRing sigma (tau • w)) := by
  apply RingEquiv.ext
  intro y
  have hfun :
      (completionGaloisRing (sigma * tau) w :
          w.Completion → ((sigma * tau) • w).Completion) =
        fun z => completionGaloisRing sigma (tau • w)
          (completionGaloisRing tau w z) :=
    (dense_range_embedding w).equalizer
      (completion_galois_isometry (sigma * tau) w).continuous
      ((completion_galois_isometry sigma (tau • w)).continuous.comp
        (completion_galois_isometry tau w).continuous)
      (funext fun x => by
        change completionGaloisRing (sigma * tau) w
            (completionEmbedding w x) =
          completionGaloisRing sigma (tau • w)
            (completionGaloisRing tau w (completionEmbedding w x))
        rw [completion_galois_embedding,
          completion_galois_embedding,
          completion_galois_embedding]
        rfl)
  exact congrFun hfun y

/-- Identity coherence in the inverse form occurring in the product action. -/
theorem galois_ring_inv (w : AbsoluteValue L ℝ) :
    completionGaloisRing (1 : Gal(L/K))⁻¹ w = RingEquiv.refl _ := by
  simpa only [inv_one] using completion_galois_one (K := K) w

/-- Multiplicative coherence in the inverse form occurring in the product
action. -/
theorem completion_galois_inv
    (sigma tau : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    completionGaloisRing (sigma * tau)⁻¹ w =
      (completionGaloisRing sigma⁻¹ w).trans
        (completionGaloisRing tau⁻¹ (sigma⁻¹ • w)) := by
  simpa only [mul_inv_rev] using
    completion_galois_ring (K := K) tau⁻¹ sigma⁻¹ w

/-- Transport from the completion at `sigma^-1 * w` to the completion at
`w`.  This is the coordinate map in the action formula preceding Lemma
VII.2.1. -/
def completionTransport
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    (sigma⁻¹ • w).Completion ≃+* w.Completion :=
  (completionGaloisRing sigma⁻¹ w).symm

/-- Coordinate transport is an isometry, hence continuous. -/
theorem completionTransport_isometry
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) :
    Isometry (completionTransport sigma w) :=
  (completionGaloisIsometry sigma⁻¹ w).symm.isometry

/-- Completion transport applies the original Galois automorphism to elements
of the dense global field. -/
@[simp]
theorem completion_transport_embedding
    (sigma : Gal(L/K)) (w : AbsoluteValue L ℝ) (x : L) :
    completionTransport sigma w (completionEmbedding (sigma⁻¹ • w) x) =
      completionEmbedding w (sigma x) := by
  change (completionGaloisRing sigma⁻¹ w).symm
      (completionEmbedding (sigma⁻¹ • w) x) = completionEmbedding w (sigma x)
  apply (completionGaloisRing sigma⁻¹ w).injective
  rw [RingEquiv.apply_symm_apply]
  rw [completion_galois_embedding]
  simp

end

end Towers.CField.ICohomo
