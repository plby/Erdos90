import Towers.ClassField.IdeleCohomology.CompletionProductAction
import Towers.NumberTheory.Locals.ArchimedeanPlaceClassification

namespace Towers.CField.ICohomo

open AbsoluteValue NumberField
open Towers.NumberTheory.Milne

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField L]
  [Algebra K L]

/-- Galois conjugation preserves infinite places. -/
def infinitePlaceAction (sigma : Gal(L/K)) (w : InfinitePlace L) :
    InfinitePlace L :=
  InfinitePlace.mk (w.embedding.comp sigma.symm.toRingEquiv.toRingHom)

omit [NumberField L] in
@[simp]
theorem infinite_action_val
    (sigma : Gal(L/K)) (w : InfinitePlace L) :
    (infinitePlaceAction sigma w).1 = sigma • w.1 := by
  apply AbsoluteValue.ext
  intro x
  change ‖w.embedding (sigma.symm x)‖ = w.1 (sigma.symm x)
  exact InfinitePlace.norm_embedding_eq w (sigma.symm x)

/-- The standard action of the Galois group on infinite places. -/
@[reducible]
def infinitePlacesAction : MulAction Gal(L/K) (InfinitePlace L) where
  smul := infinitePlaceAction
  one_smul w := by
    apply Subtype.ext
    change (infinitePlaceAction (1 : Gal(L/K)) w).1 = w.1
    rw [infinite_action_val]
    exact one_smul Gal(L/K) w.1
  mul_smul sigma tau w := by
    apply Subtype.ext
    change (infinitePlaceAction (sigma * tau) w).1 =
      (infinitePlaceAction sigma (infinitePlaceAction tau w)).1
    rw [infinite_action_val, infinite_action_val,
      infinite_action_val]
    exact mul_smul sigma tau w.1

private theorem ring_equiv_embedding
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    (h : v = u) (x : F) :
    completionEquiv h (completionEmbedding v x) =
      completionEmbedding u x := by
  subst u
  rfl

/-- Coordinate transport between conjugate infinite-place completions. -/
def infinitePlaceTransport
    (sigma : Gal(L/K)) (w : InfinitePlace L) :
    letI := infinitePlacesAction (K := K) (L := L)
    (sigma⁻¹ • w).Completion ≃+* w.Completion := by
  letI := infinitePlacesAction (K := K) (L := L)
  exact (completionEquiv
      (infinite_action_val (K := K) sigma⁻¹ w)).trans
    (completionTransport sigma w.1)

omit [NumberField L] in
/-- Infinite-place transport is continuous. -/
theorem continuous_infinite_transport
    (sigma : Gal(L/K)) (w : InfinitePlace L) :
    letI := infinitePlacesAction (K := K) (L := L)
    Continuous (infinitePlaceTransport sigma w) := by
  letI := infinitePlacesAction (K := K) (L := L)
  unfold infinitePlaceTransport
  change Continuous (fun x => completionTransport sigma w.1
    (completionEquiv
      (infinite_action_val (K := K) sigma⁻¹ w) x))
  exact (completionTransport_isometry sigma w.1).continuous.comp
    (continuous_completion_equiv
      (infinite_action_val (K := K) sigma⁻¹ w))

omit [NumberField L] in
/-- Infinite-place transport extends the Galois automorphism on the global
field, which is the principal-coordinate compatibility needed for ideles. -/
theorem infinite_transport_embedding
    (sigma : Gal(L/K)) (w : InfinitePlace L) (x : L) :
    letI := infinitePlacesAction (K := K) (L := L)
    infinitePlaceTransport sigma w
        (completionEmbedding (sigma⁻¹ • w).1 x) =
      completionEmbedding w.1 (sigma x) := by
  letI := infinitePlacesAction (K := K) (L := L)
  unfold infinitePlaceTransport
  let h := infinite_action_val (K := K) sigma⁻¹ w
  change completionTransport sigma w.1
      (completionEquiv h
        (completionEmbedding (infinitePlaceAction sigma⁻¹ w).1 x)) = _
  rw [ring_equiv_embedding h]
  exact completion_transport_embedding sigma w.1 x

end

end Towers.CField.ICohomo
