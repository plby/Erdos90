import Submission.ClassField.IdeleCohomology.TensorGaloisAction

/-!
# Milne's construction before Lemma VII.2.1

For a finite Galois extension `L / K` and a nonarchimedean absolute value
`v` of `K`, Milne uses the canonical equivalence

`L \otimes_K K_v \simeq \prod_{w \mid v} L_w`

to transfer the action through the `L` factor to the product of the
completions.  This file carries out that transfer and proves that the result
is the coordinate action already constructed in `CompletionProductAction`.
It then records the three properties listed immediately before Lemma 2.1:
continuity, fixed diagonal `K_v`, and equivariance of the diagonal copy of
`L`.
-/

namespace Submission.CField.ICohomo

open AbsoluteValue
open Submission.NumberTheory.Milne
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

set_option backward.isDefEq.respectTransparency false in
local instance constructionBaseAlgebra (v : AbsoluteValue K ℝ) :
    Algebra K v.Completion :=
  completionBaseAlgebra v

local instance constructionBaseSMul (v : AbsoluteValue K ℝ) :
    SMul K v.Completion :=
  (constructionBaseAlgebra v).toSMul

local instance constructionBaseModule (v : AbsoluteValue K ℝ) :
    Module K v.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance constructionPlaceAlgebra
    (v : AbsoluteValue K ℝ) (w : CompletionPlacesAbove (L := L) v) :
    Algebra v.Completion w.1.Completion :=
  (completionLies v w.1 w.2).toAlgebra

/-- The action obtained exactly as in the paragraph before Lemma VII.2.1:
conjugate the action on `L \otimes_K K_v` by the canonical tensor/product
equivalence. -/
def transferredGaloisAlg
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (sigma : Gal(L/K)) :
    (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) ≃ₐ[v.Completion]
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) :=
  (completionTensorCompletions (K := K) (L := L) v).symm.trans
    ((tensorGaloisAlg v sigma).trans
      (completionTensorCompletions (K := K) (L := L) v))

/-- The canonical tensor/product equivalence intertwines the action on the
`L` tensor factor with Milne's coordinate action on completions. -/
theorem tensor_completions_equivariant
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (sigma : Gal(L/K)) (x : L ⊗[K] v.Completion) :
    completionTensorCompletions (K := K) (L := L) v
        (tensorGaloisAlg v sigma x) =
      completionProductAction v sigma
        (completionTensorCompletions (K := K) (L := L) v x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simpa only [map_zero] using
      ((completionSemiringAction v).smul_zero sigma).symm
  · intro a b
    funext w
    change completionTensorPlace v w
          (tensorGaloisAlg v sigma (a ⊗ₜ[K] b)) =
      completionFamilyTransport v sigma w
        (completionTensorPlace v (sigma⁻¹ • w) (a ⊗ₜ[K] b))
    rw [tensor_galois_tmul,
      tensor_place_tmul,
      tensor_place_tmul, map_mul,
      show completionFamilyTransport v sigma w
          (completionEmbedding (sigma⁻¹ • w).1 a) =
          completionEmbedding w.1 (sigma a) by
        exact completion_transport_embedding sigma w.1 a]
    have hb := congrFun (action_base_diagonal v sigma b) w
    exact congrArg (completionEmbedding w.1 (sigma a) * ·) hb.symm
  · intro x y hx hy
    let e := completionTensorCompletions (K := K) (L := L) v
    let g := tensorGaloisAlg v sigma
    calc
      e (g (x + y)) = e (g x + g y) := congrArg e (g.map_add x y)
      _ = e (g x) + e (g y) := e.map_add _ _
      _ = completionProductAction v sigma (e x) +
          completionProductAction v sigma (e y) := by
        rw [hx, hy]
      _ = completionProductAction v sigma (e x + e y) :=
        ((completionSemiringAction v).smul_add sigma _ _).symm
      _ = completionProductAction v sigma (e (x + y)) :=
        congrArg (completionProductAction v sigma) (e.map_add x y).symm

/-- The action transported through the tensor-product decomposition is not
merely abstractly equivalent to the coordinate action: the two functions
are equal. -/
theorem transferred_alg_equiv
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (sigma : Gal(L/K))
    (alpha : ∀ w : CompletionPlacesAbove (L := L) v,
      CompletionFamilyAbove v w) :
    transferredGaloisAlg v sigma alpha =
      completionProductAction v sigma alpha := by
  let e := completionTensorCompletions (K := K) (L := L) v
  let x := e.symm alpha
  change e (tensorGaloisAlg v sigma x) =
    completionProductAction v sigma alpha
  rw [tensor_completions_equivariant]
  exact congrArg (completionProductAction v sigma) (e.apply_symm_apply alpha)

/-- The literal tensor-transfer construction is continuous and is a genuine
Galois action.  This is condition (a) together with the action laws in the
paragraph before Lemma VII.2.1. -/
theorem transferred_galois_continuous
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] :
    ContinuousGaloisAction
      (CompletionFamilyAbove (L := L) v)
      (fun sigma w => completionFamilyTransport v sigma w)
      (fun sigma alpha => transferredGaloisAlg v sigma alpha) := by
  simpa only [transferred_alg_equiv] using
    galois_action_continuous (K := K) (L := L) v

/-- Condition (b): the transported action fixes the diagonal copy of the
completed base field `K_v`. -/
theorem transferred_alg_diagonal
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (sigma : Gal(L/K)) (b : v.Completion) :
    transferredGaloisAlg v sigma
        (completionBaseDiagonal v b) =
      completionBaseDiagonal v b := by
  rw [transferred_alg_equiv]
  exact action_base_diagonal v sigma b

/-- Condition (c): the transported action sends the family defined by
`a : L` to the family defined by `sigma a`. -/
theorem transferred_alg_embedding
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (sigma : Gal(L/K)) (a : L) :
    transferredGaloisAlg v sigma
        (completionGlobalEmbedding v a) =
      completionGlobalEmbedding v (sigma a) := by
  rw [transferred_alg_equiv]
  exact action_global_embedding v sigma a

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Continuity and the prescribed action on the diagonal copy of `L`
already force the diagonal copy of `K_v` to be fixed.  This formalizes
Milne's parenthetical observation that condition (b) follows from (a) and
(c), because `K` is dense in `K_v`. -/
theorem continuous_diagonal_embedding
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (sigma : Gal(L/K))
    (f :
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) →+*
        (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w))
    (hf : Continuous f)
    (hglobal : ∀ a : L,
      f (completionGlobalEmbedding v a) =
        completionGlobalEmbedding v (sigma a))
    (b : v.Completion) :
    f (completionBaseDiagonal v b) =
      completionBaseDiagonal v b := by
  have hdiagContinuous :
      Continuous (completionBaseDiagonal (L := L) v) :=
    continuous_pi fun w =>
      (completion_lies_isometry v w.1 w.2).continuous
  have hfun :
      (fun c : v.Completion =>
        f (completionBaseDiagonal v c)) =
      completionBaseDiagonal v :=
    (dense_range_embedding v).equalizer
      (hf.comp hdiagContinuous) hdiagContinuous
      (funext fun x => by
        have hbaseGlobal :
            completionBaseDiagonal (L := L) v
                (completionEmbedding v x) =
              completionGlobalEmbedding v (algebraMap K L x) := by
          funext w
          exact RingHom.congr_fun
            (completion_lies_comp v w.1 w.2) x
        change f (completionBaseDiagonal v (completionEmbedding v x)) =
          completionBaseDiagonal v (completionEmbedding v x)
        rw [hbaseGlobal, hglobal, sigma.commutes, ← hbaseGlobal])
  exact congrFun hfun b

/-- The continuity and global-diagonal clauses determine the action
uniquely.  Thus the literal tensor-transfer construction is the unique
continuous ring action satisfying condition (c); condition (b) need not be
assumed separately. -/
theorem completion_action_unique
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (sigma : Gal(L/K))
    (f :
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) →+*
        (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w))
    (hf : Continuous f)
    (hglobal : ∀ a : L,
      f (completionGlobalEmbedding v a) =
        completionGlobalEmbedding v (sigma a)) :
    (f :
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) →
        (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w)) =
      completionProductAction v sigma := by
  let e := completionTensorCompletions (K := K) (L := L) v
  letI : MulSemiringAction Gal(L/K)
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) :=
    completionSemiringAction v
  funext alpha
  obtain ⟨x, rfl⟩ := e.surjective alpha
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simpa only [map_zero] using
      ((completionSemiringAction v).smul_zero sigma).symm
  · intro a b
    have htmul :
        e (a ⊗ₜ[K] b) =
          completionGlobalEmbedding v a *
            completionBaseDiagonal v b := by
      funext w
      change completionTensorPlace v w (a ⊗ₜ[K] b) = _
      rw [tensor_place_tmul]
      rfl
    rw [htmul, map_mul, hglobal,
      continuous_diagonal_embedding v sigma f hf hglobal,
      show completionProductAction v sigma
          (completionGlobalEmbedding v a * completionBaseDiagonal v b) =
          completionProductAction v sigma (completionGlobalEmbedding v a) *
            completionProductAction v sigma (completionBaseDiagonal v b) by
        exact (completionSemiringAction v).smul_mul sigma _ _,
      action_global_embedding,
      action_base_diagonal]
  · intro x y hx hy
    calc
      f (e (x + y)) = f (e x + e y) := congrArg f (e.map_add x y)
      _ = f (e x) + f (e y) := f.map_add _ _
      _ = completionProductAction v sigma (e x) +
          completionProductAction v sigma (e y) := by rw [hx, hy]
      _ = completionProductAction v sigma (e x + e y) :=
        ((completionSemiringAction v).smul_add sigma _ _).symm
      _ = completionProductAction v sigma (e (x + y)) :=
        congrArg (completionProductAction v sigma) (e.map_add x y).symm

end

end Submission.CField.ICohomo
