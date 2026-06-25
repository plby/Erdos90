import Towers.ClassField.IdeleCohomology.CompletionGaloisAction
import Towers.ClassField.IdeleCohomology.InfiniteIdeleAction

/-!
# The archimedean construction before Lemma VII.2.1

This is the infinite-place counterpart of `CompletionProductGaloisAction`.
It transfers the action through Milne's canonical decomposition

`L \otimes_K K_v \simeq \prod_{w \mid v} L_w`

for an infinite place `v`, and identifies it with the same coordinate
formula `(sigma * alpha)(w) = sigma(alpha(sigma⁻¹ * w))`.
-/

namespace Towers.CField.ICohomo

open AbsoluteValue NumberField
open Towers.NumberTheory.Milne
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

set_option backward.isDefEq.respectTransparency false in
local instance archimedeanConstructionBaseAlgebra (v : InfinitePlace K) :
    Algebra K v.1.Completion :=
  completionBaseAlgebra v.1

local instance archimedeanConstructionBaseSMul (v : InfinitePlace K) :
    SMul K v.1.Completion :=
  (archimedeanConstructionBaseAlgebra v).toSMul

local instance archimedeanConstructionBaseModule (v : InfinitePlace K) :
    Module K v.1.Completion :=
  Algebra.toModule

/-- Infinite places of `L` above a fixed infinite place of `K`. -/
abbrev InfiniteCompletionAbove (v : InfinitePlace K) :=
  {w : InfinitePlace L // w.comap (algebraMap K L) = v}

/-- Galois conjugation preserves the fiber of infinite places above `v`. -/
@[reducible]
instance placesAboveAction (v : InfinitePlace K) :
    MulAction Gal(L/K) (InfiniteCompletionAbove (L := L) v) where
  smul sigma w := ⟨infinitePlaceAction sigma w.1, by
    apply Subtype.ext
    apply AbsoluteValue.ext
    intro x
    change ‖w.1.embedding (sigma.symm (algebraMap K L x))‖ = v.1 x
    rw [sigma.symm.commutes, InfinitePlace.norm_embedding_eq]
    exact congrArg (fun z : InfinitePlace K => z.1 x) w.2⟩
  one_smul w := by
    apply Subtype.ext
    letI := infinitePlacesAction (K := K) (L := L)
    exact one_smul Gal(L/K) w.1
  mul_smul sigma tau w := by
    apply Subtype.ext
    letI := infinitePlacesAction (K := K) (L := L)
    exact mul_smul sigma tau w.1

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
@[simp]
theorem above_smul_val
    (v : InfinitePlace K) (sigma : Gal(L/K))
    (w : InfiniteCompletionAbove (L := L) v) :
    letI := placesAboveAction (K := K) (L := L) v
    (sigma • w).1 = infinitePlaceAction sigma w.1 :=
  rfl

/-- The family of archimedean completions above `v`. -/
abbrev InfiniteFamilyAbove
    (v : InfinitePlace K) (w : InfiniteCompletionAbove (L := L) v) :=
  w.1.1.Completion

set_option backward.isDefEq.respectTransparency false in
local instance archimedeanConstructionPlaceAlgebra
    (v : InfinitePlace K)
    (w : InfiniteCompletionAbove (L := L) v) :
    Algebra v.1.Completion w.1.1.Completion :=
  (completionLies v.1 w.1.1
    (infinite_lies_comap v w.1 w.2)).toAlgebra

/-- The coordinate transport between conjugate archimedean completions. -/
def infiniteFamilyTransport
    (v : InfinitePlace K) (sigma : Gal(L/K))
    (w : InfiniteCompletionAbove (L := L) v) :
    letI := placesAboveAction (K := K) (L := L) v
    InfiniteFamilyAbove v (sigma⁻¹ • w) ≃+*
      InfiniteFamilyAbove v w := by
  letI := placesAboveAction (K := K) (L := L) v
  letI := infinitePlacesAction (K := K) (L := L)
  exact infinitePlaceTransport sigma w.1

/-- Milne's coordinate formula on the product of archimedean completions. -/
def infiniteCompletionAction
    (v : InfinitePlace K) (sigma : Gal(L/K))
    (alpha : ∀ w : InfiniteCompletionAbove (L := L) v,
      InfiniteFamilyAbove v w) :
    ∀ w : InfiniteCompletionAbove (L := L) v,
      InfiniteFamilyAbove v w := by
  letI := placesAboveAction (K := K) (L := L) v
  exact fun w => infiniteFamilyTransport v sigma w
    (alpha (sigma⁻¹ • w))

/-- The diagonal family obtained from one global element. -/
def infiniteGlobalEmbedding
    (v : InfinitePlace K) (a : L) :
    ∀ w : InfiniteCompletionAbove (L := L) v,
      InfiniteFamilyAbove v w :=
  fun w => completionEmbedding w.1.1 a

/-- The diagonal embedding of the completed base field. -/
def infiniteBaseDiagonal
    (v : InfinitePlace K) (b : v.1.Completion) :
    ∀ w : InfiniteCompletionAbove (L := L) v,
      InfiniteFamilyAbove v w :=
  fun w => completionLies v.1 w.1.1
    (infinite_lies_comap v w.1 w.2) b

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- Archimedean completion transport is linear over the fixed completed
base field. -/
theorem infinite_transport_base
    (v : InfinitePlace K) (sigma : Gal(L/K))
    (w : InfiniteCompletionAbove (L := L) v)
    (b : v.1.Completion) :
    letI := placesAboveAction (K := K) (L := L) v
    infiniteFamilyTransport v sigma w
        (completionLies v.1 (sigma⁻¹ • w).1.1
          (infinite_lies_comap v (sigma⁻¹ • w).1
            (sigma⁻¹ • w).2) b) =
      completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2) b := by
  letI := placesAboveAction (K := K) (L := L) v
  letI := infinitePlacesAction (K := K) (L := L)
  let sourceLies := infinite_lies_comap v (sigma⁻¹ • w).1
    (sigma⁻¹ • w).2
  let targetLies := infinite_lies_comap v w.1 w.2
  have hfun :
      (fun c : v.1.Completion => infiniteFamilyTransport v sigma w
        (completionLies v.1 (sigma⁻¹ • w).1.1 sourceLies c)) =
      fun c : v.1.Completion =>
        completionLies v.1 w.1.1 targetLies c :=
    (dense_range_embedding v.1).equalizer
      ((continuous_infinite_transport sigma w.1).comp
        (completion_lies_isometry v.1
          (sigma⁻¹ • w).1.1 sourceLies).continuous)
      (completion_lies_isometry v.1 w.1.1 targetLies).continuous
      (funext fun x => by
        change infiniteFamilyTransport v sigma w
            (completionLies v.1 (sigma⁻¹ • w).1.1 sourceLies
              (completionEmbedding v.1 x)) =
          completionLies v.1 w.1.1 targetLies
            (completionEmbedding v.1 x)
        rw [show completionLies v.1 (sigma⁻¹ • w).1.1 sourceLies
              (completionEmbedding v.1 x) =
            completionEmbedding (sigma⁻¹ • w).1.1 (algebraMap K L x) by
          exact RingHom.congr_fun
            (completion_lies_comp v.1
              (sigma⁻¹ • w).1.1 sourceLies) x]
        rw [show completionLies v.1 w.1.1 targetLies
              (completionEmbedding v.1 x) =
            completionEmbedding w.1.1 (algebraMap K L x) by
          exact RingHom.congr_fun
            (completion_lies_comp v.1 w.1.1 targetLies) x]
        change infinitePlaceTransport sigma w.1
            (completionEmbedding (sigma⁻¹ • w.1).1 (algebraMap K L x)) =
          completionEmbedding w.1.1 (algebraMap K L x)
        rw [infinite_transport_embedding]
        simp)
  exact congrFun hfun b

/-- The action obtained by literally conjugating the tensor-factor action
through the archimedean tensor/product equivalence. -/
def transferredInfiniteAlg
    (v : InfinitePlace K) (sigma : Gal(L/K)) :
    (∀ w : InfiniteCompletionAbove (L := L) v,
      InfiniteFamilyAbove v w) ≃ₐ[v.1.Completion]
      (∀ w : InfiniteCompletionAbove (L := L) v,
        InfiniteFamilyAbove v w) :=
  (infiniteTensorCompletions (K := K) (L := L) v).symm.trans
    ((tensorGaloisAlg v.1 sigma).trans
      (infiniteTensorCompletions (K := K) (L := L) v))

omit [NumberField L] in
/-- The archimedean tensor/product equivalence intertwines the action through
`L` with Milne's coordinate action. -/
theorem infinite_completions_equivariant
    (v : InfinitePlace K) (sigma : Gal(L/K))
    (x : L ⊗[K] v.1.Completion) :
    infiniteTensorCompletions (K := K) (L := L) v
        (tensorGaloisAlg v.1 sigma x) =
      infiniteCompletionAction v sigma
        (infiniteTensorCompletions
          (K := K) (L := L) v x) := by
  letI := placesAboveAction (K := K) (L := L) v
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · funext w
    change (0 : InfiniteFamilyAbove v w) =
      infiniteFamilyTransport v sigma w 0
    exact (infiniteFamilyTransport v sigma w).map_zero.symm
  · intro a b
    funext w
    change infiniteTensorCompletions
          (K := K) (L := L) v
          (tensorGaloisAlg v.1 sigma (a ⊗ₜ[K] b)) w =
      infiniteFamilyTransport v sigma w
        (infiniteTensorCompletions
          (K := K) (L := L) v (a ⊗ₜ[K] b) (sigma⁻¹ • w))
    rw [tensor_galois_tmul,
      infinite_completions_tmul,
      infinite_completions_tmul, map_mul]
    rw [show infiniteFamilyTransport v sigma w
          (completionEmbedding (sigma⁻¹ • w).1.1 a) =
        completionEmbedding w.1.1 (sigma a) by
      letI := infinitePlacesAction (K := K) (L := L)
      exact infinite_transport_embedding sigma w.1 a]
    rw [infinite_transport_base]
  · intro x y hx hy
    let e := infiniteTensorCompletions (K := K) (L := L) v
    let g := tensorGaloisAlg v.1 sigma
    calc
      e (g (x + y)) = e (g x + g y) := congrArg e (g.map_add x y)
      _ = e (g x) + e (g y) := e.map_add _ _
      _ = infiniteCompletionAction v sigma (e x) +
          infiniteCompletionAction v sigma (e y) := by rw [hx, hy]
      _ = infiniteCompletionAction v sigma (e (x + y)) := by
        funext w
        change infiniteFamilyTransport v sigma w (e x (sigma⁻¹ • w)) +
            infiniteFamilyTransport v sigma w (e y (sigma⁻¹ • w)) =
          infiniteFamilyTransport v sigma w (e (x + y) (sigma⁻¹ • w))
        rw [← (infiniteFamilyTransport v sigma w).map_add]
        exact congrArg (infiniteFamilyTransport v sigma w)
          (congrFun (e.map_add x y) (sigma⁻¹ • w)).symm

set_option maxHeartbeats 1000000 in
-- Unfolding the archimedean tensor equivalence has a dependent completion family.
omit [NumberField L] in
/-- The transferred archimedean action and the coordinate formula agree
pointwise. -/
theorem transferred_infinite_alg
    (v : InfinitePlace K) (sigma : Gal(L/K))
    (alpha : ∀ w : InfiniteCompletionAbove (L := L) v,
      InfiniteFamilyAbove v w) :
    transferredInfiniteAlg v sigma alpha =
      infiniteCompletionAction v sigma alpha := by
  let e := infiniteTensorCompletions
    (K := K) (L := L) v
  let x := e.symm alpha
  change e (tensorGaloisAlg v.1 sigma x) =
    infiniteCompletionAction v sigma alpha
  rw [infinite_completions_equivariant]
  exact congrArg (infiniteCompletionAction v sigma)
    (e.apply_symm_apply alpha)

omit [NumberField L] in
/-- The identity acts trivially after archimedean tensor transfer. -/
theorem transferred_infinite_galois
    (v : InfinitePlace K) :
    transferredInfiniteAlg v (1 : Gal(L/K)) =
      AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro alpha
  unfold transferredInfiniteAlg
  rw [tensor_alg_one]
  exact (infiniteTensorCompletions
    (K := K) (L := L) v).apply_symm_apply alpha

omit [NumberField L] in
/-- Products act by composition after archimedean tensor transfer. -/
theorem transferred_galois_alg
    (v : InfinitePlace K) (sigma tau : Gal(L/K)) :
    transferredInfiniteAlg v (sigma * tau) =
      (transferredInfiniteAlg v tau).trans
        (transferredInfiniteAlg v sigma) := by
  apply AlgEquiv.ext
  intro alpha
  unfold transferredInfiniteAlg
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [tensor_galois_alg]
  rfl

set_option maxHeartbeats 5000000 in
-- Packaging the dependent archimedean product action unfolds completion fibers.
omit [NumberField L] in
/-- The archimedean tensor-transfer construction is a continuous Galois
action with Milne's coordinate formula. -/
theorem transferred_action_continuous
    (v : InfinitePlace K) :
    ContinuousGaloisAction
      (InfiniteFamilyAbove (L := L) v)
      (fun sigma w => infiniteFamilyTransport v sigma w)
      (fun sigma alpha =>
        transferredInfiniteAlg v sigma alpha) := by
  letI := placesAboveAction (K := K) (L := L) v
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro alpha
    change transferredInfiniteAlg v 1 alpha = alpha
    simpa using congrArg (fun e => e alpha)
      (transferred_infinite_galois (K := K) (L := L) v)
  · intro sigma tau alpha
    change transferredInfiniteAlg v (sigma * tau) alpha =
      transferredInfiniteAlg v sigma
        (transferredInfiniteAlg v tau alpha)
    simpa only [AlgEquiv.trans_apply] using
      congrArg (fun e => e alpha)
        (transferred_galois_alg
          (K := K) (L := L) v sigma tau)
  · intro sigma alpha w
    exact congrFun
      (transferred_infinite_alg v sigma alpha) w
  · intro sigma
    change Continuous (fun alpha =>
      transferredInfiniteAlg v sigma alpha)
    rw [show (fun alpha =>
        transferredInfiniteAlg v sigma alpha) =
        infiniteCompletionAction v sigma by
      funext alpha
      exact transferred_infinite_alg v sigma alpha]
    exact continuous_pi fun w =>
      (continuous_infinite_transport sigma w.1).comp
        (continuous_apply (sigma⁻¹ • w))

omit [NumberField L] in
/-- The archimedean transferred action fixes the diagonal copy of `K_v`. -/
theorem transferred_base_diagonal
    (v : InfinitePlace K) (sigma : Gal(L/K)) (b : v.1.Completion) :
    transferredInfiniteAlg v sigma
        (infiniteBaseDiagonal v b) =
      infiniteBaseDiagonal v b := by
  letI := placesAboveAction (K := K) (L := L) v
  rw [transferred_infinite_alg]
  funext w
  exact infinite_transport_base v sigma w b

omit [NumberField L] in
/-- The archimedean transferred action sends the diagonal family of `a` to
the diagonal family of `sigma a`. -/
theorem transferred_global_embedding
    (v : InfinitePlace K) (sigma : Gal(L/K)) (a : L) :
    transferredInfiniteAlg v sigma
        (infiniteGlobalEmbedding v a) =
      infiniteGlobalEmbedding v (sigma a) := by
  letI := placesAboveAction (K := K) (L := L) v
  rw [transferred_infinite_alg]
  funext w
  letI := infinitePlacesAction (K := K) (L := L)
  exact infinite_transport_embedding sigma w.1 a

end

end Towers.CField.ICohomo
