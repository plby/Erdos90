import Submission.ClassField.NormIndex.CompletionProductNorm
import Submission.ClassField.NormIndex.IdeleNormCompatibility
import Submission.ClassField.IdeleCohomology.ArchimedeanProduct
import Submission.ClassField.GrunwaldWang.PossibleInfiniteDegree

/-!
# Archimedean idèle norm compatibility

This file proves the infinite-place half of

`ext (Nm x) = ∏ sigma, sigma • x`.

The local completed extension at an infinite place is Galois, with Galois
group the stabilizer of that place.  Thus its field norm is the product of
the stabilizer action; orbit--stabilizer reindexing then gives the global
Galois product.
-/

namespace Submission.CField.NIndex

open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.GWang
open scoped BigOperators

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)

noncomputable local instance infinitePlacesAboveFintype
    (v : InfinitePlace K) :
    Fintype (InfinitePlacesAbove (K := K) (L := L) v) :=
  infiniteCor84ExtensionsFintype v

local instance infiniteCompletionStabilizerFintype
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    Fintype (CompletionPlaceStabilizer v.1
      (⟨w.1.1, infinite_lies_comap v w.1 w.2⟩ :
        CompletionPlacesAbove (L := L) v.1)) :=
  Fintype.ofFinite _

/-- Stabilizer of an actual infinite place in the fiber above `v`. -/
abbrev InfinitePlaceStabilizer
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :=
  letI := placesAboveAction (K := K) (L := L) v
  MulAction.stabilizer Gal(L/K) w

local instance infinitePlaceStabilizerFintype
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    Fintype (InfinitePlaceStabilizer (K := K) (L := L) v w) :=
  Fintype.ofFinite _

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- Galois conjugation is transitive on the actual infinite places above a
fixed base place. -/
theorem infinite_above_pretransitive
    (v : InfinitePlace K) :
    letI := placesAboveAction (K := K) (L := L) v
    MulAction.IsPretransitive Gal(L/K)
      (InfinitePlacesAbove (K := K) (L := L) v) := by
  letI := placesAboveAction (K := K) (L := L) v
  constructor
  intro w z
  obtain ⟨sigma, hsigma⟩ :=
    InfinitePlace.exists_smul_eq_of_comap_eq (w.2.trans z.2.symm)
  refine ⟨sigma, Subtype.ext ?_⟩
  simpa only [above_smul_val,
    infinite_action_smul] using hsigma

/-- A chosen global automorphism carrying one infinite place in the fiber to
the distinguished place. -/
noncomputable def infinitePlaceReturn
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v) :
    Gal(L/K) := by
  letI := placesAboveAction (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (InfinitePlacesAbove (K := K) (L := L) v) :=
    infinite_above_pretransitive v
  exact Classical.choose (MulAction.exists_smul_eq Gal(L/K) w w₀)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem infinite_return_smul
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v) :
    letI := placesAboveAction (K := K) (L := L) v
    infinitePlaceReturn (K := K) (L := L) v w₀ w • w = w₀ := by
  letI := placesAboveAction (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (InfinitePlacesAbove (K := K) (L := L) v) :=
    infinite_above_pretransitive v
  exact Classical.choose_spec (MulAction.exists_smul_eq Gal(L/K) w w₀)

/-- A place in the infinite fiber together with an element of its own
stabilizer. -/
abbrev InfinitePointStabilizers
    (v : InfinitePlace K) :=
  letI := placesAboveAction (K := K) (L := L) v
  Σ w : InfinitePlacesAbove (K := K) (L := L) v,
    InfinitePlaceStabilizer (K := K) (L := L) v w

noncomputable def infinitePointGalois
    (v : InfinitePlace K)
    (w₀ : InfinitePlacesAbove (K := K) (L := L) v) :
    InfinitePointStabilizers (K := K) (L := L) v → Gal(L/K) := by
  letI := placesAboveAction (K := K) (L := L) v
  exact fun p => infinitePlaceReturn v w₀ p.1 * p.2.1

noncomputable def infinitePointStabilizer
    (v : InfinitePlace K)
    (w₀ : InfinitePlacesAbove (K := K) (L := L) v) :
    Gal(L/K) → InfinitePointStabilizers (K := K) (L := L) v := by
  letI := placesAboveAction (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (InfinitePlacesAbove (K := K) (L := L) v) :=
    infinite_above_pretransitive v
  intro sigma
  let w : InfinitePlacesAbove (K := K) (L := L) v := sigma⁻¹ • w₀
  let r := infinitePlaceReturn v w₀ w
  have hr : r⁻¹ • w₀ = w := by
    calc
      r⁻¹ • w₀ = r⁻¹ • (r • w) := by
        rw [infinite_return_smul v w₀ w]
      _ = w := inv_smul_smul r w
  refine ⟨w, ⟨r⁻¹ * sigma, ?_⟩⟩
  change (r⁻¹ * sigma) • w = w
  rw [mul_smul]
  rw [show sigma • w = w₀ by
    dsimp only [w]
    exact smul_inv_smul sigma w₀]
  exact hr

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem infinite_point_after
    (v : InfinitePlace K)
    (w₀ : InfinitePlacesAbove (K := K) (L := L) v)
    (sigma : Gal(L/K)) :
    infinitePointGalois v w₀
        (infinitePointStabilizer v w₀ sigma) = sigma := by
  letI := placesAboveAction (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (InfinitePlacesAbove (K := K) (L := L) v) :=
    infinite_above_pretransitive v
  dsimp [infinitePointGalois,
    infinitePointStabilizer]
  simp

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem galois_after_forward
    (v : InfinitePlace K)
    (w₀ : InfinitePlacesAbove (K := K) (L := L) v)
    (p : InfinitePointStabilizers (K := K) (L := L) v) :
    infinitePointStabilizer v w₀
        (infinitePointGalois v w₀ p) = p := by
  letI := placesAboveAction (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (InfinitePlacesAbove (K := K) (L := L) v) :=
    infinite_above_pretransitive v
  rcases p with ⟨w, h⟩
  let r := infinitePlaceReturn v w₀ w
  have hr : r⁻¹ • w₀ = w := by
    calc
      r⁻¹ • w₀ = r⁻¹ • (r • w) := by
        rw [infinite_return_smul v w₀ w]
      _ = w := inv_smul_smul r w
  have hsource : ((r * h.1)⁻¹ • w₀ :
      InfinitePlacesAbove (K := K) (L := L) v) = w := by
    calc
      (r * h.1)⁻¹ • w₀ = h.1⁻¹ • (r⁻¹ • w₀) := by
        rw [mul_inv_rev, mul_smul]
      _ = h.1⁻¹ • w := congrArg (fun z => h.1⁻¹ • z) hr
      _ = w := (h⁻¹).2
  have hw :
      (infinitePointStabilizer v w₀
        (infinitePointGalois v w₀ ⟨w, h⟩)).1 = w :=
    hsource
  apply Sigma.ext hw
  apply (Subtype.heq_iff_coe_eq (fun sigma : Gal(L/K) => by rw [hw])).2
  change (infinitePlaceReturn v w₀ ((r * h.1)⁻¹ • w₀))⁻¹ *
      (r * h.1) = h.1
  rw [hsource]
  dsimp only [r]
  simp

/-- The global Galois group is the disjoint union of the stabilizers of all
infinite places over `v`. -/
noncomputable def infinitePlacePoint
    (v : InfinitePlace K)
    (w₀ : InfinitePlacesAbove (K := K) (L := L) v) :
    InfinitePointStabilizers (K := K) (L := L) v ≃ Gal(L/K) where
  toFun := infinitePointGalois v w₀
  invFun := infinitePointStabilizer v w₀
  left_inv := galois_after_forward v w₀
  right_inv := infinite_point_after v w₀

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem infinite_point_stabilizer
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v)
    (h : InfinitePlaceStabilizer (K := K) (L := L) v w) :
    infinitePlacePoint v w₀ ⟨w, h⟩ =
      infinitePlaceReturn v w₀ w * h.1 :=
  rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The stabilizer of an infinite place is its absolute-value decomposition
group. -/
theorem infinite_stabilizer_decomposition
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    letI := placesAboveAction (K := K) (L := L) v
    InfinitePlaceStabilizer (K := K) (L := L) v w =
      absoluteValueDecomposition v.1 w.1.1 := by
  letI := placesAboveAction (K := K) (L := L) v
  rw [absolute_decomposition_stabilizer]
  ext sigma
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hplace : infinitePlaceAction sigma w.1 = w.1 :=
      congrArg Subtype.val h
    have habs := congrArg Subtype.val hplace
    simpa only [infinite_action_val] using habs
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    change (infinitePlaceAction sigma w.1).1 = w.1.1
    simpa only [infinite_action_val] using h

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
private theorem stabilizer_smul_val
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (sigma : InfinitePlaceStabilizer (K := K) (L := L) v w) :
    sigma.1⁻¹ • w.1 = w.1 := by
  letI := placesAboveAction (K := K) (L := L) v
  have h := congrArg Subtype.val (sigma⁻¹).2
  change infinitePlaceAction sigma.1⁻¹ w.1 = w.1 at h
  simpa only [infinite_action_smul] using h

/-- The action of an infinite-place stabilizer element on its completion. -/
noncomputable def infinitePlaceStabilizer
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (sigma : InfinitePlaceStabilizer (K := K) (L := L) v w) :
    w.1.1.Completion ≃+* w.1.1.Completion :=
  (RingEquiv.cast
      (R := fun q : InfinitePlace L => q.1.Completion)
      (stabilizer_smul_val v w sigma).symm).trans
    (numberInfiniteTransport (K := K) sigma.1 w.1)

omit [NumberField L] in
private theorem infinite_place_embedding
    {q q' : InfinitePlace L} (h : q = q') (x : L) :
    RingEquiv.cast (R := fun z : InfinitePlace L => z.1.Completion) h
        (completionEmbedding q.1 x) = completionEmbedding q'.1 x := by
  subst q'
  rfl

omit [NumberField L] in
private theorem infinite_place_continuous
    {q q' : InfinitePlace L} (h : q = q') :
    Continuous (RingEquiv.cast
      (R := fun z : InfinitePlace L => z.1.Completion) h) := by
  subst q'
  exact continuous_id

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
@[simp]
theorem infinite_stabilizer_embedding
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (sigma : InfinitePlaceStabilizer (K := K) (L := L) v w)
    (x : L) :
    infinitePlaceStabilizer v w sigma
        (completionEmbedding w.1.1 x) =
      completionEmbedding w.1.1 (sigma.1 x) := by
  unfold infinitePlaceStabilizer
  rw [RingEquiv.trans_apply, infinite_place_embedding]
  exact number_transport_embedding sigma.1 w.1 x

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
private theorem infinite_stabilizer_continuous
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (sigma : InfinitePlaceStabilizer (K := K) (L := L) v w) :
    Continuous (infinitePlaceStabilizer v w sigma) := by
  unfold infinitePlaceStabilizer
  apply (number_transport_continuous sigma.1 w.1).comp
  exact infinite_place_continuous
    (stabilizer_smul_val v w sigma).symm

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The stabilizer action just defined is the canonical local decomposition
action. -/
theorem infinite_stabilizer_action
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (sigma : InfinitePlaceStabilizer (K := K) (L := L) v w)
    (x : w.1.1.Completion) :
    let hwv := infinite_lies_comap v w.1 w.2
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    let d : absoluteValueDecomposition v.1 w.1.1 :=
      MulEquiv.subgroupCongr
        (infinite_stabilizer_decomposition v w) sigma
    infinitePlaceStabilizer v w sigma x =
      decompositionCompletionEquiv v.1 w.1.1 d x := by
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  let d : absoluteValueDecomposition v.1 w.1.1 :=
    MulEquiv.subgroupCongr
      (infinite_stabilizer_decomposition v w) sigma
  have hfun :
      (fun y => infinitePlaceStabilizer v w sigma y) =
        fun y => decompositionCompletionEquiv v.1 w.1.1 d y :=
    (dense_range_embedding w.1.1).equalizer
      (infinite_stabilizer_continuous v w sigma)
      (decomposition_alg_continuous v.1 w.1.1 d)
      (funext fun y => by
        change infinitePlaceStabilizer v w sigma
            (completionEmbedding w.1.1 y) =
          decompositionCompletionEquiv v.1 w.1.1 d
            (completionEmbedding w.1.1 y)
        rw [infinite_stabilizer_embedding,
          decomposition_alg_embedding]
        rfl)
  exact congrFun hfun x

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
private theorem smul_val_fiber
    (v : InfinitePlace K) (sigma : Gal(L/K))
    (w z : InfinitePlacesAbove (K := K) (L := L) v)
    (h : letI := placesAboveAction
          (K := K) (L := L) v
        sigma • w = z) :
    sigma • w.1 = z.1 := by
  letI := placesAboveAction (K := K) (L := L) v
  calc
    sigma • w.1 = infinitePlaceAction sigma w.1 :=
      (infinite_action_smul sigma w.1).symm
    _ = (sigma • w).1 := rfl
    _ = z.1 := congrArg Subtype.val h

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
private theorem return_smul_val
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v) :
    (infinitePlaceReturn (K := K) (L := L) v w₀ w)⁻¹ • w₀.1 = w.1 := by
  letI := placesAboveAction (K := K) (L := L) v
  let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
  have hr : r⁻¹ • w₀ = w := by
    calc
      r⁻¹ • w₀ = r⁻¹ • (r • w) := by
        rw [infinite_return_smul v w₀ w]
      _ = w := inv_smul_smul r w
  exact smul_val_fiber v r⁻¹ w₀ w hr

/-- Transport from a place in the infinite fiber back to the distinguished
place. -/
noncomputable def infiniteReturnRing
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v) :
    w.1.1.Completion ≃+* w₀.1.1.Completion :=
  let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
  (RingEquiv.cast
      (R := fun q : InfinitePlace L => q.1.Completion)
      (return_smul_val v w₀ w).symm).trans
    (numberInfiniteTransport (K := K) r w₀.1)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
private theorem infinite_return_continuous
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v) :
    Continuous (infiniteReturnRing
      (K := K) (L := L) v w₀ w) := by
  let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
  unfold infiniteReturnRing
  apply (number_transport_continuous r w₀.1).comp
  exact infinite_place_continuous
    (return_smul_val v w₀ w).symm

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem infinite_return_embedding
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v)
    (x : L) :
    infiniteReturnRing (K := K) (L := L) v w₀ w
        (completionEmbedding w.1.1 x) =
      completionEmbedding w₀.1.1
        (infinitePlaceReturn (K := K) (L := L) v w₀ w x) := by
  let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
  unfold infiniteReturnRing
  rw [RingEquiv.trans_apply, infinite_place_embedding]
  exact number_transport_embedding r w₀.1 x

set_option maxHeartbeats 500000 in
-- Equality of the two completed-base embeddings is checked on the dense
-- global base field.
set_option maxRecDepth 100000 in
omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
theorem infinite_return_extension
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v)
    (b : v.1.Completion) :
    infiniteReturnRing (K := K) (L := L) v w₀ w
        (completionLies v.1 w.1.1
          (infinite_lies_comap v w.1 w.2) b) =
      completionLies v.1 w₀.1.1
        (infinite_lies_comap v w₀.1 w₀.2) b := by
  let sourceLies := infinite_lies_comap v w.1 w.2
  let targetLies := infinite_lies_comap v w₀.1 w₀.2
  let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
  have hfun :
      (fun c : v.1.Completion =>
        infiniteReturnRing (K := K) (L := L) v w₀ w
          (completionLies v.1 w.1.1 sourceLies c)) =
        fun c : v.1.Completion =>
          completionLies v.1 w₀.1.1 targetLies c :=
    (dense_range_embedding v.1).equalizer
      ((infinite_return_continuous v w₀ w).comp
        (completion_lies_isometry v.1 w.1.1 sourceLies).continuous)
      (completion_lies_isometry v.1 w₀.1.1 targetLies).continuous
      (funext fun x => by
        change infiniteReturnRing (K := K) (L := L) v w₀ w
            (completionLies v.1 w.1.1 sourceLies
              (completionEmbedding v.1 x)) =
          completionLies v.1 w₀.1.1 targetLies
            (completionEmbedding v.1 x)
        rw [show completionLies v.1 w.1.1 sourceLies
              (completionEmbedding v.1 x) =
            completionEmbedding w.1.1 (algebraMap K L x) by
          exact RingHom.congr_fun
            (completion_lies_comp v.1 w.1.1 sourceLies) x]
        rw [show completionLies v.1 w₀.1.1 targetLies
              (completionEmbedding v.1 x) =
            completionEmbedding w₀.1.1 (algebraMap K L x) by
          exact RingHom.congr_fun
            (completion_lies_comp v.1 w₀.1.1 targetLies) x]
        rw [infinite_return_embedding]
        rw [r.commutes])
  exact congrFun hfun b

private theorem ring_cast_pi
    {I : Type*} {R : I → Type*} [∀ i, Semiring (R i)]
    (x : ∀ i, R i) {i j : I} (h : i = j) :
    RingEquiv.cast h (x i) = x j := by
  subst j
  rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- On a dependent family of infinite-completion coordinates, the
stabilizer action is the corresponding coordinate of the global idèle
action. -/
theorem infinite_stabilizer_pi
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (sigma : InfinitePlaceStabilizer (K := K) (L := L) v w)
    (x : (q : InfinitePlace L) → q.1.Completion) :
    letI := placesAboveAction (K := K) (L := L) v
    infinitePlaceStabilizer v w sigma (x w.1) =
      numberInfiniteTransport (K := K) sigma.1 w.1
        (x (sigma.1⁻¹ • w.1)) := by
  letI := placesAboveAction (K := K) (L := L) v
  unfold infinitePlaceStabilizer
  rw [RingEquiv.trans_apply]
  apply congrArg (numberInfiniteTransport (K := K) sigma.1 w.1)
  exact ring_cast_pi x _

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- On a dependent family, return transport is the corresponding global
Galois-action coordinate. -/
theorem infinite_return_pi
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v)
    (x : (q : InfinitePlace L) → q.1.Completion) :
    letI := placesAboveAction (K := K) (L := L) v
    let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
    infiniteReturnRing (K := K) (L := L) v w₀ w (x w.1) =
      numberInfiniteTransport (K := K) r w₀.1
        (x (r⁻¹ • w₀.1)) := by
  letI := placesAboveAction (K := K) (L := L) v
  dsimp only
  unfold infiniteReturnRing
  rw [RingEquiv.trans_apply]
  apply congrArg (numberInfiniteTransport (K := K)
    (infinitePlaceReturn (K := K) (L := L) v w₀ w) w₀.1)
  exact ring_cast_pi x _

set_option maxHeartbeats 500000 in
-- The two continuous composites agree on the dense global field.
set_option maxRecDepth 100000 in
omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
private theorem infinite_return_stabilizer
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v)
    (h : InfinitePlaceStabilizer (K := K) (L := L) v w)
    (z : w.1.1.Completion) :
    letI := placesAboveAction (K := K) (L := L) v
    let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
    let sigma := r * h.1
    let hsource : sigma⁻¹ • w₀.1 = w.1 := by
      have hr : r⁻¹ • w₀ = w := by
        calc
          r⁻¹ • w₀ = r⁻¹ • (r • w) := by
            rw [infinite_return_smul v w₀ w]
          _ = w := inv_smul_smul r w
      apply smul_val_fiber v sigma⁻¹ w₀ w
      calc
        sigma⁻¹ • w₀ = h.1⁻¹ • (r⁻¹ • w₀) := by
          rw [mul_inv_rev, mul_smul]
        _ = h.1⁻¹ • w := congrArg (fun q => h.1⁻¹ • q) hr
        _ = w := (h⁻¹).2
    infiniteReturnRing (K := K) (L := L) v w₀ w
        (infinitePlaceStabilizer v w h z) =
      numberInfiniteTransport (K := K) sigma w₀.1
        (RingEquiv.cast
          (R := fun q : InfinitePlace L => q.1.Completion)
          hsource.symm z) := by
  letI := placesAboveAction (K := K) (L := L) v
  dsimp only
  let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
  let sigma := r * h.1
  let hsource : sigma⁻¹ • w₀.1 = w.1 := by
    have hr : r⁻¹ • w₀ = w := by
      calc
        r⁻¹ • w₀ = r⁻¹ • (r • w) := by
          rw [infinite_return_smul v w₀ w]
        _ = w := inv_smul_smul r w
    apply smul_val_fiber v sigma⁻¹ w₀ w
    calc
      sigma⁻¹ • w₀ = h.1⁻¹ • (r⁻¹ • w₀) := by
        rw [mul_inv_rev, mul_smul]
      _ = h.1⁻¹ • w := congrArg (fun q => h.1⁻¹ • q) hr
      _ = w := (h⁻¹).2
  have hfun :
      (fun y : w.1.1.Completion =>
        infiniteReturnRing (K := K) (L := L) v w₀ w
          (infinitePlaceStabilizer v w h y)) =
        fun y : w.1.1.Completion =>
          numberInfiniteTransport (K := K) sigma w₀.1
            (RingEquiv.cast
              (R := fun q : InfinitePlace L => q.1.Completion)
              hsource.symm y) :=
    (dense_range_embedding w.1.1).equalizer
      ((infinite_return_continuous v w₀ w).comp
        (infinite_stabilizer_continuous v w h))
      ((number_transport_continuous sigma w₀.1).comp
        (infinite_place_continuous hsource.symm))
      (funext fun x => by
        change infiniteReturnRing (K := K) (L := L) v w₀ w
            (infinitePlaceStabilizer v w h
              (completionEmbedding w.1.1 x)) =
          numberInfiniteTransport (K := K) sigma w₀.1
            (RingEquiv.cast hsource.symm (completionEmbedding w.1.1 x))
        rw [infinite_stabilizer_embedding,
          infinite_return_embedding,
          infinite_place_embedding,
          number_transport_embedding]
        rfl)
  exact congrFun hfun z

private noncomputable def globalTransportTerm
    (v : InfinitePlace K)
    (w₀ : InfinitePlacesAbove (K := K) (L := L) v)
    (x : (InfiniteAdeleRing L)ˣ)
    (sigma : Gal(L/K)) : w₀.1.1.Completion :=
  numberInfiniteTransport (K := K) sigma w₀.1
    ((x : InfiniteAdeleRing L) (sigma⁻¹ • w₀.1))

set_option maxHeartbeats 500000 in
-- Replace the casted source coordinate by dependent function evaluation.
set_option maxRecDepth 100000 in
omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
private theorem infinite_returned_stabilizer
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v)
    (h : InfinitePlaceStabilizer (K := K) (L := L) v w)
    (x : (InfiniteAdeleRing L)ˣ) :
    letI := placesAboveAction (K := K) (L := L) v
    infiniteReturnRing (K := K) (L := L) v w₀ w
        (infinitePlaceStabilizer v w h
          ((x : InfiniteAdeleRing L) w.1)) =
      globalTransportTerm (K := K) (L := L) v w₀ x
        (infinitePlaceReturn (K := K) (L := L) v w₀ w * h.1) := by
  letI := placesAboveAction (K := K) (L := L) v
  let r := infinitePlaceReturn (K := K) (L := L) v w₀ w
  let sigma := r * h.1
  let hsource : sigma⁻¹ • w₀.1 = w.1 := by
    have hr : r⁻¹ • w₀ = w := by
      calc
        r⁻¹ • w₀ = r⁻¹ • (r • w) := by
          rw [infinite_return_smul v w₀ w]
        _ = w := inv_smul_smul r w
    apply smul_val_fiber v sigma⁻¹ w₀ w
    calc
      sigma⁻¹ • w₀ = h.1⁻¹ • (r⁻¹ • w₀) := by
        rw [mul_inv_rev, mul_smul]
      _ = h.1⁻¹ • w := congrArg (fun q => h.1⁻¹ • q) hr
      _ = w := (h⁻¹).2
  calc
    _ = numberInfiniteTransport (K := K) sigma w₀.1
        (RingEquiv.cast hsource.symm
          ((x : InfiniteAdeleRing L) w.1)) :=
      infinite_return_stabilizer v w₀ w h _
    _ = numberInfiniteTransport (K := K) sigma w₀.1
        ((x : InfiniteAdeleRing L) (sigma⁻¹ • w₀.1)) := by
      exact congrArg (numberInfiniteTransport (K := K) sigma w₀.1)
        (ring_cast_pi
          (fun q : InfinitePlace L => (x : InfiniteAdeleRing L) q)
          hsource.symm)
    _ = _ := rfl

/-- The completed extension at an infinite place is Galois. -/
@[reducible]
noncomputable def infiniteCompletionGalois
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let hwv := infinite_lies_comap v w.1 w.2
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    IsGalois v.1.Completion w.1.1.Completion := by
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  apply IsGalois.of_card_aut_eq_finrank
  calc
    Nat.card Gal(w.1.1.Completion/v.1.Completion) =
        Nat.card (absoluteValueDecomposition v.1 w.1.1) :=
      Nat.card_congr
        (infiniteDecompositionGroup v w.1).symm.toEquiv
    _ = Module.finrank v.1.Completion w.1.1.Completion :=
      (infiniteDegreeCompatibility K L v w).symm

set_option maxHeartbeats 1000000 in
-- The local Galois instance and the two decomposition-group actions unfold together.
set_option maxRecDepth 100000 in
/-- At one infinite completion, extending the local field norm is the
product of the chosen-place stabilizer action. -/
theorem infinite_algebra_stabilizer
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (x : w.1.1.Completion) :
    let hwv := infinite_lies_comap v w.1 w.2
    let w₀ : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    completionLies v.1 w.1.1 hwv
        (Algebra.norm v.1.Completion x) =
      ∏ sigma : CompletionPlaceStabilizer v.1 w₀,
        stabilizerRingHom v.1 w₀ sigma x := by
  classical
  let hwv := infinite_lies_comap v w.1 w.2
  let w₀ : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteCompletionGalois (K := K) (L := L) v w
  letI : Fintype Gal(w.1.1.Completion/v.1.Completion) :=
    AlgEquiv.fintype v.1.Completion w.1.1.Completion
  let stabilizerToDecomposition :
      CompletionPlaceStabilizer v.1 w₀ ≃*
        absoluteValueDecomposition v.1 w.1.1 :=
    MulEquiv.subgroupCongr
      (stabilizer_decomposition_group v.1 w₀)
  let e : CompletionPlaceStabilizer v.1 w₀ ≃*
      Gal(w.1.1.Completion/v.1.Completion) :=
    stabilizerToDecomposition.trans
      (infiniteDecompositionGroup v w.1)
  change algebraMap v.1.Completion w.1.1.Completion
      (Algebra.norm v.1.Completion x) = _
  rw [Algebra.norm_eq_prod_automorphisms]
  symm
  apply Fintype.prod_equiv e.toEquiv
  intro sigma
  exact stabilizer_decomposition_action
    (K := K) (L := L) v.1 w₀ sigma x

set_option maxHeartbeats 1000000 in
-- Reindexing local automorphisms by the actual infinite-place stabilizer
-- exposes the archimedean decomposition equivalence.
set_option maxRecDepth 100000 in
/-- Actual-infinite-place form of the local norm product. -/
theorem infinite_place_stabilizer
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (x : w.1.1.Completion) :
    letI := placesAboveAction (K := K) (L := L) v
    let hwv := infinite_lies_comap v w.1 w.2
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    completionLies v.1 w.1.1 hwv
        (Algebra.norm v.1.Completion x) =
      ∏ sigma : InfinitePlaceStabilizer (K := K) (L := L) v w,
        infinitePlaceStabilizer v w sigma x := by
  classical
  letI := placesAboveAction (K := K) (L := L) v
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteCompletionGalois (K := K) (L := L) v w
  letI : Fintype Gal(w.1.1.Completion/v.1.Completion) :=
    AlgEquiv.fintype v.1.Completion w.1.1.Completion
  let stabilizerToDecomposition :
      InfinitePlaceStabilizer (K := K) (L := L) v w ≃*
        absoluteValueDecomposition v.1 w.1.1 :=
    MulEquiv.subgroupCongr
      (infinite_stabilizer_decomposition v w)
  let e : InfinitePlaceStabilizer (K := K) (L := L) v w ≃*
      Gal(w.1.1.Completion/v.1.Completion) :=
    stabilizerToDecomposition.trans
      (infiniteDecompositionGroup v w.1)
  change algebraMap v.1.Completion w.1.1.Completion
      (Algebra.norm v.1.Completion x) = _
  rw [Algebra.norm_eq_prod_automorphisms]
  symm
  apply Fintype.prod_equiv e.toEquiv
  intro sigma
  exact infinite_stabilizer_action v w sigma x

set_option maxHeartbeats 1000000 in
-- Extend one local norm to the distinguished completion and replace all
-- returned stabilizer factors by global Galois coordinates.
set_option maxRecDepth 100000 in
private theorem infinite_global_terms
    (v : InfinitePlace K)
    (w₀ w : InfinitePlacesAbove (K := K) (L := L) v)
    (x : (InfiniteAdeleRing L)ˣ) :
    letI := placesAboveAction (K := K) (L := L) v
    let targetLies := infinite_lies_comap v w₀.1 w₀.2
    completionLies v.1 w₀.1.1 targetLies
        (((infiniteCompletionNorm (K := K) (L := L) v w
          (MulEquiv.piUnits x w.1) : v.1.Completionˣ) : v.1.Completion)) =
      ∏ h : InfinitePlaceStabilizer (K := K) (L := L) v w,
        globalTransportTerm (K := K) (L := L) v w₀ x
          (infinitePlaceReturn (K := K) (L := L) v w₀ w * h.1) := by
  classical
  letI := placesAboveAction (K := K) (L := L) v
  let sourceLies := infinite_lies_comap v w.1 w.2
  let targetLies := infinite_lies_comap v w₀.1 w₀.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨sourceLies⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 sourceLies).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  let z : w.1.1.Completion := (MulEquiv.piUnits x w.1 : w.1.1.Completionˣ)
  calc
    _ = infiniteReturnRing (K := K) (L := L) v w₀ w
        (completionLies v.1 w.1.1 sourceLies
          (Algebra.norm v.1.Completion z)) := by
      symm
      exact infinite_return_extension v w₀ w
        (Algebra.norm v.1.Completion z)
    _ = infiniteReturnRing (K := K) (L := L) v w₀ w
        (∏ h : InfinitePlaceStabilizer (K := K) (L := L) v w,
          infinitePlaceStabilizer v w h z) := by
      exact congrArg (infiniteReturnRing
        (K := K) (L := L) v w₀ w)
          (infinite_place_stabilizer
            (K := K) (L := L) v w z)
    _ = ∏ h : InfinitePlaceStabilizer (K := K) (L := L) v w,
        infiniteReturnRing (K := K) (L := L) v w₀ w
          (infinitePlaceStabilizer v w h z) :=
      map_prod (infiniteReturnRing
        (K := K) (L := L) v w₀ w).toMonoidHom _ Finset.univ
    _ = _ := by
      apply Finset.prod_congr rfl
      intro h _
      exact infinite_returned_stabilizer
        (K := K) (L := L) v w₀ w h x

set_option maxHeartbeats 1000000 in
-- Multiply the local formulas and reindex the place/stabilizer pairs by the
-- global Galois group.
set_option maxRecDepth 100000 in
private theorem infinite_norms_terms
    (v : InfinitePlace K)
    (w₀ : InfinitePlacesAbove (K := K) (L := L) v)
    (x : (InfiniteAdeleRing L)ˣ) :
    letI := placesAboveAction (K := K) (L := L) v
    let targetLies := infinite_lies_comap v w₀.1 w₀.2
    (∏ w : InfinitePlacesAbove (K := K) (L := L) v,
        completionLies v.1 w₀.1.1 targetLies
          (((infiniteCompletionNorm (K := K) (L := L) v w
            (MulEquiv.piUnits x w.1) : v.1.Completionˣ) : v.1.Completion))) =
      ∏ sigma : Gal(L/K),
        globalTransportTerm (K := K) (L := L) v w₀ x sigma := by
  classical
  letI := placesAboveAction (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (InfinitePlacesAbove (K := K) (L := L) v) :=
    infinite_above_pretransitive v
  let targetLies := infinite_lies_comap v w₀.1 w₀.2
  let orbitEquiv := infinitePlacePoint
    (K := K) (L := L) v w₀
  calc
    _ = ∏ w : InfinitePlacesAbove (K := K) (L := L) v,
        ∏ h : InfinitePlaceStabilizer (K := K) (L := L) v w,
          globalTransportTerm (K := K) (L := L) v w₀ x
            (infinitePlaceReturn (K := K) (L := L) v w₀ w * h.1) := by
      apply Finset.prod_congr rfl
      intro w _
      exact infinite_global_terms
        (K := K) (L := L) v w₀ w x
    _ = ∏ p : InfinitePointStabilizers (K := K) (L := L) v,
        globalTransportTerm (K := K) (L := L) v w₀ x
          (orbitEquiv p) := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro w _
      apply Finset.prod_congr rfl
      intro h _
      rfl
    _ = ∏ sigma : Gal(L/K),
        globalTransportTerm (K := K) (L := L) v w₀ x sigma :=
      Fintype.prod_equiv orbitEquiv _ _ (fun _ => rfl)

set_option maxHeartbeats 1000000 in
-- Pass from the ring-valued coordinate calculation to units.
set_option maxRecDepth 100000 in
/-- Infinite-coordinate norm compatibility at a chosen place above `v`. -/
theorem infinite_idele_norm
    (v : InfinitePlace K)
    (w₀ : InfinitePlacesAbove (K := K) (L := L) v)
    (x : (InfiniteAdeleRing L)ˣ) :
    let targetLies := infinite_lies_comap v w₀.1 w₀.2
    Units.map (completionLies v.1 w₀.1.1 targetLies).toMonoidHom
        (infiniteNorm (K := K) (L := L) v x) =
      ∏ sigma : Gal(L/K),
        Units.map
          (numberInfiniteTransport (K := K) sigma w₀.1).toMonoidHom
          (MulEquiv.piUnits x (sigma⁻¹ • w₀.1)) := by
  classical
  letI := placesAboveAction (K := K) (L := L) v
  let targetLies := infinite_lies_comap v w₀.1 w₀.2
  apply Units.ext
  rw [Units.coe_prod]
  change completionLies v.1 w₀.1.1 targetLies
      (((infiniteNorm (K := K) (L := L) v x : v.1.Completionˣ) :
        v.1.Completion)) = _
  rw [infinite_norm]
  rw [Units.coe_prod]
  rw [_root_.map_prod]
  simpa only [Units.coe_map] using
    (infinite_norms_terms
      (K := K) (L := L) v w₀ x)

set_option maxHeartbeats 1000000 in
-- Extensionality of units and of the archimedean completion family reduces
-- the global statement to the chosen-coordinate theorem above.
set_option maxRecDepth 100000 in
/-- Norm compatibility on the infinite idèle component. -/
theorem infinite_extension_norm
    (x : (InfiniteAdeleRing L)ˣ) :
    letI := infiniteIdelesAction (K := K) (L := L)
    infiniteMonoidHom (K := K) (L := L)
        (infiniteIdeleNorm (K := K) (L := L) x) =
      ∏ sigma : Gal(L/K), sigma • x := by
  classical
  letI := infiniteIdelesAction (K := K) (L := L)
  apply Units.ext
  funext q
  let v := q.comap (algebraMap K L)
  let w₀ : InfinitePlacesAbove (K := K) (L := L) v := ⟨q, rfl⟩
  rw [Units.coe_prod]
  change (infiniteAdeleHom (K := K) (L := L)
      (infiniteIdeleNorm (K := K) (L := L) x : InfiniteAdeleRing K)) q =
    (∏ sigma : Gal(L/K), (sigma • x : (InfiniteAdeleRing L)ˣ) :
      InfiniteAdeleRing L) q
  rw [show (∏ sigma : Gal(L/K),
        (sigma • x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) q =
      ∏ sigma : Gal(L/K),
        ((sigma • x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) q by
    exact Finset.prod_apply q Finset.univ
      (fun sigma : Gal(L/K) =>
        ((sigma • x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L))]
  change completionLies v.1 q.1
      (infinite_lies_comap v q rfl)
      (MulEquiv.piUnits (infiniteIdeleNorm (K := K) (L := L) x) v) =
    ∏ sigma : Gal(L/K),
      numberInfiniteTransport (K := K) sigma q
        (MulEquiv.piUnits x (sigma⁻¹ • q))
  rw [infinite_idele]
  have h := congrArg Units.val
    (infinite_idele_norm
      (K := K) (L := L) v w₀ x)
  simpa only [Units.coe_map, Units.coe_prod] using h

set_option maxHeartbeats 1000000 in
-- The full idèle identity is the product of its infinite and finite
-- component identities.
set_option maxRecDepth 100000 in
/-- Norm compatibility for the canonical extension map on full idèles. -/
theorem idele_extension
    (x : IdeleGroup (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := infiniteIdelesAction (K := K) (L := L)
    letI := finiteIdelesAction (K := K) (L := L)
    letI := idelesGaloisAction (K := K) (L := L)
    ideleExtensionMonoid (K := K) (L := L)
        (ideleNorm (K := K) (L := L) x) =
      ∏ sigma : Gal(L/K), sigma • x := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  letI := idelesGaloisAction (K := K) (L := L)
  apply Prod.ext
  · change infiniteMonoidHom (K := K) (L := L)
        (infiniteIdeleNorm (K := K) (L := L) x.1) =
      (∏ sigma : Gal(L/K), sigma • x).1
    rw [show (∏ sigma : Gal(L/K), sigma • x).1 =
        ∏ sigma : Gal(L/K), (sigma • x).1 by
      exact map_prod (MonoidHom.fst
        (InfiniteAdeleRing L)ˣ
        (FiniteIdeles (NumberField.RingOfIntegers L) L))
          (fun sigma : Gal(L/K) => sigma • x) Finset.univ]
    exact infinite_extension_norm
      (K := K) (L := L) x.1
  · change ideleMonoidHom (K := K) (L := L)
        (finiteIdeleNorm (K := K) (L := L) x.2) =
      (∏ sigma : Gal(L/K), sigma • x).2
    rw [show (∏ sigma : Gal(L/K), sigma • x).2 =
        ∏ sigma : Gal(L/K), (sigma • x).2 by
      exact map_prod (MonoidHom.snd
        (InfiniteAdeleRing L)ˣ
        (FiniteIdeles (NumberField.RingOfIntegers L) L))
          (fun sigma : Gal(L/K) => sigma • x) Finset.univ]
    exact idele_extension_norm
      (K := K) (L := L) x.2

/-- The canonical coordinatewise extension data satisfies the exact norm
compatibility property used in Corollary VII.4.4. -/
theorem canonical_idele_compatible :
    (canonicalExtensionData (K := K) (L := L)).NormCompatible := by
  intro x
  change ideleExtensionMonoid (K := K) (L := L)
      (ideleNorm (K := K) (L := L) x) = _
  exact idele_extension (K := K) (L := L) x


end

end Submission.CField.NIndex
