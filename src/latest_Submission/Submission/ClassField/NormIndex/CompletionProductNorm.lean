import Submission.NumberTheory.Galois.PlaceCompletionDegree
import Submission.ClassField.IdeleCohomology.CompletionInducedModule
import Submission.ClassField.NormIndex.CompletionOrbitEquiv

/-!
# Norms on products of completed places

This file develops the local arithmetic identity needed for the canonical
idèle-extension map:

`ext (Nm x) = ∏ σ, σ • x`.

The first step identifies the action of the stabilizer of a chosen place,
as constructed in Chapter VII, with the local Galois action on its
completion.  Subsequent declarations reindex the global Galois product by
the places above the base place and their stabilizer.
-/

namespace Submission.CField.NIndex

open AbsoluteValue
open Submission.NumberTheory.Milne
open Submission.CField.ICohomo
open scoped BigOperators

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)

local instance completionPlacesAboveFintype
    (v : AbsoluteValue K ℝ)
    [Finite (CompletionPlacesAbove (L := L) v)] :
    Fintype (CompletionPlacesAbove (L := L) v) :=
  Fintype.ofFinite (CompletionPlacesAbove (L := L) v)

local instance completionPlaceStabilizerFintype
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :
    Fintype (CompletionPlaceStabilizer v w) :=
  Fintype.ofFinite (CompletionPlaceStabilizer v w)

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- The stabilizer of a place in the fiber above `v` is the usual
absolute-value decomposition group of its underlying place. -/
theorem stabilizer_decomposition_group
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :
    CompletionPlaceStabilizer v w =
      absoluteValueDecomposition v w.1 := by
  rw [absolute_decomposition_stabilizer]
  ext sigma
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- The two continuous actions of the decomposition group on the chosen
completion agree: the Chapter VII stabilizer action and the local Galois
action. -/
theorem stabilizer_decomposition_action
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w)
    (x : w.1.Completion) :
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    let d : absoluteValueDecomposition v w.1 :=
      MulEquiv.subgroupCongr
        (stabilizer_decomposition_group v w) sigma
    stabilizerRingHom v w sigma x =
      decompositionCompletionEquiv v w.1 d x := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  dsimp only
  let d : absoluteValueDecomposition v w.1 :=
    MulEquiv.subgroupCongr
      (stabilizer_decomposition_group v w) sigma
  have hfun :
      (fun y : w.1.Completion ↦
        stabilizerRingHom v w sigma y) =
      fun y ↦ decompositionCompletionEquiv v w.1 d y :=
    (dense_range_embedding w.1).equalizer
      (place_stabilizer_isometry v w sigma).continuous
      (decomposition_alg_continuous v w.1 d)
      (funext fun y ↦ by
        change stabilizerRingHom v w sigma
            (completionEmbedding w.1 y) =
          decompositionCompletionEquiv v w.1 d
            (completionEmbedding w.1 y)
        rw [place_stabilizer_embedding,
          decomposition_alg_embedding]
        rfl)
  exact congrFun hfun x

omit [NumberField L] in
/-- The local norm in one completion is the product of the Chapter VII
stabilizer action. -/
theorem completion_algebra_stabilizer
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    [Finite (CompletionPlacesAbove (L := L) v)]
    [Nonempty (CompletionPlacesAbove (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v)
    (x : w.1.Completion) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    completionLies v w.1 w.2
        (Algebra.norm v.Completion x) =
      ∏ sigma : CompletionPlaceStabilizer v w,
        stabilizerRingHom v w sigma x := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  letI : Fintype Gal(w.1.Completion/v.Completion) :=
    AlgEquiv.fintype v.Completion w.1.Completion
  let stabilizerToDecomposition :
      CompletionPlaceStabilizer v w ≃*
        absoluteValueDecomposition v w.1 :=
    MulEquiv.subgroupCongr
      (stabilizer_decomposition_group v w)
  let e : CompletionPlaceStabilizer v w ≃*
      Gal(w.1.Completion/v.Completion) :=
    stabilizerToDecomposition.trans
      (decompositionCompletionExtension v w.1)
  change algebraMap v.Completion w.1.Completion
      (Algebra.norm v.Completion x) = _
  rw [Algebra.norm_eq_prod_automorphisms]
  symm
  apply Fintype.prod_equiv e.toEquiv
  intro sigma
  exact stabilizer_decomposition_action
    (K := K) (L := L) v w sigma x

set_option maxHeartbeats 2000000 in
-- Reindexing the nested place/stabilizer products needs a larger reduction budget.
omit [NumberField L] in
/-- At a chosen coordinate, extending the product of all local completion
norms equals the product of all global Galois conjugates of the completion
family. -/
theorem completion_algebra_action
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    [Finite (CompletionPlacesAbove (L := L) v)]
    [Nonempty (CompletionPlacesAbove (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w0 : CompletionPlacesAbove (L := L) v)
    (alpha : ∀ w : CompletionPlacesAbove (L := L) v,
      w.1.Completion) :
    letI (w : CompletionPlacesAbove (L := L) v) :
        Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI (w : CompletionPlacesAbove (L := L) v) :
        FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    completionLies v w0.1 w0.2
        (∏ w, Algebra.norm v.Completion (alpha w)) =
      ∏ sigma : Gal(L/K), completionProductAction v sigma alpha w0 := by
  classical
  let W := CompletionPlacesAbove (L := L) v
  letI : Fintype W := Fintype.ofFinite W
  letI (w : W) : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI (w : W) : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  let orbitEquiv := completionPlaceStabilizer
    (K := K) (L := L) v w0
  have hreturnNorm (w : W) :
      let r := completionPlaceReturn v w0 w
      Algebra.norm v.Completion
          (completionProductAction v r alpha w0) =
        Algebra.norm v.Completion (alpha w) := by
    dsimp only
    let r := completionPlaceReturn v w0 w
    let normFamily (z : W) : v.Completion :=
      Algebra.norm v.Completion (alpha z)
    have hr : r⁻¹ • w0 = w := by
      calc
        r⁻¹ • w0 = r⁻¹ • (r • w) := by
          rw [place_return_smul v w0 w]
        _ = w := inv_smul_smul r w
    calc
      Algebra.norm v.Completion
          (completionProductAction v r alpha w0) =
          normFamily (r⁻¹ • w0) :=
        Algebra.norm_eq_of_algEquiv
          (completionTransportAlg v r w0)
            (alpha (r⁻¹ • w0))
      _ = normFamily w := congrArg normFamily hr
  calc
    completionLies v w0.1 w0.2
        (∏ w, Algebra.norm v.Completion (alpha w)) =
        ∏ w : W, completionLies v w0.1 w0.2
          (Algebra.norm v.Completion (alpha w)) := by
      rw [_root_.map_prod]
    _ = ∏ w : W, ∏ h : CompletionPlaceStabilizer v w0,
          completionProductAction v
            (completionPlaceStabilizer v w0 ⟨w, h⟩)
              alpha w0 := by
      apply Finset.prod_congr rfl
      intro w _
      let r := completionPlaceReturn v w0 w
      calc
        completionLies v w0.1 w0.2
            (Algebra.norm v.Completion (alpha w)) =
            completionLies v w0.1 w0.2
              (Algebra.norm v.Completion
                (completionProductAction v r alpha w0)) := by
          rw [hreturnNorm w]
        _ = ∏ h : CompletionPlaceStabilizer v w0,
              stabilizerRingHom v w0 h
                (completionProductAction v r alpha w0) :=
          completion_algebra_stabilizer
            (K := K) (L := L) v w0
              (completionProductAction v r alpha w0)
        _ = ∏ h : CompletionPlaceStabilizer v w0,
              completionProductAction v
                (completionPlaceStabilizer v w0 ⟨w, h⟩)
                  alpha w0 := by
          apply Finset.prod_congr rfl
          intro h _
          rw [completion_place_stabilizer]
          rw [completion_action_mul]
          exact (action_stabilizer_coordinate
            v w0 h (completionProductAction v r alpha)).symm
    _ = ∏ p : Σ w : W, CompletionPlaceStabilizer v w0,
          completionProductAction v
            (completionPlaceStabilizer v w0 p) alpha w0 := by
      rw [Fintype.prod_sigma]
    _ = ∏ sigma : Gal(L/K),
          completionProductAction v sigma alpha w0 := by
      exact Fintype.prod_equiv orbitEquiv _ _ (fun _ ↦ rfl)

end

end Submission.CField.NIndex
