import Towers.ClassField.BrauerLocalization.InfiniteNaturality
import Towers.FieldTheory.CentralEmbeddingBrauer

/-!
# Infinite chosen-completion crossed-product compatibility

This file develops the archimedean decomposition-field infrastructure needed
to compare scalar extension of a global crossed product with the crossed
product over a chosen infinite completion.
-/

namespace Towers.CField.BLoc

open CategoryTheory Representation groupCohomology
open IsDedekindDomain
open NumberField
open Towers.NumberTheory.Milne
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.GWang
open Towers.CField.HNorm
open Towers.TBluepr
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Units.mulDistribMulActionRight

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The decomposition group of a chosen infinite place. -/
abbrev infiniteCompletionDecomposition
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    Subgroup Gal(L/K) :=
  absoluteValueDecomposition v.1 w.1.1

/-- The fixed field of the decomposition group of a chosen infinite place. -/
abbrev infiniteDecompositionField
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    IntermediateField K L :=
  FixedPoints.intermediateField
    (infiniteCompletionDecomposition v w)

/-- Restrict the chosen upper infinite place to its decomposition field. -/
noncomputable def infiniteDecompositionPlace
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    InfinitePlace (infiniteDecompositionField v w) :=
  w.1.comap
    (algebraMap (infiniteDecompositionField v w) L)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The distinguished decomposition-field place lies above the base infinite
place. -/
theorem infinite_decomposition_comap
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    (infiniteDecompositionPlace v w).comap
        (algebraMap K (infiniteDecompositionField v w)) = v := by
  unfold infiniteDecompositionPlace
  rw [← InfinitePlace.comap_comp]
  simpa only [IsScalarTower.algebraMap_eq] using w.2

set_option synthInstance.maxHeartbeats 1000000 in
-- Two global/local degree formulas and the completion tower elaborate together.
set_option maxHeartbeats 6000000 in
/-- The completion of the distinguished infinite place of the decomposition
field has degree one over the original base completion. -/
theorem infinite_decomposition_restricted
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let u := infiniteDecompositionPlace v w
    let huv := infinite_decomposition_comap v w
    let huva := infinite_lies_comap v u huv
    letI : Fact (AbsoluteValue.LiesOver u.1 v.1) := ⟨huva⟩
    letI : Algebra v.1.Completion u.1.Completion :=
      (completionLies v.1 u.1 huva).toAlgebra
    Module.finrank v.1.Completion u.1.Completion = 1 := by
  let H := infiniteCompletionDecomposition v w
  let D := infiniteDecompositionField v w
  let u := infiniteDecompositionPlace v w
  let huv := infinite_decomposition_comap v w
  let huva := infinite_lies_comap v u huv
  let hwu : w.1.comap (algebraMap D L) = u := rfl
  let hwua := infinite_lies_comap u w.1 hwu
  let hwva := infinite_lies_comap v w.1 w.2
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  let uAbove : InfinitePlacesAbove (K := K) (L := D) v := ⟨u, huv⟩
  let wAbove : InfinitePlacesAbove (K := D) (L := L) u := ⟨w.1, hwu⟩
  letI : Fact (AbsoluteValue.LiesOver u.1 v.1) := ⟨huva⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 u.1) := ⟨hwua⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwva⟩
  letI : Algebra v.1.Completion u.1.Completion :=
    (completionLies v.1 u.1 huva).toAlgebra
  letI : Algebra u.1.Completion w.1.1.Completion :=
    (completionLies u.1 w.1.1 hwua).toAlgebra
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra
  have hKL := infiniteDegreeCompatibility K L v w
  have hKL' : Module.finrank v.1.Completion w.1.1.Completion =
      Nat.card H := hKL
  have hDecTop : absoluteValueDecomposition u.1 w.1.1 = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro tau x
    let e : H ≃* Gal(L/D) := IsGaloisGroup.mulEquivAlgEquiv H D L
    let h : H := e.symm tau
    have hh : (h.1 : Gal(L/K)) ∈
        absoluteValueDecomposition v.1 w.1.1 := h.2
    change w.1.1 (tau x) = w.1.1 x
    rw [← e.apply_symm_apply tau]
    simpa [e] using hh x
  have hDL := infiniteDegreeCompatibility D L u wAbove
  have hDL' : Module.finrank u.1.Completion w.1.1.Completion =
      Nat.card H := by
    calc
      Module.finrank u.1.Completion w.1.1.Completion =
          Nat.card (absoluteValueDecomposition u.1 w.1.1) := hDL
      _ = Nat.card Gal(L/D) := by
        rw [hDecTop]
        simpa only [D] using
          (show Nat.card (⊤ : Subgroup Gal(L/D)) = Nat.card Gal(L/D) by simp)
      _ = Nat.card H :=
        (Nat.card_congr
          (IsGaloisGroup.mulEquivAlgEquiv H D L).toEquiv).symm
  letI : IsScalarTower v.1.Completion u.1.Completion
      w.1.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    simpa using
      (completion_lies_trans v.1 u.1 w.1.1 huva hwua hwva).symm
  letI : Module.Finite v.1.Completion u.1.Completion :=
    infinite_completion_module (K := K) (L := D) v uAbove
  letI : Module.Finite u.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := D) (L := L) u wAbove
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : FiniteDimensional v.1.Completion u.1.Completion :=
    FiniteDimensional.left v.1.Completion u.1.Completion w.1.1.Completion
  have htower := Module.finrank_mul_finrank
    v.1.Completion u.1.Completion w.1.1.Completion
  rw [hDL', hKL'] at htower
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
  simpa using htower

set_option synthInstance.maxHeartbeats 1000000 in
-- The degree-one completion map and its finite-dimensional instances elaborate together.
set_option maxHeartbeats 4000000 in
/-- The completion of the distinguished decomposition-field place is
canonically equivalent to the original base completion. -/
noncomputable def infiniteDecompositionEquiv
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let u := infiniteDecompositionPlace v w
    let huv := infinite_decomposition_comap v w
    let huva := infinite_lies_comap v u huv
    letI : Fact (AbsoluteValue.LiesOver u.1 v.1) := ⟨huva⟩
    letI : Algebra v.1.Completion u.1.Completion :=
      (completionLies v.1 u.1 huva).toAlgebra
    v.1.Completion ≃ₐ[v.1.Completion] u.1.Completion := by
  let D := infiniteDecompositionField v w
  let u := infiniteDecompositionPlace v w
  let huv := infinite_decomposition_comap v w
  let huva := infinite_lies_comap v u huv
  let uAbove : InfinitePlacesAbove (K := K) (L := D) v := ⟨u, huv⟩
  letI : NumberField D := NumberField.of_module_finite K D
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Fact u.1.IsNontrivial := ⟨infinite_place_nontrivial u⟩
  letI : NontriviallyNormedField v.1.Completion :=
    absoluteNontriviallyNormed v.1
  letI : NontriviallyNormedField u.1.Completion :=
    absoluteNontriviallyNormed u.1
  letI : Fact (AbsoluteValue.LiesOver u.1 v.1) := ⟨huva⟩
  letI : Algebra v.1.Completion u.1.Completion :=
    (completionLies v.1 u.1 huva).toAlgebra
  letI : Module.Finite v.1.Completion u.1.Completion :=
    infinite_completion_module (K := K) (L := D) v uAbove
  have hdegree : Module.finrank v.1.Completion u.1.Completion = 1 :=
    infinite_decomposition_restricted v w
  have hsurj : Function.Surjective
      (algebraMap v.1.Completion u.1.Completion) := by
    change Function.Surjective
      (Algebra.linearMap v.1.Completion u.1.Completion)
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [hdegree] :
        Module.finrank v.1.Completion v.1.Completion =
          Module.finrank v.1.Completion u.1.Completion)).1
    exact (algebraMap v.1.Completion u.1.Completion).injective
  exact AlgEquiv.ofBijective
    (Algebra.ofId v.1.Completion u.1.Completion)
    ⟨(algebraMap v.1.Completion u.1.Completion).injective, hsurj⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- Both global and completed algebra structures occur in the embedding.
set_option maxHeartbeats 4000000 in
/-- The infinite decomposition field embeds into the original base
completion through its degree-one distinguished completion. -/
noncomputable def infiniteDecompositionEmbedding
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let D := infiniteDecompositionField v w
    letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
    D →ₐ[K] v.1.Completion := by
  let D := infiniteDecompositionField v w
  let u := infiniteDecompositionPlace v w
  let huv := infinite_decomposition_comap v w
  let huva := infinite_lies_comap v u huv
  letI : NumberField D := NumberField.of_module_finite K D
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Fact u.1.IsNontrivial := ⟨infinite_place_nontrivial u⟩
  letI : NontriviallyNormedField v.1.Completion :=
    absoluteNontriviallyNormed v.1
  letI : NontriviallyNormedField u.1.Completion :=
    absoluteNontriviallyNormed u.1
  letI : Fact (AbsoluteValue.LiesOver u.1 v.1) := ⟨huva⟩
  letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
  letI : SMul K v.1.Completion := completionBaseSMul v.1
  letI : Module K v.1.Completion := completionBaseModule v.1
  letI : Algebra D u.1.Completion := completionBaseAlgebra u.1
  letI : SMul D u.1.Completion := completionBaseSMul u.1
  letI : Module D u.1.Completion := completionBaseModule u.1
  letI : Algebra v.1.Completion u.1.Completion :=
    (completionLies v.1 u.1 huva).toAlgebra
  let e : v.1.Completion ≃ₐ[v.1.Completion] u.1.Completion :=
    infiniteDecompositionEquiv v w
  refine
    { toRingHom := e.symm.toRingEquiv.toRingHom.comp (completionEmbedding u.1)
      commutes' := ?_ }
  intro x
  change e.symm (completionEmbedding u.1 (algebraMap K D x)) =
    completionEmbedding v.1 x
  have hcomp := RingHom.congr_fun
    (completion_lies_comp v.1 u.1 huva) x
  change completionLies v.1 u.1 huva
      (completionEmbedding v.1 x) =
    completionEmbedding u.1 (algebraMap K D x) at hcomp
  rw [← hcomp]
  change e.symm (e (completionEmbedding v.1 x)) = completionEmbedding v.1 x
  exact e.symm_apply_apply _

set_option synthInstance.maxHeartbeats 1000000 in
-- The completion equivalence is relabelled over the decomposition field.
set_option maxHeartbeats 4000000 in
/-- The degree-one completion equivalence, regarded as an equivalence over
the infinite decomposition field. -/
noncomputable def infiniteDecompositionAlg
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let D := infiniteDecompositionField v w
    let u := infiniteDecompositionPlace v w
    letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
    letI : Algebra D v.1.Completion :=
      (infiniteDecompositionEmbedding v w).toAlgebra
    letI : Algebra D u.1.Completion := completionBaseAlgebra u.1
    v.1.Completion ≃ₐ[D] u.1.Completion := by
  let D := infiniteDecompositionField v w
  let u := infiniteDecompositionPlace v w
  let huv := infinite_decomposition_comap v w
  let huva := infinite_lies_comap v u huv
  letI : NumberField D := NumberField.of_module_finite K D
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Fact u.1.IsNontrivial := ⟨infinite_place_nontrivial u⟩
  letI : NontriviallyNormedField v.1.Completion :=
    absoluteNontriviallyNormed v.1
  letI : NontriviallyNormedField u.1.Completion :=
    absoluteNontriviallyNormed u.1
  letI : Fact (AbsoluteValue.LiesOver u.1 v.1) := ⟨huva⟩
  letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
  letI : Algebra D v.1.Completion :=
    (infiniteDecompositionEmbedding v w).toAlgebra
  letI : Algebra D u.1.Completion := completionBaseAlgebra u.1
  letI : Algebra v.1.Completion u.1.Completion :=
    (completionLies v.1 u.1 huva).toAlgebra
  let e : v.1.Completion ≃ₐ[v.1.Completion] u.1.Completion :=
    infiniteDecompositionEquiv v w
  exact
    { toRingEquiv := e.toRingEquiv
      commutes' := fun x => by
        change e (e.symm (completionEmbedding u.1 x)) =
          completionEmbedding u.1 x
        exact e.apply_symm_apply _ }

set_option synthInstance.maxHeartbeats 1000000 in
-- The three completion maps and their scalar towers unfold together.
set_option maxHeartbeats 5000000 in
/-- The decomposition-field embedding is compatible with the chosen upper
infinite completion. -/
theorem infinite_completion_embedding
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let D := infiniteDecompositionField v w
    let hwva := infinite_lies_comap v w.1 w.2
    ∀ x : D,
      completionLies v.1 w.1.1 hwva
          (infiniteDecompositionEmbedding v w x) =
        completionEmbedding w.1.1 (algebraMap D L x) := by
  dsimp only
  let D := infiniteDecompositionField v w
  let u := infiniteDecompositionPlace v w
  let huv := infinite_decomposition_comap v w
  let huva := infinite_lies_comap v u huv
  let hwu : w.1.comap (algebraMap D L) = u := rfl
  let hwua := infinite_lies_comap u w.1 hwu
  let hwva := infinite_lies_comap v w.1 w.2
  letI : NumberField D := NumberField.of_module_finite K D
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Fact u.1.IsNontrivial := ⟨infinite_place_nontrivial u⟩
  letI : NontriviallyNormedField v.1.Completion :=
    absoluteNontriviallyNormed v.1
  letI : NontriviallyNormedField u.1.Completion :=
    absoluteNontriviallyNormed u.1
  letI : Fact (AbsoluteValue.LiesOver u.1 v.1) := ⟨huva⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 u.1) := ⟨hwua⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwva⟩
  letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
  letI : Algebra D u.1.Completion := completionBaseAlgebra u.1
  letI : Algebra v.1.Completion u.1.Completion :=
    (completionLies v.1 u.1 huva).toAlgebra
  let e : v.1.Completion ≃ₐ[v.1.Completion] u.1.Completion :=
    infiniteDecompositionEquiv v w
  intro x
  change completionLies v.1 w.1.1 hwva
      (e.symm (completionEmbedding u.1 x)) =
    completionEmbedding w.1.1 (algebraMap D L x)
  calc
    completionLies v.1 w.1.1 hwva
          (e.symm (completionEmbedding u.1 x)) =
        completionLies u.1 w.1.1 hwua
          (completionLies v.1 u.1 huva
            (e.symm (completionEmbedding u.1 x))) :=
      (RingHom.congr_fun
        (completion_lies_trans v.1 u.1 w.1.1 huva hwua hwva)
        (e.symm (completionEmbedding u.1 x))).symm
    _ = completionLies u.1 w.1.1 hwua
          (e (e.symm (completionEmbedding u.1 x))) := rfl
    _ = completionLies u.1 w.1.1 hwua
          (completionEmbedding u.1 x) := by rw [e.apply_symm_apply]
    _ = completionEmbedding w.1.1 (algebraMap D L x) :=
      RingHom.congr_fun (completion_lies_comp u.1 w.1.1 hwua) x

set_option synthInstance.maxHeartbeats 1000000 in
-- The tensor lift exposes all three algebra structures in the completion tower.
set_option maxHeartbeats 3000000 in
/-- Scalar extension from the infinite decomposition field to the original
base completion maps into the chosen upper completion. -/
noncomputable def infiniteDecompositionCompletion
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let D := infiniteDecompositionField v w
    let F := v.1.Completion
    let E := w.1.1.Completion
    let hwva := infinite_lies_comap v w.1 w.2
    letI : Algebra K F := completionBaseAlgebra v.1
    letI : Algebra D F :=
      (infiniteDecompositionEmbedding v w).toAlgebra
    letI : Algebra F E :=
      (completionLies v.1 w.1.1 hwva).toAlgebra
    (L ⊗[D] F) →ₐ[F] E := by
  let D := infiniteDecompositionField v w
  let hwva := infinite_lies_comap v w.1 w.2
  letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
  letI : Algebra D v.1.Completion :=
    (infiniteDecompositionEmbedding v w).toAlgebra
  letI : SMul D v.1.Completion :=
    (infiniteDecompositionEmbedding v w).toAlgebra.toSMul
  letI : Module D v.1.Completion := Algebra.toModule
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra
  letI : SMul v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra.toSMul
  letI : Module v.1.Completion w.1.1.Completion := Algebra.toModule
  letI : Algebra D w.1.1.Completion :=
    ((completionEmbedding w.1.1).comp (algebraMap D L)).toAlgebra
  letI : SMul D w.1.1.Completion :=
    (((completionEmbedding w.1.1).comp
      (algebraMap D L)).toAlgebra).toSMul
  letI : Module D w.1.1.Completion := Algebra.toModule
  letI : IsScalarTower D v.1.Completion w.1.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    exact (infinite_completion_embedding
      v w x).symm
  let j : L →ₐ[D] w.1.1.Completion :=
    { toRingHom := completionEmbedding w.1.1
      commutes' := fun _ => rfl }
  exact (j.liftEquiv D v.1.Completion L w.1.1.Completion).comp
    (Algebra.TensorProduct.commRight D v.1.Completion L).symm.toAlgHom

set_option synthInstance.maxHeartbeats 1000000 in
-- Unfolding the tensor lift and completion scalar action is expensive.
set_option maxHeartbeats 1500000 in
@[simp]
theorem infinite_decomposition_tmul
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (a : L) (b : v.1.Completion) :
    let D := infiniteDecompositionField v w
    let hwva := infinite_lies_comap v w.1 w.2
    letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
    letI : Algebra D v.1.Completion :=
      (infiniteDecompositionEmbedding v w).toAlgebra
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwva).toAlgebra
    infiniteDecompositionCompletion v w (a ⊗ₜ[D] b) =
      completionEmbedding w.1.1 a *
        completionLies v.1 w.1.1 hwva b := by
  dsimp only
  let D := infiniteDecompositionField v w
  let hwva := infinite_lies_comap v w.1 w.2
  letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
  letI : Algebra D v.1.Completion :=
    (infiniteDecompositionEmbedding v w).toAlgebra
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra
  letI : SMul v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra.toSMul
  letI : Module v.1.Completion w.1.1.Completion := Algebra.toModule
  simp only [completionEmbedding_apply, WithAbs.equiv_symm_apply]
  change b • completionEmbedding w.1.1 a =
    completionEmbedding w.1.1 a *
      completionLies v.1 w.1.1 hwva b
  rw [Algebra.smul_def]
  exact mul_comm _ _

set_option synthInstance.maxHeartbeats 1000000 in
-- Surjectivity transports through the degree-one decomposition-field completion.
set_option maxHeartbeats 6000000 in
/-- The decomposition-field tensor map reaches the whole chosen infinite
completion. -/
theorem infinite_decomposition_surjective
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let D := infiniteDecompositionField v w
    let hwva := infinite_lies_comap v w.1 w.2
    letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
    letI : Algebra D v.1.Completion :=
      (infiniteDecompositionEmbedding v w).toAlgebra
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwva).toAlgebra
    Function.Surjective
      (infiniteDecompositionCompletion v w) := by
  dsimp only
  let H := infiniteCompletionDecomposition v w
  let D := infiniteDecompositionField v w
  let u := infiniteDecompositionPlace v w
  let huv := infinite_decomposition_comap v w
  let huva := infinite_lies_comap v u huv
  let hwu : w.1.comap (algebraMap D L) = u := rfl
  let hwua := infinite_lies_comap u w.1 hwu
  let hwva := infinite_lies_comap v w.1 w.2
  let wAbove : InfinitePlacesAbove (K := D) (L := L) u := ⟨w.1, hwu⟩
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Fact u.1.IsNontrivial := ⟨infinite_place_nontrivial u⟩
  letI : NontriviallyNormedField v.1.Completion :=
    absoluteNontriviallyNormed v.1
  letI : NontriviallyNormedField u.1.Completion :=
    absoluteNontriviallyNormed u.1
  letI : Fact (AbsoluteValue.LiesOver u.1 v.1) := ⟨huva⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 u.1) := ⟨hwua⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwva⟩
  letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
  letI : Algebra D v.1.Completion :=
    (infiniteDecompositionEmbedding v w).toAlgebra
  letI : Algebra D u.1.Completion := completionBaseAlgebra u.1
  letI : Algebra v.1.Completion u.1.Completion :=
    (completionLies v.1 u.1 huva).toAlgebra
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra
  letI : Algebra u.1.Completion w.1.1.Completion :=
    (completionLies u.1 w.1.1 hwua).toAlgebra
  let eD : v.1.Completion ≃ₐ[D] u.1.Completion :=
    infiniteDecompositionAlg v w
  let pull : (L ⊗[D] u.1.Completion) →ₗ[D]
      (L ⊗[D] v.1.Completion) :=
    TensorProduct.AlgebraTensorModule.map
      (LinearMap.id (R := D) (M := L)) eD.symm.toLinearMap
  have hmap (b : u.1.Completion) :
      completionLies v.1 w.1.1 hwva (eD.symm b) =
        completionLies u.1 w.1.1 hwua b := by
    calc
      completionLies v.1 w.1.1 hwva (eD.symm b) =
          completionLies u.1 w.1.1 hwua
            (completionLies v.1 u.1 huva (eD.symm b)) :=
        (RingHom.congr_fun
          (completion_lies_trans v.1 u.1 w.1.1 huva hwua hwva)
          (eD.symm b)).symm
      _ = completionLies u.1 w.1.1 hwua
          (eD (eD.symm b)) := rfl
      _ = completionLies u.1 w.1.1 hwua b := by
        rw [eD.apply_symm_apply]
  intro y
  obtain ⟨z, hz⟩ :=
    infinite_tensor_surjective u wAbove y
  refine ⟨pull z, ?_⟩
  rw [← hz]
  clear hz y
  induction z with
  | zero => simp [pull]
  | add x y hx hy => simp [pull, hx, hy]
  | tmul a b =>
      rw [show pull (a ⊗ₜ[D] b) = a ⊗ₜ[D] eD.symm b by
        exact TensorProduct.AlgebraTensorModule.map_tmul _ _ _ _]
      rw [infinite_decomposition_tmul,
        infinite_tensor_tmul, hmap]

set_option synthInstance.maxHeartbeats 1000000 in
-- The tensor-map bijectivity proof compares three finite dimensions.
set_option maxHeartbeats 6000000 in
/-- Scalar extension from the infinite decomposition field to the original
base completion is exactly the chosen upper completion. -/
noncomputable def infiniteDecompositionTensor
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let D := infiniteDecompositionField v w
    let F := v.1.Completion
    let E := w.1.1.Completion
    let hwva := infinite_lies_comap v w.1 w.2
    letI : Algebra K F := completionBaseAlgebra v.1
    letI : Algebra D F :=
      (infiniteDecompositionEmbedding v w).toAlgebra
    letI : Algebra F E :=
      (completionLies v.1 w.1.1 hwva).toAlgebra
    (L ⊗[D] F) ≃ₐ[F] E := by
  let H := infiniteCompletionDecomposition v w
  let D := infiniteDecompositionField v w
  let hwva := infinite_lies_comap v w.1 w.2
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwva⟩
  letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
  letI : Algebra D v.1.Completion :=
    (infiniteDecompositionEmbedding v w).toAlgebra
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra
  letI : Module.Finite v.1.Completion
      (TensorProduct D v.1.Completion L) :=
    Module.Finite.base_change D v.1.Completion L
  letI : Module.Finite v.1.Completion
      (TensorProduct D L v.1.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight D v.1.Completion L).toLinearEquiv
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  have hsource : Module.finrank v.1.Completion
      (TensorProduct D L v.1.Completion) = Module.finrank D L := by
    calc
      Module.finrank v.1.Completion (TensorProduct D L v.1.Completion) =
          Module.finrank v.1.Completion
            (TensorProduct D v.1.Completion L) :=
        (Algebra.TensorProduct.commRight D v.1.Completion L).toLinearEquiv
          |>.finrank_eq.symm
      _ = Module.finrank D L := Module.finrank_baseChange
  let eH : H ≃* Gal(L/D) := IsGaloisGroup.mulEquivAlgEquiv H D L
  have htarget : Module.finrank v.1.Completion w.1.1.Completion =
      Module.finrank D L := by
    calc
      Module.finrank v.1.Completion w.1.1.Completion = Nat.card H :=
        infiniteDegreeCompatibility K L v w
      _ = Nat.card Gal(L/D) := Nat.card_congr eH.toEquiv
      _ = Module.finrank D L := IsGalois.card_aut_eq_finrank D L
  let f := infiniteDecompositionCompletion v w
  have hsurj : Function.Surjective f :=
    infinite_decomposition_surjective v w
  have hinj : Function.Injective f := by
    change Function.Injective f.toLinearMap
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hsource.trans htarget.symm)).2 hsurj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- The fixed-field and local-completion Galois equivalences elaborate together.
set_option maxHeartbeats 4000000 in
/-- The Galois group over the infinite decomposition field is the Galois
group of the chosen completed extension. -/
noncomputable def infiniteDecompositionGalois
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let D := infiniteDecompositionField v w
    let hwva := infinite_lies_comap v w.1 w.2
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwva).toAlgebra
    Gal(L/D) ≃* Gal(w.1.1.Completion/v.1.Completion) := by
  let H := infiniteCompletionDecomposition v w
  let D := infiniteDecompositionField v w
  let hwva := infinite_lies_comap v w.1 w.2
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwva⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  let eH : H ≃* Gal(L/D) := IsGaloisGroup.mulEquivAlgEquiv H D L
  exact eH.symm.trans (infiniteDecompositionGroup v w.1)

set_option synthInstance.maxHeartbeats 1000000 in
-- The Galois equivalence unfolds through the continuous decomposition action.
set_option maxHeartbeats 4000000 in
omit [NumberField L] in
/-- The infinite decomposition-field Galois equivalence extends the
corresponding global automorphism on the embedded global field. -/
@[simp]
theorem infinite_decomposition_embedding
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (sigma : Gal(L/(infiniteDecompositionField v w)))
    (x : L) :
    let hwva := infinite_lies_comap v w.1 w.2
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwva).toAlgebra
    infiniteDecompositionGalois v w sigma
        (completionEmbedding w.1.1 x) =
      completionEmbedding w.1.1 (sigma x) := by
  let H := infiniteCompletionDecomposition v w
  let D := infiniteDecompositionField v w
  let hwva := infinite_lies_comap v w.1 w.2
  letI : NumberField L := NumberField.of_module_finite K L
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwva⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  let eH : H ≃* Gal(L/D) := IsGaloisGroup.mulEquivAlgEquiv H D L
  change decompositionCompletionEquiv v.1 w.1.1 _
      (completionEmbedding w.1.1 x) = completionEmbedding w.1.1 (sigma x)
  rw [decomposition_alg_embedding]
  have hs := eH.apply_symm_apply sigma
  have hsx := congrArg (fun tau : Gal(L/D) => tau x) hs
  exact congrArg (completionEmbedding w.1.1) hsx

set_option synthInstance.maxHeartbeats 1000000 in
-- The restricted global cocycle and completed Galois action elaborate together.
set_option maxHeartbeats 4000000 in
/-- Restrict a global cocycle to the decomposition group of an infinite
place and transport it to the corresponding extension of completions. -/
noncomputable def infiniteRestrictedCocycle
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    let hwva := infinite_lies_comap v w.1 w.2
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwva).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    NMCocycl₂
      (G := Gal(w.1.1.Completion/v.1.Completion))
      (M := w.1.1.Completionˣ) := by
  let H := infiniteCompletionDecomposition v w
  let D := infiniteDecompositionField v w
  let hwva := infinite_lies_comap v w.1 w.2
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwva⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  let cD : NMCocycl₂ (G := Gal(L/D)) (M := Lˣ) :=
    NMCocycl₂.restrict (galoisTowerInclusion K D L)
      (fun _ _ => rfl) c
  exact transportedGaloisCocycle
    (completionEmbedding w.1.1)
    (infiniteDecompositionGalois v w)
    (fun sigma a =>
      (infinite_decomposition_embedding
        v w sigma a).symm)
    cD

set_option synthInstance.maxHeartbeats 1000000 in
-- The crossed-product base-change theorem exposes the full completion tower.
set_option maxHeartbeats 6000000 in
/-- At an infinite place, localization of a global crossed product is
represented by the global cocycle restricted to the chosen decomposition
group and transported to the chosen extension of completions. -/
theorem brauer_change_crossed
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    let hwva := infinite_lies_comap v w.1 w.2
    letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwva).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    brauerBaseChange K v.1.Completion
        (CProduc.brauerClass K L c) =
      CProduc.brauerClass v.1.Completion w.1.1.Completion
        (infiniteRestrictedCocycle v w c) := by
  let H := infiniteCompletionDecomposition v w
  let D := infiniteDecompositionField v w
  let hwva := infinite_lies_comap v w.1 w.2
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwva⟩
  letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
  letI : SMul K v.1.Completion := (completionBaseAlgebra v.1).toSMul
  letI : Module K v.1.Completion := Algebra.toModule
  letI : Algebra D v.1.Completion :=
    (infiniteDecompositionEmbedding v w).toAlgebra
  letI : SMul D v.1.Completion :=
    (infiniteDecompositionEmbedding v w).toAlgebra.toSMul
  letI : Module D v.1.Completion := Algebra.toModule
  letI : IsScalarTower K D v.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    exact (infiniteDecompositionEmbedding v w).commutes x |>.symm
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra
  letI : SMul v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwva).toAlgebra.toSMul
  letI : Module v.1.Completion w.1.1.Completion := Algebra.toModule
  letI : Algebra D w.1.1.Completion :=
    ((completionEmbedding w.1.1).comp (algebraMap D L)).toAlgebra
  letI : SMul D w.1.1.Completion :=
    (((completionEmbedding w.1.1).comp
      (algebraMap D L)).toAlgebra).toSMul
  letI : Module D w.1.1.Completion := Algebra.toModule
  letI : IsScalarTower D v.1.Completion w.1.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    exact (infinite_completion_embedding
      v w x).symm
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  let cD : NMCocycl₂ (G := Gal(L/D)) (M := Lˣ) :=
    NMCocycl₂.restrict (galoisTowerInclusion K D L)
      (fun _ _ => rfl) c
  let i : L →+* w.1.1.Completion := completionEmbedding w.1.1
  let g : Gal(L/D) ≃* Gal(w.1.1.Completion/v.1.Completion) :=
    infiniteDecompositionGalois v w
  let hi : ∀ sigma : Gal(L/D), ∀ a : L,
      i (sigma a) = g sigma (i a) := fun sigma a =>
    (infinite_decomposition_embedding
      v w sigma a).symm
  let hbase : ∀ a : D,
      i (algebraMap D L a) =
        algebraMap v.1.Completion w.1.1.Completion
          (algebraMap D v.1.Completion a) := fun a =>
    (infinite_completion_embedding
      v w a).symm
  let coeffEquiv : L ⊗[D] v.1.Completion ≃ₐ[v.1.Completion]
      w.1.1.Completion :=
    infiniteDecompositionTensor v w
  have hcoeff : ∀ (a : L) (b : v.1.Completion),
      coeffEquiv (a ⊗ₜ[D] b) =
        i a * algebraMap v.1.Completion w.1.1.Completion b := by
    intro a b
    exact infinite_decomposition_tmul v w a b
  calc
    brauerBaseChange K v.1.Completion
        (CProduc.brauerClass K L c) =
        brauerBaseChange D v.1.Completion
          (brauerBaseChange K D (CProduc.brauerClass K L c)) :=
      (base_change_tower K D v.1.Completion
        (CProduc.brauerClass K L c)).symm
    _ = brauerBaseChange D v.1.Completion
        (CProduc.brauerClass D L cD) := by
      apply congrArg (brauerBaseChange D v.1.Completion)
      exact (restricted_crossed_brauer K D L c).symm
    _ = CProduc.brauerClass v.1.Completion w.1.1.Completion
        (transportedGaloisCocycle i g hi cD) :=
      brauer_base_crossed i g hi hbase cD coeffEquiv hcoeff
    _ = CProduc.brauerClass v.1.Completion w.1.1.Completion
        (infiniteRestrictedCocycle v w c) := rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- The fixed-field and stabilizer descriptions of the same automorphism unfold together.
set_option maxHeartbeats 6000000 in
/-- The decomposition-field automorphism corresponding to an infinite
chosen-place stabilizer element is that element after forgetting to
`Gal(L/K)`. -/
theorem infinite_automorphism_stabilizer
    (completion : HasseCompletionData K L)
    (v : InfinitePlace K) :
    let w := completion.infiniteUpper v
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    ∀ sigma : CompletionPlaceStabilizer v.1 w0,
      galoisTowerInclusion K
          (infiniteDecompositionField v w) L
          ((infiniteDecompositionGalois v w).symm
            (infiniteCompletionStabilizer
              (K := K) (L := L) v w sigma)) =
        (sigma : Gal(L/K)) := by
  let w := completion.infiniteUpper v
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  dsimp only
  intro sigma
  apply AlgEquiv.ext
  intro x
  simp only [infiniteDecompositionGalois,
    IsGaloisGroup.mulEquivAlgEquiv, infiniteCompletionStabilizer,
    MulEquiv.trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply,
    MulSemiringAction.toAlgAut_apply, galois_tower_inclusion,
    MulSemiringAction.toAlgEquiv_apply]
  change (sigma : Gal(L/K)) x = (sigma : Gal(L/K)) x
  rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- Expanding both archimedean cocycle constructions requires the completion tower.
set_option maxHeartbeats 6000000 in
/-- Restricting the cocycle produced by infinite-completion base change back
along the stabilizer-to-local-Galois equivalence gives direct completed
restriction of the original global cocycle. -/
theorem infinite_stabilizer_restricted
    (completion : HasseCompletionData K L)
    (v : InfinitePlace K)
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    let w := completion.infiniteUpper v
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
        w.1.1.Completionˣ := completionDistribAction v.1 w0
    infinite2Stabilizer
        (K := K) (L := L) v w
        (MHTwo.mk
          (infiniteRestrictedCocycle v w c)) =
      multiplicativeChosenStabilizer
        (K := K) (L := L) completion (.inr v)
        (MHTwo.mk c) := by
  let w := completion.infiniteUpper v
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
      w.1.1.Completionˣ := completionDistribAction v.1 w0
  dsimp only
  change MHTwo.mk
      (NMCocycl₂.restrict
        (infiniteCompletionStabilizer
          (K := K) (L := L) v w).toMonoidHom _
        (infiniteRestrictedCocycle v w c)) =
    MHTwo.mk
      (NMCocycl₂.mapCoefficients
        (Units.map (completionEmbedding w.1.1).toMonoidHom) _
        (NMCocycl₂.restrict
          (CompletionPlaceStabilizer v.1 w0).subtype _ c))
  apply congrArg MHTwo.mk
  apply NMCocycl₂.ext
  rintro ⟨sigma, tau⟩
  apply Units.ext
  simp only [NMCocycl₂.restrict_apply,
    NMCocycl₂.mapCoefficients_apply,
    infiniteRestrictedCocycle,
    transportedGaloisCocycle]
  have hsigma : galoisTowerInclusion K
        (infiniteDecompositionField v w) L
        ((infiniteDecompositionGalois v w).symm
          ((infiniteCompletionStabilizer
            (K := K) (L := L) v w).toMonoidHom sigma)) =
      (CompletionPlaceStabilizer v.1 w0).subtype sigma := by
    simpa only using
      (infinite_automorphism_stabilizer
        (K := K) (L := L) completion v sigma)
  have htau : galoisTowerInclusion K
        (infiniteDecompositionField v w) L
        ((infiniteDecompositionGalois v w).symm
          ((infiniteCompletionStabilizer
            (K := K) (L := L) v w).toMonoidHom tau)) =
      (CompletionPlaceStabilizer v.1 w0).subtype tau := by
    simpa only using
      (infinite_automorphism_stabilizer
        (K := K) (L := L) completion v tau)
  rw [hsigma, htau]
  rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- The three archimedean comparison equivalences expose dependent completion instances.
set_option maxHeartbeats 6000000 in
/-- For a represented global class, the infinite chosen-completion
comparison sends the crossed product of the completion-restricted cocycle to
the cohomological localization of the original global crossed product. -/
theorem infinite_chosen_crossed
    (completion : HasseCompletionData K L)
    (v : InfinitePlace K)
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    let w := completion.infiniteUpper v
    let hwv := infinite_lies_comap v w.1 w.2
    letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    resizedChosen2
        K L completion (.inr v)
        (Additive.ofMul
          (CProduc.relativeBrauerClass
            v.1.Completion w.1.1.Completion
            (infiniteRestrictedCocycle v w c))) =
      resizedGlobalChosen
        (K := K) (L := L) completion (.inr v)
        (relativeBrauerResized K L
          (Additive.ofMul (CProduc.relativeBrauerClass K L c))) := by
  let w := completion.infiniteUpper v
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
      w.1.1.Completionˣ := completionDistribAction v.1 w0
  dsimp only
  apply (uliftHasseNorm
    (K := K) (L := L) v.1 w0).injective
  change (uliftHasseNorm
      (K := K) (L := L) v.1 w0)
      ((uliftHasseNorm
        (K := K) (L := L) v.1 w0).symm
        ((infiniteHStabilizer
          (K := K) (L := L) v w)
          (relativeBrauer2
            v.1.Completion w.1.1.Completion
            (Additive.ofMul
              (CProduc.relativeBrauerClass
                v.1.Completion w.1.1.Completion
                (infiniteRestrictedCocycle v w c)))))) =
    (uliftHasseNorm
      (K := K) (L := L) v.1 w0)
      (resizedGlobalChosen
        (K := K) (L := L) completion (.inr v)
        (relativeBrauerResized K L
          (Additive.ofMul (CProduc.relativeBrauerClass K L c))))
  rw [AddEquiv.apply_symm_apply,
    relative_brauer_cohomology,
    relative_brauer_resized]
  change (infiniteHStabilizer
      (K := K) (L := L) v w)
      (multiplicativeLiftAdditive
        (MHTwo.mk
          (infiniteRestrictedCocycle v w c))) =
    uliftHasseNorm
      (K := K) (L := L) v.1 w0
      (resizedGlobalChosen
        (K := K) (L := L) completion (.inr v)
        (hasseGlobalResized
          (K := K) (L := L)
          (multiplicativeLiftAdditive
            (MHTwo.mk c))))
  rw [infinite_stabilizer_multiplicative
      (K := K) (L := L) v w,
    infinite_stabilizer_restricted
      (K := K) (L := L) completion v c]
  exact (multiplicative_additive_chosen
    (K := K) (L := L) completion (.inr v) (MHTwo.mk c)).symm

set_option synthInstance.maxHeartbeats 1000000 in
-- The represented local and global relative-Brauer classes elaborate together.
set_option maxHeartbeats 6000000 in
/-- Infinite chosen-completion crossed-product compatibility for a global
relative Brauer class presented by a normalized cocycle. -/
theorem chosen_crossed_compatibility
    (completion : HasseCompletionData K L)
    (v : InfinitePlace K)
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    ((((resizedChosen2
          K L completion (.inr v)).symm
        (resizedGlobalChosen
          (K := K) (L := L) completion (.inr v)
          (relativeBrauerResized K L
            (Additive.ofMul
              (CProduc.relativeBrauerClass K L c))))).toMul :
        localRelativeBrauer K L completion (.inr v)) :
      BrauerGroup
        (hasseAbsoluteValue (Sum.inr v)).Completion) =
      brauerBaseChange K
        (hasseAbsoluteValue (Sum.inr v)).Completion
        (CProduc.relativeBrauerClass K L c : BrauerGroup K) := by
  let w := completion.infiniteUpper v
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  rw [← infinite_chosen_crossed
      (K := K) (L := L) completion v c,
    AddEquiv.symm_apply_apply]
  change CProduc.brauerClass v.1.Completion w.1.1.Completion
      (infiniteRestrictedCocycle v w c) =
    brauerBaseChange K v.1.Completion (CProduc.brauerClass K L c)
  exact (brauer_change_crossed v w c).symm

set_option maxHeartbeats 2000000 in
-- Descent from arbitrary `H²` classes unfolds the global crossed-product equivalence.
/-- The infinite-place chosen-completion crossed-product comparison is
unconditional. -/
theorem chosenCrossedCompatibility
    (completion : HasseCompletionData K L) :
    ChosenCrossedCompatibility
      (K := K) (L := L) completion := by
  intro x v
  let e := CProduc.hRelativeBrauer K L
  obtain ⟨c, hc⟩ := MHTwo.exists_mk_eq (e.symm x)
  have hx : x = CProduc.relativeBrauerClass K L c := by
    symm
    change e (MHTwo.mk c) = x
    rw [hc, e.apply_symm_apply]
  rw [hx]
  exact chosen_crossed_compatibility
    (K := K) (L := L) completion v c

end


end Towers.CField.BLoc
