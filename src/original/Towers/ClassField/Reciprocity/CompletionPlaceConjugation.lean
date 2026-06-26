import Towers.NumberTheory.Galois.DecompositionGroup
import Towers.ClassField.IdeleCohomology.CompletionProductAction

/-!
# Conjugation between completed places

This file isolates the completion-level conjugation machinery used in
Lemma V.5.1.  Keeping it below the idèle extension-map API lets the same
argument be reused by universe-polymorphic finite-place Artin maps without
pulling in the substantially heavier Chapter VII norm tower.
-/

namespace Towers.CField.Recip

open AbsoluteValue
open Towers.NumberTheory.Milne
open Towers.CField.ICohomo

noncomputable section

universe u

/-- Galois conjugation between two places above `v`, extended to their
completions as an algebra equivalence over the completed base field. -/
def placeConjugationAlg
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K)) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra v.Completion (sigma • w).1.Completion :=
      (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
    w.1.Completion ≃ₐ[v.Completion] (sigma • w).1.Completion := by
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra v.Completion (sigma • w).1.Completion :=
    (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
  apply AlgEquiv.ofRingEquiv
    (f := completionGaloisRing sigma w.1)
  intro b
  have hfun :
      (fun c : v.Completion ↦ completionGaloisRing sigma w.1
        (completionLies v w.1 w.2 c)) =
      fun c : v.Completion ↦
        completionLies v (sigma • w).1 (sigma • w).2 c :=
    (dense_range_embedding v).equalizer
      ((completion_galois_isometry sigma w.1).continuous.comp
        (completion_lies_isometry v w.1 w.2).continuous)
      (completion_lies_isometry v
        (sigma • w).1 (sigma • w).2).continuous
      (funext fun x ↦ by
        simp only [Function.comp_apply]
        rw [show completionLies v w.1 w.2
              (completionEmbedding v x) =
            completionEmbedding w.1 (algebraMap K L x) by
          exact RingHom.congr_fun
            (completion_lies_comp v w.1 w.2) x]
        rw [completion_galois_embedding]
        rw [show completionLies v (sigma • w).1 (sigma • w).2
              (completionEmbedding v x) =
            completionEmbedding (sigma • w).1 (algebraMap K L x) by
          exact RingHom.congr_fun
            (completion_lies_comp v
              (sigma • w).1 (sigma • w).2) x]
        simp)
  exact congrFun hfun b

@[simp]
theorem conjugation_alg_embedding
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K)) (x : L) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra v.Completion (sigma • w).1.Completion :=
      (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
    placeConjugationAlg v w sigma
        (completionEmbedding w.1 x) =
      completionEmbedding (sigma • w).1 (sigma x) :=
  completion_galois_embedding sigma w.1 x

/-- Conjugation identifies the decomposition groups at `w` and `sigma • w`. -/
def absoluteDecompositionConj
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K)) :
    absoluteValueDecomposition v w.1 ≃*
      absoluteValueDecomposition v (sigma • w).1 where
  toFun tau := ⟨sigma * tau.1 * sigma⁻¹, by
    intro x
    change w.1 (sigma.symm ((sigma * tau.1 * sigma⁻¹) x)) =
      w.1 (sigma.symm x)
    simpa [AlgEquiv.mul_apply] using tau.2 (sigma.symm x)⟩
  invFun tau := ⟨sigma⁻¹ * tau.1 * sigma, by
    intro x
    simpa [AlgEquiv.mul_apply, smul_absolute_value] using
      tau.2 (sigma x)⟩
  left_inv tau := by
    apply Subtype.ext
    group
  right_inv tau := by
    apply Subtype.ext
    group
  map_mul' tau rho := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

/-- The completion isomorphism induced by `sigma` intertwines local
automorphisms with conjugation by `sigma` in the global Galois group.  This
is the completion-level conjugation square used in Lemma V.5.1. -/
def CompletionConjugationCompatibility
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K)) : Prop := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Fact (AbsoluteValue.LiesOver (sigma • w).1 v) := ⟨(sigma • w).2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra v.Completion (sigma • w).1.Completion :=
    (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
  exact ∀ tau : absoluteValueDecomposition v w.1,
    (placeConjugationAlg v w sigma).autCongr
        (decompositionCompletionEquiv v w.1 tau) =
      decompositionCompletionEquiv v (sigma • w).1
        (absoluteDecompositionConj v w sigma tau)

theorem completionConjugationCompatibility
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K)) :
    CompletionConjugationCompatibility v w sigma := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Fact (AbsoluteValue.LiesOver (sigma • w).1 v) := ⟨(sigma • w).2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra v.Completion (sigma • w).1.Completion :=
    (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
  dsimp [CompletionConjugationCompatibility]
  intro tau
  apply decomposition_alg_unique v (sigma • w).1
    (absoluteDecompositionConj v w sigma tau)
  · change Continuous (fun y ↦
      completionGaloisRing sigma w.1
        (decompositionCompletionEquiv v w.1 tau
          ((completionGaloisRing sigma w.1).symm y)))
    exact (completion_galois_isometry sigma w.1).continuous.comp
      ((decomposition_alg_continuous v w.1 tau).comp
        (completionGaloisIsometry sigma w.1).symm.continuous)
  · intro x
    have hinv :
        (placeConjugationAlg v w sigma).symm
            (completionEmbedding (sigma • w).1 x) =
          completionEmbedding w.1 (sigma.symm x) := by
      apply (placeConjugationAlg v w sigma).injective
      rw [AlgEquiv.apply_symm_apply]
      rw [conjugation_alg_embedding]
      simp
    simp only [AlgEquiv.trans_apply, hinv]
    rw [decomposition_alg_embedding]
    rw [conjugation_alg_embedding]
    rfl

/-- A local homomorphism into the automorphism group of one completed layer,
viewed in the ambient global Galois group through the decomposition-group
isomorphism. -/
def completionArtinGlobal
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Normal K L] [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v)
    (phi :
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      v.Completionˣ →* Gal(w.1.Completion/v.Completion)) :
    v.Completionˣ →* Gal(L/K) := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  exact (absoluteValueDecomposition v w.1).subtype.comp
    ((decompositionCompletionExtension v w.1).symm.toMonoidHom.comp
      phi)

/-- Transport a local homomorphism from the completion at `w` to the
completion at the conjugate place `sigma • w`. -/
def conjugateCompletionArtin
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K))
    (phi :
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      v.Completionˣ →* Gal(w.1.Completion/v.Completion)) :
    letI : Algebra v.Completion (sigma • w).1.Completion :=
      (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
    v.Completionˣ →* Gal((sigma • w).1.Completion/v.Completion) := by
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra v.Completion (sigma • w).1.Completion :=
    (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
  exact (placeConjugationAlg v w sigma).autCongr.toMonoidHom.comp phi

/-- Completion-level local Artin conjugation compatibility.  Transporting a
local map along the completion isomorphism induced by `sigma` changes its
global value by conjugation with `sigma`. -/
theorem artin_conjugation_compatibility
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Normal K L] [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K))
    (phi :
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      v.Completionˣ →* Gal(w.1.Completion/v.Completion)) :
    completionArtinGlobal v (sigma • w)
        (conjugateCompletionArtin v w sigma phi) =
      (MulAut.conj sigma).toMonoidHom.comp
        (completionArtinGlobal v w phi) := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Fact (AbsoluteValue.LiesOver (sigma • w).1 v) := ⟨(sigma • w).2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra v.Completion (sigma • w).1.Completion :=
    (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
  apply MonoidHom.ext
  intro x
  let tau : absoluteValueDecomposition v w.1 :=
    (decompositionCompletionExtension v w.1).symm (phi x)
  have hcompletion :=
    completionConjugationCompatibility v w sigma tau
  have hphi : decompositionCompletionEquiv v w.1 tau = phi x := by
    exact (decompositionCompletionExtension v w.1).apply_symm_apply
      (phi x)
  have hdecomposition :
      (decompositionCompletionExtension v (sigma • w).1).symm
          ((placeConjugationAlg v w sigma).autCongr (phi x)) =
        absoluteDecompositionConj v w sigma tau := by
    apply (decompositionCompletionExtension
      v (sigma • w).1).injective
    rw [MulEquiv.apply_symm_apply]
    change (placeConjugationAlg v w sigma).autCongr (phi x) = _
    rw [← hphi]
    exact hcompletion
  simpa only [completionArtinGlobal, conjugateCompletionArtin,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      congrArg Subtype.val hdecomposition

/-- In an abelian global Galois group, the decomposition groups at conjugate
completed places are the same subgroup. -/
theorem absolute_smul_commutative
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [IsMulCommutative Gal(L/K)]
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K)) :
    absoluteValueDecomposition v w.1 =
      absoluteValueDecomposition v (sigma • w).1 := by
  ext tau
  constructor
  · intro htau x
    change w.1 (sigma.symm (tau x)) = w.1 (sigma.symm x)
    change w.1 ((sigma⁻¹ * tau) x) = w.1 (sigma.symm x)
    rw [mul_comm' sigma⁻¹ tau]
    exact htau (sigma.symm x)
  · intro htau x
    have hx := htau (sigma x)
    simp only [places_above_val,
      smul_absolute_value, AlgEquiv.symm_apply_apply] at hx
    change w.1 ((sigma⁻¹ * tau * sigma) x) = w.1 x at hx
    have hconj : sigma⁻¹ * tau * sigma = tau := by
      rw [mul_comm' sigma⁻¹ tau]
      group
    rwa [hconj] at hx

end

end Towers.CField.Recip
