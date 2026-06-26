import Towers.ClassField.BrauerLocalization.FiniteNaturality
import Towers.FieldTheory.CentralEmbeddingBrauer

/-!
# Finite chosen-completion crossed-product compatibility

This file identifies the finite completion cocycle used by crossed-product
base change with direct restriction to the chosen global place stabilizer.
-/

namespace Towers.CField.BLoc

open CategoryTheory Representation groupCohomology
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm
open Towers.TBluepr

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

set_option synthInstance.maxHeartbeats 1000000 in
-- The decomposition-field and completion Galois equivalences elaborate together.
set_option maxHeartbeats 6000000 in
/-- The decomposition-field automorphism corresponding to a chosen-place
stabilizer element is that same element after forgetting to `Gal(L/K)`. -/
theorem completion_automorphism_stabilizer
    (completion : HasseCompletionData K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    let v := (FinitePlace.mk P).val
    let w := hasseChosenPlace completion (.inl P)
    let W := CompletionPlacesAbove (L := L) v
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Finite W := absolute_extensions_separable v
    letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K) W :=
      completion_above_pretransitive P
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    ∀ sigma : CompletionPlaceStabilizer v w,
      galoisTowerInclusion K
          (completionDecompositionField v
            (fun a b => (FinitePlace.mk P).add_le a b) w) L
          ((decompositionGaloisCompletion v
            (fun a b => (FinitePlace.mk P).add_le a b) w).symm
            (completionStabilizerEquiv
              (K := K) (L := L) v w sigma)) =
        (sigma : Gal(L/K)) := by
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  dsimp only
  intro sigma
  apply AlgEquiv.ext
  intro x
  simp only [decompositionGaloisCompletion,
    IsGaloisGroup.mulEquivAlgEquiv, completionStabilizerEquiv,
    MulEquiv.trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply,
    MulSemiringAction.toAlgAut_apply, galois_tower_inclusion,
    MulSemiringAction.toAlgEquiv_apply]
  change (sigma : Gal(L/K)) x = (sigma : Gal(L/K)) x
  rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- Expanding both cocycle constructions requires the full completion tower.
set_option maxHeartbeats 6000000 in
/-- Restricting the cocycle produced by completion base change back along
the stabilizer-to-local-Galois equivalence gives the direct completed
restriction of the original global cocycle. -/
theorem h_stabilizer_restricted
    (completion : HasseCompletionData K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    let v := (FinitePlace.mk P).val
    let w := hasseChosenPlace completion (.inl P)
    let W := CompletionPlacesAbove (L := L) v
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Finite W := absolute_extensions_separable v
    letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K) W :=
      completion_above_pretransitive P
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
        w.1.Completionˣ := completionDistribAction v w
    localHStabilizer
        (K := K) (L := L) v w
        (MHTwo.mk
          (restrictedGaloisCocycle v
            (fun a b => (FinitePlace.mk P).add_le a b) w c)) =
      multiplicativeChosenStabilizer
        (K := K) (L := L) completion (.inl P)
        (MHTwo.mk c) := by
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
      w.1.Completionˣ := completionDistribAction v w
  dsimp only
  change MHTwo.mk
      (NMCocycl₂.restrict
        (completionStabilizerEquiv
          (K := K) (L := L) v w).toMonoidHom _
        (restrictedGaloisCocycle v
          (fun a b => (FinitePlace.mk P).add_le a b) w c)) =
    MHTwo.mk
      (NMCocycl₂.mapCoefficients
        (Units.map (completionEmbedding w.1).toMonoidHom) _
        (NMCocycl₂.restrict
          (CompletionPlaceStabilizer v w).subtype _ c))
  apply congrArg MHTwo.mk
  apply NMCocycl₂.ext
  rintro ⟨sigma, tau⟩
  apply Units.ext
  simp only [NMCocycl₂.restrict_apply,
    NMCocycl₂.mapCoefficients_apply,
    restrictedGaloisCocycle,
    completionStabilizerEquiv,
    transportedGaloisCocycle]
  have hsigma : galoisTowerInclusion K
        (completionDecompositionField v
          (fun a b => (FinitePlace.mk P).add_le a b) w) L
        ((decompositionGaloisCompletion v
          (fun a b => (FinitePlace.mk P).add_le a b) w).symm
          (((MulEquiv.subgroupCongr
            (hasse_stabilizer_decomposition v w)).trans
              (decompositionCompletionExtension v w.1)).toMonoidHom
            sigma)) = (sigma : Gal(L/K)) := by
    simpa only [completionStabilizerEquiv] using
      (completion_automorphism_stabilizer
        (K := K) (L := L) completion P sigma)
  have htau : galoisTowerInclusion K
        (completionDecompositionField v
          (fun a b => (FinitePlace.mk P).add_le a b) w) L
        ((decompositionGaloisCompletion v
          (fun a b => (FinitePlace.mk P).add_le a b) w).symm
          (((MulEquiv.subgroupCongr
            (hasse_stabilizer_decomposition v w)).trans
              (decompositionCompletionExtension v w.1)).toMonoidHom
            tau)) = (tau : Gal(L/K)) := by
    simpa only [completionStabilizerEquiv] using
      (completion_automorphism_stabilizer
        (K := K) (L := L) completion P tau)
  rw [hsigma, htau]
  rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- The three comparison equivalences expose several dependent completion instances.
set_option maxHeartbeats 6000000 in
/-- For a represented global class, the finite chosen-completion comparison
sends the crossed product of the completion-restricted cocycle to the
cohomological localization of the original global crossed product. -/
theorem chosen_crossed_product
    (completion : HasseCompletionData K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    let v := (FinitePlace.mk P).val
    let w := hasseChosenPlace completion (.inl P)
    let W := CompletionPlacesAbove (L := L) v
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Finite W := absolute_extensions_separable v
    letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K) W :=
      completion_above_pretransitive P
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    resizedChosen2
        K L completion (.inl P)
        (Additive.ofMul
          (CProduc.relativeBrauerClass v.Completion w.1.Completion
            (restrictedGaloisCocycle v
              (fun a b => (FinitePlace.mk P).add_le a b) w c))) =
      resizedGlobalChosen
        (K := K) (L := L) completion (.inl P)
        (relativeBrauerResized K L
          (Additive.ofMul (CProduc.relativeBrauerClass K L c))) := by
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
      w.1.Completionˣ := completionDistribAction v w
  dsimp only
  apply (uliftHasseNorm
    (K := K) (L := L) v w).injective
  change (uliftHasseNorm
      (K := K) (L := L) v w)
      ((uliftHasseNorm
        (K := K) (L := L) v w).symm
        ((h2Stabilizer
          (K := K) (L := L) v w
          (fun a b => (FinitePlace.mk P).add_le a b))
          (relativeBrauer2
            v.Completion w.1.Completion
            (Additive.ofMul
              (CProduc.relativeBrauerClass
                v.Completion w.1.Completion
                (restrictedGaloisCocycle v
                  (fun a b => (FinitePlace.mk P).add_le a b) w c)))))) =
    (uliftHasseNorm
      (K := K) (L := L) v w)
      (resizedGlobalChosen
        (K := K) (L := L) completion (.inl P)
        (relativeBrauerResized K L
          (Additive.ofMul (CProduc.relativeBrauerClass K L c))))
  rw [AddEquiv.apply_symm_apply,
    relative_brauer_cohomology,
    relative_brauer_resized]
  change (h2Stabilizer
      (K := K) (L := L) v w
      (fun a b => (FinitePlace.mk P).add_le a b))
      (multiplicativeLiftAdditive
        (MHTwo.mk
          (restrictedGaloisCocycle v
            (fun a b => (FinitePlace.mk P).add_le a b) w c))) =
    uliftHasseNorm
      (K := K) (L := L) v w
      (resizedGlobalChosen
        (K := K) (L := L) completion (.inl P)
        (hasseGlobalResized
          (K := K) (L := L)
          (multiplicativeLiftAdditive
            (MHTwo.mk c))))
  rw [h_stabilizer_multiplicative
      (K := K) (L := L) v
      (fun a b => (FinitePlace.mk P).add_le a b) w,
    h_stabilizer_restricted
      (K := K) (L := L) completion P c]
  exact (multiplicative_additive_chosen
    (K := K) (L := L) completion (.inl P) (MHTwo.mk c)).symm

set_option synthInstance.maxHeartbeats 1000000 in
-- The represented local and global relative-Brauer classes elaborate together.
set_option maxHeartbeats 6000000 in
/-- Finite chosen-completion crossed-product compatibility for a global
relative Brauer class presented by a normalized cocycle. -/
theorem crossed_compatibility_relative
    (completion : HasseCompletionData K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    ((((resizedChosen2
          K L completion (.inl P)).symm
        (resizedGlobalChosen
          (K := K) (L := L) completion (.inl P)
          (relativeBrauerResized K L
            (Additive.ofMul
              (CProduc.relativeBrauerClass K L c))))).toMul :
        localRelativeBrauer K L completion (.inl P)) :
      BrauerGroup
        (hasseAbsoluteValue (Sum.inl P)).Completion) =
      brauerBaseChange K
        (hasseAbsoluteValue (Sum.inl P)).Completion
        (CProduc.relativeBrauerClass K L c : BrauerGroup K) := by
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  rw [← chosen_crossed_product
      (K := K) (L := L) completion P c,
    AddEquiv.symm_apply_apply]
  change CProduc.brauerClass v.Completion w.1.Completion
      (restrictedGaloisCocycle v
        (fun a b => (FinitePlace.mk P).add_le a b) w c) =
    brauerBaseChange K v.Completion (CProduc.brauerClass K L c)
  exact (base_change_crossed v
    (fun a b => (FinitePlace.mk P).add_le a b) w c).symm

set_option maxHeartbeats 2000000 in
-- Descent from arbitrary `H²` classes unfolds the global crossed-product equivalence.
/-- The finite-place chosen-completion crossed-product comparison is
unconditional. -/
theorem completionCrossedCompatibility
    (completion : HasseCompletionData K L) :
    CompletionCrossedCompatibility
      (K := K) (L := L) completion := by
  intro x P
  let e := CProduc.hRelativeBrauer K L
  obtain ⟨c, hc⟩ := MHTwo.exists_mk_eq (e.symm x)
  have hx : x = CProduc.relativeBrauerClass K L c := by
    symm
    change e (MHTwo.mk c) = x
    rw [hc, e.apply_symm_apply]
  rw [hx]
  exact crossed_compatibility_relative
    (K := K) (L := L) completion P c

end

end Towers.CField.BLoc
