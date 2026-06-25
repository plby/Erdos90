import Submission.ClassField.LocalReciprocity.UniversePolymorphicArtin
import Submission.NumberTheory.Galois.PlaceCompletionDegree
import Submission.ClassField.Ideles.FinitePlaceCompletion
import Submission.ClassField.IdeleCohomology.CompletionProductAction

/-!
# The normalized finite-place Artin map in arbitrary universes

This is the universe-polymorphic Proposition III.3.6 Artin map at a chosen
completion, transported to the prime-adic source used by idèles and embedded
in the ambient number-field Galois group.
-/

namespace Submission.CField.Recip

open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LRecip
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.RExist
open scoped IsMulCommutative

noncomputable section

universe u

/-- The normalized finite-place character formula, with global source and
target models, before Chapter VII gives it its section-specific name. -/
structure UniverseFormulaData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) where
  artin : (P.adicCompletion K)ˣ →* Gal(L/K)
  cupInvariant :
    (P.adicCompletion K)ˣ →
      CharacterModule (Additive Gal(L/K)) → LocalInvariant
  formula : ∀ a chi,
    chi (Additive.ofMul (artin a)) = cupInvariant a chi

set_option maxHeartbeats 8000000 in
-- The completion, decomposition group, and Shrink transports elaborate together.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The canonically normalized III.3.6 package at a chosen upper completion,
with the source and target models used by global idèles. -/
noncomputable def characterFormulaUniverse
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    UniverseFormulaData K L P := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : CharZero v.Completion :=
    (RingHom.charZero_iff (algebraMap K v.Completion).injective).mp
      inferInstance
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let decomp := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau => decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decomp.symm sigma) (decomp.symm tau)
  let intoGlobal : Gal(w.1.Completion/v.Completion) →* Gal(L/K) :=
    (absoluteValueDecomposition v w.1).subtype.comp
      decomp.symm.toMonoidHom
  let toAbsoluteCompletion : (P.adicCompletion K)ˣ →* v.Completionˣ :=
    Units.map
      (placeCompletionAdic P).symm.toRingHom
  let artin : (P.adicCompletion K)ˣ →* Gal(L/K) :=
    intoGlobal.comp
      ((abelianArtinUniverse
        v.Completion w.1.Completion).comp toAbsoluteCompletion)
  let cupInvariant
      (a : (P.adicCompletion K)ˣ)
      (chi : CharacterModule (Additive Gal(L/K))) : LocalInvariant :=
    characterCupUniverse v.Completion w.1.Completion
      (toAbsoluteCompletion a)
      (chi.comp intoGlobal.toAdditive)
  refine
    { artin := artin
      cupInvariant := cupInvariant
      formula := ?_ }
  intro a chi
  change chi (Additive.ofMul
      (intoGlobal (abelianArtinUniverse
        v.Completion w.1.Completion (toAbsoluteCompletion a)))) =
    characterCupUniverse v.Completion w.1.Completion
      (toAbsoluteCompletion a)
      (chi.comp intoGlobal.toAdditive)
  exact (abelian_universe_comp v.Completion w.1.Completion
    intoGlobal (toAbsoluteCompletion a) chi).symm

/-- The Artin-map projection of the universe-polymorphic finite-place
character formula. -/
noncomputable def adicArtinUniverse
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (P.adicCompletion K)ˣ →* Gal(L/K) :=
  (characterFormulaUniverse K L P w).artin

set_option maxHeartbeats 20000000 in
-- The universe-polymorphic completion and decomposition-group comparison exceeds the
-- smaller budget while reducing the transported crossed-product representatives.
set_option synthInstance.maxHeartbeats 1000000 in
-- The completion and decomposition-group instances elaborate together.
/-- The finite-place cup invariant is the canonical invariant
of the literal multiplicative local crossed product. -/
theorem formula_universe_cup
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (y : (P.adicCompletion K)ˣ)
    (chi : CharacterModule (Additive Gal(L/K))) :
    let v := (FinitePlace.mk P).val
    let W := CompletionPlacesAbove (L := L) v
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : NontriviallyNormedField v.Completion :=
      placeNontriviallyNormed P
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : ValuativeRel v.Completion :=
      placeValuativeRel P
    letI : Valuation.Compatible
        (NormedField.valuation (K := v.Completion)) :=
      Valuation.Compatible.ofValuation
        (NormedField.valuation (K := v.Completion))
    letI : IsNonarchimedeanLocalField v.Completion :=
      placeNonarchimedeanField P
    letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
    letI : CharZero v.Completion :=
      (RingHom.charZero_iff (algebraMap K v.Completion).injective).mp
        inferInstance
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Finite W := absolute_extensions_separable v
    letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K) W :=
      completion_above_pretransitive P
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    let decomp := decompositionCompletionExtension v w.1
    letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
      refine ⟨⟨fun sigma tau ↦ decomp.symm.injective ?_⟩⟩
      simpa only [map_mul] using
        mul_comm (decomp.symm sigma) (decomp.symm tau)
    let intoGlobal : Gal(w.1.Completion/v.Completion) →* Gal(L/K) :=
      (absoluteValueDecomposition v w.1).subtype.comp
        decomp.symm.toMonoidHom
    let b : v.Completionˣ := Units.map
      (placeCompletionAdic P).symm.toRingHom y
    (carryBrauerInvariant v.Completion
      (((CProduc.hRelativeBrauer
        v.Completion w.1.Completion
        (multiplicativeCupClass v.Completion w.1.Completion b
          (chi.comp intoGlobal.toAdditive)) :
          relativeBrauerGroup v.Completion w.1.Completion) :
        BrauerGroup v.Completion))).toAdd =
      (characterFormulaUniverse K L P w).cupInvariant y chi := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion := placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : CharZero v.Completion :=
    (RingHom.charZero_iff (algebraMap K v.Completion).injective).mp
      inferInstance
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let decomp := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau ↦ decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decomp.symm sigma) (decomp.symm tau)
  let intoGlobal : Gal(w.1.Completion/v.Completion) →* Gal(L/K) :=
    (absoluteValueDecomposition v w.1).subtype.comp
      decomp.symm.toMonoidHom
  let b : v.Completionˣ := Units.map
    (placeCompletionAdic P).symm.toRingHom y
  dsimp only
  change (carryBrauerInvariant v.Completion
      (((CProduc.hRelativeBrauer
        v.Completion w.1.Completion
        (multiplicativeCupClass v.Completion w.1.Completion b
          (chi.comp intoGlobal.toAdditive)) :
          relativeBrauerGroup v.Completion w.1.Completion) :
        BrauerGroup v.Completion))).toAdd =
    characterCupUniverse v.Completion w.1.Completion b
      (chi.comp intoGlobal.toAdditive)
  exact (character_universe_multiplicative
    v.Completion w.1.Completion b
      (chi.comp intoGlobal.toAdditive)).symm

end

end Submission.CField.Recip
