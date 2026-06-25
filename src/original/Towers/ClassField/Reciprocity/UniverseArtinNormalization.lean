import Towers.ClassField.LocalReciprocity.UniverseResidueCup
import Towers.ClassField.Reciprocity.UniverseArtinIndependence

/-!
# Ambient-universe normalization of finite-place Artin maps

This file keeps the arbitrary-universe finite-place normalization below the
Type-0 Lemma V.5.1 implementation.  The local norm-residue equivalence is
transported through `Small.{0}`/`Shrink`, identified with the ambient
cup-normalized Artin map, and packaged in the existing
`LayerLocalArtin` interface.
-/

namespace Towers.CField.Recip

open scoped IsMulCommutative
open AbsoluteValue IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.LRecip
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

/-- A number field in an arbitrary ambient universe has a Type-0 model. -/
theorem numberSmallZero
    (F : Type u) [Field F] [NumberField F] : Small.{0} F := by
  let b := Module.finBasis ℚ F
  exact small_of_injective b.repr.injective

/-- A valued copy of a Type-0-small field remains Type-0-small. -/
theorem absSmallZero
    (F : Type u) [Field F] [Small.{0} F]
    (v : AbsoluteValue F ℝ) : Small.{0} (WithAbs v) :=
  small_of_injective (WithAbs.equiv v).injective

/-- Uniform completion preserves Type-0 smallness. -/
theorem uniformSmallZero
    (X : Type u) [Small.{0} X] [UniformSpace X] :
    Small.{0} (UniformSpace.Completion X) := by
  let eSet : Set X ≃ Set (Shrink.{0} X) :=
    Equiv.Set.congr (equivShrink X)
  let eSetSet : Set (Set X) ≃ Set (Set (Shrink.{0} X)) :=
    Equiv.Set.congr eSet
  letI : Small.{0} (Set (Set X)) :=
    small_of_injective eSetSet.injective
  letI : Small.{0} (Filter X) := by
    apply small_of_injective (f := fun f : Filter X ↦ f.sets)
    intro f g h
    apply Filter.ext
    intro s
    change f.sets = g.sets at h
    change s ∈ f.sets ↔ s ∈ g.sets
    rw [h]
  letI : Small.{0} (CauchyFilter X) :=
    small_of_injective Subtype.val_injective
  change Small.{0} (Quotient (inseparableSetoid (CauchyFilter X)))
  exact small_of_surjective Quotient.mk_surjective

/-- The completion attached to an absolute value on a number field admits a
Type-0 model, even when the number field itself is universe-polymorphic. -/
theorem absoluteSmallZero
    (F : Type u) [Field F] [NumberField F]
    (v : AbsoluteValue F ℝ) : Small.{0} v.Completion := by
  letI : Small.{0} F := numberSmallZero F
  letI : Small.{0} (WithAbs v) := absSmallZero F v
  exact uniformSmallZero (WithAbs v)

set_option maxHeartbeats 8000000 in
-- The completion, decomposition group, and Shrink transports elaborate together.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The transported `Small.{0}` norm-residue map at a finite completion,
embedded in the ambient global Galois group and written on the prime-adic
source. -/
noncomputable def globalArtinSmall
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (P.adicCompletion K)ˣ →* Gal(L/K) := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Small.{0} v.Completion :=
    absoluteSmallZero K v
  letI : Small.{0} w.1.Completion :=
    absoluteSmallZero L w.1
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
  exact ((absoluteValueDecomposition v w.1).subtype.comp
      decomp.symm.toMonoidHom).comp
    ((abelianLocalSmall
      v.Completion w.1.Completion).comp
        (Units.map
          (placeCompletionAdic P).symm.toRingHom))

set_option maxHeartbeats 8000000 in
-- The ambient and Shrink local Artin maps elaborate with the same completion stack.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The ambient finite-place Artin map is the transported `Small.{0}`
norm-residue map. -/
theorem artin_universe_small
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    adicArtinUniverse K L P w =
      globalArtinSmall P w := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Small.{0} v.Completion :=
    absoluteSmallZero K v
  letI : Small.{0} w.1.Completion :=
    absoluteSmallZero L w.1
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
  let toAbsoluteCompletion : (P.adicCompletion K)ˣ →* v.Completionˣ :=
    Units.map
      (placeCompletionAdic P).symm.toRingHom
  change intoGlobal.comp
      ((abelianArtinUniverse
        v.Completion w.1.Completion).comp toAbsoluteCompletion) =
    intoGlobal.comp
      ((abelianLocalSmall
        v.Completion w.1.Completion).comp toAbsoluteCompletion)
  rw [abelian_small_universe]

end

end Towers.CField.Recip
