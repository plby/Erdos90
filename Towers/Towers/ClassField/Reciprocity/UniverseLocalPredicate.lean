import Towers.ClassField.Reciprocity.ArtinMapStatements
import Towers.ClassField.Reciprocity.UniverseArtinNormalization
import Towers.ClassField.NormIndex.CompletionPlaceBridge

/-!
# The ambient finite-place Artin map satisfies the Chapter V local predicate
-/

namespace Towers.CField.Recip

open scoped IsMulCommutative
open AbsoluteValue IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.LRecip
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.NIndex

noncomputable section

universe u

set_option maxHeartbeats 8000000 in
-- The quotient equivalence and completion/decomposition transports elaborate together.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The ambient finite-place map satisfies the full finite-layer local Artin
predicate in arbitrary universes. -/
theorem global_artin_universe
    {K : Type u} [Field K] [NumberField K]
    (L : FASubext K) [NumberField L.1]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L.1) P) :
    let w := (placesAboveFactors
      (K := K) (L := L.1) P).symm Q
    LayerLocalArtin L P Q
      (adicArtinUniverse K L.1 P w) := by
  let w := (placesAboveFactors
    (K := K) (L := L.1) P).symm Q
  let v := (FinitePlace.mk P).val
  letI : Small.{0} v.Completion :=
    absoluteSmallZero K v
  letI : Small.{0} w.1.Completion :=
    absoluteSmallZero L.1 w.1
  have hwq : w.1.IsEquiv
      (FinitePlace.mk (upperPrime (K := K) (L := L.1) P Q)).val := by
    exact
      (Towers.CField.NIndex.primeCompletionModel
        K L.1 P Q).isEquiv_upper
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
  letI : Finite (CompletionPlacesAbove (L := L.1) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L.1) v) :=
    absolute_value_extension (K := K) (L := L.1) v
  letI : MulAction.IsPretransitive Gal(L.1/K)
      (CompletionPlacesAbove (L := L.1) v) :=
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
  let e := abelianArtinSmall
    v.Completion w.1.Completion
  refine ⟨w.1, w.2, hwq, e, ?_, ?_⟩
  · intro x
    rw [artin_universe_small]
    simp only [globalArtinSmall,
      abelianLocalSmall, MonoidHom.comp_apply,
      Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom]
    simp only [v, w, e]
  · intro q
    exact global_universe_independent P w q

end

end Towers.CField.Recip
