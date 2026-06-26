import Towers.ClassField.BrauerLocalization.LocalHilbert90
import Towers.ClassField.IdeleCohomology.FiniteLocalHerbrand
import Towers.ClassField.Ideles.FinitePlaceCompletion

/-!
# Direct finite local Tate-zero calculation for Proposition VII.2.7

This is Milne's local Herbrand calculation transported from the completed
local Galois group to the global completion-place stabilizer.
-/

namespace Towers.CField.BLoc

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Shifting
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm
open groupCohomology

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 500000 in
-- The two cyclic groups and their completion representations elaborate together.
set_option maxHeartbeats 5000000 in
/-- The finite-place Tate-zero cardinality follows directly from the local
unit filtration and valuation sequence, without a spectral hypothesis. -/
theorem tate_cardinality_direct
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI : Fintype (CompletionPlaceStabilizer
      (FinitePlace.mk P).val w) := Fintype.ofFinite _
    Finite (tateZero
        (placeUnitsRepresentation (FinitePlace.mk P).val w)) ∧
      Nat.card (tateZero
        (placeUnitsRepresentation (FinitePlace.mk P).val w)) =
        Nat.card (CompletionPlaceStabilizer (FinitePlace.mk P).val w) := by
  let v := (FinitePlace.mk P).val
  let F := v.Completion
  let E := w.1.Completion
  let W := CompletionPlacesAbove (L := L) v
  let H := CompletionPlaceStabilizer v w
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic H := Subgroup.isCyclic H
  letI : CommGroup H := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField F :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist F := placeUltrametricDist P
  letI : ValuativeRel F := placeValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    placeNonarchimedeanField P
  letI : CharZero F :=
    charZero_of_injective_ringHom (completionEmbedding v).injective
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional F E :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois F E := placeCompletionGalois v w
  let J := Gal(E/F)
  letI : IsCyclic J :=
    (decompositionCompletionExtension v w.1).isCyclic.mp
      (Subgroup.isCyclic (absoluteValueDecomposition v w.1))
  letI : Fintype J := Fintype.ofFinite J
  letI : CommGroup J := IsCyclic.commGroup
  obtain ⟨j, hj⟩ := IsCyclic.exists_generator (α := J)
  let A := placeUnitsRepresentation v w
  let M := Rep.ofAlgebraAutOnUnits F E
  let eGlobal : uliftIntegralRepresentation M ≅
      hasseGlobalRepresentation F E := by
    apply Rep.mkIso
    apply Representation.Equiv.mk
      (LinearEquiv.refl (ULift.{u} ℤ) (Additive Eˣ))
    intro σ
    rfl
  let eMTate : tateZero M ≃+
      H2 (uliftIntegralRepresentation M) :=
    (tateIntLift M).trans
      (tateCohomologyTwo
        (uliftIntegralRepresentation M) j hj).toAddEquiv
  let eMNeg : tateNegOne M ≃+
      H1 (uliftIntegralRepresentation M) :=
    (tateULift M).trans
      (tateCohomologyNeg
        (uliftIntegralRepresentation M) j hj).toAddEquiv
  let eGlobalH1 : H1 (uliftIntegralRepresentation M) ≃+
      H1 (hasseGlobalRepresentation F E) :=
    ((groupCohomology.functor (ULift.{u} ℤ) J 1).mapIso
      eGlobal).toLinearEquiv.toAddEquiv
  letI : Subsingleton (tateNegOne M) :=
    ⟨fun x y ↦ by
      apply eMNeg.injective
      apply eGlobalH1.injective
      exact (hasse_global_units F E (eGlobalH1 (eMNeg x))).trans
        (hasse_global_units F E (eGlobalH1 (eMNeg y))).symm⟩
  have hM : HerbrandQuotientValue M (Module.finrank F E : ℚ) :=
    units_herbrand_value F E
  letI : Finite (tateZero M) := hM.1
  letI : Finite (tateNegOne M) := hM.2.1
  have hMcard : Nat.card (tateZero M) = Module.finrank F E := by
    have hq := hM.2.2
    have hneg : Nat.card (tateNegOne M) = 1 := Nat.card_unique
    rw [hneg, Nat.cast_one, div_one] at hq
    exact_mod_cast hq
  let eGlobalH2 : H2 (uliftIntegralRepresentation M) ≃+
      H2 (hasseGlobalRepresentation F E) :=
    ((groupCohomology.functor (ULift.{u} ℤ) J 2).mapIso
      eGlobal).toLinearEquiv.toAddEquiv
  let eLocal := h2Stabilizer
    (K := K) (L := L) v w (fun x y ↦ (FinitePlace.mk P).add_le x y)
  let ePresentation : H2 (uliftIntegralRepresentation A) ≃+
      H2 (hasseUnitsRepresentation v w) :=
    ((groupCohomology.functor (ULift.{u} ℤ) H 2).mapIso
      (uliftIsoHasse
        (K := K) (L := L) v w)).toLinearEquiv.toAddEquiv
  let eATate : tateZero A ≃+
      H2 (uliftIntegralRepresentation A) :=
    (tateIntLift A).trans
      (tateCohomologyTwo
        (uliftIntegralRepresentation A) g hg).toAddEquiv
  let e : tateZero M ≃+ tateZero A :=
    eMTate.trans (eGlobalH2.trans
      (eLocal.trans (ePresentation.symm.trans eATate.symm)))
  let hfinite : Finite (tateZero A) :=
    Finite.of_equiv (tateZero M) e.toEquiv
  refine ⟨hfinite, ?_⟩
  calc
    Nat.card (tateZero A) =
        Nat.card (tateZero M) := Nat.card_congr e.symm.toEquiv
    _ = Module.finrank F E := hMcard
    _ = Nat.card (absoluteValueDecomposition v w.1) :=
      finrank_decomposition_card P w
    _ = Nat.card H := by
      change Nat.card (absoluteValueDecomposition v w.1) =
        Nat.card (CompletionPlaceStabilizer v w)
      rw [hasse_stabilizer_decomposition v w]

end

end Towers.CField.BLoc
