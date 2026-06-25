import Towers.ClassField.BrauerLocalization.LocalHilbert90
import Towers.ClassField.BrauerLocalization.KillingSelection
import Towers.ClassField.BrauerLocalization.Relative2Comparison
import Towers.ClassField.LocalBrauer.FiniteRelativeCardinality

/-!
# Finite local Tate-zero cardinality in Proposition VII.2.7

At a finite place, cyclic periodicity identifies the Tate-zero numerator
with degree-two cohomology of the chosen completion stabilizer.  The existing
decomposition-group comparison and crossed-product theorem identify that
group with the relative Brauer group of the completed extension.  Its
cardinality is the local degree once the spectral local-invariant
base-change formula is supplied.
-/

namespace Towers.CField.BLoc

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Shifting
open Towers.CField.BGroups
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.CBrauer
open Towers.CField.HNorm
open groupCohomology

noncomputable section

universe u

/-- A singleton finite-place selection whose selected completion is
literally the prescribed completion `w`. -/
private noncomputable def finiteCompletionSelection
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    FiniteCompletionSelection K L {P} 1 := by
  classical
  let default : HasseCompletionData K L :=
    Classical.choice (hasseExistenceBridge K L)
  let completion : HasseCompletionData K L :=
    { finiteUpper := fun Q ↦
        if hQP : Q = P then
          hQP ▸ placesAboveFactors
            (K := K) (L := L) P w
        else default.finiteUpper Q
      infiniteUpper := default.infiniteUpper }
  refine
    { completion := completion
      selected := fun Q ↦
        hasseChosenPlace completion (.inl Q.1)
      chosen_eq_selected := fun _ ↦ rfl
      degree_dvd := fun _ ↦ one_dvd _ }

/-- The local spectral formula with all structures installed canonically.
Packaging it as a proposition makes transport between equal completion
places independent of the algebra instances occurring in the formula. -/
private def completionSpectralFormula
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) : Prop :=
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion := placeValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  SpectralChangeFormula v.Completion w.1.Completion

set_option synthInstance.maxHeartbeats 500000 in
-- The singleton selection and completed local-field structures are dependent.
set_option maxHeartbeats 5000000 in
/-- Spectral base change gives the local relative-Brauer cardinality at an
arbitrary prescribed finite completion. -/
theorem spectral_base_change
    (hbaseChange : FiniteSpectralChange.{u})
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI : Algebra (FinitePlace.mk P).val.Completion w.1.Completion :=
      (completionLies (FinitePlace.mk P).val w.1 w.2).toAlgebra
    Nat.card (relativeBrauerGroup
        (FinitePlace.mk P).val.Completion w.1.Completion) =
      Module.finrank (FinitePlace.mk P).val.Completion w.1.Completion := by
  let v := (FinitePlace.mk P).val
  let selection := finiteCompletionSelection (K := K) (L := L) P w
  let Q : ({P} : Finset (finitePrime K)) := ⟨P, by simp⟩
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion := placeValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  let hlocal : SpectralChangeFormula
      v.Completion w.1.Completion := by
    have hselected : selection.selected Q = w := by
      change (finiteCompletionSelection
        (K := K) (L := L) P w).selected Q = w
      simp only [finiteCompletionSelection, Q]
      simp only [hasseChosenPlace]
      rw [dif_pos rfl]
      change (placesAboveFactors
        (K := K) (L := L) P).symm
          ((placesAboveFactors
            (K := K) (L := L) P) w) = w
      exact (placesAboveFactors
        (K := K) (L := L) P).symm_apply_apply w
    have hwrapped : completionSpectralFormula
        P (selection.selected Q) := by
      simpa [completionSpectralFormula,
        SelectedSpectralFormula, Q, v] using
          hbaseChange K L {P} 1 selection Q
    have hw : completionSpectralFormula P w :=
      hselected ▸ hwrapped
    simpa [completionSpectralFormula, v] using hw
  exact relative_spectral_change
    v.Completion w.1.Completion hlocal

set_option synthInstance.maxHeartbeats 500000 in
-- Tate periodicity, completion transport, and crossed products elaborate together.
set_option maxHeartbeats 5000000 in
/-- The finite-place part of the local Tate-zero cardinality bridge follows
from the spectral base-change formula already required by VIII.4.2. -/
theorem cardinality_base_change
    (hbaseChange : FiniteSpectralChange.{u})
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
  let W := CompletionPlacesAbove (L := L) v
  let H := CompletionPlaceStabilizer v w
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic H := Subgroup.isCyclic H
  letI : CommGroup H := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
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
  let A := placeUnitsRepresentation v w
  let eTate : tateZero A ≃+
      H2 (uliftIntegralRepresentation A) :=
    (tateIntLift A).trans
      (tateCohomologyTwo
        (uliftIntegralRepresentation A) g hg).toAddEquiv
  let ePresentation : H2 (uliftIntegralRepresentation A) ≃+
      H2 (hasseUnitsRepresentation v w) :=
    ((groupCohomology.functor (ULift.{u} ℤ) H 2).mapIso
      (uliftIsoHasse
        (K := K) (L := L) v w)).toLinearEquiv.toAddEquiv
  let eLocal := h2Stabilizer
    (K := K) (L := L) v w (fun x y ↦ (FinitePlace.mk P).add_le x y)
  let eBrauer := relativeBrauer2
    v.Completion w.1.Completion
  let e : tateZero A ≃+
      Additive (relativeBrauerGroup v.Completion w.1.Completion) :=
    eTate.trans (ePresentation.trans (eLocal.symm.trans eBrauer.symm))
  have hcardRelative :=
    spectral_base_change
      hbaseChange P w
  letI : Finite (relativeBrauerGroup v.Completion w.1.Completion) :=
    Nat.finite_of_card_ne_zero <| by
      rw [hcardRelative]
      exact Nat.ne_of_gt (Module.finrank_pos (R := v.Completion)
        (M := w.1.Completion))
  let hfinite : Finite (tateZero A) :=
    Finite.of_equiv (Additive
      (relativeBrauerGroup v.Completion w.1.Completion)) e.symm.toEquiv
  refine ⟨hfinite, ?_⟩
  calc
    Nat.card (tateZero A) =
        Nat.card (relativeBrauerGroup v.Completion w.1.Completion) :=
      Nat.card_congr e.toEquiv
    _ = Module.finrank v.Completion w.1.Completion := hcardRelative
    _ = Nat.card (absoluteValueDecomposition v w.1) :=
      finrank_decomposition_card P w
    _ = Nat.card H := by
      change Nat.card (absoluteValueDecomposition v w.1) =
        Nat.card (CompletionPlaceStabilizer v w)
      rw [hasse_stabilizer_decomposition v w]


end

end Towers.CField.BLoc
