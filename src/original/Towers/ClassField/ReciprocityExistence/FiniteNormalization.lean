import Towers.ClassField.ReciprocityExistence.LocalNormalization
import Towers.ClassField.ReciprocityExistence.IdeleCup
import Towers.ClassField.ReciprocityExistence.PlaceCompletion

/-!
# Finite-place normalization of the Theorem VII.8.1 local coordinate

The chosen-completion comparison is normalized by the same finite local
invariant as Proposition III.3.6.  This isolates the remaining finite-place
work to identifying the evaluated global cup with a local multiplicative
cup class.
-/

namespace Towers.CField.RExist

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LClass
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm
open Towers.CField.BLoc

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

set_option maxHeartbeats 10000000 in
-- The finite-place branch installs the full dependent completion tower.
/-- The finite-place invariant of a chosen-completion coordinate is the
canonical finite relative invariant of the multiplicative local `H²` class
which produced that coordinate. -/
theorem multiplicative_h_2
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    let completion := completionChoice K L
    let v := (FinitePlace.mk P).val
    let w := hasseChosenPlace completion (.inl P)
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : NontriviallyNormedField v.Completion :=
      placeNontriviallyNormed P
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Finite (CompletionPlacesAbove (L := L) v) :=
      absolute_extensions_separable v
    letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
      absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) v) :=
      completion_above_pretransitive P
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    letI : ValuativeRel v.Completion :=
      placeValuativeRel P
    letI : Valuation.Compatible
        (NormedField.valuation (K := v.Completion)) :=
      Valuation.Compatible.ofValuation
        (NormedField.valuation (K := v.Completion))
    letI : IsNonarchimedeanLocalField v.Completion :=
      placeNonarchimedeanField P
    ∀ x : MHTwo Gal(w.1.Completion/v.Completion)
        w.1.Completionˣ,
      finitePlaceInvariant K P
          (localBrauerInclusion K L completion (.inl P)
            ((resizedChosen2
                K L completion (.inl P)).symm
              ((uliftHasseNorm
                  (K := K) (L := L) v w).symm
                ((h2Stabilizer
                    (K := K) (L := L) v w
                    (fun a b => (FinitePlace.mk P).add_le a b))
                  (multiplicativeLiftAdditive x))))) =
        (carryBrauerInvariant v.Completion
          ((CProduc.hRelativeBrauer
              v.Completion w.1.Completion x :
            relativeBrauerGroup v.Completion w.1.Completion) :
          BrauerGroup v.Completion)).toAdd := by
  let completion := completionChoice K L
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite (CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  dsimp only
  intro x
  have hcoordinate :
      (resizedChosen2
          K L completion (.inl P)).symm
          ((uliftHasseNorm
              (K := K) (L := L) v w).symm
            ((h2Stabilizer
                (K := K) (L := L) v w
                (fun a b => (FinitePlace.mk P).add_le a b))
              (multiplicativeLiftAdditive x))) =
        (relativeBrauer2
          v.Completion w.1.Completion).symm
            (multiplicativeLiftAdditive x) := by
    change (relativeBrauer2
        v.Completion w.1.Completion).symm
      ((h2Stabilizer
          (K := K) (L := L) v w
          (fun a b => (FinitePlace.mk P).add_le a b)).symm
        ((uliftHasseNorm
            (K := K) (L := L) v w)
          ((uliftHasseNorm
              (K := K) (L := L) v w).symm
            ((h2Stabilizer
                (K := K) (L := L) v w
                (fun a b => (FinitePlace.mk P).add_le a b))
              (multiplicativeLiftAdditive x))))) = _
    rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  rw [hcoordinate]
  change (carryBrauerInvariant v.Completion
      (((relativeBrauer2
          v.Completion w.1.Completion).symm
        (multiplicativeLiftAdditive x)).toMul :
        BrauerGroup v.Completion)).toAdd = _
  rw [resized_multiplicative_2]

end

end Towers.CField.RExist
