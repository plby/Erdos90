import Towers.ClassField.ReciprocityExistence.CompletionFormula
import Towers.ClassField.ReciprocityExistence.IdeleCup
import Towers.ClassField.BrauerLocalization.CompletionNaturality

/-!
# The finite Shapiro coordinate used in Theorem VII.8.1

This specializes the completion-product evaluation formula to the
simultaneous completion choice used by the global multiplicative idèle cup.
-/

namespace Towers.CField.RExist

open IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm
open Towers.CField.BLoc
open groupCohomology

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

set_option maxHeartbeats 2000000 in
-- The chosen completion is a dependent field of the Hasse-norm completion data.
/-- The finite branch of the placewise Shapiro map in Theorem VII.8.1 is
restriction followed by evaluation at its selected upper completion. -/
theorem finiteShapiroCoordinate
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : H2 (resizedPlaceRepresentation
      (K := K) (L := L) (.inl P))) :
    let completion := completionChoice K L
    let w := hasseChosenPlace completion (.inl P)
    resizedPlaceStabilizer
        (K := K) (L := L) completion (.inl P) x =
      groupCohomology.map
        (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
        (uliftIntegralHom
          (completionUnitsEvaluation
            (K := K) (L := L) (FinitePlace.mk P).val w)) 2 x := by
  let completion := completionChoice K L
  let w := hasseChosenPlace completion (.inl P)
  change uliftUnitsH
      (K := K) (L := L) P w x = _
  exact ulift_units_h
    (K := K) (L := L) P w x

set_option maxHeartbeats 2000000 in
-- The dependent finite-place fiber must reduce through the placewise trans equivalence.
/-- After the local crossed-product comparison, the finite coordinate is
obtained by applying the inverse chosen-completion `H²` equivalence to the
explicit restriction-and-evaluation class. -/
theorem relativeBrauerCoordinate
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : H2 (resizedPlaceRepresentation
      (K := K) (L := L) (.inl P))) :
    let completion := completionChoice K L
    let w := hasseChosenPlace completion (.inl P)
    completionRelativeBrauer
        (K := K) (L := L) completion (.inl P) x =
      (resizedChosen2
        K L completion (.inl P)).symm
        (groupCohomology.map
          (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
          (uliftIntegralHom
            (completionUnitsEvaluation
              (K := K) (L := L) (FinitePlace.mk P).val w)) 2 x) := by
  change (resizedChosen2
      K L (completionChoice K L) (.inl P)).symm
      (resizedPlaceStabilizer
        (K := K) (L := L) (completionChoice K L) (.inl P) x) = _
  rw [finiteShapiroCoordinate]
  rfl

end

end Towers.CField.RExist
