import Towers.ClassField.BrauerLocalization.Relative2Comparison
import Towers.ClassField.HasseNorm.IdeleDecomposition

/-!
# Local relative Brauer groups at chosen completions

For a finite Galois extension of number fields and one chosen completion above
every base place, this file packages the local crossed-product and Shapiro
comparisons.  At a finite place the base field here is initially the
absolute-value completion; a later compatibility theorem transports across
`placeCompletionAdic` to the adic completion used in the
statement of Theorem VIII.4.2.
-/

namespace Towers.CField.BLoc

open CategoryTheory Representation groupCohomology
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.BGroups
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The upper completed field selected above a number-field place. -/
noncomputable abbrev chosenCompletionExtension
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) : Type u :=
  (hasseChosenPlace completion v).1.Completion

noncomputable instance chosenCompletionAlgebra
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    Algebra (hasseAbsoluteValue v).Completion
      (chosenCompletionExtension K L completion v) :=
  (completionLies (hasseAbsoluteValue v)
    (hasseChosenPlace completion v).1
    (hasseChosenPlace completion v).2).toAlgebra

noncomputable instance basePlaceNontrivial
    (v : NumberFieldPlace K) :
    Fact (hasseAbsoluteValue v).IsNontrivial := by
  cases v with
  | inl P => exact ⟨absolute_value_nontrivial P⟩
  | inr v => exact ⟨infinite_place_nontrivial v⟩

/-- The natural embedding of the global field into the absolute-value
completion used by the cohomological local comparison. -/
noncomputable instance baseCompletionAlgebra
    (v : NumberFieldPlace K) :
    Algebra K (hasseAbsoluteValue v).Completion :=
  completionBaseAlgebra (hasseAbsoluteValue v)

noncomputable instance chosenCompletionDimensional
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    FiniteDimensional (hasseAbsoluteValue v).Completion
      (chosenCompletionExtension K L completion v) := by
  cases v with
  | inl P =>
      let v := (FinitePlace.mk P).val
      let w := hasseChosenPlace completion (.inl P)
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P
      exact Towers.NumberTheory.Milne.placeCompletionDimensional v w
  | inr v =>
      let w := completion.infiniteUpper v
      exact infinite_completion_module (K := K) (L := L) v w

noncomputable instance chosenCompletionGalois
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    IsGalois (hasseAbsoluteValue v).Completion
      (chosenCompletionExtension K L completion v) := by
  cases v with
  | inl P =>
      let v := (FinitePlace.mk P).val
      let w := hasseChosenPlace completion (.inl P)
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P
      letI : Finite (CompletionPlacesAbove (L := L) v) :=
        absolute_extensions_separable v
      letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
        absolute_value_extension (K := K) (L := L) v
      letI : MulAction.IsPretransitive Gal(L/K)
          (CompletionPlacesAbove (L := L) v) :=
        completion_above_pretransitive P
      exact placeCompletionGalois v w
  | inr v =>
      let w := completion.infiniteUpper v
      exact infiniteHasseGalois K L v w

/-- The relative Brauer group of the chosen completed extension at `v`. -/
noncomputable abbrev localRelativeBrauer
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :=
  relativeBrauerGroup (hasseAbsoluteValue v).Completion
    (chosenCompletionExtension K L completion v)

/-- Local crossed products followed by the completion-place stabilizer
comparison, in the orientation from local relative Brauer classes to the
chosen stabilizer `H²`. -/
noncomputable def resizedChosen2
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    Additive (localRelativeBrauer K L completion v) ≃+
      H2 (chosenUnitsRepresentation
        (K := K) (L := L) completion v) := by
  cases v with
  | inl P =>
      let v := (FinitePlace.mk P).val
      let w := hasseChosenPlace completion (.inl P)
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P
      letI : Finite (CompletionPlacesAbove (L := L) v) :=
        absolute_extensions_separable v
      letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
        absolute_value_extension (K := K) (L := L) v
      letI : MulAction.IsPretransitive Gal(L/K)
          (CompletionPlacesAbove (L := L) v) :=
        completion_above_pretransitive P
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      letI : FiniteDimensional v.Completion w.1.Completion :=
        Towers.NumberTheory.Milne.placeCompletionDimensional v w
      letI : IsGalois v.Completion w.1.Completion :=
        placeCompletionGalois v w
      exact (relativeBrauer2
          v.Completion w.1.Completion).trans
        ((h2Stabilizer
            (K := K) (L := L) v w
            (fun x y => (FinitePlace.mk P).add_le x y)).trans
          (uliftHasseNorm
            (K := K) (L := L) v w).symm)
  | inr v =>
      let w := completion.infiniteUpper v
      let hwv := infinite_lies_comap v w.1 w.2
      let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
      letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
      letI : Algebra v.1.Completion w.1.1.Completion :=
        (completionLies v.1 w.1.1 hwv).toAlgebra
      letI : FiniteDimensional v.1.Completion w.1.1.Completion :=
        infinite_completion_module (K := K) (L := L) v w
      letI : IsGalois v.1.Completion w.1.1.Completion :=
        infiniteHasseGalois K L v w
      exact (relativeBrauer2
          v.1.Completion w.1.1.Completion).trans
        ((infiniteHStabilizer
            (K := K) (L := L) v w).trans
          (uliftHasseNorm
            (K := K) (L := L) v.1 w0).symm)

set_option synthInstance.maxHeartbeats 300000 in
-- Assembling the dependent direct sum of local Brauer comparisons requires a
-- deeper search for representation and module instances.
/-- Assemble the local relative-Brauer comparisons over all places. -/
noncomputable def brauerDirectChosen
    (completion : HasseCompletionData K L) :
    DirectSum (NumberFieldPlace K)
        (fun v => Additive (localRelativeBrauer K L completion v)) ≃+
      DirectSum (NumberFieldPlace K)
        (fun v => H2 (chosenUnitsRepresentation
          (K := K) (L := L) completion v)) :=
  DirectSum.congrAddEquiv fun v =>
    resizedChosen2 K L completion v

set_option synthInstance.maxHeartbeats 300000 in
-- Combining Shapiro with every local crossed-product equivalence elaborates a
-- deeply nested family of cohomology instances.
/-- Proposition VII.2.5(b), Shapiro, and local crossed products assembled as
an equivalence from completion-product `H²` to local relative Brauer groups. -/
noncomputable def directRelativeBrauer
    (completion : HasseCompletionData K L) :
    DirectSum (NumberFieldPlace K)
        (fun v => H2 (resizedPlaceRepresentation
          (K := K) (L := L) v)) ≃+
      DirectSum (NumberFieldPlace K)
        (fun v => Additive
          (localRelativeBrauer K L completion v)) :=
  (resizedDirectStabilizer
      (K := K) (L := L) completion).trans
    (brauerDirectChosen
      K L completion).symm

end

end Towers.CField.BLoc
