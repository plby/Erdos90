import Towers.ClassField.NormIndex.FiniteOrbitReindexing

/-!
# Reindexing the finite idèle norm by completion places
-/

namespace Towers.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open scoped BigOperators

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The defining factor-indexed finite idèle norm, reindexed by completion
places above the base finite place. -/
theorem idele_coe_places
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    let v := (FinitePlace.mk P).val
    let W := CompletionPlacesAbove (L := L) v
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Finite W := absolute_extensions_separable v
    letI : Fintype W := Fintype.ofFinite W
    let Q := fun w : W =>
      placeUpperFactor (K := K) (L := L) P w
    (((finiteNorm (K := K) (L := L) P x :
        (P.adicCompletion K)ˣ) : P.adicCompletion K)) =
      ∏ w : W, (finiteCompletionNorm (K := K) (L := L) P (Q w)
        (x.1 (upperPrime (K := K) (L := L) P (Q w))) :
          P.adicCompletion K) := by
  classical
  dsimp only
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite W := absolute_extensions_separable v
  letI : Fintype W := Fintype.ofFinite W
  let eW := placesAboveFactors
    (K := K) (L := L) P
  change (↑(∏ Q' : UpperPrimeFactors (K := K) (L := L) P,
      finiteCompletionNorm (K := K) (L := L) P Q'
        (x.1 (upperPrime (K := K) (L := L) P Q'))) :
          P.adicCompletion K) = _
  rw [Units.coe_prod]
  symm
  exact Fintype.prod_equiv eW _ _ (fun _ => rfl)

end

end Towers.CField.NIndex
