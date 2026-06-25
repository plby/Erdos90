import Submission.ClassField.NormIndex.FiniteLocalStabilizer

/-!
# Prime coordinates for completion-place returns

The chosen Galois element returning one completion place to another carries
the finite prime centered at the source place to the prime centered at the
target place.
-/

namespace Submission.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance finiteNormReturnPrimeNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance finiteNormReturnPrimeCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

local instance finiteNormReturnPrimePretransitive
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  completion_above_pretransitive P

/-- The chosen return element carries the centered prime of `w` to the
centered prime of `w₀`. -/
theorem return_smul_centered
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
    let qw := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    let q₀ := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w₀)
    r • qw = q₀ := by
  letI := finitePrimeAction (K := K) (L := L)
  dsimp only
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let qfun := fun z : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val =>
    upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P z)
  calc
    r • qfun w = qfun (r • w) :=
      (upper_place_smul
        (K := K) (L := L) P r w).symm
    _ = qfun w₀ := congrArg qfun
      (place_return_smul (FinitePlace.mk P).val w₀ w)

/-- Source-coordinate form of
`return_smul_centered`. -/
theorem centered_return_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
    let qw := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    let q₀ := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w₀)
    qw = r⁻¹ • q₀ := by
  letI := finitePrimeAction (K := K) (L := L)
  dsimp only
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let qw := upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)
  let q₀ := upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w₀)
  have h := return_smul_centered
    (K := K) (L := L) P w₀ w
  calc
    qw = r⁻¹ • (r • qw) := (inv_smul_smul r qw).symm
    _ = r⁻¹ • q₀ := congrArg (fun q => r⁻¹ • q) h

end

end Submission.CField.NIndex
