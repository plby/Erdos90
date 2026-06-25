import Towers.ClassField.ReciprocityExistence.OrbitEvaluation

/-!
# The two finite-orbit completion maps

This file constructs the literal prime-adic and canonical presentations of
the base-completion embedding, and proves both maps continuous.
-/

namespace Towers.CField.RExist

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]


/-- Extend the base completion through the literal prime-adic coordinate
selected by `w`. -/
noncomputable def baseChosenAdic
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (FinitePlace.mk P).val.Completion →+*
      (upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w)).adicCompletion L := by
  let Qw := placeUpperFactor
    (K := K) (L := L) P w
  let Q := upperPrime (K := K) (L := L) P Qw
  let hQ : Q.under (NumberField.RingOfIntegers K) = P :=
    upperPrime_under (K := K) (L := L) P Qw
  exact (NIndex.coordinateExtensionHom
      (K := K) (L := L) Q).comp
    ((RingEquiv.cast
      (R := fun R : HeightOneSpectrum
        (NumberField.RingOfIntegers K) => R.adicCompletion K)
      hQ.symm).toRingHom.comp
        (placeCompletionAdic P).toRingHom)

/-- Extend the base completion canonically and then use the prime-adic
model of the chosen upper completion. -/
noncomputable def chosenAdicDirect
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (FinitePlace.mk P).val.Completion →+*
      (upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w)).adicCompletion L :=
  (completionPlaceAdic
      (K := K) (L := L) P w).toRingHom.comp
    (completionLies (FinitePlace.mk P).val w.1 w.2)

/-- Casting a prime-adic completion along an equality is continuous. -/
private theorem continuous_adic_cast
    {F : Type u} [Field F] [NumberField F]
    {P P' : HeightOneSpectrum (NumberField.RingOfIntegers F)}
    (h : P = P') :
    Continuous (RingEquiv.cast
      (R := fun R : HeightOneSpectrum
        (NumberField.RingOfIntegers F) => R.adicCompletion F) h) := by
  subst P'
  exact continuous_id

set_option maxHeartbeats 10000000 in
-- The dependent prime cast and the two completion models elaborate together.
set_option synthInstance.maxHeartbeats 300000 in
-- The literal upper-prime index must normalize with its contraction.
set_option maxRecDepth 100000 in
/-- The literal-prime presentation of the local embedding is continuous. -/
theorem chosen_adic_continuous
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Continuous (baseChosenAdic
      (K := K) (L := L) P w) := by
  let Qw := placeUpperFactor
    (K := K) (L := L) P w
  let Q := upperPrime (K := K) (L := L) P Qw
  let hQ : Q.under (NumberField.RingOfIntegers K) = P :=
    upperPrime_under (K := K) (L := L) P Qw
  change Continuous
    ((NIndex.coordinateExtensionHom
      (K := K) (L := L) Q).comp
      ((RingEquiv.cast
        (R := fun R : HeightOneSpectrum
          (NumberField.RingOfIntegers K) => R.adicCompletion K)
        hQ.symm).toRingHom.comp
          (placeCompletionAdic P).toRingHom))
  exact (NIndex.extension_ring_continuous
    (K := K) (L := L) Q).comp
      ((continuous_adic_cast hQ.symm).comp
        (place_adic_isometry P).continuous)

set_option maxHeartbeats 3000000 in
-- The direct map composes the two canonical continuous completion maps.
/-- The canonical presentation of the local embedding is continuous. -/
theorem chosen_direct_continuous
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Continuous (chosenAdicDirect
      (K := K) (L := L) P w) := by
  exact (place_adic_continuous
    (K := K) (L := L) P w).comp
      (completion_lies_isometry
        (FinitePlace.mk P).val w.1 w.2).continuous

end


end Towers.CField.RExist
