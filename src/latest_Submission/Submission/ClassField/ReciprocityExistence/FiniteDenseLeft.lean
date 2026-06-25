import Submission.ClassField.ReciprocityExistence.FiniteOrbitMaps

/-!
# Left dense-point calculation for finite-orbit completion naturality

This calculation is isolated from the right-hand and density arguments so
Lean can serialize and release its dependent completion elaboration state.
-/

namespace Submission.CField.RExist

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Casting the prime index carries its canonical dense embedding to the
canonical dense embedding. -/
theorem adic_cast_embedding
    {F : Type u} [Field F] [NumberField F]
    {P P' : HeightOneSpectrum (NumberField.RingOfIntegers F)}
    (h : P = P') (x : F) :
    RingEquiv.cast
        (R := fun R : HeightOneSpectrum
          (NumberField.RingOfIntegers F) => R.adicCompletion F)
        h (FinitePlace.embedding P x) =
      FinitePlace.embedding P' x := by
  subst P'
  rfl

set_option maxHeartbeats 5000000 in
-- The prime cast and the literal upper-completion embedding normalize together.
set_option maxRecDepth 100000 in
theorem chosen_embedding_left
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : K) :
    let Qw := placeUpperFactor
      (K := K) (L := L) P w
    let Q := upperPrime (K := K) (L := L) P Qw
    let hQ : Q.under (NumberField.RingOfIntegers K) = P :=
      upperPrime_under (K := K) (L := L) P Qw
    let eK := placeCompletionAdic P
    let v := (FinitePlace.mk P).val
    NIndex.coordinateExtensionHom
        (K := K) (L := L) Q
          (RingEquiv.cast hQ.symm (eK (completionEmbedding v x))) =
      FinitePlace.embedding Q (algebraMap K L x) := by
  dsimp only
  let Qw := placeUpperFactor
    (K := K) (L := L) P w
  let Q := upperPrime (K := K) (L := L) P Qw
  let hQ : Q.under (NumberField.RingOfIntegers K) = P :=
    upperPrime_under (K := K) (L := L) P Qw
  let eK := placeCompletionAdic P
  let v := (FinitePlace.mk P).val
  rw [finite_place_adic P x]
  rw [adic_cast_embedding hQ.symm x]
  exact NIndex.extension_comp_embedding
    (K := K) (L := L) Q x

end

end Submission.CField.RExist
