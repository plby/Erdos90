import Submission.ClassField.ReciprocityExistence.FiniteDenseLeft
import Submission.ClassField.ReciprocityExistence.FiniteDenseRight

/-!
# Dense-point agreement for the two finite-orbit completion maps
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

set_option maxHeartbeats 5000000 in
-- The two separately cached dense-point calculations are composed here.
set_option maxRecDepth 100000 in
/-- Raw prime-adic form of agreement on the dense copy of `K`. -/
theorem chosen_embedding_raw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : K) :
    let Qw := placeUpperFactor
      (K := K) (L := L) P w
    let Q := upperPrime (K := K) (L := L) P Qw
    let hQ : Q.under (NumberField.RingOfIntegers K) = P :=
      upperPrime_under (K := K) (L := L) P Qw
    let eK := placeCompletionAdic P
    let eL := completionPlaceAdic (K := K) (L := L) P w
    let v := (FinitePlace.mk P).val
    NIndex.coordinateExtensionHom
        (K := K) (L := L) Q
          (RingEquiv.cast hQ.symm (eK (completionEmbedding v x))) =
      eL (completionLies v w.1 w.2
        (completionEmbedding v x)) := by
  exact (chosen_embedding_left
    (K := K) (L := L) P w x).trans
      (chosen_adic_embedding
        (K := K) (L := L) P w x)

set_option maxHeartbeats 3000000 in
-- The raw dense-point calculation is already an opaque checked theorem.
set_option maxRecDepth 100000 in
/-- The two completion embeddings agree on the dense copy of `K`. -/
theorem base_chosen_embedding
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : K) :
    baseChosenAdic
        (K := K) (L := L) P w
        (completionEmbedding (FinitePlace.mk P).val x) =
      chosenAdicDirect
        (K := K) (L := L) P w
        (completionEmbedding (FinitePlace.mk P).val x) := by
  exact chosen_embedding_raw
    (K := K) (L := L) P w x

end

end Submission.CField.RExist
