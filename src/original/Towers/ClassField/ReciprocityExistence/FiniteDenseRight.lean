import Towers.ClassField.ReciprocityExistence.FiniteOrbitMaps

/-!
# Right dense-point calculation for finite-orbit completion naturality

This calculation is isolated so its completion-place transports are cached
before the two sides are assembled.
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

set_option maxHeartbeats 5000000 in
-- The absolute-value and prime-adic completion embeddings normalize together.
set_option maxRecDepth 100000 in
theorem chosen_adic_embedding
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : K) :
    let Qw := placeUpperFactor
      (K := K) (L := L) P w
    let Q := upperPrime (K := K) (L := L) P Qw
    let eL := completionPlaceAdic (K := K) (L := L) P w
    let v := (FinitePlace.mk P).val
    FinitePlace.embedding Q (algebraMap K L x) =
      eL (completionLies v w.1 w.2
        (completionEmbedding v x)) := by
  dsimp only
  let Qw := placeUpperFactor
    (K := K) (L := L) P w
  let Q := upperPrime (K := K) (L := L) P Qw
  let eL := completionPlaceAdic (K := K) (L := L) P w
  let v := (FinitePlace.mk P).val
  rw [← place_adic_embedding
    (K := K) (L := L) P w (algebraMap K L x)]
  exact congrArg eL (RingHom.congr_fun
    (completion_lies_comp v w.1 w.2) x).symm

end

end Towers.CField.RExist
