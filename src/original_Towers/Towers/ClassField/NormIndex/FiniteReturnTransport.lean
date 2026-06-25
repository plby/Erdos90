import Towers.ClassField.NormIndex.FiniteReturnEmbedding

/-!
# Return transport for finite local norms

This file proves that the chosen Galois element returning one completion
place to another also transports the corresponding finite local extension.
It is kept separate because the density argument is substantially heavier
than the finite orbit reindexing that uses it.
-/

namespace Towers.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance finiteNormReturnNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance finiteNormReturnCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

local instance finiteNormReturnPretransitive
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  completion_above_pretransitive P

private theorem continuous_cast_return
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') :
    Continuous (RingEquiv.cast
      (R := fun R => R.adicCompletion L) h) := by
  subst Q'
  exact continuous_id

private noncomputable def returnTransportSource
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
    let q₀ := upperPrime (K := K) (L := L) P Q₀
    P.adicCompletion K → q₀.adicCompletion L := by
  letI := finitePrimeAction (K := K) (L := L)
  exact fun b =>
    finitePlaceTransport (K := K)
      (completionPlaceReturn (FinitePlace.mk P).val w₀ w)
      (upperPrime (K := K) (L := L) P
        (placeUpperFactor (K := K) (L := L) P w₀))
      (RingEquiv.cast
        (centered_return_smul
          (K := K) (L := L) P w₀ w)
        (factorExtensionHom (K := K) (L := L) P
          (placeUpperFactor (K := K) (L := L) P w) b))

private noncomputable def returnTransportTarget
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    P.adicCompletion K →
      (upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w₀)).adicCompletion L :=
  fun b => factorExtensionHom (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w₀) b

set_option maxHeartbeats 1000000 in
-- The dense-image comparison retains several dependent upper-prime casts.
/-- Transporting the extension of a lower local element from `w` to `w₀`
is the extension at `w₀`.  Equality is checked directly at the requested
completed point, using the dense global field, rather than first constructing
an equality of the two large dependent functions. -/
lemma extension_return_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (b : P.adicCompletion K) :
    letI := finitePrimeAction (K := K) (L := L)
    let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
    let Qw := placeUpperFactor (K := K) (L := L) P w
    let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
    let qw := upperPrime (K := K) (L := L) P Qw
    let q₀ := upperPrime (K := K) (L := L) P Q₀
    let hq : qw = r⁻¹ • q₀ :=
      centered_return_smul (K := K) (L := L) P w₀ w
    finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers L) => R.adicCompletion L)
          hq (factorExtensionHom (K := K) (L := L) P Qw b)) =
      factorExtensionHom (K := K) (L := L) P Q₀ b := by
  letI := finitePrimeAction (K := K) (L := L)
  dsimp only
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let Qw := placeUpperFactor (K := K) (L := L) P w
  let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
  let qw := upperPrime (K := K) (L := L) P Qw
  let q₀ := upperPrime (K := K) (L := L) P Q₀
  let hq : qw = r⁻¹ • q₀ :=
    centered_return_smul (K := K) (L := L) P w₀ w
  change returnTransportSource
      (K := K) (L := L) P w₀ w b =
    returnTransportTarget (K := K) (L := L) P w₀ b
  exact adic_completion_continuous P
    (returnTransportSource (K := K) (L := L) P w₀ w)
    (returnTransportTarget (K := K) (L := L) P w₀)
    (by
      change Continuous (fun c : P.adicCompletion K =>
      finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers L) => R.adicCompletion L)
          hq (factorExtensionHom (K := K) (L := L) P Qw c)))
      exact (finite_transport_continuous (K := K) r q₀).comp
        ((continuous_cast_return hq).comp
          (factor_extension_continuous
            (K := K) (L := L) P Qw)))
    (by
      change Continuous (fun c : P.adicCompletion K =>
        factorExtensionHom (K := K) (L := L) P Q₀ c)
      exact factor_extension_continuous
        (K := K) (L := L) P Q₀)
    (fun a => return_transport_embedding
      (K := K) (L := L) P w₀ w a)
    b

end

end Towers.CField.NIndex
