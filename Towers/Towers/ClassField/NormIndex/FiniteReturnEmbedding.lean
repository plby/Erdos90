import Towers.ClassField.NormIndex.FiniteReturnPrime

/-!
# Return transport on global elements

The local return-transport identity is first proved on the dense image of
the global field.  The completion-level equality is obtained from this in a
separate module by continuity.
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

/-- Two continuous functions out of a finite completion which agree on the
dense global field agree at every completed point.  Keeping the topological
argument opaque avoids forming a large equality of dependent local maps. -/
theorem adic_completion_continuous
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [TopologicalSpace E] [T2Space E]
    (f g : P.adicCompletion K → E)
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a : K, f (FinitePlace.embedding P a) =
      g (FinitePlace.embedding P a))
    (b : P.adicCompletion K) :
    f b = g b := by
  exact congrFun
    ((P.denseRange_algebraMap K).equalizer hf hg (funext h)) b

local instance finiteNormReturnEmbeddingNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance finiteNormReturnEmbeddingCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

local instance finiteNormReturnEmbeddingPretransitive
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  completion_above_pretransitive P

set_option maxHeartbeats 1000000 in
-- Return transport unfolds two dependent completion coordinates simultaneously.
set_option maxRecDepth 100000 in
/-- The return-transport identity on the dense image of the global field. -/
theorem return_transport_embedding
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (a : K) :
    letI := finitePrimeAction (K := K) (L := L)
    let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
    let Qw := placeUpperFactor (K := K) (L := L) P w
    let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
    let qw := upperPrime (K := K) (L := L) P Qw
    let q₀ := upperPrime (K := K) (L := L) P Q₀
    let hq : qw = r⁻¹ • q₀ :=
      centered_return_smul (K := K) (L := L) P w₀ w
    finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hq
          (factorExtensionHom (K := K) (L := L) P Qw
            (FinitePlace.embedding P a))) =
      factorExtensionHom (K := K) (L := L) P Q₀
        (FinitePlace.embedding P a) := by
  letI := finitePrimeAction (K := K) (L := L)
  dsimp only
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let Qw := placeUpperFactor (K := K) (L := L) P w
  let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
  let qw := upperPrime (K := K) (L := L) P Qw
  let q₀ := upperPrime (K := K) (L := L) P Q₀
  let hq : qw = r⁻¹ • q₀ :=
    centered_return_smul (K := K) (L := L) P w₀ w
  rw [show factorExtensionHom (K := K) (L := L) P Qw
        (FinitePlace.embedding P a) =
      FinitePlace.embedding qw (algebraMap K L a) by
    exact ring_comp_embedding
      (K := K) (L := L) P Qw a]
  rw [adic_completion_embedding]
  rw [place_transport_embedding]
  rw [r.commutes]
  exact (ring_comp_embedding
    (K := K) (L := L) P Q₀ a).symm

end

end Towers.CField.NIndex
