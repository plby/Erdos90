import Submission.ClassField.NormIndex.NormCompatibility
import Submission.ClassField.NormIndex.FiniteExtensionCoordinate
import Submission.ClassField.NormIndex.FiniteIdeleReindex
import Submission.ClassField.NormIndex.FiniteProductEvaluation
import Submission.ClassField.NormIndex.FiniteOrbitReindexing
import Submission.ClassField.NormIndex.PointStabilizerTransport

/-!
# Norm compatibility of the canonical idèle extension

This file specializes the completion-product norm identity to the concrete
finite and infinite coordinates of the idèle norm, and then assembles the
coordinate equalities into

`ext (Nm x) = ∏ sigma, sigma • x`.
-/

namespace Submission.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open scoped BigOperators

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)

private theorem units_cast_pi
    {I : Type*} {R : I → Type*}
    [∀ i, Semiring (R i)]
    (x : ∀ i, (R i)ˣ) {i j : I} (h : i = j) :
    Units.map (RingEquiv.cast h).toRingHom.toMonoidHom (x i) = x j := by
  subst j
  rfl

private theorem prod_maps
    {W A C : Type*} [Fintype W] [CommMonoid A] [CommMonoid C]
    (F : A →* C) (z : A) (a : W → A) (hz : z = ∏ w, a w) :
    F z = ∏ w, F (a w) := by
  calc
    F z = F (∏ w, a w) := congrArg F hz
    _ = ∏ w, F (a w) := map_prod F a Finset.univ

/-- Transport a factorization through a monoid hom, while replacing the
transported outer factor by an equal map into the common target. -/
private theorem transport_common_target
    {H A B C : Type*} [Fintype H]
    [CommMonoid A] [CommMonoid B] [CommMonoid C]
    (F₀ : A →* C) (F : A →* B) (R : B →* C)
    (a : A) (b : H → B)
    (hreturn : R (F a) = F₀ a)
    (hlocal : F a = ∏ h, b h) :
    F₀ a = ∏ h, R (b h) := by
  calc
    F₀ a = R (F a) := hreturn.symm
    _ = R (∏ h, b h) := congrArg R hlocal
    _ = ∏ h, R (b h) := map_prod R b Finset.univ

private noncomputable def completionPlaceUpper
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    HeightOneSpectrum (NumberField.RingOfIntegers L) :=
  upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)

private noncomputable def placeIdeleRaw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    P.adicCompletion K :=
  ((finiteCompletionNorm (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
      (x.1 (completionPlaceUpper (K := K) (L := L) P w)) :
        (P.adicCompletion K)ˣ) : P.adicCompletion K)

private opaque placeIdeleData
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    {z : P.adicCompletion K //
      z = placeIdeleRaw (K := K) (L := L) P x w} :=
  ⟨placeIdeleRaw (K := K) (L := L) P x w, rfl⟩

private noncomputable def completionPlaceNorm
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    P.adicCompletion K :=
  (placeIdeleData (K := K) (L := L) P x w).1

private theorem place_idele_raw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    completionPlaceNorm (K := K) (L := L) P x w =
      placeIdeleRaw (K := K) (L := L) P x w :=
  (placeIdeleData (K := K) (L := L) P x w).2

private noncomputable def placeStabilizerRaw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w) :
    (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L := by
  letI := finitePrimeAction (K := K) (L := L)
  let qw := completionPlaceUpper (K := K) (L := L) P w
  let hfix : qw = h.1⁻¹ • qw := by
    dsimp only [qw, completionPlaceUpper]
    exact centered_upper_stabilizer
      (K := K) (L := L) P w h
  exact finitePlaceTransport (K := K) h.1 qw
    (RingEquiv.cast hfix (x.1 qw : qw.adicCompletion L))

private opaque placeStabilizerData
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w) :
    {z : (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L //
      z = placeStabilizerRaw (K := K) (L := L) P x w h} :=
  ⟨placeStabilizerRaw (K := K) (L := L) P x w h, rfl⟩

private noncomputable def placeStabilizerTerm
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w) :
    (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L :=
  (placeStabilizerData (K := K) (L := L) P x w h).1

private theorem place_stabilizer_raw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w) :
    placeStabilizerTerm (K := K) (L := L) P x w h =
      placeStabilizerRaw (K := K) (L := L) P x w h :=
  (placeStabilizerData (K := K) (L := L) P x w h).2

private noncomputable def completionPlaceRaw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    P.adicCompletion K →+*
      (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L := by
  exact factorExtensionHom (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)

private opaque completionPlaceData
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    {f : P.adicCompletion K →+*
        (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L //
      f = completionPlaceRaw (K := K) (L := L) P w} :=
  ⟨completionPlaceRaw (K := K) (L := L) P w, rfl⟩

private noncomputable def extensionRingHom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    P.adicCompletion K →+*
      (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L :=
  (completionPlaceData (K := K) (L := L) P w).1

private theorem completion_extension_raw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    extensionRingHom (K := K) (L := L) P w =
      completionPlaceRaw (K := K) (L := L) P w :=
  (completionPlaceData (K := K) (L := L) P w).2

set_option maxHeartbeats 100000 in
-- Isolate the definitional comparison with the factor-indexed embedding.
set_option maxRecDepth 100000 in
private theorem completion_place_raw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (b : P.adicCompletion K) :
    completionPlaceRaw (K := K) (L := L) P w b =
      factorExtensionHom (K := K) (L := L) P
        (placeUpperFactor (K := K) (L := L) P w) b := by
  rfl

set_option maxHeartbeats 100000 in
-- Compose the opaque-map equation with its concrete application equation.
set_option maxRecDepth 100000 in
private theorem extension_ring_hom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (b : P.adicCompletion K) :
    extensionRingHom (K := K) (L := L) P w b =
      factorExtensionHom (K := K) (L := L) P
        (placeUpperFactor (K := K) (L := L) P w) b :=
  (RingHom.congr_fun
    (completion_extension_raw
      (K := K) (L := L) P w) b).trans
    (completion_place_raw
      (K := K) (L := L) P w b)

set_option maxHeartbeats 100000 in
-- Unfold the completed norm only in this small comparison lemma.
set_option maxRecDepth 100000 in
private theorem completion_raw_algebra
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    let Q := placeUpperFactor
      (K := K) (L := L) P w
    let q := upperPrime (K := K) (L := L) P Q
    let hP : P.asIdeal.map
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot P.ne_bot
    letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
      adicFactorAlgebra
        (K := K) (L := L) P hP Q
    letI : FiniteDimensional (P.adicCompletion K) (q.adicCompletion L) :=
      finite_completion_module (K := K) (L := L) P Q
    placeIdeleRaw (K := K) (L := L) P x w =
      Algebra.norm (P.adicCompletion K) (x.1 q : q.adicCompletion L) := by
  dsimp only
  rfl

set_option maxHeartbeats 100000 in
-- Unfold one stabilizer term without exposing it in the product theorem.
set_option maxRecDepth 100000 in
private theorem stabilizer_raw_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w) :
    letI := finitePrimeAction (K := K) (L := L)
    let Q := placeUpperFactor
      (K := K) (L := L) P w
    let q := upperPrime (K := K) (L := L) P Q
    placeStabilizerRaw (K := K) (L := L) P x w h =
      finitePlaceTransport (K := K) h.1 q
        (RingEquiv.cast
          (centered_upper_stabilizer
            (K := K) (L := L) P w h)
          (x.1 q : q.adicCompletion L)) := by
  dsimp only
  rfl

set_option maxHeartbeats 100000 in
-- Package the local norm comparison behind its opaque name.
set_option maxRecDepth 100000 in
private theorem completion_place_algebra
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    let Q := placeUpperFactor
      (K := K) (L := L) P w
    let q := upperPrime (K := K) (L := L) P Q
    let hP : P.asIdeal.map
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot P.ne_bot
    letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
      adicFactorAlgebra
        (K := K) (L := L) P hP Q
    letI : FiniteDimensional (P.adicCompletion K) (q.adicCompletion L) :=
      finite_completion_module (K := K) (L := L) P Q
    completionPlaceNorm (K := K) (L := L) P x w =
      Algebra.norm (P.adicCompletion K) (x.1 q : q.adicCompletion L) :=
  (place_idele_raw
    (K := K) (L := L) P x w).trans
    (completion_raw_algebra
      (K := K) (L := L) P w x)

set_option maxHeartbeats 100000 in
-- Package one stabilizer transport behind its opaque name.
set_option maxRecDepth 100000 in
private theorem place_stabilizer_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w) :
    letI := finitePrimeAction (K := K) (L := L)
    let Q := placeUpperFactor
      (K := K) (L := L) P w
    let q := upperPrime (K := K) (L := L) P Q
    placeStabilizerTerm (K := K) (L := L) P x w h =
      finitePlaceTransport (K := K) h.1 q
        (RingEquiv.cast
          (centered_upper_stabilizer
            (K := K) (L := L) P w h)
          (x.1 q : q.adicCompletion L)) :=
  (place_stabilizer_raw
    (K := K) (L := L) P x w h).trans
    (stabilizer_raw_transport
      (K := K) (L := L) P w x h)

private noncomputable def globalTransportRaw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (sigma : Gal(L/K)) :
    (completionPlaceUpper (K := K) (L := L) P w₀).adicCompletion L := by
  letI := finitePrimeAction (K := K) (L := L)
  let q₀ := completionPlaceUpper (K := K) (L := L) P w₀
  exact finitePlaceTransport (K := K) sigma q₀
    (x.1 (sigma⁻¹ • q₀) : (sigma⁻¹ • q₀).adicCompletion L)

private opaque globalTransportData
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (sigma : Gal(L/K)) :
    {z : (completionPlaceUpper (K := K) (L := L) P w₀).adicCompletion L //
      z = globalTransportRaw
        (K := K) (L := L) P w₀ x sigma} :=
  ⟨globalTransportRaw
    (K := K) (L := L) P w₀ x sigma, rfl⟩

private noncomputable def globalPlaceTransport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (sigma : Gal(L/K)) :
    (completionPlaceUpper (K := K) (L := L) P w₀).adicCompletion L :=
  (globalTransportData
    (K := K) (L := L) P w₀ x sigma).1

private theorem global_transport_raw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (sigma : Gal(L/K)) :
    globalPlaceTransport (K := K) (L := L) P w₀ x sigma =
      globalTransportRaw
        (K := K) (L := L) P w₀ x sigma :=
  (globalTransportData
    (K := K) (L := L) P w₀ x sigma).2

set_option maxHeartbeats 100000 in
-- Expose the concrete transport only at the final coordinate boundary.
set_option maxRecDepth 100000 in
private theorem global_transport_term
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (sigma : Gal(L/K)) :
    letI := finitePrimeAction (K := K) (L := L)
    let Q₀ := placeUpperFactor
      (K := K) (L := L) P w₀
    let q₀ := upperPrime (K := K) (L := L) P Q₀
    globalPlaceTransport (K := K) (L := L) P w₀ x sigma =
      finitePlaceTransport (K := K) sigma q₀
        (x.1 (sigma⁻¹ • q₀) : (sigma⁻¹ • q₀).adicCompletion L) := by
  rw [global_transport_raw]
  rfl

set_option maxHeartbeats 100000 in
-- The local norm formula before transporting its factors to the chosen place.
set_option maxRecDepth 100000 in
private theorem extension_stabilizer_terms
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI : Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
      Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    extensionRingHom (K := K) (L := L) P w
        (completionPlaceNorm (K := K) (L := L) P x w) =
      ∏ h : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        placeStabilizerTerm (K := K) (L := L) P x w h := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Fintype (CompletionPlaceStabilizer v w) :=
    Fintype.ofFinite (CompletionPlaceStabilizer v w)
  let Q := placeUpperFactor (K := K) (L := L) P w
  let q := upperPrime (K := K) (L := L) P Q
  let hP : P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  letI : FiniteDimensional (P.adicCompletion K) (q.adicCompletion L) :=
    finite_completion_module (K := K) (L := L) P Q
  rw [extension_ring_hom]
  rw [completion_place_algebra]
  simp_rw [place_stabilizer_transport]
  exact extension_algebra_stabilizer
    (K := K) (L := L) P w (x.1 q : q.adicCompletion L)


set_option maxHeartbeats 500000 in
-- One returned stabilizer factor is the global Galois factor indexed by the
-- product of the return element and the stabilizer element.
set_option maxRecDepth 100000 in
private theorem returned_global_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
    let Qw := placeUpperFactor (K := K) (L := L) P w
    let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
    let qw := upperPrime (K := K) (L := L) P Qw
    let q₀ := upperPrime (K := K) (L := L) P Q₀
    let hreturn : qw = r⁻¹ • q₀ :=
      centered_return_smul (K := K) (L := L) P w₀ w
    finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn
          (placeStabilizerTerm (K := K) (L := L) P x w h)) =
      globalPlaceTransport (K := K) (L := L) P w₀ x (r * h.1) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  dsimp only
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let Qw := placeUpperFactor (K := K) (L := L) P w
  let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
  let qw := upperPrime (K := K) (L := L) P Qw
  let q₀ := upperPrime (K := K) (L := L) P Q₀
  let hreturn : qw = r⁻¹ • q₀ :=
    centered_return_smul (K := K) (L := L) P w₀ w
  let hfix : qw = h.1⁻¹ • qw :=
    centered_upper_stabilizer
      (K := K) (L := L) P w h
  have hpoint := transport_point_stabilizer
    (K := K) (L := L) P w₀ w h
      (fun R => (x.1 R : R.adicCompletion L))
  dsimp only at hpoint
  calc
    finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn
          (placeStabilizerTerm (K := K) (L := L) P x w h)) =
      finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn
          (finitePlaceTransport (K := K) h.1 qw
            (RingEquiv.cast hfix (x.1 qw : qw.adicCompletion L)))) :=
      congrArg (fun z => finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn z))
        (place_stabilizer_transport
          (K := K) (L := L) P w x h)
    _ = finitePlaceTransport (K := K) (r * h.1) q₀
        (x.1 ((r * h.1)⁻¹ • q₀) :
          ((r * h.1)⁻¹ • q₀).adicCompletion L) :=
      hpoint
    _ = globalPlaceTransport (K := K) (L := L) P w₀ x (r * h.1) :=
      (global_transport_term
        (K := K) (L := L) P w₀ x (r * h.1)).symm






private noncomputable def returnMonoidRaw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L →*
      (completionPlaceUpper (K := K) (L := L) P w₀).adicCompletion L := by
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let hreturn : completionPlaceUpper (K := K) (L := L) P w =
      r⁻¹ • completionPlaceUpper (K := K) (L := L) P w₀ := by
    dsimp only [completionPlaceUpper]
    exact centered_return_smul
      (K := K) (L := L) P w₀ w
  exact
    { toFun := fun z => finitePlaceTransport (K := K) r
        (completionPlaceUpper (K := K) (L := L) P w₀)
        (RingEquiv.cast hreturn z)
      map_one' := by rw [map_one, map_one]
      map_mul' := by
        intro a b
        rw [map_mul, map_mul] }

private opaque returnMonoidData
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    {f : (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L →*
        (completionPlaceUpper (K := K) (L := L) P w₀).adicCompletion L //
      f = returnMonoidRaw (K := K) (L := L) P w₀ w} :=
  ⟨returnMonoidRaw (K := K) (L := L) P w₀ w, rfl⟩

private noncomputable def returnMonoidHom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L →*
      (completionPlaceUpper (K := K) (L := L) P w₀).adicCompletion L :=
  (returnMonoidData (K := K) (L := L) P w₀ w).1

private theorem completion_return_monoid
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    returnMonoidHom (K := K) (L := L) P w₀ w =
      returnMonoidRaw (K := K) (L := L) P w₀ w :=
  (returnMonoidData (K := K) (L := L) P w₀ w).2

set_option maxHeartbeats 100000 in
-- Compare one application of the opaque return map with its raw map.
set_option maxRecDepth 100000 in
private theorem return_monoid_raw
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (z : (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L) :
    returnMonoidHom (K := K) (L := L) P w₀ w z =
      returnMonoidRaw (K := K) (L := L) P w₀ w z :=
  congrArg (fun f => f z)
    (completion_return_monoid (K := K) (L := L) P w₀ w)

set_option maxHeartbeats 500000 in
-- Expose the concrete return transport only from the raw map.
set_option maxRecDepth 100000 in
private theorem place_return_monoid
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (z : (completionPlaceUpper (K := K) (L := L) P w).adicCompletion L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
    let hreturn : completionPlaceUpper (K := K) (L := L) P w =
        r⁻¹ • completionPlaceUpper (K := K) (L := L) P w₀ := by
      dsimp only [completionPlaceUpper]
      exact centered_return_smul
        (K := K) (L := L) P w₀ w
    returnMonoidRaw (K := K) (L := L) P w₀ w z =
      finitePlaceTransport (K := K) r
        (completionPlaceUpper (K := K) (L := L) P w₀)
        (RingEquiv.cast hreturn z) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  dsimp only
  rfl

set_option maxHeartbeats 500000 in
-- Return the factor embedding at a completion place to the chosen base point.
set_option maxRecDepth 100000 in
private theorem factor_extension_returned
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    factorExtensionHom (K := K) (L := L) P
        (placeUpperFactor (K := K) (L := L) P w₀)
        (completionPlaceNorm (K := K) (L := L) P x w) =
      returnMonoidHom (K := K) (L := L) P w₀ w
        (factorExtensionHom (K := K) (L := L) P
          (placeUpperFactor (K := K) (L := L) P w)
          (completionPlaceNorm (K := K) (L := L) P x w)) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let Qw := placeUpperFactor (K := K) (L := L) P w
  let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
  let qw := completionPlaceUpper (K := K) (L := L) P w
  let q₀ := completionPlaceUpper (K := K) (L := L) P w₀
  let hreturn : qw = r⁻¹ • q₀ := by
    dsimp only [qw, q₀, completionPlaceUpper]
    exact centered_return_smul
      (K := K) (L := L) P w₀ w
  calc
    _ = finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn
          (factorExtensionHom (K := K) (L := L) P Qw
            (completionPlaceNorm (K := K) (L := L) P x w))) :=
      (extension_return_transport
        (K := K) (L := L) P w₀ w
          (completionPlaceNorm (K := K) (L := L) P x w)).symm
    _ = returnMonoidRaw (K := K) (L := L) P w₀ w
        (factorExtensionHom (K := K) (L := L) P Qw
          (completionPlaceNorm (K := K) (L := L) P x w)) :=
      (place_return_monoid
        (K := K) (L := L) P w₀ w _).symm
    _ = returnMonoidHom (K := K) (L := L) P w₀ w
        (factorExtensionHom (K := K) (L := L) P Qw
          (completionPlaceNorm (K := K) (L := L) P x w)) :=
      (return_monoid_raw
        (K := K) (L := L) P w₀ w _).symm

set_option maxHeartbeats 100000 in
-- Replace the concrete factor embedding by its completion-place wrapper.
set_option maxRecDepth 100000 in
private theorem returned_extension_named
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    returnMonoidHom (K := K) (L := L) P w₀ w
      (factorExtensionHom (K := K) (L := L) P
        (placeUpperFactor (K := K) (L := L) P w)
        (completionPlaceNorm (K := K) (L := L) P x w)) =
      returnMonoidHom (K := K) (L := L) P w₀ w
        (extensionRingHom
        (K := K) (L := L) P w
          (completionPlaceNorm (K := K) (L := L) P x w)) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  exact congrArg (returnMonoidHom (K := K) (L := L) P w₀ w)
    (extension_ring_hom
    (K := K) (L := L) P w _).symm

set_option maxHeartbeats 100000 in
-- Apply the return map to the already-named centered factorization.
set_option maxRecDepth 100000 in
private theorem returned_named_terms
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    letI : Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
      Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    returnMonoidHom (K := K) (L := L) P w₀ w
      (extensionRingHom
        (K := K) (L := L) P w
          (completionPlaceNorm (K := K) (L := L) P x w)) =
      returnMonoidHom (K := K) (L := L) P w₀ w
        (∏ h : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        placeStabilizerTerm (K := K) (L := L) P x w h) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  letI : Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
    Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
  exact congrArg (returnMonoidHom (K := K) (L := L) P w₀ w)
    (extension_stabilizer_terms
    (K := K) (L := L) P w x)

set_option maxHeartbeats 100000 in
-- Distribute the return monoid hom over the finite stabilizer product.
set_option maxRecDepth 100000 in
private theorem returned_stabilizer_terms
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    letI : Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
      Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    returnMonoidHom (K := K) (L := L) P w₀ w
      (∏ h : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        placeStabilizerTerm (K := K) (L := L) P x w h) =
      ∏ h : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        returnMonoidHom (K := K) (L := L) P w₀ w
          (placeStabilizerTerm (K := K) (L := L) P x w h) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  letI : Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
    Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
  exact map_prod (returnMonoidHom (K := K) (L := L) P w₀ w)
    _ Finset.univ

set_option maxHeartbeats 500000 in
-- Identify one opaque returned factor with its global Galois-coordinate term.
set_option maxRecDepth 100000 in
private theorem returned_stabilizer_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    returnMonoidHom (K := K) (L := L) P w₀ w
        (placeStabilizerTerm (K := K) (L := L) P x w h) =
      globalPlaceTransport (K := K) (L := L) P w₀ x
        (completionPlaceReturn (FinitePlace.mk P).val w₀ w * h.1) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let qw := completionPlaceUpper (K := K) (L := L) P w
  let q₀ := completionPlaceUpper (K := K) (L := L) P w₀
  let hreturn : qw = r⁻¹ • q₀ := by
    dsimp only [qw, q₀, completionPlaceUpper]
    exact centered_return_smul
      (K := K) (L := L) P w₀ w
  calc
    _ = returnMonoidRaw (K := K) (L := L) P w₀ w
        (placeStabilizerTerm (K := K) (L := L) P x w h) :=
      return_monoid_raw
        (K := K) (L := L) P w₀ w _
    _ = finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn
          (placeStabilizerTerm (K := K) (L := L) P x w h)) :=
      place_return_monoid
        (K := K) (L := L) P w₀ w _
    _ = _ := returned_global_transport
      (K := K) (L := L) P w₀ w h x

set_option maxHeartbeats 100000 in
-- Replace each returned stabilizer factor by its global Galois-coordinate term.
set_option maxRecDepth 100000 in
private theorem returned_stabilizer_global
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    letI : Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
      Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    (∏ h : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        returnMonoidHom (K := K) (L := L) P w₀ w
          (placeStabilizerTerm (K := K) (L := L) P x w h)) =
      ∏ h : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        globalPlaceTransport (K := K) (L := L) P w₀ x
          (completionPlaceReturn (FinitePlace.mk P).val w₀ w * h.1) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  letI : Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
    Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
  apply Finset.prod_congr rfl
  intro h _
  exact returned_stabilizer_transport
    (K := K) (L := L) P w₀ w h x

set_option maxHeartbeats 500000 in
-- Assemble the small return-map equalities for one completion place.
set_option maxRecDepth 100000 in
private theorem extension_global_terms
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    letI : Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
      Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
    factorExtensionHom (K := K) (L := L) P Q₀
        (completionPlaceNorm (K := K) (L := L) P x w) =
      ∏ h : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        globalPlaceTransport (K := K) (L := L) P w₀ x
          (completionPlaceReturn (FinitePlace.mk P).val w₀ w * h.1) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  letI : Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
    Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)
  calc
    _ = returnMonoidHom (K := K) (L := L) P w₀ w
        (factorExtensionHom (K := K) (L := L) P
          (placeUpperFactor (K := K) (L := L) P w)
        (completionPlaceNorm (K := K) (L := L) P x w)) :=
      factor_extension_returned
        (K := K) (L := L) P w₀ w x
    _ = returnMonoidHom (K := K) (L := L) P w₀ w
        (extensionRingHom
        (K := K) (L := L) P w
          (completionPlaceNorm (K := K) (L := L) P x w)) :=
      returned_extension_named
        (K := K) (L := L) P w₀ w x
    _ = returnMonoidHom (K := K) (L := L) P w₀ w
        (∏ h : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        placeStabilizerTerm (K := K) (L := L) P x w h) :=
      returned_named_terms
        (K := K) (L := L) P w₀ w x
    _ = ∏ h : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        returnMonoidHom (K := K) (L := L) P w₀ w
          (placeStabilizerTerm (K := K) (L := L) P x w h) :=
      returned_stabilizer_terms
        (K := K) (L := L) P w₀ w x
    _ = _ := returned_stabilizer_global
      (K := K) (L := L) P w₀ w x

set_option maxHeartbeats 300000 in
-- Map the named completion-place norms through the chosen factor embedding.
set_option maxRecDepth 100000 in
private theorem factor_extension_norms
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    let v := (FinitePlace.mk P).val
    let W := CompletionPlacesAbove (L := L) v
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Finite W := absolute_extensions_separable v
    letI : Fintype W := Fintype.ofFinite W
    let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
    factorExtensionHom (K := K) (L := L) P Q₀
        (((finiteNorm (K := K) (L := L) P x :
          (P.adicCompletion K)ˣ) : P.adicCompletion K)) =
      ∏ w : W, factorExtensionHom (K := K) (L := L) P Q₀
        (completionPlaceNorm (K := K) (L := L) P x w) := by
  classical
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite W := absolute_extensions_separable v
  letI : Fintype W := Fintype.ofFinite W
  let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
  apply prod_maps
    (factorExtensionHom (K := K) (L := L) P Q₀).toMonoidHom
    (((finiteNorm (K := K) (L := L) P x :
      (P.adicCompletion K)ˣ) : P.adicCompletion K))
    (fun w => completionPlaceNorm (K := K) (L := L) P x w)
  simp_rw [place_idele_raw]
  simpa only [placeIdeleRaw, completionPlaceUpper] using
    (idele_coe_places
      (K := K) (L := L) P x)


set_option maxHeartbeats 1000000 in
-- Multiply the directly transported local formulas and reindex the resulting
-- point-stabilizer product by the global Galois group.
set_option maxRecDepth 100000 in
private theorem norms_global_terms
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    let v := (FinitePlace.mk P).val
    let W := CompletionPlacesAbove (L := L) v
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Finite W := absolute_extensions_separable v
    letI : Fintype W := Fintype.ofFinite W
    letI : Nonempty W :=
      absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K) W :=
      completion_above_pretransitive P
    letI (w : W) : Fintype (CompletionPlaceStabilizer v w) :=
      Fintype.ofFinite (CompletionPlaceStabilizer v w)
    let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
    (∏ w : W, factorExtensionHom (K := K) (L := L) P Q₀
        (completionPlaceNorm (K := K) (L := L) P x w)) =
      ∏ sigma : Gal(L/K),
        globalPlaceTransport (K := K) (L := L) P w₀ x sigma := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite W := absolute_extensions_separable v
  letI : Fintype W := Fintype.ofFinite W
  letI : Nonempty W :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI (w : W) : Fintype (CompletionPlaceStabilizer v w) :=
    Fintype.ofFinite (CompletionPlaceStabilizer v w)
  let Q₀ := placeUpperFactor (K := K) (L := L) P w₀
  let orbitEquiv := placePointStabilizer
    (K := K) (L := L) v w₀
  calc
    _ = ∏ w : W, ∏ h : CompletionPlaceStabilizer v w,
        globalPlaceTransport (K := K) (L := L) P w₀ x
          (completionPlaceReturn v w₀ w * h.1) := by
      apply Finset.prod_congr rfl
      intro w _
      exact extension_global_terms
        (K := K) (L := L) P w₀ w x
    _ = ∏ p : PlacePointStabilizers (K := K) (L := L) v,
        globalPlaceTransport (K := K) (L := L) P w₀ x
          (orbitEquiv p) := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro w _
      apply Finset.prod_congr rfl
      intro h _
      rfl
    _ = ∏ sigma : Gal(L/K),
        globalPlaceTransport (K := K) (L := L) P w₀ x sigma :=
      Fintype.prod_equiv orbitEquiv _ _ (fun _ => rfl)

private theorem extension_transport_coe
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    let Q₀ := placeUpperFactor
      (K := K) (L := L) P w₀
    let q₀ := upperPrime (K := K) (L := L) P Q₀
    factorExtensionHom (K := K) (L := L) P Q₀
        (((finiteNorm (K := K) (L := L) P x :
          (P.adicCompletion K)ˣ) : P.adicCompletion K)) =
      ∏ sigma : Gal(L/K),
        finitePlaceTransport (K := K) sigma q₀
          (x.1 (sigma⁻¹ • q₀) : (sigma⁻¹ • q₀).adicCompletion L) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  dsimp only
  simp_rw [← global_transport_term
    (K := K) (L := L) P w₀ x]
  exact (factor_extension_norms
    (K := K) (L := L) P w₀ x).trans
      (norms_global_terms
        (K := K) (L := L) P w₀ x)

set_option maxHeartbeats 300000 in
-- Keeping the ring-valued calculation opaque makes the final units extensionality
-- step inexpensive for the kernel.
set_option maxRecDepth 100000 in
/-- Finite-coordinate norm compatibility, initially centered at a normalized
completion place above the base prime. -/
theorem extension_idele_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    let Q₀ := placeUpperFactor
      (K := K) (L := L) P w₀
    let q₀ := upperPrime (K := K) (L := L) P Q₀
    factorMonoidHom (K := K) (L := L) P Q₀
        (finiteNorm (K := K) (L := L) P x) =
      ∏ sigma : Gal(L/K),
        Units.map
          (finitePlaceTransport (K := K) sigma q₀).toRingHom.toMonoidHom
          (x.1 (sigma⁻¹ • q₀)) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  dsimp only
  apply Units.ext
  rw [Units.coe_prod]
  exact extension_transport_coe
    (K := K) (L := L) P w₀ x

/-- Finite-coordinate norm compatibility at an arbitrary upper prime
factor. -/
theorem factor_extension_norm
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q₀ : UpperPrimeFactors (K := K) (L := L) P)
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    let q₀ := upperPrime (K := K) (L := L) P Q₀
    factorMonoidHom (K := K) (L := L) P Q₀
        (finiteNorm (K := K) (L := L) P x) =
      ∏ sigma : Gal(L/K),
        Units.map
          (finitePlaceTransport (K := K) sigma q₀).toRingHom.toMonoidHom
          (x.1 (sigma⁻¹ • q₀)) := by
  letI := finitePrimeAction (K := K) (L := L)
  let w₀ := (placesAboveFactors
    (K := K) (L := L) P).symm Q₀
  have hw : placeUpperFactor
      (K := K) (L := L) P w₀ = Q₀ := by
    exact place_upper_symm
      (K := K) (L := L) P Q₀
  rw [← hw]
  exact extension_idele_transport
    (K := K) (L := L) P w₀ x

set_option maxHeartbeats 1000000 in
-- The prime-factor model is changed to the literal height-one prime used by
-- finite idèles; all dependent coordinates reduce after the prime equality.
set_option maxRecDepth 100000 in
/-- Literal finite-coordinate form of norm compatibility. -/
theorem extension_idele_norm
    (Q₀ : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    extensionMonoidHom (K := K) (L := L) Q₀
        (finiteNorm (K := K) (L := L)
          (Q₀.under (NumberField.RingOfIntegers K)) x) =
      ∏ sigma : Gal(L/K),
        Units.map
          (finitePlaceTransport (K := K) sigma Q₀).toRingHom.toMonoidHom
          (x.1 (sigma⁻¹ • Q₀)) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  let P := Q₀.under (NumberField.RingOfIntegers K)
  let Q := upperPrimeFactor (K := K) (L := L) Q₀
  let hQ := upper_prime_factor (K := K) (L := L) Q₀
  rw [extension_monoid_hom]
  rw [factor_extension_norm]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro sigma _
  exact units_cast_pi
    (fun R : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
      Units.map
        (finitePlaceTransport (K := K) sigma R).toRingHom.toMonoidHom
        (x.1 (sigma⁻¹ • R))) hQ

set_option synthInstance.maxHeartbeats 200000 in
-- The finite restricted-product action unfolds transported completion
-- instances when elaborating the product action.
/-- Norm compatibility on the finite restricted product. -/
theorem idele_extension_norm
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := finiteIdelesAction (K := K) (L := L)
    ideleMonoidHom (K := K) (L := L)
        (finiteIdeleNorm (K := K) (L := L) x) =
      ∏ sigma : Gal(L/K), sigma • x := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  apply RestrictedProduct.ext
  intro Q₀
  change (ideleMonoidHom (K := K) (L := L)
      (finiteIdeleNorm (K := K) (L := L) x)).1 Q₀ = _
  rw [idele_monoid_hom, finite_idele_norm]
  rw [extension_idele_norm]
  calc
    (∏ sigma : Gal(L/K),
        Units.map
          (finitePlaceTransport (K := K) sigma Q₀).toRingHom.toMonoidHom
          (x.1 (sigma⁻¹ • Q₀))) =
        ∏ sigma : Gal(L/K), (sigma • x).1 Q₀ := by
      apply Finset.prod_congr rfl
      intro sigma _
      exact (ideles_action_coordinate
        (K := K) (L := L) sigma x Q₀).symm
    _ = (∏ sigma : Gal(L/K), sigma • x).1 Q₀ :=
      (finite_idele_prod (L := L)
        (fun sigma : Gal(L/K) => sigma • x) Q₀).symm

end

end Submission.CField.NIndex
