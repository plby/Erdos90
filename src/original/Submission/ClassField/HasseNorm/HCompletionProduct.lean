import Submission.ClassField.HasseNorm.InfiniteCompletionPlaces

/-!
# The idèle `H²` completion-product decomposition

This file identifies the prime-adic finite-place model occurring in the
finite-stage limit with the normalized absolute-value completion product.
It then combines the finite and infinite summands to finish Proposition
VII.2.5(b) in degree two.
-/

namespace Submission.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

private theorem continuous_completion_cast
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') :
    Continuous (RingEquiv.cast
      (R := fun R : HeightOneSpectrum
        (NumberField.RingOfIntegers L) => R.adicCompletion L) h) := by
  subst Q'
  exact continuous_id

private theorem adic_completion_cast
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') (x : L) :
    RingEquiv.cast
        (R := fun R : HeightOneSpectrum
          (NumberField.RingOfIntegers L) => R.adicCompletion L) h
        (FinitePlace.embedding Q x) =
      FinitePlace.embedding Q' x := by
  subst Q'
  rfl

private noncomputable def completionCenteredPrime
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    HeightOneSpectrum (NumberField.RingOfIntegers L) :=
  upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)

private theorem completion_centered_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    completionCenteredPrime (K := K) (L := L) P (sigma • w) =
      sigma • completionCenteredPrime (K := K) (L := L) P w :=
  upper_place_smul
    (K := K) (L := L) P sigma w

private noncomputable def finiteAdicTransport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    (sigma⁻¹ • w).1.Completion →
      (completionCenteredPrime (K := K) (L := L) P w).adicCompletion L := by
  letI := finitePrimeAction (K := K) (L := L)
  exact fun y =>
    completionPlaceAdic (K := K) (L := L) P w
      (completionTransport sigma w.1 y)

private noncomputable def completionAdicTransport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    (sigma⁻¹ • w).1.Completion →
      (completionCenteredPrime (K := K) (L := L) P w).adicCompletion L := by
  letI := finitePrimeAction (K := K) (L := L)
  exact fun y =>
    finitePlaceTransport (K := K) sigma
      (completionCenteredPrime (K := K) (L := L) P w)
      (RingEquiv.cast
        (completion_centered_smul
          (K := K) (L := L) P sigma⁻¹ w)
        (completionPlaceAdic
          (K := K) (L := L) P (sigma⁻¹ • w) y))

private theorem adic_transport_embedding
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : L) :
    letI := finitePrimeAction (K := K) (L := L)
    completionPlaceAdic (K := K) (L := L) P w
        (completionTransport sigma w.1
          (completionEmbedding (sigma⁻¹ • w).1 x)) =
      finitePlaceTransport (K := K) sigma
        (completionCenteredPrime (K := K) (L := L) P w)
        (RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers L) => R.adicCompletion L)
          (completion_centered_smul
            (K := K) (L := L) P sigma⁻¹ w)
          (completionPlaceAdic
            (K := K) (L := L) P (sigma⁻¹ • w)
              (completionEmbedding (sigma⁻¹ • w).1 x))) := by
  letI := finitePrimeAction (K := K) (L := L)
  have htransport : completionTransport sigma w.1
      (completionEmbedding (sigma⁻¹ • w).1 x) =
        completionEmbedding w.1 (sigma x) := by
    simpa only [places_above_val] using
      completion_transport_embedding sigma w.1 x
  rw [htransport]
  rw [place_adic_embedding]
  rw [place_adic_embedding]
  let q := completionCenteredPrime (K := K) (L := L) P w
  let q' := completionCenteredPrime (K := K) (L := L) P (sigma⁻¹ • w)
  let hq : q' = sigma⁻¹ • q :=
    completion_centered_smul (K := K) (L := L) P sigma⁻¹ w
  change FinitePlace.embedding q (sigma x) =
    finitePlaceTransport (K := K) sigma q
      (RingEquiv.cast hq (FinitePlace.embedding q' x))
  rw [adic_completion_cast hq x, place_transport_embedding]

private theorem place_transport_continuous
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    Continuous (fun y : (sigma⁻¹ • w).1.Completion =>
      completionPlaceAdic (K := K) (L := L) P w
        (completionTransport sigma w.1 y)) := by
  letI := finitePrimeAction (K := K) (L := L)
  exact (place_adic_continuous
    (K := K) (L := L) P w).comp
      (completionTransport_isometry sigma w.1).continuous

private theorem adic_transport_continuous
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    Continuous (fun y : (sigma⁻¹ • w).1.Completion =>
      finitePlaceTransport (K := K) sigma
        (completionCenteredPrime (K := K) (L := L) P w)
        (RingEquiv.cast
          (completion_centered_smul
            (K := K) (L := L) P sigma⁻¹ w)
          (completionPlaceAdic
            (K := K) (L := L) P (sigma⁻¹ • w) y))) := by
  letI := finitePrimeAction (K := K) (L := L)
  exact (finite_transport_continuous (K := K) sigma
    (completionCenteredPrime (K := K) (L := L) P w)).comp
      ((continuous_completion_cast
        (completion_centered_smul
          (K := K) (L := L) P sigma⁻¹ w)).comp
        (place_adic_continuous
          (K := K) (L := L) P (sigma⁻¹ • w)))

private theorem continuous_maps_range
    {A B D : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
    (i : D → A) (hi : DenseRange i) (f g : A → B)
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, f (i x) = g (i x)) (a : A) :
    f a = g a :=
  congrFun (hi.equalizer hf hg (funext h)) a

set_option maxHeartbeats 300000 in
-- Pointwise compatibility of the two completion transports uses density and
-- continuity across dependent completion models.
private theorem adic_transport_pointwise
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (z : (sigma⁻¹ • w).1.Completion) :
    letI := finitePrimeAction (K := K) (L := L)
    finiteAdicTransport (K := K) (L := L) P sigma w z =
      completionAdicTransport
        (K := K) (L := L) P sigma w z := by
  letI := finitePrimeAction (K := K) (L := L)
  apply continuous_maps_range
    (i := completionEmbedding (sigma⁻¹ • w).1)
    (hi := dense_range_embedding (sigma⁻¹ • w).1)
    (f := finiteAdicTransport
      (K := K) (L := L) P sigma w)
    (g := completionAdicTransport
      (K := K) (L := L) P sigma w) (a := z)
  · change Continuous (fun y : (sigma⁻¹ • w).1.Completion =>
      completionPlaceAdic (K := K) (L := L) P w
        (completionTransport sigma w.1 y))
    exact place_transport_continuous
      (K := K) (L := L) P sigma w
  · change Continuous (fun y : (sigma⁻¹ • w).1.Completion =>
      finitePlaceTransport (K := K) sigma
        (completionCenteredPrime (K := K) (L := L) P w)
        (RingEquiv.cast
          (completion_centered_smul
            (K := K) (L := L) P sigma⁻¹ w)
          (completionPlaceAdic
            (K := K) (L := L) P (sigma⁻¹ • w) y)))
    exact adic_transport_continuous
      (K := K) (L := L) P sigma w
  · intro x
    change completionPlaceAdic (K := K) (L := L) P w
        (completionTransport sigma w.1
          (completionEmbedding (sigma⁻¹ • w).1 x)) = _
    exact adic_transport_embedding
      (K := K) (L := L) P sigma w x

/-- The normalized completion transport at a finite place agrees with the
prime-adic transport at its centered upper prime. -/
theorem place_adic_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (z : (sigma⁻¹ • w).1.Completion) :
    letI := finitePrimeAction (K := K) (L := L)
    let q := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    let q' := upperPrime (K := K) (L := L) P
      (placeUpperFactor
        (K := K) (L := L) P (sigma⁻¹ • w))
    let hq : q' = sigma⁻¹ • q :=
      upper_place_smul
        (K := K) (L := L) P sigma⁻¹ w
    completionPlaceAdic (K := K) (L := L) P w
        (completionFamilyTransport (FinitePlace.mk P).val sigma w z) =
      finitePlaceTransport (K := K) sigma q
        (RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers L) => R.adicCompletion L)
          hq
          (completionPlaceAdic
            (K := K) (L := L) P (sigma⁻¹ • w) z)) := by
  letI := finitePrimeAction (K := K) (L := L)
  change finiteAdicTransport
      (K := K) (L := L) P sigma w z =
    completionAdicTransport
      (K := K) (L := L) P sigma w z
  exact adic_transport_pointwise
    (K := K) (L := L) P sigma w z

/-- The normalized finite completion places above `P`, indexed instead by
the literal upper primes above `P`. -/
noncomputable def placesAbovePrimes
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CompletionPlacesAbove (L := L) (FinitePlace.mk P).val ≃
      FinitePrimesAbove (K := K) (L := L) P :=
  (placesAboveFactors
    (K := K) (L := L) P).trans
      (upperPrimesAbove (K := K) (L := L) P)

@[simp]
theorem places_above_primes
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    placesAbovePrimes
        (K := K) (L := L) P w =
      completionPlaceAbove
        (K := K) (L := L) P w := by
  change (upperPrimesAbove (K := K) (L := L) P)
      ((upperPrimesAbove
        (K := K) (L := L) P).symm
          (completionPlaceAbove
            (K := K) (L := L) P w)) = _
  exact (upperPrimesAbove
    (K := K) (L := L) P).apply_symm_apply _

/-- The finite completion-place/upper-prime correspondence is Galois
equivariant. -/
theorem above_primes_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := aboveMulAction (K := K) (L := L) P
    placesAbovePrimes
        (K := K) (L := L) P (sigma • w) =
      sigma • placesAbovePrimes
        (K := K) (L := L) P w := by
  letI := aboveMulAction (K := K) (L := L) P
  rw [places_above_primes,
    places_above_primes]
  apply Subtype.ext
  exact place_above_smul
    (K := K) (L := L) P sigma w

private theorem pi_congr_image
    {ι ι' : Type*} (S : ι' → Type*)
    [∀ i, NonUnitalNonAssocSemiring (S i)]
    (e : ι ≃ ι') (f : ∀ i, S (e i)) (i : ι) :
    RingEquiv.piCongrLeft S e f (e i) = f i := by
  change Equiv.piCongrLeft S e f (e i) = f i
  exact Equiv.piCongrLeft_apply_apply S e f i

private theorem ring_cast_heq
    {ι : Type*} {R : ι → Type*}
    [∀ i, Mul (R i)] [∀ i, Add (R i)]
    {i j : ι} (h : i = j) (x : R i) :
    HEq (RingEquiv.cast h x) x := by
  subst j
  rfl

@[simp]
theorem adic_above_image
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (alpha : ∀ w : CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val, w.1.Completion)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    adicPrimesAbove
        (K := K) (L := L) P alpha
        (placesAbovePrimes
          (K := K) (L := L) P w) =
      completionPlaceAdic
        (K := K) (L := L) P w (alpha w) := by
  unfold adicPrimesAbove
  rw [RingEquiv.trans_apply]
  change RingEquiv.piCongrLeft
      (fun Q : FinitePrimesAbove (K := K) (L := L) P =>
        Q.1.adicCompletion L)
      (upperPrimesAbove (K := K) (L := L) P)
      (ringAdicFactors
        (K := K) (L := L) P alpha)
      ((upperPrimesAbove (K := K) (L := L) P)
        (placesAboveFactors
          (K := K) (L := L) P w)) = _
  rw [pi_congr_image]
  unfold ringAdicFactors
  change RingEquiv.piCongrLeft
      (fun Q : UpperPrimeFactors (K := K) (L := L) P =>
        (upperPrime (K := K) (L := L) P Q).adicCompletion L)
      (placesAboveFactors
        (K := K) (L := L) P)
      ((RingEquiv.piCongrRight fun w =>
        completionPlaceAdic (K := K) (L := L) P w) alpha)
      (placesAboveFactors
        (K := K) (L := L) P w) = _
  rw [pi_congr_image]
  rfl

private theorem above_reindex_heq
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (alpha : ∀ w : CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val, w.1.Completion)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := aboveMulAction (K := K) (L := L) P
    HEq
      (adicPrimesAbove
        (K := K) (L := L) P alpha
          (sigma⁻¹ • placesAbovePrimes
            (K := K) (L := L) P w))
      (adicPrimesAbove
        (K := K) (L := L) P alpha
          (placesAbovePrimes
            (K := K) (L := L) P (sigma⁻¹ • w))) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  have hindex := above_primes_smul
    (K := K) (L := L) P sigma⁻¹ w
  exact congr_arg_heq
    (adicPrimesAbove
      (K := K) (L := L) P alpha) hindex.symm

private noncomputable def completionAdicAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (alpha : ∀ w : CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val, w.1.Completion) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := aboveMulAction (K := K) (L := L) P
    ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      Q.1.adicCompletion L := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  exact adicPrimesAbove
    (K := K) (L := L) P
    (completionProductAction (FinitePlace.mk P).val sigma alpha)

private noncomputable def aboveAdicAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (alpha : ∀ w : CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val, w.1.Completion) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := aboveMulAction (K := K) (L := L) P
    ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      Q.1.adicCompletion L := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  exact fun Q => finitePlaceTransport (K := K) sigma Q.1
    (adicPrimesAbove
      (K := K) (L := L) P alpha (sigma⁻¹ • Q))

set_option maxHeartbeats 1000000 in
-- Transporting the completion-product action through the adic comparison
-- unfolds dependent coordinate casts.
set_option synthInstance.maxHeartbeats 300000 in
private theorem primes_above_image
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (alpha : ∀ w : CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val, w.1.Completion)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := aboveMulAction (K := K) (L := L) P
    completionAdicAction
        (K := K) (L := L) P sigma alpha
        (placesAbovePrimes
          (K := K) (L := L) P w) =
      aboveAdicAction
        (K := K) (L := L) P sigma alpha
        (placesAbovePrimes
          (K := K) (L := L) P w) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  let e := placesAbovePrimes
    (K := K) (L := L) P
  change adicPrimesAbove
      (K := K) (L := L) P
      (completionProductAction (FinitePlace.mk P).val sigma alpha) (e w) =
    finitePlaceTransport (K := K) sigma (e w).1
      (adicPrimesAbove
        (K := K) (L := L) P alpha (sigma⁻¹ • e w))
  rw [adic_above_image]
  change completionPlaceAdic (K := K) (L := L) P w
      (completionFamilyTransport (FinitePlace.mk P).val sigma w
        (alpha (sigma⁻¹ • w))) =
    finitePlaceTransport (K := K) sigma (e w).1
      (adicPrimesAbove
        (K := K) (L := L) P alpha (sigma⁻¹ • e w))
  have hvalue :=
    above_reindex_heq
      (K := K) (L := L) P sigma alpha w
  let q := completionCenteredPrime (K := K) (L := L) P w
  let q' := completionCenteredPrime
    (K := K) (L := L) P (sigma⁻¹ • w)
  let hq : q' = sigma⁻¹ • q :=
    completion_centered_smul
      (K := K) (L := L) P sigma⁻¹ w
  let xlocal := completionPlaceAdic
    (K := K) (L := L) P (sigma⁻¹ • w) (alpha (sigma⁻¹ • w))
  have himage : adicPrimesAbove
      (K := K) (L := L) P alpha (e (sigma⁻¹ • w)) = xlocal :=
    adic_above_image
      (K := K) (L := L) P alpha (sigma⁻¹ • w)
  have hproduct : HEq
      (adicPrimesAbove
        (K := K) (L := L) P alpha (sigma⁻¹ • e w)) xlocal :=
    hvalue.trans (heq_of_eq himage)
  have hcast : HEq
      (RingEquiv.cast
        (R := fun R : HeightOneSpectrum
          (NumberField.RingOfIntegers L) => R.adicCompletion L)
        hq xlocal) xlocal := by
    exact ring_cast_heq hq xlocal
  have hinner : RingEquiv.cast
      (R := fun R : HeightOneSpectrum
        (NumberField.RingOfIntegers L) => R.adicCompletion L)
      hq xlocal =
        adicPrimesAbove
          (K := K) (L := L) P alpha (sigma⁻¹ • e w) :=
    eq_of_heq (hcast.trans hproduct.symm)
  rw [← hinner]
  exact place_adic_transport
    (K := K) (L := L) P sigma w (alpha (sigma⁻¹ • w))

set_option maxHeartbeats 1000000 in
-- Ring-level equivariance compares the normalized completion action at every
-- upper prime with the prime-adic action.
set_option synthInstance.maxHeartbeats 300000 in
/-- The finite completion-product ring equivalence intertwines the two
coordinatewise Galois actions. -/
theorem primes_above_action
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (alpha : ∀ w : CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val, w.1.Completion) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := aboveMulAction (K := K) (L := L) P
    completionAdicAction
        (K := K) (L := L) P sigma alpha =
      aboveAdicAction
        (K := K) (L := L) P sigma alpha := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  let e := placesAbovePrimes
    (K := K) (L := L) P
  funext Q
  obtain ⟨w, rfl⟩ := e.surjective Q
  exact primes_above_image
    (K := K) (L := L) P sigma alpha w

set_option maxHeartbeats 1000000 in
-- Passing the ring equivariance proof to units elaborates nested subtype and
-- dependent-function coercions.
set_option synthInstance.maxHeartbeats 300000 in
/-- Multiplicative form of the finite completion-product equivariance. -/
theorem pi_above_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (x : (∀ w : CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val, w.1.Completion)ˣ) :
    letI := unitsDistribAction
      (K := K) (L := L) (FinitePlace.mk P).val
    letI := aboveUnitsAction (K := K) (L := L) P
    piPrimesAbove
        (K := K) (L := L) P (sigma • x) =
      sigma • piPrimesAbove
        (K := K) (L := L) P x := by
  letI := unitsDistribAction
    (K := K) (L := L) (FinitePlace.mk P).val
  letI := aboveUnitsAction (K := K) (L := L) P
  funext Q
  apply Units.ext
  exact congrFun
    (primes_above_action
      (K := K) (L := L) P sigma (x :
        ∀ w : CompletionPlacesAbove
          (L := L) (FinitePlace.mk P).val, w.1.Completion)) Q

set_option maxHeartbeats 1000000 in
-- The representation isomorphism packages the full dependent completion-
-- product equivariance calculation.
set_option synthInstance.maxHeartbeats 300000 in
/-- Equivariant representation isomorphism from the normalized finite
completion product to the literal prime-adic orbit. -/
noncomputable def resizedIsoOrbit
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    resizedPlaceRepresentation
        (K := K) (L := L) (.inl P) ≅
      resizedAboveRepresentation
        (K := K) (L := L) P := by
  apply Rep.mkIso
  let e := piPrimesAbove
    (K := K) (L := L) P
  refine
    { toLinearEquiv :=
        { toEquiv := e.toAdditive.toEquiv
          map_add' := e.toAdditive.map_add
          map_smul' := fun r x => map_zsmul e.toAdditive r.down x }
      isIntertwining' := ?_ }
  intro sigma
  letI := unitsDistribAction
    (K := K) (L := L) (FinitePlace.mk P).val
  letI := aboveUnitsAction (K := K) (L := L) P
  apply LinearMap.ext
  intro x
  change Additive.ofMul
      (e ((unitsDistribAction
        (K := K) (L := L) (FinitePlace.mk P).val).smul sigma x.toMul)) =
    Additive.ofMul
      ((aboveUnitsAction
        (K := K) (L := L) P).smul sigma (e x.toMul))
  exact congrArg Additive.ofMul
    (pi_above_smul
      (K := K) (L := L) P sigma x.toMul)

/-- The finite orbit `H²` used by the stage limit is the `H²` of the
completion product at the corresponding finite number-field place. -/
noncomputable def resizedPlaceProduct
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    OrbitH2 K L P ≃+
      H2 (resizedPlaceRepresentation
        (K := K) (L := L) (.inl P)) :=
  (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
    (resizedIsoOrbit
      (K := K) (L := L) P)).toLinearEquiv.toAddEquiv).symm

/-- Assemble the finite-place completion-product comparisons. -/
noncomputable def resizedHDirect :
    DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitH2 K L) ≃+
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (fun P => H2 (resizedPlaceRepresentation
          (K := K) (L := L) (.inl P))) :=
  DirectSum.congrAddEquiv fun P =>
    resizedPlaceProduct
      (K := K) (L := L) P

private abbrev PlaceH2
    (v : NumberFieldPlace K) : Type _ :=
  H2 (resizedPlaceRepresentation
    (K := K) (L := L) v)

private noncomputable def completionDirectSplit :
    DirectSum (NumberFieldPlace K)
        (fun v => H2 (resizedPlaceRepresentation
          (K := K) (L := L) v)) →+
      (DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
          (fun P => H2 (resizedPlaceRepresentation
            (K := K) (L := L) (.inl P)))) ×
        DirectSum (InfinitePlace K)
          (fun v => H2 (resizedPlaceRepresentation
            (K := K) (L := L) (.inr v))) where
  toFun x :=
    (DFinsupp.comapDomain Sum.inl Sum.inl_injective x,
      DFinsupp.comapDomain Sum.inr Sum.inr_injective x)
  map_zero' := by
    apply Prod.ext
    · exact DFinsupp.comapDomain_zero Sum.inl Sum.inl_injective
    · exact DFinsupp.comapDomain_zero Sum.inr Sum.inr_injective
  map_add' x y := by
    apply Prod.ext
    · exact DFinsupp.comapDomain_add Sum.inl Sum.inl_injective x y
    · exact DFinsupp.comapDomain_add Sum.inr Sum.inr_injective x y

private noncomputable def completionDirectInclusion :
    DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (fun P => H2 (resizedPlaceRepresentation
          (K := K) (L := L) (.inl P))) →+
      DirectSum (NumberFieldPlace K)
        (fun v => H2 (resizedPlaceRepresentation
          (K := K) (L := L) v)) := by
  classical
  exact DirectSum.toAddMonoid fun P =>
    DirectSum.of
      (fun v => H2 (resizedPlaceRepresentation
        (K := K) (L := L) v)) (.inl P)

private noncomputable def infiniteDirectInclusion :
    DirectSum (InfinitePlace K)
        (fun v => H2 (resizedPlaceRepresentation
          (K := K) (L := L) (.inr v))) →+
      DirectSum (NumberFieldPlace K)
        (fun w => H2 (resizedPlaceRepresentation
          (K := K) (L := L) w)) := by
  classical
  exact DirectSum.toAddMonoid fun v =>
    DirectSum.of
      (fun w => H2 (resizedPlaceRepresentation
        (K := K) (L := L) w)) (.inr v)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
private theorem product_split_inclusion
    (a : DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (fun P => H2 (resizedPlaceRepresentation
        (K := K) (L := L) (.inl P)))) :
    DFinsupp.comapDomain Sum.inl Sum.inl_injective
        (completionDirectInclusion
          (K := K) (L := L) a) = a := by
  classical
  induction a using DirectSum.induction_on with
  | zero =>
      exact DFinsupp.comapDomain_zero
        (β := PlaceH2 (K := K) (L := L))
        Sum.inl Sum.inl_injective
  | of P q =>
      simpa only [completionDirectInclusion,
          DirectSum.toAddMonoid_of] using
        (DFinsupp.comapDomain_single
          (β := PlaceH2 (K := K) (L := L))
          Sum.inl Sum.inl_injective P q)
  | add a b ha hb =>
      change (completionDirectSplit (K := K) (L := L)
        (completionDirectInclusion
          (K := K) (L := L) (a + b))).1 = a + b
      rw [(completionDirectInclusion
          (K := K) (L := L)).map_add,
        (completionDirectSplit (K := K) (L := L)).map_add]
      change DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (completionDirectInclusion
            (K := K) (L := L) a) +
        DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (completionDirectInclusion
            (K := K) (L := L) b) = a + b
      rw [ha, hb]
      rfl

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
private theorem completion_split_inclusion
    (b : DirectSum (InfinitePlace K)
      (fun v => H2 (resizedPlaceRepresentation
        (K := K) (L := L) (.inr v)))) :
    DFinsupp.comapDomain Sum.inl Sum.inl_injective
        (infiniteDirectInclusion
          (K := K) (L := L) b) = 0 := by
  classical
  induction b using DirectSum.induction_on with
  | zero =>
      exact DFinsupp.comapDomain_zero
        (β := PlaceH2 (K := K) (L := L))
        Sum.inl Sum.inl_injective
  | of v q =>
      apply DirectSum.ext
      intro P
      simp [infiniteDirectInclusion,
        DFinsupp.comapDomain_apply, DirectSum.toAddMonoid_of,
        DirectSum.of_eq_of_ne]
  | add a b ha hb =>
      change (completionDirectSplit (K := K) (L := L)
        (infiniteDirectInclusion
          (K := K) (L := L) (a + b))).1 = 0
      rw [(infiniteDirectInclusion
          (K := K) (L := L)).map_add,
        (completionDirectSplit (K := K) (L := L)).map_add]
      change DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (infiniteDirectInclusion
            (K := K) (L := L) a) +
        DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (infiniteDirectInclusion
            (K := K) (L := L) b) = 0
      rw [ha, hb, add_zero]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
private theorem split_inclusion_infinite
    (a : DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (fun P => H2 (resizedPlaceRepresentation
        (K := K) (L := L) (.inl P)))) :
    DFinsupp.comapDomain Sum.inr Sum.inr_injective
        (completionDirectInclusion
          (K := K) (L := L) a) = 0 := by
  classical
  induction a using DirectSum.induction_on with
  | zero =>
      exact DFinsupp.comapDomain_zero
        (β := PlaceH2 (K := K) (L := L))
        Sum.inr Sum.inr_injective
  | of P q =>
      apply DirectSum.ext
      intro v
      simp [completionDirectInclusion,
        DFinsupp.comapDomain_apply, DirectSum.toAddMonoid_of,
        DirectSum.of_eq_of_ne]
  | add a b ha hb =>
      change (completionDirectSplit (K := K) (L := L)
        (completionDirectInclusion
          (K := K) (L := L) (a + b))).2 = 0
      rw [(completionDirectInclusion
          (K := K) (L := L)).map_add,
        (completionDirectSplit (K := K) (L := L)).map_add]
      change DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (completionDirectInclusion
            (K := K) (L := L) a) +
        DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (completionDirectInclusion
            (K := K) (L := L) b) = 0
      rw [ha, hb, add_zero]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
private theorem split_infinite_inclusion
    (b : DirectSum (InfinitePlace K)
      (fun v => H2 (resizedPlaceRepresentation
        (K := K) (L := L) (.inr v)))) :
    DFinsupp.comapDomain Sum.inr Sum.inr_injective
        (infiniteDirectInclusion
          (K := K) (L := L) b) = b := by
  classical
  induction b using DirectSum.induction_on with
  | zero =>
      exact DFinsupp.comapDomain_zero
        (β := PlaceH2 (K := K) (L := L))
        Sum.inr Sum.inr_injective
  | of v q =>
      simpa only [infiniteDirectInclusion,
          DirectSum.toAddMonoid_of] using
        (DFinsupp.comapDomain_single
          (β := PlaceH2 (K := K) (L := L))
          Sum.inr Sum.inr_injective v q)
  | add a b ha hb =>
      change (completionDirectSplit (K := K) (L := L)
        (infiniteDirectInclusion
          (K := K) (L := L) (a + b))).2 = a + b
      rw [(infiniteDirectInclusion
          (K := K) (L := L)).map_add,
        (completionDirectSplit (K := K) (L := L)).map_add]
      change DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (infiniteDirectInclusion
            (K := K) (L := L) a) +
        DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (infiniteDirectInclusion
            (K := K) (L := L) b) = a + b
      rw [ha, hb]
      rfl

/-- A direct sum over finite-or-infinite number-field places is the product
of its finite and infinite direct sums. -/
noncomputable def completionDirectInfinite :
    DirectSum (NumberFieldPlace K)
        (fun v => H2 (resizedPlaceRepresentation
          (K := K) (L := L) v)) ≃+
      (DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
          (fun P => H2 (resizedPlaceRepresentation
            (K := K) (L := L) (.inl P)))) ×
        DirectSum (InfinitePlace K)
          (fun v => H2 (resizedPlaceRepresentation
            (K := K) (L := L) (.inr v))) := by
  classical
  apply AddEquiv.ofBijective completionDirectSplit
  constructor
  · intro x y h
    apply DirectSum.ext
    intro v
    cases v with
    | inl P => exact congrArg (fun z => z.1 P) h
    | inr v => exact congrArg (fun z => z.2 v) h
  · intro y
    refine ⟨completionDirectInclusion
        (K := K) (L := L) y.1 +
      infiniteDirectInclusion
        (K := K) (L := L) y.2, ?_⟩
    apply Prod.ext
    · change (completionDirectSplit (K := K) (L := L)
          (completionDirectInclusion
              (K := K) (L := L) y.1 +
            infiniteDirectInclusion
              (K := K) (L := L) y.2)).1 = y.1
      rw [(completionDirectSplit (K := K) (L := L)).map_add]
      change DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (completionDirectInclusion
            (K := K) (L := L) y.1) +
        DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (infiniteDirectInclusion
            (K := K) (L := L) y.2) = y.1
      rw [product_split_inclusion,
        completion_split_inclusion, add_zero]
    · change (completionDirectSplit (K := K) (L := L)
          (completionDirectInclusion
              (K := K) (L := L) y.1 +
            infiniteDirectInclusion
              (K := K) (L := L) y.2)).2 = y.2
      rw [(completionDirectSplit (K := K) (L := L)).map_add]
      change DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (completionDirectInclusion
            (K := K) (L := L) y.1) +
        DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (infiniteDirectInclusion
            (K := K) (L := L) y.2) = y.2
      rw [split_inclusion_infinite,
        split_infinite_inclusion, zero_add]

/-- Unconditional degree-two completion-product decomposition of the
concrete idèle representation. -/
noncomputable def resizedHDecomposition :
    ResizedIdeleDecomposition K L :=
  (resizedHLimit (K := K) (L := L)).symm |>.trans
    (resizedIdelesLimit
      (K := K) (L := L)) |>.trans
    ((resizedDirectSum
        (K := K) (L := L)).prodCongr
      ((resizedCofinalStage
        (K := K) (L := L)).trans
          (resizedHDirect
            (K := K) (L := L)))) |>.trans
    (AddEquiv.prodComm : _ ≃+ _) |>.trans
    (completionDirectInfinite
      (K := K) (L := L)).symm

end

end Submission.CField.HNorm
