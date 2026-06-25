import Towers.NumberTheory.Completions.TotalQuotientAlgebra

/-!
# Compatibility of integral and fraction semilocal decompositions

The fraction-ring equivalence is obtained by extending the integral
semilocal ring equivalence.  This file records that compatibility without
unfolding the dependent product localization.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain
open scoped TensorProduct

noncomputable section

universe u

variable {R S L : Type u}
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The flat total-quotient algebra sends a base fraction represented by
an element to the same element viewed in the upper total quotient ring. -/
theorem fraction_algebra_flat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (a : A) :
    @algebraMap (FractionRing A) (FractionRing B) _ _
        (fractionRingFlat A B) (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (algebraMap A B a) := by
  change IsLocalization.lift _ (algebraMap A (FractionRing A) a) = _
  rw [IsLocalization.lift_eq]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- The product fraction-ring instance has dependent valuation-ring factors.
set_option maxHeartbeats 1000000 in
omit [FaithfulSMul R S] in
/-- The total-quotient equivalence extends the integral semilocal ring
equivalence on the whole product. -/
theorem tensor_fraction_algebra
    [Ring.HasFiniteQuotients S]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊥)
    (x : AdicCompletion I R ⊗[R] S) :
    adicFractionCompletions
        (L := L) I hI
        (algebraMap (AdicCompletion I R ⊗[R] S)
          (FractionRing (AdicCompletion I R ⊗[R] S)) x) =
      algebraMap
        (∀ P : (UniqueFactorizationMonoid.factors
          (I.map (algebraMap R S))).toFinset,
          (factorHeightSpectrum
            (I.map (algebraMap R S)) P).adicCompletionIntegers L)
        (∀ P : (UniqueFactorizationMonoid.factors
          (I.map (algebraMap R S))).toFinset,
          (factorHeightSpectrum
            (I.map (algebraMap R S)) P).adicCompletion L)
        ((completionPiIntegers (K := L)
          (I.map (algebraMap R S)) hI)
          (adicTensorRing I x)) := by
  let J : Ideal S := I.map (algebraMap R S)
  let e₀ : AdicCompletion I R ⊗[R] S ≃+*
      (∀ P : (UniqueFactorizationMonoid.factors J).toFinset,
        (factorHeightSpectrum J P).adicCompletionIntegers L) :=
    (adicTensorRing I).toRingEquiv.trans
      (completionPiIntegers (K := L) J hI)
  letI : IsFractionRing
      (∀ P : (UniqueFactorizationMonoid.factors J).toFinset,
        (factorHeightSpectrum J P).adicCompletionIntegers L)
      (∀ P : (UniqueFactorizationMonoid.factors J).toFinset,
        (factorHeightSpectrum J P).adicCompletion L) :=
    fraction_ring_pi _ _
  change IsFractionRing.ringEquivOfRingEquiv e₀
      (algebraMap (AdicCompletion I R ⊗[R] S)
        (FractionRing (AdicCompletion I R ⊗[R] S)) x) =
    algebraMap
      (∀ P : (UniqueFactorizationMonoid.factors J).toFinset,
        (factorHeightSpectrum J P).adicCompletionIntegers L)
      (∀ P : (UniqueFactorizationMonoid.factors J).toFinset,
        (factorHeightSpectrum J P).adicCompletion L) (e₀ x)
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap e₀ x

omit [FaithfulSMul R S] in
/-- Coordinate form of the extension compatibility. -/
theorem adic_fraction_algebra
    [Ring.HasFiniteQuotients S]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊥)
    (x : AdicCompletion I R ⊗[R] S)
    (P : (UniqueFactorizationMonoid.factors
      (I.map (algebraMap R S))).toFinset) :
    adicFractionCompletions
        (L := L) I hI
        (algebraMap (AdicCompletion I R ⊗[R] S)
          (FractionRing (AdicCompletion I R ⊗[R] S)) x) P =
      algebraMap
        ((factorHeightSpectrum
          (I.map (algebraMap R S)) P).adicCompletionIntegers L)
        ((factorHeightSpectrum
          (I.map (algebraMap R S)) P).adicCompletion L)
        (completionPiIntegers (K := L)
          (I.map (algebraMap R S)) hI
          (adicTensorRing I x) P) := by
  exact congrFun
    (tensor_fraction_algebra
      (L := L) I hI x) P

variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

set_option synthInstance.maxHeartbeats 100000 in
-- The named prime algebra equivalences carry dependent coordinate instances.
set_option maxHeartbeats 1000000 in
/-- The named fraction-field algebra equivalence extends the named integral
algebra equivalence in every upper completed factor. -/
theorem adic_tensor_fraction
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (x : AdicCompletion P.asIdeal R ⊗[R] S)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    fractionPiCompletions
        (K := K) (L := L) P hP
        (algebraMap (AdicCompletion P.asIdeal R ⊗[R] S)
          (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) x) Q =
      algebraMap
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L)
        (adicPiIntegers
          (K := K) (L := L) P hP x Q) := by
  change adicFractionCompletions
      (L := L) P.asIdeal hP
      (algebraMap (AdicCompletion P.asIdeal R ⊗[R] S)
        (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) x) Q = _
  exact adic_fraction_algebra
    (L := L) P.asIdeal hP x Q

end

end Towers.NumberTheory.Milne
