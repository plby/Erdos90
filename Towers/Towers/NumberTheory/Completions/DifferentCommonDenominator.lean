import Towers.NumberTheory.Completions.PiBaseLocalization
import Towers.NumberTheory.Completions.TotalQuotientAlgebra
import Towers.NumberTheory.Completions.TotalQuotientCompatibility


/-!
# Common-denominator localization after an integral product decomposition

An integral completed tensor algebra is identified with a finite product of
completed valuation rings.  This file transports the common-denominator
localization of that product back across the integral algebra equivalence.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain nonZeroDivisors

noncomputable section

universe u

section Transport

variable {C A ι : Type*} (B L : ι → Type u)
  [CommRing C] [CommRing A] [Algebra C A] [Finite ι]
  [∀ i, CommRing (B i)] [∀ i, CommRing (L i)]
  [∀ i, Algebra C (B i)] [∀ i, Algebra (B i) (L i)]

/-- The action of an algebra `A` on a product of localization targets,
transported through an integral product decomposition of `A`. -/
@[reducible] noncomputable def piLocalizationTarget
    (e₀ : A ≃ₐ[C] (∀ i, B i)) : Algebra A (∀ i, L i) :=
  RingHom.toAlgebra <|
    (algebraMap (∀ i, B i) (∀ i, L i)).comp e₀.toRingEquiv.toRingHom

/-- Transport the common-denominator localization of a finite product across
an algebra equivalence identifying its integral model with that product. -/
theorem localization_pi_alg
    (e₀ : A ≃ₐ[C] (∀ i, B i))
    [∀ i, IsLocalization
      (Algebra.algebraMapSubmonoid (B i) C⁰) (L i)] :
    letI : Algebra A (∀ i, L i) :=
      piLocalizationTarget B L e₀
    IsLocalization
      (Algebra.algebraMapSubmonoid A C⁰) (∀ i, L i) := by
  letI : Algebra A (∀ i, L i) :=
    piLocalizationTarget B L e₀
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (∀ i, B i) C⁰) (∀ i, L i) :=
    submonoid_non_divisors B L
  apply IsLocalization.of_ringEquiv_left
    (R := A) (S := ∀ i, B i) (K := ∀ i, L i)
    (M₁ := Algebra.algebraMapSubmonoid (∀ i, B i) C⁰)
    (M₂ := Algebra.algebraMapSubmonoid A C⁰) e₀.toRingEquiv
  · ext x
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, (e₀.commutes c).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨algebraMap C A c, ⟨c, hc, rfl⟩, e₀.commutes c⟩
  · intro a
    rfl

end Transport

section PrimeAdicCompletion

open scoped TensorProduct

variable {R S K L : Type u}
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent product requires synthesizing every completed factor structure.
set_option maxHeartbeats 1000000 in
/-- The completed tensor algebra acts on the product of completed upper
fields by first using its integral product decomposition and then including
each completed valuation ring in its fraction field. -/
@[reducible] noncomputable def adicLocalizationAlgebra
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    Algebra (AdicCompletion P.asIdeal R ⊗[R] S)
      (∀ Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) := by
  let C := P.adicCompletionIntegers K
  let A := AdicCompletion P.asIdeal R ⊗[R] S
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI : Algebra C A :=
    adicTensorAlgebra (S := S) (K := K) P
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  let e₀ : A ≃ₐ[C] (∀ Q, B Q) :=
    adicPiIntegers
      (K := K) (L := L) P hP
  exact piLocalizationTarget B E e₀

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent product requires synthesizing every completed factor structure.
set_option maxHeartbeats 1000000 in
/-- The semilocal fraction-ring decomposition, regarded as an algebra
equivalence over the completed tensor algebra using the integral product
decomposition on the target. -/
noncomputable def adicFractionLocalization
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    letI : Algebra (AdicCompletion P.asIdeal R ⊗[R] S)
        (∀ Q : (UniqueFactorizationMonoid.factors
          (P.asIdeal.map (algebraMap R S))).toFinset,
          (factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) :=
      adicLocalizationAlgebra (K := K) (L := L) P hP
    FractionRing (AdicCompletion P.asIdeal R ⊗[R] S) ≃ₐ[
      AdicCompletion P.asIdeal R ⊗[R] S]
      (∀ Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) := by
  let C := P.adicCompletionIntegers K
  let A := AdicCompletion P.asIdeal R ⊗[R] S
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI : Algebra C A :=
    adicTensorAlgebra (S := S) (K := K) P
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  let e₀ : A ≃ₐ[C] (∀ Q, B Q) :=
    adicPiIntegers
      (K := K) (L := L) P hP
  letI : Algebra A (∀ Q, E Q) :=
    adicLocalizationAlgebra (K := K) (L := L) P hP
  refine AlgEquiv.ofRingEquiv
    (f := adicFractionCompletions
      (L := L) P.asIdeal hP) ?_
  intro x
  change adicFractionCompletions
      (L := L) P.asIdeal hP (algebraMap A (FractionRing A) x) =
    algebraMap (∀ Q, B Q) (∀ Q, E Q) (e₀ x)
  exact tensor_fraction_algebra
    (L := L) P.asIdeal hP x

set_option synthInstance.maxHeartbeats 100000 in
-- The coordinate localization instances occur under a dependent product.
set_option maxHeartbeats 1000000 in
omit [FaithfulSMul R S] in
/-- Once every completed upper field is known to be the localization of its
integer ring at the nonzero elements of the completed lower integer ring,
their product is the corresponding common-denominator localization of the
completed tensor algebra. -/
theorem localization_adic_coordinate
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (hcoord : ∀ Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset,
      letI : Algebra (P.adicCompletionIntegers K)
          ((factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
        adicCompletionAlgebra (K := K) (L := L) P hP Q
      IsLocalization
        (Algebra.algebraMapSubmonoid
          ((factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L)
          (P.adicCompletionIntegers K)⁰)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L)) :
    letI : Algebra (P.adicCompletionIntegers K)
        (AdicCompletion P.asIdeal R ⊗[R] S) :=
      adicTensorAlgebra (S := S) (K := K) P
    letI : Algebra (AdicCompletion P.asIdeal R ⊗[R] S)
        (∀ Q : (UniqueFactorizationMonoid.factors
          (P.asIdeal.map (algebraMap R S))).toFinset,
          (factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) :=
      adicLocalizationAlgebra (K := K) (L := L) P hP
    IsLocalization
      (Algebra.algebraMapSubmonoid
        (AdicCompletion P.asIdeal R ⊗[R] S)
        (P.adicCompletionIntegers K)⁰)
      (∀ Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) := by
  let C := P.adicCompletionIntegers K
  let A := AdicCompletion P.asIdeal R ⊗[R] S
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI : Algebra C A :=
    adicTensorAlgebra (S := S) (K := K) P
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : IsLocalization
      (Algebra.algebraMapSubmonoid (B Q) C⁰) (E Q) :=
    hcoord Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  let e₀ : A ≃ₐ[C] (∀ Q, B Q) :=
    adicPiIntegers
      (K := K) (L := L) P hP
  exact localization_pi_alg B E e₀

set_option synthInstance.maxHeartbeats 100000 in
-- Both localization targets contain dependent products of completed factors.
set_option maxHeartbeats 1000000 in
omit [FaithfulSMul R S] in
/-- The usual total quotient ring of the completed tensor algebra is already
obtained by inverting the diagonal image of the nonzero elements of the
completed lower integer ring. -/
theorem localization_tensor_fraction
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (hcoord : ∀ Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset,
      letI : Algebra (P.adicCompletionIntegers K)
          ((factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
        adicCompletionAlgebra (K := K) (L := L) P hP Q
      IsLocalization
        (Algebra.algebraMapSubmonoid
          ((factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L)
          (P.adicCompletionIntegers K)⁰)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L)) :
    letI : Algebra (P.adicCompletionIntegers K)
        (AdicCompletion P.asIdeal R ⊗[R] S) :=
      adicTensorAlgebra (S := S) (K := K) P
    IsLocalization
      (Algebra.algebraMapSubmonoid
        (AdicCompletion P.asIdeal R ⊗[R] S)
        (P.adicCompletionIntegers K)⁰)
      (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) := by
  let A := AdicCompletion P.asIdeal R ⊗[R] S
  let E := ∀ Q : (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset,
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI : Algebra (P.adicCompletionIntegers K) A :=
    adicTensorAlgebra (S := S) (K := K) P
  letI : Algebra A E :=
    adicLocalizationAlgebra (K := K) (L := L) P hP
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid A (P.adicCompletionIntegers K)⁰) E :=
    localization_adic_coordinate
      (K := K) (L := L) P hP hcoord
  exact IsLocalization.isLocalization_of_algEquiv
    (Algebra.algebraMapSubmonoid A (P.adicCompletionIntegers K)⁰)
    (adicFractionLocalization
      (K := K) (L := L) P hP).symm

end PrimeAdicCompletion

end

end Towers.NumberTheory.Milne
