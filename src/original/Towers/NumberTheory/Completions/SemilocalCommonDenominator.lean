import Towers.NumberTheory.Completions.DifferentCommonDenominator
import Towers.NumberTheory.Completions.SemilocalCoordinateAlgebra

/-!
# Common denominators for semilocal completed scalar extension

The coordinate localization theorem for completed valuation rings supplies
the remaining hypothesis in the common-denominator construction.  Thus both
the product of upper completed fields and the total quotient ring of the
completed tensor algebra are obtained by inverting the non-zero elements of
the concrete completed lower valuation ring.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain nonZeroDivisors
open scoped TensorProduct

noncomputable section

universe u

variable {R S K L : Type u}
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]

set_option synthInstance.maxHeartbeats 100000 in
-- Each coordinate carries dependent completed valuation-ring structures.
set_option maxHeartbeats 1000000 in
/-- Each completed upper coordinate is unconditionally the localization at
the non-zero elements of the concrete completed lower integer ring. -/
theorem adic_localization_coordinate
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    let C := P.adicCompletionIntegers K
    let B := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    let E := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
    letI : Algebra C B :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    IsLocalization (Algebra.algebraMapSubmonoid B C⁰) E := by
  let C := P.adicCompletionIntegers K
  let B := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  exact adic_integer_localization
    (K := K) (L := L) P hP Q

set_option synthInstance.maxHeartbeats 100000 in
-- The product localization synthesizes all dependent coordinate instances.
set_option maxHeartbeats 1000000 in
/-- The product of upper completed fields is the common-denominator
localization of the completed tensor algebra. -/
theorem localization_adic_product
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
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
  apply localization_adic_coordinate
    (K := K) (L := L) P hP
  intro Q
  exact adic_localization_coordinate
    (K := K) (L := L) P hP Q

set_option synthInstance.maxHeartbeats 100000 in
-- The transported product localization has dependent completed factors.
set_option maxHeartbeats 1000000 in
/-- The total quotient ring of completed scalar extension is obtained by
inverting the diagonal image of the lower completed ring's non-zero
elements. -/
theorem localization_fraction_ring
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    letI : Algebra (P.adicCompletionIntegers K)
        (AdicCompletion P.asIdeal R ⊗[R] S) :=
      adicTensorAlgebra (S := S) (K := K) P
    IsLocalization
      (Algebra.algebraMapSubmonoid
        (AdicCompletion P.asIdeal R ⊗[R] S)
        (P.adicCompletionIntegers K)⁰)
      (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) := by
  apply localization_tensor_fraction
    (K := K) (L := FractionRing S) P hP
  intro Q
  exact adic_localization_coordinate
    (K := K) (L := FractionRing S) P hP Q

end

end Towers.NumberTheory.Milne
