import Submission.NumberTheory.Completions.SemilocalCoordinateAlgebra
import Submission.NumberTheory.Completions.TotalQuotientCompatibility

/-!
# Compatibility of completed coordinate algebra structures

The algebra action of a lower completed integer ring on an upper completed
field agrees with restriction of the action of the lower completion field.
This supplies the mixed scalar tower used by trace and different arguments.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain
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
-- The three algebras are dependent completed valuation coordinates.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The lower completed integer ring, lower completion field, and an upper
completion field form a scalar tower for the canonical coordinate actions. -/
theorem adic_scalar_tower
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    let C := P.adicCompletionIntegers K
    let F := P.adicCompletion K
    let E := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
    letI : Algebra C F := C.subtype.toAlgebra
    letI : Algebra F E :=
      adicFactorAlgebra (K := K) (L := L) P hP Q
    letI : Algebra C E :=
      adicIntegerAlgebra (K := K) (L := L) P hP Q
    IsScalarTower C F E := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let E := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI : Algebra C F := C.subtype.toAlgebra
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  exact adic_integer_algebra
    (K := K) (L := L) P hP Q c

set_option synthInstance.maxHeartbeats 100000 in
-- Both named equivalences carry dependent products of completed coordinates.
set_option maxHeartbeats 1000000 in
/-- In one coordinate, the fraction-field equivalence restricts to the
integral equivalence followed by the valuation-ring inclusion. -/
theorem fraction_restricts_integral
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
          (K := K) (L := L) P hP x Q) :=
  adic_tensor_fraction
    (K := K) (L := L) P hP x Q

end

end Submission.NumberTheory.Milne
