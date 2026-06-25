import Submission.NumberTheory.Completions.SemilocalCoordinateAlgebra
import Submission.NumberTheory.Completions.SemilocalCoordinateMap

/-!
# Base-ring compatibility of completed semilocal coordinates

This file isolates the expensive dependent-coordinate calculation showing
that the completed integral coordinate algebra extends the original map of
Dedekind domains.  Keeping the calculation generic prevents every number
field consumer from unfolding the full semilocal construction again.
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

private theorem adic_integers_base
    [Ring.HasFiniteQuotients R]
    (P : HeightOneSpectrum R) (r : R) :
    (adicRingIntegers (K := K) P).symm
        (algebraMap R (P.adicCompletionIntegers K) r) =
      AdicCompletion.of P.asIdeal R r := by
  letI : Finite (R ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  apply (adicRingIntegers (K := K) P).injective
  rw [(adicRingIntegers (K := K) P).apply_symm_apply]
  change algebraMap R (P.adicCompletionIntegers K) r =
    adicRingEquiv (K := K) P
      (adicCompletionPrime P
        (AdicCompletion.of P.asIdeal R r))
  rw [adic_completion_equiv,
    adic_ring_equiv,
    adic_integers_algebra]

omit [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
  [FaithfulSMul R S] in
private theorem adic_tmul_base
    (P : HeightOneSpectrum R) (r : R) :
    AdicCompletion.of P.asIdeal R r ⊗ₜ[R] (1 : S) =
      (1 : AdicCompletion P.asIdeal R) ⊗ₜ[R] algebraMap R S r := by
  rw [show AdicCompletion.of P.asIdeal R r =
      algebraMap R (AdicCompletion P.asIdeal R) r by
    simpa using
      (AdicCompletion.algebraMap_apply (I := P.asIdeal) (R := R) r).symm]
  rw [← mul_one (algebraMap R (AdicCompletion P.asIdeal R) r),
    ← Algebra.smul_def, TensorProduct.smul_tmul]
  simp only [Algebra.smul_def, mul_one]

set_option maxRecDepth 100000 in
/-- The ring homomorphism underlying one completed integral coordinate. -/
noncomputable def adicIntegerHom
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    P.adicCompletionIntegers K →+*
      (factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L := by
  letI : Algebra (P.adicCompletionIntegers K)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  exact algebraMap (P.adicCompletionIntegers K)
    ((factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L)

set_option maxHeartbeats 3000000 in
-- Unfolding the completed semilocal tensor coordinate is elaboration-heavy.
set_option maxRecDepth 100000 in
omit [FaithfulSMul R S] in
/-- A completed integral factor sends a base scalar to the same scalar
through the upper Dedekind domain. -/
theorem adic_integer_base
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset)
    (r : R) :
    let D := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    adicIntegerHom
        (K := K) (L := L) P hP Q
        (algebraMap R (P.adicCompletionIntegers K) r) =
      algebraMap S D (algebraMap R S r) := by
  let C := P.adicCompletionIntegers K
  let D := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  letI : Algebra C D :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  let eC := adicRingIntegers (K := K) P
  change completionPiIntegers (K := L)
      (P.asIdeal.map (algebraMap R S)) hP
      (adicTensorRing P.asIdeal
        (eC.symm (algebraMap R C r) ⊗ₜ (1 : S))) Q = _
  rw [adic_integers_base,
    adic_tmul_base,
    adic_tensor_tmul]
  exact adic_pi_integers
    (L := L) (P.asIdeal.map (algebraMap R S)) hP (algebraMap R S r) Q

end

end Submission.NumberTheory.Milne
