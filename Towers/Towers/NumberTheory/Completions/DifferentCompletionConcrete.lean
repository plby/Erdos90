import Towers.NumberTheory.Completions.DifferentSemilocalImage
import Towers.NumberTheory.Completions.SemilocalCommonDenominator
import Towers.NumberTheory.Completions.SemilocalCoordinateMap
import Towers.NumberTheory.Completions.TotalQuotientCompatibility


/-!
# The different under prime-adic completion

This file specializes the semilocal trace-dual machinery to the canonical
decomposition of a completed scalar extension into the completions at the
primes above a fixed height-one prime.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain Module Submodule nonZeroDivisors
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
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
/-- Transport the concrete completed valuation ring tensor product to the
inverse-limit model used by the semilocal decomposition. -/
noncomputable def adicIntegersAbstract
    [Ring.HasFiniteQuotients R]
    (P : HeightOneSpectrum R) :
    let C := P.adicCompletionIntegers K
    let A := AdicCompletion P.asIdeal R
    letI : Algebra C A :=
      (adicRingIntegers (K := K) P).symm.toRingHom.toAlgebra
    letI : Algebra C (A ⊗[R] S) :=
      adicTensorAlgebra (S := S) (K := K) P
    C ⊗[R] S ≃ₐ[C] A ⊗[R] S := by
  let C := P.adicCompletionIntegers K
  let A := AdicCompletion P.asIdeal R
  letI : Finite (R ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let eC : A ≃+* C := adicRingIntegers (K := K) P
  letI : Algebra C A := eC.symm.toRingHom.toAlgebra
  let eCR : C ≃ₐ[R] A := AlgEquiv.ofRingEquiv (f := eC.symm) fun r => by
    apply eC.injective
    rw [eC.apply_symm_apply]
    change algebraMap R C r = eC (AdicCompletion.of P.asIdeal R r)
    symm
    change adicRingEquiv (K := K) P
        (adicCompletionPrime P
          (AdicCompletion.of P.asIdeal R r)) = algebraMap R C r
    rw [adic_completion_equiv,
      adic_ring_equiv,
      adic_integers_algebra]
  let eTensorR : C ⊗[R] S ≃ₐ[R] A ⊗[R] S :=
    Algebra.TensorProduct.congr eCR (AlgEquiv.refl : S ≃ₐ[R] S)
  letI : Algebra C (A ⊗[R] S) :=
    adicTensorAlgebra (S := S) (K := K) P
  exact AlgEquiv.ofRingEquiv (f := eTensorR.toRingEquiv) fun c => by
    change eC.symm c ⊗ₜ[R] (1 : S) =
      algebraMap A (A ⊗[R] S) (eC.symm c)
    rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
omit [IsDedekindDomain S] [Module.Finite R S] [FaithfulSMul R S] in
@[simp]
theorem integers_abstract_tmul
    [Ring.HasFiniteQuotients R]
    (P : HeightOneSpectrum R) (c : P.adicCompletionIntegers K) (s : S) :
    let C := P.adicCompletionIntegers K
    let A := AdicCompletion P.asIdeal R
    letI : Algebra C A :=
      (adicRingIntegers (K := K) P).symm.toRingHom.toAlgebra
    letI : Algebra C (A ⊗[R] S) :=
      adicTensorAlgebra (S := S) (K := K) P
    adicIntegersAbstract (S := S) (K := K) P
        (c ⊗ₜ[R] s) =
      (adicRingIntegers (K := K) P).symm c ⊗ₜ[R] s := by
  simp [adicIntegersAbstract]

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
/-- The canonical integral semilocal decomposition, transported from the
inverse-limit model of the adic completion to its valuation-ring model. -/
noncomputable def integersPiDifferent
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    let C := P.adicCompletionIntegers K
    let ι := (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset
    let B : ι → Type u := fun Q => (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    letI (Q : ι) : Algebra C (B Q) :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    letI : Algebra C (∀ Q, B Q) :=
      piIntegersAlgebra (K := K) (L := L) P hP
    C ⊗[R] S ≃ₐ[C] (∀ Q, B Q) := by
  let C := P.adicCompletionIntegers K
  let A := AdicCompletion P.asIdeal R
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q => (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let eC : A ≃+* C := adicRingIntegers (K := K) P
  letI : Algebra C A := eC.symm.toRingHom.toAlgebra
  letI : Algebra C (A ⊗[R] S) :=
    adicTensorAlgebra (S := S) (K := K) P
  let eTensor := adicIntegersAbstract
    (S := S) (K := K) P
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  exact eTensor.trans
    (adicPiIntegers
      (K := K) (L := L) P hP)

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
omit [FaithfulSMul R S] in
/-- Pure tensors have the expected coordinates in the transported integral
semilocal decomposition. -/
theorem pi_different_tmul
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (c : P.adicCompletionIntegers K) (s : S)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    let C := P.adicCompletionIntegers K
    let B := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    letI : Algebra C B :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    integersPiDifferent
        (K := K) (L := L) P hP (c ⊗ₜ[R] s) Q =
      algebraMap C B c * algebraMap S B s := by
  let C := P.adicCompletionIntegers K
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q => (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  let e₀ := integersPiDifferent
    (K := K) (L := L) P hP
  have hfactor : c ⊗ₜ[R] s =
      algebraMap C (C ⊗[R] S) c * ((1 : C) ⊗ₜ[R] s) := by
    rw [Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp
  have hone : e₀ ((1 : C) ⊗ₜ[R] s) Q = algebraMap S (B Q) s := by
    change (adicPiIntegers
        (K := K) (L := L) P hP)
        (adicIntegersAbstract
          (S := S) (K := K) P ((1 : C) ⊗ₜ[R] s)) Q = _
    rw [integers_abstract_tmul]
    simp only [map_one]
    rw [pi_integers_tmul]
    simp only [one_smul]
    exact adic_pi_integers
      (L := L) (P.asIdeal.map (algebraMap R S)) hP s Q
  rw [hfactor, map_mul]
  change e₀ (algebraMap C (C ⊗[R] S) c) Q *
      e₀ ((1 : C) ⊗ₜ[R] s) Q = _
  rw [show e₀ (algebraMap C (C ⊗[R] S) c) Q =
      algebraMap C (B Q) c by exact congrFun (e₀.commutes c) Q, hone]

end

end Towers.NumberTheory.Milne
