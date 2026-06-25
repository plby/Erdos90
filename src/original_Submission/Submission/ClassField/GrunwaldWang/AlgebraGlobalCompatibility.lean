import Submission.ClassField.Ideles.IdeleNorm
import Submission.NumberTheory.Completions.SemilocalCoordinateMap

/-!
# Global scalars in a finite semilocal completion factor

The algebra action on a prime-adic factor of the semilocal completion agrees
with the original global field embedding.
-/

namespace Submission.CField.GWang

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

set_option synthInstance.maxHeartbeats 100000 in
-- Expanding the dependent semilocal factor algebra requires a larger
-- reduction budget.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] in
/-- The semilocal coordinate algebra agrees with the global field embedding
on the fraction field before passing to completions. -/
theorem factor_algebra_global
    (P : HeightOneSpectrum (RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    let hP : P.asIdeal.map
        (algebraMap (RingOfIntegers K) (RingOfIntegers L)) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot P.ne_bot
    let q := upperPrime (K := K) (L := L) P Q
    letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
      adicFactorAlgebra
        (K := K) (L := L) P hP Q
    (algebraMap (P.adicCompletion K) (q.adicCompletion L)).comp
        (FinitePlace.embedding P) =
      (FinitePlace.embedding q).comp (algebraMap K L) := by
  dsimp only
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let q := upperPrime (K := K) (L := L) P Q
  let E := q.adicCompletion L
  let hP : P.asIdeal.map
      (algebraMap (RingOfIntegers K) (RingOfIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra F E :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  letI : Algebra C E :=
    adicIntegerAlgebra
      (K := K) (L := L) P hP Q
  apply IsFractionRing.ringHom_ext (A := RingOfIntegers K)
  intro r
  have hlower :
      algebraMap K F (algebraMap (RingOfIntegers K) K r) =
        algebraMap C F (algebraMap (RingOfIntegers K) C r) := by
    rfl
  change algebraMap F E
      (algebraMap K F (algebraMap (RingOfIntegers K) K r)) =
    algebraMap L E (algebraMap (RingOfIntegers L) L
      (algebraMap (RingOfIntegers K) (RingOfIntegers L) r))
  rw [hlower]
  calc
    algebraMap F E
        (algebraMap C F (algebraMap (RingOfIntegers K) C r)) =
        algebraMap C E (algebraMap (RingOfIntegers K) C r) :=
      (adic_integer_algebra
        (K := K) (L := L) P hP Q _).symm
    _ = algebraMap L E (algebraMap (RingOfIntegers L) L
        (algebraMap (RingOfIntegers K) (RingOfIntegers L) r)) := by
      let D := q.adicCompletionIntegers L
      letI : Algebra C D :=
        adicCompletionAlgebra
          (K := K) (L := L) P hP Q
      change algebraMap D E
          (algebraMap C D (algebraMap (RingOfIntegers K) C r)) =
        algebraMap D E
          (algebraMap (RingOfIntegers L) D
            (algebraMap (RingOfIntegers K) (RingOfIntegers L) r))
      apply congrArg (algebraMap D E)
      let A := AdicCompletion P.asIdeal (RingOfIntegers K)
      let eC : A ≃+* C :=
        adicRingIntegers (K := K) P
      have heC :
          eC.symm (algebraMap (RingOfIntegers K) C r) =
            AdicCompletion.of P.asIdeal (RingOfIntegers K) r := by
        apply eC.injective
        rw [eC.apply_symm_apply]
        change algebraMap (RingOfIntegers K) C r =
          adicRingEquiv (K := K) P
            (adicCompletionPrime P
              (AdicCompletion.of P.asIdeal (RingOfIntegers K) r))
        rw [adic_completion_equiv,
          adic_ring_equiv,
          adic_integers_algebra]
      change completionPiIntegers (K := L)
          (P.asIdeal.map
            (algebraMap (RingOfIntegers K) (RingOfIntegers L))) hP
          (adicTensorRing P.asIdeal
            (eC.symm (algebraMap (RingOfIntegers K) C r) ⊗ₜ
              (1 : RingOfIntegers L))) Q = _
      rw [heC]
      have htensor :
          AdicCompletion.of P.asIdeal (RingOfIntegers K) r
              ⊗ₜ[RingOfIntegers K]
              (1 : RingOfIntegers L) =
            (1 : AdicCompletion P.asIdeal (RingOfIntegers K))
              ⊗ₜ[RingOfIntegers K]
              algebraMap (RingOfIntegers K) (RingOfIntegers L) r := by
        have hof :
            AdicCompletion.of P.asIdeal (RingOfIntegers K) r =
              algebraMap (RingOfIntegers K)
                (AdicCompletion P.asIdeal (RingOfIntegers K)) r := by
          simpa using
            (AdicCompletion.algebraMap_apply
              (I := P.asIdeal) (R := RingOfIntegers K) r).symm
        rw [hof]
        rw [← mul_one (algebraMap (RingOfIntegers K)
          (AdicCompletion P.asIdeal (RingOfIntegers K)) r),
          ← Algebra.smul_def, TensorProduct.smul_tmul]
        simp only [Algebra.smul_def, mul_one]
      rw [htensor,
        adic_tensor_tmul]
      exact adic_pi_integers
        (L := L)
        (P.asIdeal.map
          (algebraMap (RingOfIntegers K) (RingOfIntegers L))) hP
        (algebraMap (RingOfIntegers K) (RingOfIntegers L) r) Q

end

end Submission.CField.GWang
