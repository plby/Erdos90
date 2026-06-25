import Submission.NumberTheory.Completions.SemilocalCompletionAssembly
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The canonical map to a semilocal completion

For a nonzero ideal of a Dedekind domain, its adic completion is the
product of the completed valuation rings at the prime factors of the
ideal.  This file packages the resulting canonical map from the original
domain to that product.  The map is flat, and it is injective when the
ideal is proper.  Faithful flatness is deliberately only asserted for the
already-established localized coordinate maps: globally, primes away from
the chosen ideal disappear from the spectrum of the completion.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

universe u

variable {R K : Type u} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The product of the completed valuation rings at the prime factors of
an ideal. -/
abbrev SemilocalCompletionProduct (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (I : Ideal R) :=
  ∀ P : (factors I).toFinset,
    (factorHeightSpectrum I P).adicCompletionIntegers K


set_option maxHeartbeats 1000000 in
-- Constructing the product ring homomorphism elaborates all completed factors.
set_option synthInstance.maxHeartbeats 300000 in
-- Typeclass synthesis must assemble the semilocal product's ring structure.
/-- The canonical map from a Dedekind domain to the product of completed
valuation rings at the prime factors of a nonzero ideal. -/
noncomputable def semilocalCompletionMap [Ring.HasFiniteQuotients R]
    (I : Ideal R) (hI : I ≠ ⊥) :
    R →+* SemilocalCompletionProduct K I :=
  (completionPiIntegers (K := K) I hI).toRingHom.comp
    (algebraMap R (AdicCompletion I R))

set_option maxHeartbeats 1000000 in
-- Unfolding the canonical product map traverses the completed-factor equivalence.
set_option synthInstance.maxHeartbeats 300000 in
-- Typeclass synthesis must recover the product's induced algebra structure.
@[simp]
theorem semilocal_completion [Ring.HasFiniteQuotients R]
    (I : Ideal R) (hI : I ≠ ⊥) (x : R) :
    semilocalCompletionMap (K := K) I hI x =
      completionPiIntegers (K := K) I hI
        (AdicCompletion.of I R x) := by
  change completionPiIntegers (K := K) I hI
      (algebraMap R (AdicCompletion I R) x) = _
  rw [AdicCompletion.algebraMap_apply]
  simp

set_option maxHeartbeats 1000000 in
-- Building the algebra equivalence elaborates the full semilocal product structure.
set_option synthInstance.maxHeartbeats 300000 in
-- Typeclass synthesis must assemble the induced algebra and module instances.
/-- With the algebra structure induced by the canonical map, the product
description is an equivalence of `R`-algebras. -/
noncomputable def semilocalCompletionAlg [Ring.HasFiniteQuotients R]
    (I : Ideal R) (hI : I ≠ ⊥) :
    letI : Algebra R (SemilocalCompletionProduct K I) :=
      (semilocalCompletionMap (K := K) I hI).toAlgebra
    AdicCompletion I R ≃ₐ[R]
      SemilocalCompletionProduct K I := by
  letI : Algebra R (SemilocalCompletionProduct K I) :=
    (semilocalCompletionMap (K := K) I hI).toAlgebra
  exact AlgEquiv.ofRingEquiv
    (f := completionPiIntegers (K := K) I hI)
    (fun _ => rfl)

set_option maxHeartbeats 1000000 in
-- Transporting flatness across the semilocal equivalence is elaboration-intensive.
set_option synthInstance.maxHeartbeats 300000 in
-- Typeclass synthesis must resolve the transported module structures.
/-- The canonical map to the semilocal completed product is flat. -/
theorem semilocal_completion_flat [Ring.HasFiniteQuotients R]
    (I : Ideal R) (hI : I ≠ ⊥) :
    @Module.Flat R (SemilocalCompletionProduct K I) _ _
      (semilocalCompletionMap (K := K) I hI).toAlgebra.toModule := by
  let A := (semilocalCompletionMap (K := K) I hI).toAlgebra
  letI : Algebra R (SemilocalCompletionProduct K I) := A
  letI : SMul R (SemilocalCompletionProduct K I) := A.toSMul
  letI : Module R (SemilocalCompletionProduct K I) := A.toModule
  exact Module.Flat.of_linearEquiv
    (semilocalCompletionAlg (K := K) I hI).symm.toLinearEquiv

set_option maxHeartbeats 1000000 in
-- The injectivity proof unfolds both completion maps and their product equivalence.
set_option synthInstance.maxHeartbeats 300000 in
-- Typeclass synthesis must resolve the completed product's ring instances.
/-- If the ideal is proper, the canonical map to its semilocal completed
product is injective. -/
theorem semilocal_completion_injective [Ring.HasFiniteQuotients R]
    (I : Ideal R) (hI : I ≠ ⊥) (hI_top : I ≠ ⊤) :
    Function.Injective (semilocalCompletionMap (K := K) I hI) := by
  letI : IsHausdorff I R := IsHausdorff.of_isDomain I hI_top
  exact (completionPiIntegers (K := K) I hI).injective.comp
    (AdicCompletion.of_injective I R)

set_option maxHeartbeats 1000000 in
-- Converting injectivity into faithful scalar action elaborates the induced algebra.
set_option synthInstance.maxHeartbeats 300000 in
-- Typeclass synthesis must recover the induced scalar and ring structures.
/-- Hence the induced scalar action is faithful for a nonzero proper
ideal. -/
theorem semilocal_faithful_s [Ring.HasFiniteQuotients R]
    (I : Ideal R) (hI : I ≠ ⊥) (hI_top : I ≠ ⊤) :
    @FaithfulSMul R (SemilocalCompletionProduct K I)
      (semilocalCompletionMap (K := K) I hI).toAlgebra.toSMul := by
  let A := (semilocalCompletionMap (K := K) I hI).toAlgebra
  letI : Algebra R (SemilocalCompletionProduct K I) := A
  letI : SMul R (SemilocalCompletionProduct K I) := A.toSMul
  exact (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (semilocal_completion_injective (K := K) I hI hI_top)

/-- At every prime factor, the original ideal maps into the maximal ideal
of the corresponding completed valuation ring. -/
theorem ideal_maximal_factor [Ring.HasFiniteQuotients R]
    (I : Ideal R) (P : (factors I).toFinset) :
    I.map (algebraMap R
        ((factorHeightSpectrum I P).adicCompletionIntegers K)) ≤
      IsLocalRing.maximalIdeal
        ((factorHeightSpectrum I P).adicCompletionIntegers K) := by
  let v := factorHeightSpectrum I P
  letI : Finite (R ⧸ v.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have hPdvd : (P : Ideal R) ∣ I :=
    dvd_of_mem_factors (Multiset.mem_toFinset.mp P.prop)
  calc
    I.map (algebraMap R
        ((factorHeightSpectrum I P).adicCompletionIntegers K)) ≤
        (P : Ideal R).map (algebraMap R
          ((factorHeightSpectrum I P).adicCompletionIntegers K)) :=
      Ideal.map_mono (Ideal.dvd_iff_le.mp hPdvd)
    _ = IsLocalRing.maximalIdeal
          ((factorHeightSpectrum I P).adicCompletionIntegers K) := by
      simpa only [v, factorHeightSpectrum] using
        adic_integers_maximal
          (K := K) v

end

end Submission.NumberTheory.Milne
