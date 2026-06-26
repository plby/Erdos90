import Submission.NumberTheory.Completions.AdicDenseEquiv
import Submission.NumberTheory.Completions.AdicIntegersComplete
import Submission.NumberTheory.Completions.AdicLocalRing

/-!
# The abstract adic completion of a local Dedekind ring

The localization of a Dedekind domain at a height-one prime is dense and
faithfully flat in the integer ring of its adic completion.  Its abstract
maximal-ideal-adic completion is therefore canonically isomorphic to that
completed valuation ring.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain HeightOneSpectrum WithZeroMulInt WithZero
open scoped WithZero Valued algebraMap Topology

noncomputable section

universe u

variable {R K : Type u} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

set_option synthInstance.maxHeartbeats 300000 in
-- The target ideals unfold the completed valuation ring during synthesis.
set_option maxHeartbeats 800000 in
-- The contraction proof unfolds both completed valuation-ring ideals.
/-- The dense local map identifies the abstract completions of the local
ring and the completed valuation ring. -/
noncomputable def adicPrimeIntegers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal))
        (Localization.AtPrime v.asIdeal) ≃+*
      AdicCompletion
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (v.adicCompletionIntegers K) := by
  let A := Localization.AtPrime v.asIdeal
  let B := v.adicCompletionIntegers K
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let M : Ideal B := IsLocalRing.maximalIdeal B
  let f : A →+* B := primeAdicIntegers (K := K) v
  letI : IsTopologicalRing B :=
    Subring.instIsTopologicalRing
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer
  letI : Algebra A B := f.toAlgebra
  letI : Module.FaithfullyFlat A B :=
    integers_faithfully_flat (K := K) v
  apply adicDenseRing f m M
  · exact adic_integers_range (K := K) v
  · intro n
    exact open_maximal_integers (K := K) v n
  · intro n
    have hmap : (m ^ n).map f = M ^ n :=
      by
        simpa only [m, M, f, A, B] using
          maximal_adic_integers (K := K) v n
    calc
      (M ^ n).comap f = ((m ^ n).map f).comap f := by rw [hmap]
      _ = m ^ n := by
        change ((m ^ n).map (algebraMap A B)).comap
          (algebraMap A B) = m ^ n
        exact Ideal.comap_map_eq_self_of_faithfullyFlat (m ^ n)

set_option synthInstance.maxHeartbeats 300000 in
-- The target completeness instance unfolds the valuation integer ring.
/-- The maximal-ideal-adic completion of the local ring at `v` is the
integer ring in the `v`-adic completion of the fraction field. -/
noncomputable def adicRingEquiv
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal))
        (Localization.AtPrime v.asIdeal) ≃+*
      v.adicCompletionIntegers K := by
  let M := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  letI : IsAdicComplete M (v.adicCompletionIntegers K) :=
    adic_integers_complete (K := K) v
  exact (adicPrimeIntegers (K := K) v).trans
    (AdicCompletion.ofAlgEquiv M).symm.toRingEquiv

set_option synthInstance.maxHeartbeats 300000 in
-- Unfolding the completed valuation-ring topology is expensive.
@[simp]
theorem adic_ring_equiv
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    (x : Localization.AtPrime v.asIdeal) :
    adicRingEquiv (K := K) v
        (AdicCompletion.of
          (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal))
          (Localization.AtPrime v.asIdeal) x) =
      primeAdicIntegers (K := K) v x := by
  let M := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  letI : IsTopologicalRing (v.adicCompletionIntegers K) :=
    Subring.instIsTopologicalRing
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer
  letI : IsAdicComplete M (v.adicCompletionIntegers K) :=
    adic_integers_complete (K := K) v
  rw [adicRingEquiv]
  rw [RingEquiv.trans_apply]
  rw [adicPrimeIntegers]
  rw [adic_dense_ring]
  exact AdicCompletion.ofAlgEquiv_symm_of _ _

end

end Submission.NumberTheory.Milne
