import Submission.NumberTheory.Completions.ExponentCompatibility
import Submission.NumberTheory.Completions.FractionFieldSetup
import Submission.NumberTheory.Completions.SemilocalCoordinateDescent
import Submission.NumberTheory.Completions.CompletedSemilocalBound


/-!
# The uniform localized different bound

This file assembles the completed semilocal calculation into the local ideal
bound used in Milne's proof of Theorem 8.42.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- A localization of a Dedekind domain with finite quotients at a nonzero
prime again has finite quotients. -/
theorem prime_finite_quotients
    [Ring.HasFiniteQuotients R]
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    Ring.HasFiniteQuotients (Localization.AtPrime p) := by
  let P : HeightOneSpectrum R := ⟨p, inferInstance, hp⟩
  letI : p.IsMaximal := P.isMaximal
  let A := Localization.AtPrime p
  letI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      R hp A
  constructor
  intro I hI
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal A
    (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal A)) I hI
  letI : Finite (R ⧸ p ^ n) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero n hp)
  let e : R ⧸ p ^ n ≃+*
      A ⧸ IsLocalRing.maximalIdeal A ^ n :=
    (quotientLocalizationPrime R p n).trans
      (Ideal.quotEquivOfEq (by
        rw [IsLocalization.AtPrime.map_eq_maximalIdeal]))
  rw [hn]
  exact Finite.of_equiv (R ⧸ p ^ n) e.toEquiv

section Assembly

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
  Localization.AtPrime.liftAlgebra

variable {S : Type u} [CommRing S] [IsDomain S] [IsDedekindDomain S]
  [CharZero R] [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

set_option synthInstance.maxHeartbeats 500000 in
-- The proof specializes the completed product bound to two localizations.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
omit [Ring.HasFiniteQuotients S] in
/-- The final descent step, assuming the concrete identification of the
completed image of the semilocal different at the selected coordinate. -/
theorem localized_different_completed
    (p : Ideal R) (hprime : p.IsPrime) (hp : p ≠ ⊥)
    (P : Ideal S) (hPprime : P.IsPrime) (_hP : P ≠ ⊥)
    [P.LiesOver p]
    (N : ℕ) (hdegree : Module.finrank (FractionRing R) (FractionRing S) ≤ N)
    (hcompleted :
      letI : p.IsPrime := hprime
      letI : P.IsPrime := hPprime
      let A := Localization.AtPrime p
      let B := SemilocalizationAtPrime S p
      let K := FractionRing R
      let L := FractionRing S
      letI : IsDiscreteValuationRing A :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
          R hp A
      letI : CharZero A :=
        CharZero.of_addMonoidHom
          (algebraMap R A).toAddMonoidHom (by simp)
          (IsLocalization.injective A p.primeCompl_le_nonZeroDivisors)
      letI : Module.IsTorsionFree A B :=
        semilocalization_torsion_free p
      letI : FaithfulSMul A B :=
        (faithfulSMul_iff_algebraMap_injective A B).mpr
          (Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)
      letI : Module.Finite A B := semilocalization_prime_module p
      letI : Ring.HasFiniteQuotients A := prime_finite_quotients p hp
      letI : Ring.HasFiniteQuotients B :=
        Ring.HasFiniteQuotients.of_module_finite A B
      let v := maximalHeightSpectrum p hp
      let hmap := maximal_semilocalization_bot
        (S := S) p hp
      let Q := semilocalFactorIndex p hp P
      let C := v.adicCompletionIntegers K
      let D := (factorHeightSpectrum
        (v.asIdeal.map (algebraMap A B)) Q).adicCompletionIntegers L
      letI : Algebra C D :=
        adicCompletionAlgebra
          (K := K) (L := L) v hmap Q
      letI : CharZero C := adicIntegersChar (K := K) v
      letI : Module.IsTorsionFree C D := by
        exact adic_torsion_free
          (K := K) (L := L) v hmap Q
      (differentIdeal A B).map (algebraMap B D) = differentIdeal C D) :
    (differentIdeal R S).map
        (algebraMap S (Localization.AtPrime P)) ∣
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^
        differentExponentIdeal p hprime hp N := by
  letI : p.IsPrime := hprime
  letI : P.IsPrime := hPprime
  let A := Localization.AtPrime p
  let B := SemilocalizationAtPrime S p
  let K := FractionRing R
  let L := FractionRing S
  letI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp A
  letI : CharZero A :=
    CharZero.of_addMonoidHom
      (algebraMap R A).toAddMonoidHom (by simp)
      (IsLocalization.injective A p.primeCompl_le_nonZeroDivisors)
  letI : Module.IsTorsionFree A B :=
    semilocalization_torsion_free p
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr
      (Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)
  letI : Module.Finite A B := semilocalization_prime_module p
  letI : Ring.HasFiniteQuotients A := prime_finite_quotients p hp
  letI : Ring.HasFiniteQuotients B :=
    Ring.HasFiniteQuotients.of_module_finite A B
  letI : IsIntegralClosure S R L :=
    IsIntegralClosure.of_isIntegrallyClosed S R L
  letI : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L :=
    IsIntegralClosure.isLocalization_of_isSeparable R K L S
  letI : IsFractionRing A K := prime_fraction_ring p
  letI : IsFractionRing B L :=
    semilocalization_prime_fraction p
  letI : IsIntegralClosure B A L :=
    semilocalization_fraction_ring p
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    semilo_local_ring p
  let v := maximalHeightSpectrum p hp
  let hmap := maximal_semilocalization_bot
    (S := S) p hp
  let Q := semilocalFactorIndex p hp P
  let C := v.adicCompletionIntegers K
  let D := (factorHeightSpectrum
    (v.asIdeal.map (algebraMap A B)) Q).adicCompletionIntegers L
  letI : Algebra C D :=
    adicCompletionAlgebra (K := K) (L := L) v hmap Q
  letI : CharZero C := adicIntegersChar (K := K) v
  letI : Module.IsTorsionFree C D :=
    adic_torsion_free
      (K := K) (L := L) v hmap Q
  have hbound : differentIdeal C D ∣
      IsLocalRing.maximalIdeal D ^
        (N * (dvrCastValuation C N.factorial + 1)) :=
    different_dvd_maximal
      (K := K) (L := L) v hmap N hdegree Q
  have hbound' : differentIdeal C D ∣
      IsLocalRing.maximalIdeal D ^
        differentExponentIdeal p hprime hp N := by
    rw [← completed_different_ideal
      p hprime hp N]
    simpa only [completedDifferentIdeal, v, C] using hbound
  let q : Ideal B := sPrime p P
  let vQ := factorHeightSpectrum (v.asIdeal.map (algebraMap A B)) Q
  let e := primeEquivSemilocal p P
  letI : Finite (B ⧸ vQ.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient vQ.ne_bot
  have hsemilocal :
      (differentIdeal A B).map
          (algebraMap B (Localization.AtPrime vQ.asIdeal)) ∣
        IsLocalRing.maximalIdeal (Localization.AtPrime vQ.asIdeal) ^
          differentExponentIdeal p hprime hp N := by
    exact localized_dvd_maximal
      (K := L) vQ (differentIdeal A B) (differentIdeal C D)
      (differentExponentIdeal p hprime hp N) hcompleted hbound'
  change (differentIdeal A B).map
      (algebraMap B (Localization.AtPrime q)) ∣
    IsLocalRing.maximalIdeal (Localization.AtPrime q) ^
      differentExponentIdeal p hprime hp N at hsemilocal
  rw [Ideal.dvd_iff_le] at hsemilocal ⊢
  apply (e.toRingEquiv.idealComapOrderIso.symm.le_iff_le).mp
  change (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^
      differentExponentIdeal p hprime hp N).map e.toRingEquiv ≤
    ((differentIdeal R S).map
      (algebraMap S (Localization.AtPrime P))).map e.toRingEquiv
  dsimp only [e, q, B] at hsemilocal ⊢
  rw [Ideal.map_pow,
    maximal_ideal_semilocal,
    different_ideal_semilocal]
  exact hsemilocal

end Assembly

end

end Submission.NumberTheory.Milne
