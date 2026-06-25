import Submission.NumberTheory.Completions.LowerLocalSetup
import Submission.NumberTheory.Completions.LocalUniformExponent
import Submission.NumberTheory.Dedekind.LocalizationQuotientPowers

/-!
# Compatibility of completed and localized different exponents

The explicit exponent formed from the completed valuation integer ring of
the maximal ideal of `R_p` agrees with the exponent formed directly in
`R_p`.  Thus it is exactly `differentExponentIdeal p ...`.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain

noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDedekindDomain R] [CharZero R]

set_option synthInstance.maxHeartbeats 200000 in
-- Completion and residue-field instances unfold through two localizations.
/-- The explicit different exponent formed in the completed valuation
integer ring of the maximal ideal of `R_p`. -/
noncomputable def completedDifferentIdeal
    [Ring.HasFiniteQuotients R]
    (p : Ideal R) (hprime : p.IsPrime) (hp : p ≠ ⊥) (N : ℕ) : ℕ := by
  letI : p.IsPrime := hprime
  let P : HeightOneSpectrum R := ⟨p, hprime, hp⟩
  letI : p.IsMaximal := P.isMaximal
  let A := Localization.AtPrime p
  let K := FractionRing R
  letI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      R hp A
  letI : CharZero A :=
    CharZero.of_addMonoidHom
      (algebraMap R A).toAddMonoidHom
      (by simp)
      (IsLocalization.injective A p.primeCompl_le_nonZeroDivisors)
  let v := maximalHeightSpectrum p hp
  let C := v.adicCompletionIntegers K
  letI : Finite (R ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient hp
  let eResidue : R ⧸ p ^ 1 ≃+* A ⧸ IsLocalRing.maximalIdeal A :=
    (quotientLocalizationPrime R p 1).trans
      (Ideal.quotEquivOfEq (by
        rw [pow_one, IsLocalization.AtPrime.map_eq_maximalIdeal]))
  letI : Finite (R ⧸ p ^ 1) := by
    simpa only [pow_one] using (inferInstance : Finite (R ⧸ p))
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Finite.of_equiv (R ⧸ p ^ 1) eResidue.toEquiv
  letI : Finite (A ⧸ v.asIdeal) := by
    simpa only [v, height_spectrum_ideal] using
      (inferInstance : Finite (A ⧸ IsLocalRing.maximalIdeal A))
  letI : CharZero C :=
    CharZero.of_addMonoidHom
      (algebraMap A C).toAddMonoidHom
      (by simp)
      (FaithfulSMul.algebraMap_injective A C)
  exact N *
    (dvrCastValuation C N.factorial + 1)

set_option synthInstance.maxHeartbeats 200000 in
-- The two localized DVR structures and the completed valuation ring unfold deeply.
set_option maxHeartbeats 1000000 in
/-- The completed-base exponent is the local exponent used in the uniform
different bound. -/
theorem completed_different_ideal
    [Ring.HasFiniteQuotients R]
    (p : Ideal R) (hprime : p.IsPrime) (hp : p ≠ ⊥) (N : ℕ) :
    completedDifferentIdeal p hprime hp N =
      differentExponentIdeal p hprime hp N := by
  letI : p.IsPrime := hprime
  let P : HeightOneSpectrum R := ⟨p, hprime, hp⟩
  letI : p.IsMaximal := P.isMaximal
  let A := Localization.AtPrime p
  let K := FractionRing R
  letI : Algebra A K := inferInstance
  letI : IsFractionRing A K := inferInstance
  letI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      R hp A
  letI : CharZero A :=
    CharZero.of_addMonoidHom
      (algebraMap R A).toAddMonoidHom
      (by simp)
      (IsLocalization.injective A p.primeCompl_le_nonZeroDivisors)
  let v := maximalHeightSpectrum p hp
  let A' := Localization.AtPrime v.asIdeal
  let C := v.adicCompletionIntegers K
  letI : Finite (R ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient hp
  let eResidue : R ⧸ p ^ 1 ≃+* A ⧸ IsLocalRing.maximalIdeal A :=
    (quotientLocalizationPrime R p 1).trans
      (Ideal.quotEquivOfEq (by
        rw [pow_one, IsLocalization.AtPrime.map_eq_maximalIdeal]))
  letI : Finite (R ⧸ p ^ 1) := by
    simpa only [pow_one] using (inferInstance : Finite (R ⧸ p))
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Finite.of_equiv (R ⧸ p ^ 1) eResidue.toEquiv
  letI : Finite (A ⧸ v.asIdeal) := by
    simpa only [v, height_spectrum_ideal] using
      (inferInstance : Finite (A ⧸ IsLocalRing.maximalIdeal A))
  letI : CharZero C :=
    CharZero.of_addMonoidHom
      (algebraMap A C).toAddMonoidHom
      (by simp)
      (FaithfulSMul.algebraMap_injective A C)
  letI : IsDiscreteValuationRing A' :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A v.ne_bot A'
  letI : CharZero A' :=
    CharZero.of_addMonoidHom
      (algebraMap A A').toAddMonoidHom
      (by simp)
      (IsLocalization.injective A' v.asIdeal.primeCompl_le_nonZeroDivisors)
  have hcompleted : dvrCastValuation C N.factorial =
      dvrCastValuation A' N.factorial :=
    dvr_valuation_integers
      (R := A) (K := K) v N.factorial
  letI : Module.IsTorsionFree A A' := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact IsLocalization.injective A' v.asIdeal.primeCompl_le_nonZeroDivisors
  have hlocalized : dvrCastValuation A' N.factorial =
      dvrCastValuation A N.factorial := by
    apply dvr_valuation_maximal A A'
    change v.asIdeal.map (algebraMap A A') = IsLocalRing.maximalIdeal A'
    exact Localization.AtPrime.map_eq_maximalIdeal (I := v.asIdeal)
  have hvaluation : dvrCastValuation C N.factorial =
      dvrCastValuation A N.factorial := hcompleted.trans hlocalized
  change N * (dvrCastValuation C N.factorial + 1) =
    N * (dvrCastValuation A N.factorial + 1)
  rw [hvaluation]

end

end Submission.NumberTheory.Milne
