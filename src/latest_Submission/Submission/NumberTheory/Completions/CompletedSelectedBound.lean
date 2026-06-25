import Submission.NumberTheory.Completions.CompletedSemilocalBound
import Submission.NumberTheory.Completions.ExponentCompatibility
import Submission.NumberTheory.Completions.FractionFieldSetup


/-!
# The completed different bound at a selected semilocal prime

The uniform completed-factor estimate is specialized to the localization of
the lower Dedekind domain at a nonzero prime and the corresponding
semilocalization of the upper domain.  A global upper prime selects the
coordinate to which the estimate is applied.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

universe u

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
  Localization.AtPrime.liftAlgebra

variable {R S : Type u}
  [CommRing R] [IsDomain R] [IsDedekindDomain R] [CharZero R]
  [CommRing S] [IsDomain S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

omit [CharZero R] in
/-- Localization at a nonzero prime preserves the finite-quotient property
needed to form prime-adic completions. -/
theorem localization_prime_quotients
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

section SelectedCoordinate

set_option synthInstance.maxHeartbeats 500000 in
-- The proposition constructs the selected dependent completion coordinate.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The proposition asserting the expanded completed different bound in the
semilocal factor selected by `P`. -/
noncomputable def SelectedSemilocalDifferent
    (p : Ideal R) (hprime : p.IsPrime) (hp : p ≠ ⊥)
    (P : Ideal S) (hPprime : P.IsPrime) (_hP : P ≠ ⊥)
    [P.LiesOver p] (N : ℕ) : Prop := by
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
  letI : Ring.HasFiniteQuotients A :=
    localization_prime_quotients p hp
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
  letI : Module.IsTorsionFree C D :=
    adic_torsion_free
      (K := K) (L := L) v hmap Q
  exact differentIdeal C D ∣
    IsLocalRing.maximalIdeal D ^
      (N * (dvrCastValuation C N.factorial + 1))

set_option synthInstance.maxHeartbeats 500000 in
-- Two localizations and the selected dependent completion coordinate are
-- instantiated simultaneously.
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
omit [Ring.HasFiniteQuotients S] in
/-- The completed different at the factor selected by `P` is bounded by the
uniform exponent attached to the lower prime `p`. -/
theorem different_selected_semilocal
    (p : Ideal R) (hprime : p.IsPrime) (hp : p ≠ ⊥)
    (P : Ideal S) (hPprime : P.IsPrime) (hP : P ≠ ⊥)
    [P.LiesOver p]
    (N : ℕ)
    (hdegree : Module.finrank (FractionRing R) (FractionRing S) ≤ N) :
    SelectedSemilocalDifferent
      p hprime hp P hPprime hP N := by
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
  letI : Ring.HasFiniteQuotients A :=
    localization_prime_quotients p hp
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
    adicCompletionAlgebra
      (K := K) (L := L) v hmap Q
  letI : CharZero C := adicIntegersChar (K := K) v
  letI : Module.IsTorsionFree C D :=
    adic_torsion_free
      (K := K) (L := L) v hmap Q
  exact different_dvd_maximal
    (R := A) (S := B) (K := K) (L := L) v hmap N hdegree Q

end SelectedCoordinate

end

end Submission.NumberTheory.Milne
