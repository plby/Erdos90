import Towers.NumberTheory.Completions.DifferentAdicRecovery
import Towers.NumberTheory.Completions.LocalizedUniformBound
import Towers.NumberTheory.Globals.UnramifiedExtensionFiniteness

/-!
# Milne's finiteness theorem for extensions with restricted ramification

This file closes the completion argument and applies the resulting uniform
localized different bound to the Hermite reduction.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain Module nonZeroDivisors
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

set_option synthInstance.maxHeartbeats 500000 in
-- The recovery theorem and the descent wrapper use the same two localized
-- fraction-field towers and the same dependent completion coordinate.
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
omit [Ring.HasFiniteQuotients S] in
/-- The uniform localized different bound at every nonzero upper prime. -/
theorem localized_different_uniform
    (p : Ideal R) (hprime : p.IsPrime) (hp : p ≠ ⊥)
    (P : Ideal S) (hPprime : P.IsPrime) (_hP : P ≠ ⊥)
    [P.LiesOver p]
    (N : ℕ) (hdegree : Module.finrank (FractionRing R) (FractionRing S) ≤ N) :
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
  letI : Module.Free A B := semilocalization_module_free p hp
  let κ := Module.Free.ChooseBasisIndex A B
  letI : Finite κ := semilocalization_choose_basis p
  let b : Basis κ A B := Module.Free.chooseBasis A B
  let C := v.adicCompletionIntegers K
  let D := (factorHeightSpectrum
    (v.asIdeal.map (algebraMap A B)) Q).adicCompletionIntegers L
  letI : Algebra C D :=
    adicCompletionAlgebra (K := K) (L := L) v hmap Q
  letI : CharZero C := adicIntegersChar (K := K) v
  letI : Module.IsTorsionFree C D :=
    adic_torsion_free (K := K) (L := L) v hmap Q
  have hcompleted :
      (differentIdeal A B).map (algebraMap B D) =
        differentIdeal C D :=
    different_adic_factor
      (R := A) (S := B) (K := K) (L := L) v hmap b Q
  have hbound : differentIdeal C D ∣
      IsLocalRing.maximalIdeal D ^
        (N * (dvrCastValuation C N.factorial + 1)) :=
    different_dvd_maximal
      (K := K) (L := L) v hmap N hdegree Q
  have hbound' : differentIdeal C D ∣
      IsLocalRing.maximalIdeal D ^
        differentExponentIdeal p hprime hp N := by
    rw [← completed_different_ideal p hprime hp N]
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
  rw [Ideal.map_pow, maximal_ideal_semilocal,
    different_ideal_semilocal]
  exact hsemilocal

section

variable (A : Type u) [Field A] [CharZero A]

set_option synthInstance.maxHeartbeats 500000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/-- Milne's Theorem 8.42: for a number field `K`, a finite set `T` of
nonzero primes in the integer ring of `K`, and a relative degree `N`, only finitely many
embedded extensions of degree `N` are unramified outside `T`. -/
theorem finite_extensions_outside
    (K : EmbeddedNumberField A)
    (T : Finset (Ideal (NumberField.RingOfIntegers K))) (N : ℕ)
    (hprime : ∀ p ∈ T, p.IsPrime) (hne : ∀ p ∈ T, p ≠ ⊥) :
    {L : EmbeddedNumberField A |
      ∃ hKL : K.1 ≤ L.1,
        embeddedRelativeDegree A K L hKL = N ∧
          IsUnramifiedOutside A K L hKL T}.Finite := by
  letI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
  let m := differentExponentBound T hprime hne N
  apply extensions_outside_localized
    A K T N m hne
  intro L hKL hdegree _ P hP _ hPT
  letI : NumberField L := @NumberField.mk _ _ inferInstance L.prop
  letI : Algebra K L :=
    RingHom.toAlgebra (IntermediateField.inclusion hKL)
  let R := NumberField.RingOfIntegers K
  let S := NumberField.RingOfIntegers L
  let p : Ideal R := P.under R
  change p ∈ T at hPT
  have hp : p ≠ ⊥ := hne p hPT
  let hpprime : p.IsPrime := hprime p hPT
  let hPprime : P.IsPrime := inferInstance
  letI : P.LiesOver p := inferInstance
  letI : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra _ _
  have hdegree' :
      Module.finrank (FractionRing R) (FractionRing S) =
        embeddedRelativeDegree A K L hKL := by
    apply Algebra.finrank_eq_of_equiv_equiv
      (FractionRing.algEquiv R K).toRingEquiv
      (FractionRing.algEquiv S L).toRingEquiv
    ext x
    exact congrArg (fun y : L.1 => (y : A))
      (IsFractionRing.algEquiv_commutes
        (FractionRing.algEquiv R K)
        (FractionRing.algEquiv S L) x)
  have hfinrank :
      Module.finrank (FractionRing R) (FractionRing S) ≤ N := by
    rw [hdegree', hdegree]
  have hlocal := localized_different_uniform
    (R := R) (S := S) p hpprime hp P hPprime hP N hfinrank
  have hexponent :
      differentExponentIdeal p hpprime hp N ≤ m := by
    simpa only [m] using
      different_exponent_bound T hprime hne N hPT
  change (differentIdeal R S).map
      (algebraMap S (Localization.AtPrime P)) ∣
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ m
  exact hlocal.trans (pow_dvd_pow _ hexponent)

end

end

end Towers.NumberTheory.Milne
