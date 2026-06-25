import Submission.NumberTheory.Completions.AdicChineseRemainder
import Submission.NumberTheory.Completions.AdicLocalEquiv
import Submission.NumberTheory.Dedekind.LocalizationQuotientPowers
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Assembly of semilocal completions

Prime-adic completion commutes with localization at that prime.  Combining
this fact with Chinese remaindering and the concrete local-completion
equivalence identifies completion at a nonzero Dedekind ideal with the
product of the completed valuation integer rings at its prime factors.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain

noncomputable section

universe u

variable {R K : Type u} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private noncomputable def powTransportPrime
    (P : HeightOneSpectrum R) (n : ℕ) :
    R ⧸ P.asIdeal ^ n ≃+*
      Localization.AtPrime P.asIdeal ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ n := by
  letI : P.asIdeal.IsMaximal := P.isMaximal
  exact (quotientLocalizationPrime R P.asIdeal n).trans
    (Ideal.quotEquivOfEq (by
      rw [IsLocalization.AtPrime.map_eq_maximalIdeal]))

private noncomputable def powHomPrime
    (P : HeightOneSpectrum R) (n : ℕ) :
    R ⧸ P.asIdeal ^ n →+*
      Localization.AtPrime P.asIdeal ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ n :=
  (powTransportPrime P n).toRingHom

private theorem hom_prime_injective
    (P : HeightOneSpectrum R) (n : ℕ) :
    Function.Injective (powHomPrime P n) :=
  (powTransportPrime P n).injective

private theorem hom_prime_surjective
    (P : HeightOneSpectrum R) (n : ℕ) :
    Function.Surjective (powHomPrime P n) :=
  (powTransportPrime P n).surjective

/-- Quotienting at a prime power commutes with localization at that prime. -/
private noncomputable def quotientPowPrime
    (P : HeightOneSpectrum R) (n : ℕ) :
    R ⧸ P.asIdeal ^ n ≃+*
      Localization.AtPrime P.asIdeal ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ n :=
  RingEquiv.ofBijective (powHomPrime P n)
    ⟨hom_prime_injective P n, hom_prime_surjective P n⟩

private noncomputable def adicQuotientPrime
    (P : HeightOneSpectrum R) (n : ℕ) :
    (R ⧸ (P.asIdeal ^ n • (⊤ : Submodule R R))) ≃+*
      (Localization.AtPrime P.asIdeal ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ n •
          (⊤ : Submodule (Localization.AtPrime P.asIdeal)
            (Localization.AtPrime P.asIdeal)))) :=
  (Ideal.quotEquivOfEq (by simp)).trans <|
    (quotientPowPrime P n).trans <|
      Ideal.quotEquivOfEq (by simp)

@[simp]
private theorem adic_prime_mk
    (P : HeightOneSpectrum R) (n : ℕ) (x : R) :
    adicQuotientPrime P n
        (Submodule.mkQ (P.asIdeal ^ n • (⊤ : Submodule R R)) x) =
      Submodule.mkQ
        (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ n •
          (⊤ : Submodule (Localization.AtPrime P.asIdeal)
            (Localization.AtPrime P.asIdeal)))
        (algebraMap R (Localization.AtPrime P.asIdeal) x) :=
  rfl

private theorem adic_prime_transition
    (P : HeightOneSpectrum R) {m n : ℕ} (hmn : m ≤ n)
    (x : R ⧸ (P.asIdeal ^ n • (⊤ : Submodule R R))) :
    AdicCompletion.transitionMap
        (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal))
        (Localization.AtPrime P.asIdeal) hmn
        (adicQuotientPrime P n x) =
      adicQuotientPrime P m
        (AdicCompletion.transitionMap P.asIdeal R hmn x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change AdicCompletion.transitionMap
          (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal))
          (Localization.AtPrime P.asIdeal) hmn
          (adicQuotientPrime P n
            (Submodule.mkQ (P.asIdeal ^ n • (⊤ : Submodule R R)) x)) =
        adicQuotientPrime P m
          (AdicCompletion.transitionMap P.asIdeal R hmn
            (Submodule.mkQ (P.asIdeal ^ n • (⊤ : Submodule R R)) x))
      rw [adic_prime_mk]
      change Submodule.factor _ (Submodule.mkQ _ _) =
        adicQuotientPrime P m
          (Submodule.factor _ (Submodule.mkQ _ x))
      rw [Submodule.factor_mk, Submodule.factor_mk]
      rw [adic_prime_mk]

private theorem adic_symm_transition
    (P : HeightOneSpectrum R) {m n : ℕ} (hmn : m ≤ n)
    (x : Localization.AtPrime P.asIdeal ⧸
      (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ n •
        (⊤ : Submodule (Localization.AtPrime P.asIdeal)
          (Localization.AtPrime P.asIdeal)))) :
    AdicCompletion.transitionMap P.asIdeal R hmn
        ((adicQuotientPrime P n).symm x) =
      (adicQuotientPrime P m).symm
        (AdicCompletion.transitionMap
          (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal))
          (Localization.AtPrime P.asIdeal) hmn x) := by
  apply (adicQuotientPrime P m).injective
  rw [RingEquiv.apply_symm_apply]
  rw [← adic_prime_transition]
  rw [RingEquiv.apply_symm_apply]

/-- Global prime-adic completion agrees with completion after localization
at that prime. -/
noncomputable def adicCompletionPrime
    (P : HeightOneSpectrum R) :
    AdicCompletion P.asIdeal R ≃+*
      AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal))
        (Localization.AtPrime P.asIdeal) where
  toFun x := ⟨fun n => adicQuotientPrime P n (x.val n),
    fun hmn => by
      rw [adic_prime_transition]
      rw [x.property hmn]⟩
  invFun x := ⟨fun n => (adicQuotientPrime P n).symm (x.val n),
    fun hmn => by
      rw [adic_symm_transition]
      rw [x.property hmn]⟩
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (adicQuotientPrime P n).symm_apply_apply (x.val n)
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (adicQuotientPrime P n).apply_symm_apply (x.val n)
  map_mul' x y := by
    apply AdicCompletion.ext
    intro n
    exact map_mul (adicQuotientPrime P n) (x.val n) (y.val n)
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact map_add (adicQuotientPrime P n) (x.val n) (y.val n)

@[simp]
theorem adic_completion_equiv
    (P : HeightOneSpectrum R) (x : R) :
    adicCompletionPrime P (AdicCompletion.of P.asIdeal R x) =
      AdicCompletion.of
        (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal))
        (Localization.AtPrime P.asIdeal)
        (algebraMap R (Localization.AtPrime P.asIdeal) x) := by
  apply AdicCompletion.ext
  intro n
  exact adic_prime_mk P n x

open UniqueFactorizationMonoid

/-- Regard a prime factor of a nonzero Dedekind ideal as a height-one
prime. -/
noncomputable def factorHeightSpectrum
    (I : Ideal R) (P : (factors I).toFinset) : HeightOneSpectrum R := by
  have hp : Prime (P : Ideal R) :=
    prime_of_factor (P : Ideal R) (Multiset.mem_toFinset.mp P.prop)
  exact ⟨P, Ideal.isPrime_of_prime hp, hp.ne_zero⟩

set_option synthInstance.maxHeartbeats 100000 in
-- Typeclass search reconstructs a ring structure on a dependent product.
set_option maxHeartbeats 1000000 in
-- Elaborating the product of the concrete local equivalences is expensive.
/-- A nonzero ideal-adic completion of a Dedekind domain with finite
quotients is the product of the concrete completed valuation integer rings
at its prime factors. -/
noncomputable def completionPiIntegers
    [Ring.HasFiniteQuotients R] (I : Ideal R) (hI : I ≠ ⊥) :
    AdicCompletion I R ≃+*
      (∀ P : (factors I).toFinset,
        (factorHeightSpectrum I P).adicCompletionIntegers K) :=
  (adicPiFactors I hI).trans <|
    RingEquiv.piCongrRight fun P => by
      let v := factorHeightSpectrum I P
      letI : Finite (R ⧸ v.asIdeal) :=
        Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      exact (adicCompletionPrime v).trans
        (adicRingEquiv (K := K) v)

end

end Submission.NumberTheory.Milne
