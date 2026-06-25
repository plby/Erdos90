import Submission.NumberTheory.Ramification.FactorizationInExtensions
import Submission.NumberTheory.Density.ChebotarevDensity
import Submission.NumberTheory.Density.PrimeIdealNatural
import Submission.NumberTheory.Splitting


/-!
# Completely split primes and the infinitude consequence of Chebotarev

This file defines Milne's set `Spl(L/K)` of finite primes splitting completely
in a number-field extension.  It also proves the final assertion of Corollary
8.32 from its density formula: a positive-density splitting set is infinite.

The analytic Chebotarev theorem itself is not currently available in
Mathlib; the exact splitting consequences are proved from its explicit
proposition in `CDensit`.
-/

namespace Submission.NumberTheory.Milne

open IsDedekindDomain NumberField
open scoped NumberField

noncomputable section

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- A finite prime of `K` splits completely in `L` when it has `[L : K]`
distinct primes above it, all with ramification index and inertia degree one. -/
def SplitsCompletelyAt
    (p : HeightOneSpectrum (𝓞 K)) : Prop :=
  (Ideal.primesOver p.asIdeal (𝓞 L)).ncard = Module.finrank K L ∧
    ∀ P ∈ Ideal.primesOver p.asIdeal (𝓞 L),
      Ideal.ramificationIdx p.asIdeal P = 1 ∧
        Ideal.inertiaDeg p.asIdeal P = 1

/-- Milne's `Spl(L/K)`, the set of finite primes splitting completely in the
extension. -/
def splittingPrimes : Set (HeightOneSpectrum (𝓞 K)) :=
  {p | SplitsCompletelyAt K L p}

omit [NumberField K] [NumberField L] in
@[simp]
theorem splitting_primes (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ splittingPrimes K L ↔ SplitsCompletelyAt K L p :=
  Iff.rfl

/-- In a finite Galois extension, one prime above `p` with ramification and
inertia degrees both one forces `p` to split completely. -/
theorem splits_completely_prime
    [FiniteDimensional K L] [IsGalois K L]
    (p : HeightOneSpectrum (𝓞 K))
    (P : Ideal (𝓞 L)) (hP : P ∈ Ideal.primesOver p.asIdeal (𝓞 L))
    (he : Ideal.ramificationIdx p.asIdeal P = 1)
    (hf : Ideal.inertiaDeg p.asIdeal P = 1) :
    SplitsCompletelyAt K L p := by
  letI := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  letI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p.asIdeal := hP.2
  have heIn : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx
      (p := p.asIdeal) (P := P) (B := 𝓞 L) (G := Gal(L/K))]
    exact he
  have hfIn : Ideal.inertiaDegIn p.asIdeal (𝓞 L) = 1 := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg
      (p := p.asIdeal) (P := P) (B := 𝓞 L) (G := Gal(L/K))]
    exact hf
  have hcount :
      (Ideal.primesOver p.asIdeal (𝓞 L)).ncard = Module.finrank K L := by
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := p.asIdeal) (B := 𝓞 L) (G := Gal(L/K)) p.ne_bot
    rw [heIn, hfIn, one_mul, mul_one, IsGalois.card_aut_eq_finrank] at h
    exact h
  refine ⟨hcount, ?_⟩
  intro Q hQ
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver p.asIdeal := hQ.2
  constructor
  · calc
      Ideal.ramificationIdx p.asIdeal Q =
          Ideal.ramificationIdx p.asIdeal P :=
        Ideal.ramificationIdx_eq_of_isGaloisGroup
          p.asIdeal Q P Gal(L/K)
      _ = 1 := he
  · calc
      Ideal.inertiaDeg p.asIdeal Q = Ideal.inertiaDeg p.asIdeal P :=
        Ideal.inertiaDeg_eq_of_isGaloisGroup p.asIdeal Q P Gal(L/K)
      _ = 1 := hf

/-- For a finite Galois extension, the standard partial Frobenius class is
the identity exactly at the primes that split completely. -/
theorem arithmetic_option_identity
    [FiniteDimensional K L] [IsGalois K L]
    (p : HeightOneSpectrum (𝓞 K)) :
    arithmeticFrobeniusOption K L p =
        some (ConjClasses.mk (1 : Gal(L/K))) ↔
      SplitsCompletelyAt K L p := by
  classical
  by_cases hram : p ∈ ramifiedPrimes K L
  · constructor
    · intro h
      simp [arithmeticFrobeniusOption, hram] at h
    · intro hsplit
      rcases hram with ⟨Q, hQprime, hQ0, hQunder, hQram⟩
      have hQmem : Q ∈ Ideal.primesOver p.asIdeal (𝓞 L) :=
        ⟨hQprime, ⟨hQunder.symm⟩⟩
      exact (hQram (hsplit.2 Q hQmem).1).elim
  · rw [arithmeticFrobeniusOption]
    simp only [if_neg hram, Option.some.injEq]
    let P : Ideal (𝓞 L) := (arithmeticFrobeniusAbove K L p).1
    have hPmem : P ∈ Ideal.primesOver p.asIdeal (𝓞 L) :=
      (arithmeticFrobeniusAbove K L p).2
    letI : P.IsPrime := hPmem.1
    letI : P.LiesOver p.asIdeal := hPmem.2
    have hPunder : P.under (𝓞 K) = p.asIdeal :=
      (Ideal.LiesOver.over (p := p.asIdeal) (P := P)).symm
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver p.ne_bot hPmem
    haveI : Finite (𝓞 L ⧸ P) :=
      Ring.HasFiniteQuotients.finiteQuotient hP0
    have heP : Ideal.ramificationIdx p.asIdeal P = 1 := by
      by_contra heP
      apply hram
      exact ⟨P, hPmem.1, hP0, hPunder, heP⟩
    letI : Algebra.IsUnramifiedAt (𝓞 K) P :=
      (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
        (R := 𝓞 K) (S := 𝓞 L) (p := P) hP0).2 (by
          simpa [hPunder] using heP)
    letI := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    letI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
      IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
    have hfrob :
        arithFrobAt (𝓞 K) Gal(L/K) P = 1 ↔
          Ideal.inertiaDeg p.asIdeal P = 1 := by
      simpa [hPunder] using
        (number_frob_deg
          (K := K) (L := L) P)
    have hclass :
        arithmeticFrobeniusClass K L p =
            ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) P) := by
      rfl
    rw [hclass, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left, hfrob]
    constructor
    · intro hf
      exact splits_completely_prime K L p P hPmem heP hf
    · intro hsplit
      exact (hsplit.2 P hPmem).2

/-- The completely split primes are exactly the primes with defined,
identity Frobenius class. -/
theorem splitting_identity_frobenius
    [FiniteDimensional K L] [IsGalois K L] :
    splittingPrimes K L =
      primesFrobeniusClass K (arithmeticFrobeniusOption K L)
        (ConjClasses.mk (1 : Gal(L/K))) := by
  ext p
  exact (arithmetic_option_identity K L p).symm

/-- Milne, Corollary 8.32: Chebotarev gives the completely split primes
density `1 / [L : K]`. -/
theorem splitting_density_chebotarev
    [FiniteDimensional K L] [IsGalois K L]
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K (splittingPrimes K L)
      (1 / Module.finrank K L : ℝ) := by
  have hoption :
      ChebotarevDensityProperty K (arithmeticFrobeniusOption K L) :=
    (chebotarev_property_option K L).2 hcheb
  rw [splitting_identity_frobenius K L]
  convert identity_frobenius_density K hoption using 1
  rw [IsGalois.card_aut_eq_finrank]

/-- Milne, Corollary 8.32, infinitude assertion: once Chebotarev supplies the
density `1 / [L : K]`, infinitely many primes split completely in `L`. -/
theorem splitting_primes_density
    (hdensity : PNDensit K (splittingPrimes K L)
      (1 / Module.finrank K L : ℝ)) :
    (splittingPrimes K L).Infinite := by
  apply Set.Infinite.prime_ideal_densi K hdensity
  apply one_div_pos.mpr
  exact_mod_cast Module.finrank_pos

/-- The infinitude conclusion of Corollary 8.32, now derived directly from
Chebotarev rather than requiring the density formula as a separate input. -/
theorem splitting_infinite_chebotarev
    [FiniteDimensional K L] [IsGalois K L]
    (hcheb : ChebotarevDensityTheorem K L) :
    (splittingPrimes K L).Infinite :=
  splitting_primes_density K L
    (splitting_density_chebotarev K L hcheb)

/-- The unconditional rational-base infinitude part of Corollary 8.32: in a
finite Galois number field, completely split rational primes are unbounded. -/
theorem splitting_completely_unbounded
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M] [IsGalois ℚ M] :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ Submission.splitsCompletely M p :=
  Submission.SPExist.prime_splits_completely M

end

end Submission.NumberTheory.Milne
