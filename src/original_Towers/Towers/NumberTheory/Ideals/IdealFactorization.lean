import Towers.NumberTheory.Dedekind.DedekindLocalizations

/-!
# Milne, Algebraic Number Theory, Theorem 3.7 and Lemma 3.9

Nonzero ideals in a Dedekind domain have a canonical multiset of prime factors. Its
multiplicities are the uniquely determined exponents in Milne's factorization theorem.
-/

namespace Towers.NumberTheory.Milne

open UniqueFactorizationMonoid

/-- Lemma 3.8 in its general noetherian-ring form: every ideal contains a product of
prime ideals. -/
theorem ideal_contains_ideals
    (A : Type*) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ Z : Multiset (PrimeSpectrum A),
      (Z.map PrimeSpectrum.asIdeal).prod ≤ I := by
  exact PrimeSpectrum.exists_primeSpectrum_prod_le A I

/-- The nonzero-domain form of Lemma 3.8. Here the product is nonzero, so none of its
prime-ideal factors can be the zero ideal. -/
theorem nonzero_contains_ideals
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hA : ¬IsField A) {I : Ideal A} (hI : I ≠ ⊥) :
    ∃ Z : Multiset (PrimeSpectrum A),
      (Z.map PrimeSpectrum.asIdeal).prod ≤ I ∧
        (Z.map PrimeSpectrum.asIdeal).prod ≠ ⊥ := by
  exact PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain hA hI

/-- Theorem 3.7 in canonical-multiset form. The product of the normalized prime factors is
the original ideal, and membership in the multiset is equivalent to being a prime ideal
containing it. Repeated membership records the unique exponent of that prime. -/
theorem ideal_normalized_factors
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥) :
    (normalizedFactors I).prod = I ∧
      ∀ P : Ideal A,
        P ∈ normalizedFactors I ↔ P.IsPrime ∧ I ≤ P := by
  exact ⟨Ideal.prod_normalizedFactors_eq_self hI,
    fun P => Ideal.mem_normalizedFactors_iff hI⟩

/-- Remark 3.12: a prime has positive multiplicity in the factorization of a nonzero ideal
exactly when it contains that ideal. -/
theorem prime_normalized_factors
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsPrime) :
    P ∈ normalizedFactors I ↔ I ≤ P := by
  simpa [hP] using (Ideal.mem_normalizedFactors_iff (I := I) hI (p := P))

/-- Remark 3.12 in its localization form: a prime occurs with positive multiplicity in a
nonzero ideal exactly when that ideal remains proper after localization at the prime. -/
theorem normalized_localization_top
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsPrime) :
    P ∈ normalizedFactors I ↔
      Ideal.map (algebraMap A (Localization.AtPrime P)) I ≠ ⊤ := by
  letI : P.IsPrime := hP
  rw [prime_normalized_factors A I P hI hP,
    localization_ne_top]

/-- Lemma 3.9: powers of relatively prime ideals remain relatively prime. -/
theorem coprime_ideal_powers
    (A : Type*) [CommRing A] (I J : Ideal A)
    (h : IsCoprime I J) (m n : ℕ) :
    IsCoprime (I ^ m) (J ^ n) := by
  exact h.pow

/-- The consequence following Lemma 3.9: powers of two distinct nonzero prime ideals in
a Dedekind domain are relatively prime. -/
theorem distinct_powers_coprime
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (P Q : Ideal A) (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hP0 : P ≠ ⊥) (hQ0 : Q ≠ ⊥) (hPQ : P ≠ Q) (m n : ℕ) :
    IsCoprime (P ^ m) (Q ^ n) := by
  letI : P.IsMaximal := hP.isMaximal hP0
  letI : Q.IsMaximal := hQ.isMaximal hQ0
  exact (Ideal.isCoprime_of_isMaximal hPQ).pow

/-- The remark after Corollary 3.13: for nonzero ideals in a Dedekind domain, ideal
divisibility is precisely reverse set-theoretic inclusion. -/
theorem dvd_reverse_inclusion
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (I J : Ideal A) :
    I ∣ J ↔ J ≤ I := by
  exact Ideal.dvd_iff_le

end Towers.NumberTheory.Milne
