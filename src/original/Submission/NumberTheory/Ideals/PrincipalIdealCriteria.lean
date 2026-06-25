import Mathlib

/-!
# Milne, Algebraic Number Theory, Corollary 3.14, Proposition 3.18, and Theorem 3.20

We record two criteria making a Dedekind domain principal and the invertibility of every
nonzero fractional ideal.
-/

namespace Submission.NumberTheory.Milne

/-- Corollary 3.14: for a domain with finitely many prime ideals, being Dedekind is
equivalent to being a principal ideal domain. -/
theorem dedekind_domain_primes
    (R : Type*) [CommRing R] [IsDomain R]
    (hfinite : {I : Ideal R | I.IsPrime}.Finite) :
    IsDedekindDomain R ↔ IsPrincipalIdealRing R := by
  constructor
  · intro hDedekind
    letI : IsDedekindDomain R := hDedekind
    exact IsPrincipalIdealRing.of_finite_primes hfinite
  · intro hPrincipal
    letI : IsPrincipalIdealRing R := hPrincipal
    infer_instance

/-- Proposition 3.18: a Dedekind domain that is a UFD is a PID. -/
theorem dedekind_domain_monoid
    (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [UniqueFactorizationMonoid R] :
    IsPrincipalIdealRing R := by
  exact IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid R

/-- The group assertion in Theorem 3.20: every nonzero fractional ideal of a Dedekind
domain has a multiplicative inverse. -/
theorem fractional_ne_zero
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (I : FractionalIdeal (nonZeroDivisors R) (FractionRing R))
    (hI : I ≠ 0) :
    IsUnit I := by
  exact hI.isUnit

/-- The free-abelian factorization assertion in Theorem 3.20. The integer
`FractionalIdeal.count (FractionRing R) v I` is the uniquely determined exponent of the
nonzero prime ideal `v` in `I`. -/
theorem fractional_finprod_powers
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (I : FractionalIdeal (nonZeroDivisors R) (FractionRing R))
    (hI : I ≠ 0) :
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) ^
          FractionalIdeal.count (FractionRing R) v I = I := by
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization' (FractionRing R) hI

/-- The uniqueness assertion in Theorem 3.20: a nonzero fractional ideal has a unique
finitely supported family of integer exponents at the nonzero prime ideals. -/
theorem fractional_unique_exponents
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (I : FractionalIdeal (nonZeroDivisors R) (FractionRing R))
    (hI : I ≠ 0) :
    ∃! exps : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ,
      exps.prod (fun v n ↦
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) ^ n) = I := by
  let h := FractionalIdeal.finite_factors I
  let exps : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ :=
    Finsupp.mk h.toFinset
      (fun v ↦ FractionalIdeal.count (FractionRing R) v I)
      (fun _ ↦ h.mem_toFinset)
  refine ⟨exps, ?_, ?_⟩
  · rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      (K := FractionRing R) hI]
    dsimp only [exps, Finsupp.prod]
    rw [finprod_eq_finsetProd_of_mulSupport_subset (s := h.toFinset)]
    · rfl
    · rw [Set.Finite.coe_toFinset]
      intro v hv hvpow
      rw [Function.mem_mulSupport, hvpow, zpow_zero] at hv
      exact hv rfl
  · intro other hother
    apply Finsupp.ext
    intro v
    change other v = FractionalIdeal.count (FractionRing R) v I
    rw [← hother]
    exact (FractionalIdeal.count_finsuppProd (FractionRing R) v other).symm

end Submission.NumberTheory.Milne
