import Mathlib

/-!
# Milne, Algebraic Number Theory, Propositions 3.4--3.6

Localization preserves the noetherian, integrally closed, and Dedekind properties. A
noetherian domain is Dedekind exactly when its localizations at nonzero prime ideals are DVRs.
-/

namespace Submission.NumberTheory.Milne

/-- Proposition 3.5(a): a localization of a noetherian ring is noetherian. -/
theorem localization_noetherian_ring
    (A S : Type*) [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] [IsNoetherianRing A] :
    IsNoetherianRing S := by
  exact IsLocalization.isNoetherianRing M S inferInstance

/-- Proposition 3.5(b): localization preserves integral closedness when no zero divisor is
inverted. -/
theorem localization_integrally_closed
    (A S : Type*) [CommRing A] [IsDomain A] [CommRing S] [Algebra A S]
    (M : Submonoid A) (hM : M ≤ nonZeroDivisors A) [IsLocalization M S]
    [IsIntegrallyClosed A] :
    IsIntegrallyClosed S := by
  exact isIntegrallyClosed_of_isLocalization S M hM

/-- Proposition 3.4: a localization of a Dedekind domain is Dedekind. -/
theorem localization_dedekind_domain
    (A S : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [CommRing S] [IsDomain S] [Algebra A S]
    (M : Submonoid A) (hM : M ≤ nonZeroDivisors A) [IsLocalization M S] :
    IsDedekindDomain S := by
  exact IsLocalization.isDedekindDomain A hM S

/-- Remark 3.11: a power of a maximal ideal is unchanged by extension to the
localization at that ideal followed by contraction. -/
theorem localization_comap_pow
    (A : Type*) [CommRing A] (P : Ideal A) (hP : P.IsMaximal) (m : ℕ) :
    Ideal.comap (algebraMap A (Localization.AtPrime P))
        (Ideal.map (algebraMap A (Localization.AtPrime P)) (P ^ m)) =
      P ^ m := by
  letI : P.IsPrime := hP.isPrime
  by_cases hm : m = 0
  · subst m
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top, Ideal.comap_top]
  · apply IsLocalization.under_map_of_isPrimary_disjoint
      P.primeCompl (Localization.AtPrime P)
    · apply Ideal.isPrimary_of_isMaximal_radical
      rw [Ideal.radical_pow P hm, hP.isPrime.radical]
      exact hP
    · rw [Set.disjoint_left]
      intro x hxP hxpow
      exact hxP (Ideal.pow_le_self hm hxpow)

/-- Remark 3.12: an ideal remains proper after localization at `P` exactly when it is
contained in `P`. -/
theorem localization_ne_top
    (A : Type*) [CommRing A] (P : Ideal A) [P.IsPrime] (I : Ideal A) :
    Ideal.map (algebraMap A (Localization.AtPrime P)) I ≠ ⊤ ↔ I ≤ P := by
  rw [IsLocalization.map_algebraMap_ne_top_iff_disjoint
    P.primeCompl (Localization.AtPrime P) I]
  constructor
  · intro h x hxI
    by_contra hxP
    exact Set.disjoint_left.mp h hxP hxI
  · intro h
    rw [Set.disjoint_left]
    intro x hxP hxI
    exact hxP (h hxI)

/-- Proposition 3.6: a noetherian domain is Dedekind iff every localization at a nonzero
prime ideal is a discrete valuation ring. -/
theorem dedekind_domain_discrete
    (A : Type*) [CommRing A] [IsDomain A] :
    IsDedekindDomain A ↔
      IsNoetherianRing A ∧
        ∀ (P : Ideal A) (_ : P ≠ ⊥) [P.IsPrime],
          IsDiscreteValuationRing (Localization.AtPrime P) := by
  constructor
  · intro hDedekind
    letI : IsDedekindDomain A := hDedekind
    refine ⟨inferInstance, ?_⟩
    intro P hP _
    exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _
  · rintro ⟨hNoetherian, hLocal⟩
    letI : IsDedekindDomainDvr A :=
      { toIsNoetherian := hNoetherian
        is_dvr_at_nonzero_prime := by
          intro P hP hPrime
          letI : P.IsPrime := hPrime
          exact hLocal P hP }
    infer_instance

/-- Corollary 3.13: inclusion of ideals can be checked after localization at every nonzero
prime ideal. The nonfield hypothesis is necessary for this formulation, since a field has no
nonzero prime ideals. -/
theorem ideal_localization_nonzero
    (R : Type*) [CommRing R] [IsDomain R] (hR : ¬IsField R)
    (I J : Ideal R) :
    I ≤ J ↔
      ∀ (P : Ideal R) (_ : P ≠ ⊥) [P.IsPrime],
        Ideal.map (algebraMap R (Localization.AtPrime P)) I ≤
          Ideal.map (algebraMap R (Localization.AtPrime P)) J := by
  constructor
  · intro hIJ P _ _
    exact Ideal.map_mono hIJ
  · intro hlocal
    apply Ideal.le_of_localization_maximal
    intro P hP
    letI : P.IsPrime := hP.isPrime
    exact hlocal P (Ring.ne_bot_of_isMaximal_of_not_isField hP hR)

/-- The equality form of Corollary 3.13. -/
theorem localization_nonzero_prime
    (R : Type*) [CommRing R] [IsDomain R] (hR : ¬IsField R)
    (I J : Ideal R) :
    I = J ↔
      ∀ (P : Ideal R) (_ : P ≠ ⊥) [P.IsPrime],
        Ideal.map (algebraMap R (Localization.AtPrime P)) I =
          Ideal.map (algebraMap R (Localization.AtPrime P)) J := by
  constructor
  · rintro rfl
    simp
  · intro hlocal
    apply le_antisymm
    · exact (ideal_localization_nonzero R hR I J).mpr
        (fun P hP0 _ => (hlocal P hP0).le)
    · exact (ideal_localization_nonzero R hR J I).mpr
        (fun P hP0 _ => (hlocal P hP0).ge)

end Submission.NumberTheory.Milne
