import Towers.NumberTheory.Dedekind.LocalizationQuotientPowers

/-!
# The linear form of localization invariance for ideal-power quotients

Milne's Lemma 3.10 is a ring equivalence.  Here we record that it is compatible with the natural
`A`-module structures, which is the form needed in direct-sum decompositions of torsion modules.
-/

namespace Towers.NumberTheory.Milne

variable (A : Type*) [CommRing A] [IsDomain A]

/-- The localization equivalence on quotients by a power of a maximal ideal, regarded as an
`A`-linear equivalence. -/
noncomputable def linearLocalizationPrime
    (P : Ideal A) [P.IsMaximal] (m : ℕ) :
    (A ⧸ P ^ m) ≃ₗ[A]
      (Localization.AtPrime P ⧸
        (P.map (algebraMap A (Localization.AtPrime P))) ^ m) :=
  (AlgEquiv.ofRingEquiv
    (f := quotientLocalizationPrime A P m) (by
      intro a
      exact localization_prime_mk A P m a)).toLinearEquiv

omit [IsDomain A] in
@[simp]
theorem linear_localization_mk
    (P : Ideal A) [P.IsMaximal] (m : ℕ) (a : A) :
    linearLocalizationPrime A P m
        (Ideal.Quotient.mk (P ^ m) a) =
      Ideal.Quotient.mk
        ((P.map (algebraMap A (Localization.AtPrime P))) ^ m)
        (algebraMap A (Localization.AtPrime P) a) :=
  localization_prime_mk A P m a

end Towers.NumberTheory.Milne
