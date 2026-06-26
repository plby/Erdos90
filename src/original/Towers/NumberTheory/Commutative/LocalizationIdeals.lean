import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Milne, Chapter 1, Propositions 1.11 and 1.12

Extension and contraction classify the ideals of a localization and give a
bijection between its prime ideals and the primes of the original ring that
are disjoint from the denominator submonoid.
-/

namespace Towers.NumberTheory.Milne

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Submonoid R) [IsLocalization M S]

include M in
/-- Milne, Proposition 1.11, first assertion: extending the contraction of
an ideal of a localization recovers that ideal. -/
theorem localization_map_comap (J : Ideal S) :
    Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) J) = J :=
  IsLocalization.map_under M S J

/-- Milne, Proposition 1.11, second assertion: contracting the extension of
a prime ideal disjoint from the denominators recovers the prime ideal. -/
theorem localization_comap_disjoint
    (I : Ideal R) (hI : I.IsPrime) (hdisjoint : Disjoint (M : Set R) I) :
    Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) = I :=
  IsLocalization.under_map_of_isPrime_disjoint M S hI hdisjoint

/-- Milne, Proposition 1.12: extension and contraction give an
order-preserving bijection between prime ideals of a localization and prime
ideals of the original ring disjoint from the denominator submonoid. -/
noncomputable def localizationOrderIso :
    {p : Ideal S // p.IsPrime} ≃o
      {p : Ideal R // p.IsPrime ∧ Disjoint (M : Set R) p} :=
  IsLocalization.orderIsoOfPrime M S

section AtPrime

variable (p : Ideal R) [p.IsPrime]

/-- **Milne, Example 1.13(a).** Localization at a prime ideal is a local
ring. -/
theorem localization_local_ring :
    IsLocalRing (Localization.AtPrime p) := by
  infer_instance

/-- **Milne, Example 1.13(a).** The extension of `p` is the unique maximal
ideal of the localization `R_p`. -/
theorem localization_maximal_ideal :
    Ideal.map (algebraMap R (Localization.AtPrime p)) p =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
  Localization.AtPrime.map_eq_maximalIdeal

end AtPrime

end Towers.NumberTheory.Milne
