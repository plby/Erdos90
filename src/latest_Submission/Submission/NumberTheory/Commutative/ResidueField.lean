import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The residue field of a localized prime

Exercise 2-8 in Milne's *Algebraic Number Theory*: for a prime ideal `p` of a domain `A`,
the quotient `A_p / p A_p` is the fraction field of `A / p`.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsLocalRing

variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]

/-- The extension of `p` to `A_p` is its unique maximal ideal. -/
theorem localization_maximal_ideal :
    p.map (algebraMap A (Localization.AtPrime p)) =
      maximalIdeal (Localization.AtPrime p) :=
  Localization.AtPrime.map_eq_maximalIdeal

/-- Exercise 2-8: `A_p / p A_p`, represented by the residue field at `p`, is a fraction
field of `A / p`. -/
theorem localization_prime_fraction :
    IsFractionRing (A ⧸ p) p.ResidueField := by
  infer_instance

end Submission.NumberTheory.Milne
