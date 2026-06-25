import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Monic factorization over an integrally closed domain

Exercise 2-2 in Milne's *Algebraic Number Theory*: a monic polynomial over an integrally
closed domain is irreducible exactly when it remains irreducible over the fraction field.
In particular, reducibility over the fraction field descends to the original ring.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

variable {A K : Type*} [CommRing A] [IsIntegrallyClosed A]
variable [Field K] [Algebra A K] [IsFractionRing A K]

/-- Gauss's lemma in the form underlying Exercise 2-2. -/
theorem monic_irreducible_field
    {f : A[X]} (hf : f.Monic) :
    Irreducible f ↔ Irreducible (f.map (algebraMap A K)) :=
  hf.irreducible_iff_irreducible_map_fraction_map

/-- Exercise 2-2: if a monic polynomial becomes reducible over the fraction field, it was
already reducible over the integrally closed domain. -/
theorem monic_irreducible_fraction
    {f : A[X]} (hf : f.Monic)
    (hred : ¬Irreducible (f.map (algebraMap A K))) :
    ¬Irreducible f := by
  exact fun hirr => hred ((monic_irreducible_field hf).mp hirr)

end Submission.NumberTheory.Milne
