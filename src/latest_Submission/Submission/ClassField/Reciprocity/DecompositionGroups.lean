import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Chapter V, Section 5, Lemma 5.1: decomposition groups

For a Galois extension, primes above the same base prime are conjugate.  Their
decomposition groups are therefore conjugate stabilizers, and hence are equal
when the Galois group is abelian.

Milne also asserts that the local Artin map into this decomposition group is
independent of the prime above the base prime.  The current development has no
construction of the local reciprocity map, so this file records exactly the
decomposition-group clause and introduces no axiom for the remaining clause.
-/

namespace Submission.CField.Recip

open scoped Pointwise

/-- **Lemma V.5.1, decomposition-group clause.** In a finite abelian Galois
extension, the stabilizers of two primes above the same base prime are equal.
These stabilizers are the decomposition groups of the primes. -/
theorem decomposition_group_lies
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommGroup G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] :
    MulAction.stabilizer G P = MulAction.stabilizer G Q := by
  obtain ⟨sigma, hsigma⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup p P Q G
  rw [← hsigma, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext tau
  simp [MulAut.conj_apply]

end Submission.CField.Recip
