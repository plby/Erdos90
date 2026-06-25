import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Milne, Chapter 4, Exercise 1

The inclusion of a field `k` into `k[X]` gives the requested example.  The ideal `(X)` is a
nonzero prime ideal of `k[X]`, while its contraction to `k` is zero.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

noncomputable section

variable (k : Type*) [Field k]

private abbrev XIdeal : Ideal k[X] :=
  Ideal.span {(X : k[X])}

theorem x_ideal_prime : (XIdeal k).IsPrime := by
  change (Ideal.span {(X : k[X])}).IsPrime
  rw [← Polynomial.ker_constantCoeff]
  exact RingHom.ker_isPrime _

theorem x_ne_bot : XIdeal k ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact Polynomial.X_ne_zero

theorem x_comap_bot :
    (XIdeal k).comap (algebraMap k k[X]) = ⊥ := by
  change (Ideal.span {(X : k[X])}).comap (algebraMap k k[X]) = ⊥
  ext a
  simp [← Polynomial.ker_constantCoeff, RingHom.mem_ker]

/--
Milne, Chapter 4, Exercise 1: a nonzero prime ideal of an integral domain can contract to zero
in a subring when the larger ring is not integral over the smaller one.
-/
theorem prime_zero_contraction :
    ∃ p : Ideal k[X], p.IsPrime ∧ p ≠ ⊥ ∧ p.comap (algebraMap k k[X]) = ⊥ := by
  exact ⟨XIdeal k, x_ideal_prime k,
    x_ne_bot k, x_comap_bot k⟩

end

end Submission.NumberTheory.Milne
