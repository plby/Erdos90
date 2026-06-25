import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Milne, Chapter 3, Exercise 1

For a field `k`, the two-variable polynomial ring `k[X, Y]` is not a Dedekind domain.  We
model it as the iterated polynomial ring `k[X][Y]`.  The obstruction is the strict chain of
prime ideals

`(0) ⊊ (Y) ⊊ (Y, X)`.

Only the middle ideal needs to be prime for the Dedekind-domain contradiction: it is the kernel
of evaluation at `Y = 0`, while `(Y, X)` is proper because simultaneous evaluation at `(0, 0)`
kills both generators.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

variable (k : Type*) [Field k]

private abbrev BivariatePolynomial := Polynomial (Polynomial k)

private abbrev yIdeal : Ideal (BivariatePolynomial k) :=
  Ideal.span {(X : BivariatePolynomial k)}

private abbrev xyIdeal : Ideal (BivariatePolynomial k) :=
  Ideal.span {(X : BivariatePolynomial k), C (X : Polynomial k)}

theorem y_ideal_prime : (yIdeal k).IsPrime := by
  change (Ideal.span {(X : BivariatePolynomial k)}).IsPrime
  rw [← Polynomial.ker_constantCoeff]
  exact RingHom.ker_isPrime _

theorem y_ne_bot : yIdeal k ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact Polynomial.X_ne_zero

theorem y_ideal_xy : yIdeal k < xyIdeal k := by
  constructor
  · exact Ideal.span_mono (by simp)
  · intro h
    have hCX : C (X : Polynomial k) ∈ yIdeal k := by
      exact h (Ideal.subset_span (by simp))
    change C (X : Polynomial k) ∈
      Ideal.span {(X : BivariatePolynomial k)} at hCX
    rw [← Polynomial.ker_constantCoeff] at hCX
    have hzero : (X : Polynomial k) = 0 := by
      change Polynomial.constantCoeff (C (X : Polynomial k)) = 0 at hCX
      simp at hCX
    exact Polynomial.X_ne_zero hzero

theorem xy_ne_top : xyIdeal k ≠ ⊤ := by
  have hle : xyIdeal k ≤ RingHom.ker (Polynomial.evalEvalRingHom (0 : k) 0) := by
    rw [Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> simp [RingHom.mem_ker]
  intro htop
  have hone : (1 : BivariatePolynomial k) ∈
      RingHom.ker (Polynomial.evalEvalRingHom (0 : k) 0) := by
    exact hle (htop ▸ by simp)
  simp at hone

/-- Milne, Chapter 3, Exercise 1: `k[X, Y]` is not a Dedekind domain. -/
theorem bivariate_dedekindnot_domain :
    ¬ IsDedekindDomain (BivariatePolynomial k) := by
  intro hDedekind
  letI : IsDedekindDomain (BivariatePolynomial k) := hDedekind
  have hmax : (yIdeal k).IsMaximal :=
    (y_ideal_prime k).isMaximal (y_ne_bot k)
  have heq : yIdeal k = xyIdeal k :=
    hmax.eq_of_le (xy_ne_top k) (y_ideal_xy k).le
  exact (y_ideal_xy k).ne heq

end

end Towers.NumberTheory.Milne
