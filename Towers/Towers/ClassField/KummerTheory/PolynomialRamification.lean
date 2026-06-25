import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Chapter VII, Appendix A: the ramification calculation

Proposition A.5 deduces an unramifiedness criterion from the discriminant of
`X^n - a`.  The derivative calculation used in that proof is recorded here.
The remaining implication needs a bridge from polynomial discriminants to
relative discriminant ideals and local ramification for a general number-field
extension; that exact Kummer-specific theorem is not currently packaged.

Remark A.6 concerns delicate ramification at primes dividing `n` and is outside
the presently available local Kummer API.
-/

namespace Towers.CField.KTheory

open Polynomial

variable {R : Type*} [CommRing R]

/-- The derivative identity used in the proof of Proposition A.5. -/
theorem derivative_sub_c (n : ℕ) (a : R) :
    derivative (X ^ n - C a) = C (n : R) * X ^ (n - 1) := by
  simp [derivative_sub, derivative_pow]

/-- Evaluating the derivative of `X^n - a` at a chosen root gives
`n * alpha^(n-1)`, the element whose norm controls the discriminant in A.5. -/
theorem derivative_x_c (n : ℕ) (a alpha : R) :
    eval alpha (derivative (X ^ n - C a)) = (n : R) * alpha ^ (n - 1) := by
  rw [derivative_sub_c]
  simp

set_option maxRecDepth 100000 in
/-- The discriminant calculation in Proposition A.5:
`disc(X^n-a) = (-1)^(n(n-1)/2+n-1) n^n a^(n-1)`.
In particular, this is `± n^n a^(n-1)` as in the printed proof. -/
theorem radicalPolynomial_discr [Nontrivial R]
    (n : ℕ) (hn : 0 < n) (a : R) :
    (X ^ n - C a).discr =
      (-1 : R) ^ (n * (n - 1) / 2 + (n - 1)) *
        (n : R) ^ n * a ^ (n - 1) := by
  let f : R[X] := X ^ n - C a
  have hdeg : f.natDegree = n := by
    simpa only [f] using
      (natDegree_X_pow_sub_C (R := R) (n := n) (r := a))
  have hmonic : f.Monic := by
    simpa only [f] using monic_X_pow_sub_C a hn.ne'
  have hdegree : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos, hdeg]
    exact hn
  have hres := resultant_deriv (f := f) hdegree
  rw [derivative_sub_c, hdeg] at hres
  rw [resultant_C_mul_right] at hres
  rw [resultant_X_pow_right f n (n - 1) (by rw [hdeg])] at hres
  · have hres' :
        (n : R) ^ n *
            ((-1 : R) ^ (n * (n - 1)) * (-a) ^ (n - 1)) =
          (-1 : R) ^ (n * (n - 1) / 2) * f.discr := by
      simpa [f, hn.ne', hn.ne'.symm, hmonic.leadingCoeff] using hres
    have hsign :
        (-1 : R) ^ (n * (n - 1) / 2) *
            (-1 : R) ^ (n * (n - 1) / 2) = 1 := by
      rw [← pow_add]
      simp [← two_mul]
    calc
      f.discr =
          (-1 : R) ^ (n * (n - 1) / 2) *
            ((-1 : R) ^ (n * (n - 1) / 2) * f.discr) := by
        rw [← mul_assoc, hsign, one_mul]
      _ = (-1 : R) ^ (n * (n - 1) / 2) *
          ((n : R) ^ n *
            ((-1 : R) ^ (n * (n - 1)) * (-a) ^ (n - 1))) := by
        rw [← hres']
      _ = (-1 : R) ^ (n * (n - 1) / 2 + (n - 1)) *
          (n : R) ^ n * a ^ (n - 1) := by
        have heven : Even (n * (n - 1)) := by
          exact Nat.even_mul_pred_self n
        have hnega : (-a) ^ (n - 1) =
            (-1 : R) ^ (n - 1) * a ^ (n - 1) := by
          exact neg_pow a (n - 1)
        rw [Even.neg_one_pow heven, one_mul, hnega]
        calc
          (-1 : R) ^ (n * (n - 1) / 2) *
                ((n : R) ^ n *
                  ((-1 : R) ^ (n - 1) * a ^ (n - 1))) =
              ((-1 : R) ^ (n * (n - 1) / 2) *
                (-1 : R) ^ (n - 1)) *
                  (n : R) ^ n * a ^ (n - 1) := by ring
          _ = _ := by rw [← pow_add]

/-- Consequently, the discriminant of `X^n-a` is a unit whenever both `n`
and `a` are units.  This is the local algebra used in Proposition A.5 away
from the primes dividing `n a`. -/
theorem unit_radical_discr [Nontrivial R]
    (n : ℕ) (hn : 0 < n) (a : R)
    (hnunit : IsUnit (n : R)) (haunit : IsUnit a) :
    IsUnit (X ^ n - C a).discr := by
  rw [radicalPolynomial_discr n hn a]
  exact ((isUnit_neg_one.pow _).mul (hnunit.pow _)).mul (haunit.pow _)

/-- If one assumes only that the *product* `n * a` has valuation one, the
valuation of the unsigned discriminant factor `n^n * a^(n-1)` is the
valuation of `n`, not automa one.  This identity pinpoints why the
printed hypothesis of Proposition A.5 also needs the exponent to be a local
unit (or an equivalent integrality assumption). -/
theorem radical_discriminant_factor
    {M N : Type*} [CommMonoid M] [CommMonoid N]
    (v : M →* N) (n : ℕ) (hn : 0 < n) (x a : M)
    (hproduct : v (x * a) = 1) :
    v (x ^ n * a ^ (n - 1)) = v x := by
  have hsucc : n - 1 + 1 = n := by omega
  calc
    v (x ^ n * a ^ (n - 1)) =
        v (x * (x * a) ^ (n - 1)) := by
      congr 1
      rw [mul_pow, ← mul_assoc, ← pow_succ', hsucc]
    _ = v x * v (x * a) ^ (n - 1) := by simp only [map_mul, map_pow]
    _ = v x := by rw [hproduct, one_pow, mul_one]

section Field

variable {K : Type*} [Field K]

/-- Away from the characteristic divisors of `n a`, the radical polynomial
is separable.  This is the polynomial-theoretic input to Proposition A.5. -/
theorem radicalPolynomial_separable
    {n : ℕ} {a : K} (hn : (n : K) ≠ 0) (ha : a ≠ 0) :
    (X ^ n - C a).Separable :=
  separable_X_pow_sub_C a hn ha

/-- The complete discriminant calculation in Proposition A.5 for a quadratic
radical polynomial. -/
theorem quadratic_radical_discr (a : K) :
    (X ^ 2 - C a).discr = 4 * a := by
  rw [discr_of_degree_eq_two]
  · simp [coeff_sub, coeff_X_pow]
  · rw [degree_X_pow_sub_C]
    all_goals norm_num

end Field

end Towers.CField.KTheory
