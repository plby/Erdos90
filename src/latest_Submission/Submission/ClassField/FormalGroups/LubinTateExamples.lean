import Mathlib

/-!
# Class Field Theory, Chapter I, Section 2: elementary examples

Mathlib does not yet package one-parameter formal group laws.  The elementary
identities in Milne's Examples 2.5, 2.7, and 2.10 can nevertheless be stated
directly over commutative rings and polynomial rings.
-/

namespace Submission.CField.FGroups

open Polynomial

noncomputable section

/-- The multiplicative formal-group expression `X + Y + XY`. -/
def multiplicativeLaw {R : Type*} [CommRing R] (x y : R) : R :=
  x + y + x * y

/-- Example 2.5(b): translation by one turns the multiplicative formal-group
expression into ordinary multiplication. -/
theorem add_multiplicative_law
    {R : Type*} [CommRing R] (x y : R) :
    1 + multiplicativeLaw x y = (1 + x) * (1 + y) := by
  simp [multiplicativeLaw]
  ring

/-- The endomorphism `(1 + T)^n - 1` from Example 2.7. -/
def multiplicativePowerEndomorphism
    {R : Type*} [CommRing R] (n : ℕ) (x : R) : R :=
  (1 + x) ^ n - 1

/-- Example 2.7: `(1 + T)^n - 1` respects `X + Y + XY`. -/
theorem multiplicative_endomorphism_law
    {R : Type*} [CommRing R] (n : ℕ) (x y : R) :
    multiplicativePowerEndomorphism n (multiplicativeLaw x y) =
      multiplicativeLaw (multiplicativePowerEndomorphism n x)
        (multiplicativePowerEndomorphism n y) := by
  simp only [multiplicativePowerEndomorphism]
  rw [add_multiplicative_law, mul_pow]
  simp [multiplicativeLaw]
  ring

/-- Example 2.10(a): the basic Lubin--Tate polynomial `pi*X + X^q`. -/
def basicLubinTate
    {R : Type*} [CommRing R] (pi : R) (q : ℕ) : R[X] :=
  C pi * X + X ^ q

@[simp]
theorem basic_lubin_coeff
    {R : Type*} [CommRing R] [Nontrivial R] (pi : R) {q : ℕ} (hq : q ≠ 0) :
    (basicLubinTate pi q).coeff 0 = 0 := by
  simp [basicLubinTate, Ne.symm hq]

@[simp]
theorem basic_lubin_tate
    {R : Type*} [CommRing R] [Nontrivial R] (pi : R) {q : ℕ} (hq : 1 < q) :
    (basicLubinTate pi q).coeff 1 = pi := by
  have h1q : 1 ≠ q := Nat.ne_of_lt hq
  simp [basicLubinTate, h1q]

/-- Modulo `pi`, the basic Lubin--Tate polynomial is `X^q`. -/
theorem basic_lubin_span
    {R : Type*} [CommRing R] (pi : R) (q : ℕ) :
    (basicLubinTate pi q).map
        (Ideal.Quotient.mk (Ideal.span {pi})) = X ^ q := by
  simp [basicLubinTate]

/-- Example 2.10(b): for `K = Q_p`, Milne uses `(1 + X)^p - 1`. -/
def cyclotomicLubinTate (p : ℕ) : ℤ[X] :=
  (1 + X) ^ p - 1

@[simp]
theorem cyclotomic_lubin_coeff (p : ℕ) :
    (cyclotomicLubinTate p).coeff 0 = 0 := by
  rw [cyclotomicLubinTate, coeff_sub,
    coeff_one_add_X_pow ℤ p 0]
  simp

@[simp]
theorem lubin_tate_coeff (p : ℕ) :
    (cyclotomicLubinTate p).coeff 1 = p := by
  rw [cyclotomicLubinTate, coeff_sub,
    coeff_one_add_X_pow ℤ p 1]
  rw [coeff_one]
  simp

/-- In characteristic `p`, `(1 + X)^p - 1` reduces to `X^p`. -/
theorem cyclotomic_lubin_prime
    (p : ℕ) [Fact p.Prime] :
    (cyclotomicLubinTate p).map (Int.castRingHom (ZMod p)) = X ^ p := by
  rw [cyclotomicLubinTate, ← coe_mapRingHom, map_sub, map_pow,
    map_add, map_one]
  simp only [coe_mapRingHom, map_X]
  rw [add_pow_char]
  simp

end

end Submission.CField.FGroups
