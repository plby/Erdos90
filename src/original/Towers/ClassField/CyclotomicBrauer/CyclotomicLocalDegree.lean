import Towers.ClassField.CyclotomicBrauer.OrderGrowth
import Towers.ClassField.CyclotomicBrauer.RationalPrimeTransport

/-!
# Lemma VII.7.3: local degrees in a prime-power cyclotomic field

This file combines multiplicative-order growth with Mathlib's ramification
and inertia formulas.  It proves the ideal-theoretic divisibility needed
for the full cyclotomic overfield, before passing to the cyclic fixed field.
-/

namespace Towers.CField.CBrauer

open IsDedekindDomain NumberField

noncomputable section

universe u

/-- In a rational cyclotomic field of conductor `ell ^ (R + 1)`, the local
degree at `(p)` is divisible by `ell ^ a` provided `a ≤ R` at the ramified
prime and the corresponding multiplicative order has that divisibility at
every unramified prime. -/
theorem dvd_ramification_inertia
    (P : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ell R a : ℕ) (hell : ell.Prime) (haR : a ≤ R)
    (C : Type u) [Field C] [NumberField C]
    [hcycl : IsCyclotomicExtension {ell ^ (R + 1)} ℚ C]
    (horder : Rat.HeightOneSpectrum.natGenerator P ≠ ell →
      ell ^ a ∣ orderOf
        (Rat.HeightOneSpectrum.natGenerator P : ZMod (ell ^ (R + 1)))) :
    let pZ : Ideal ℤ := Ideal.span
      ({(Rat.HeightOneSpectrum.natGenerator P : ℤ)} : Set ℤ)
    ell ^ a ∣ pZ.ramificationIdxIn (NumberField.RingOfIntegers C) *
      pZ.inertiaDegIn (NumberField.RingOfIntegers C) := by
  dsimp only
  let p := Rat.HeightOneSpectrum.natGenerator P
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator P
  letI : Fact ell.Prime := ⟨hell⟩
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (ell ^ (R + 1)) :=
    ⟨pow_ne_zero (R + 1) hell.ne_zero⟩
  by_cases hpeq : p = ell
  · rw [show Rat.HeightOneSpectrum.natGenerator P = ell from hpeq]
    rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow
        (hK := hcycl) ell R C,
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime_pow
        (hK := hcycl) ell R C,
      mul_one]
    exact (pow_dvd_pow ell haR).trans (dvd_mul_right _ _)
  · have hpNotDvd : ¬p ∣ ell ^ (R + 1) := by
      intro hdvd
      rcases (Nat.dvd_prime hell).mp (hp.dvd_of_dvd_pow hdvd) with hp1 | hpell
      · exact hp.ne_one hp1
      · exact hpeq hpell
    change ell ^ a ∣ pZ.ramificationIdxIn (NumberField.RingOfIntegers C) *
      pZ.inertiaDegIn (NumberField.RingOfIntegers C)
    rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
        (m := ell ^ (R + 1)) (hK := hcycl) p C hpNotDvd,
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
        (m := ell ^ (R + 1)) (hK := hcycl) p C hpNotDvd,
      one_mul]
    exact horder hpeq

/-- Raising the conductor exponent preserves the order divisibility at an
unramified rational prime. -/
theorem dvd_larger_conductor
    (P : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ell a r R : ℕ) (hrR : r ≤ R + 1)
    (h : ell ^ a ∣ orderOf
      (Rat.HeightOneSpectrum.natGenerator P : ZMod (ell ^ r))) :
    ell ^ a ∣ orderOf
      (Rat.HeightOneSpectrum.natGenerator P : ZMod (ell ^ (R + 1))) :=
  h.trans (order_cast_dvd
    (Rat.HeightOneSpectrum.natGenerator P) ell r (R + 1) hrR)

end

end Towers.CField.CBrauer
