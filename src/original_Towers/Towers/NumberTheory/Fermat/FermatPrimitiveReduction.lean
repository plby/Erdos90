import Towers.NumberTheory.Fermat.FirstCaseTheorem

/-!
# Milne, Algebraic Number Theory, Theorem 6.8: primitive reduction

This file removes the coprimality hypothesis from the primitive form of the first-case theorem.
-/

namespace Towers.NumberTheory.Milne

open Algebra IsCyclotomicExtension NumberField
open scoped Cyclotomic

variable {p : ℕ} {K : Type*} [Field K] [CharZero K] [hp : Fact p.Prime]
variable [hK : IsCyclotomicExtension {p} ℚ K]

/-- Milne, Theorem 6.8. A common divisor of a putative solution can be divided out before
applying the primitive first-case theorem.  The cyclotomic field is automa a CM field
because the odd prime conductor is greater than two. -/
theorem no_case_regular
    [NumberField K] {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (hpodd : Odd p) {x y z : ℤ} (hxyz : ¬(p : ℤ) ∣ x * y * z)
    (hclass : ¬p ∣ NumberField.classNumber K)
    (hFermat : x ^ p + y ^ p = z ^ p) : False := by
  have hp2 : 2 < p := by
    have hpge2 := hp.out.two_le
    obtain ⟨k, hk⟩ := hpodd
    omega
  letI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField K
      ⟨p, Set.mem_singleton p, hp2⟩
  have hx : x ≠ 0 := by
    intro hx
    apply hxyz
    simp [hx]
  obtain ⟨k, x₀, y₀, hk, hgcd, hxk, hyk⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left y hx)
  have hkℤ : (k : ℤ) ≠ 0 := by
    exact_mod_cast hk.ne'
  have hxy₀ : IsCoprime x₀ y₀ := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have hscaled : (x₀ ^ p + y₀ ^ p) * (k : ℤ) ^ p = z ^ p := by
    calc
      (x₀ ^ p + y₀ ^ p) * (k : ℤ) ^ p =
          (x₀ * k) ^ p + (y₀ * k) ^ p := by ring
      _ = x ^ p + y ^ p := by rw [hxk, hyk]
      _ = z ^ p := hFermat
  have hkpow : (k : ℤ) ^ p ∣ z ^ p := by
    refine ⟨x₀ ^ p + y₀ ^ p, ?_⟩
    rw [mul_comm]
    exact hscaled.symm
  have hkz : (k : ℤ) ∣ z :=
    (IsIntegrallyClosed.pow_dvd_pow_iff hp.out.ne_zero).mp hkpow
  obtain ⟨z₀, hzk⟩ := hkz
  have hFermat₀ : x₀ ^ p + y₀ ^ p = z₀ ^ p := by
    apply mul_right_cancel₀ (pow_ne_zero p hkℤ)
    calc
      (x₀ ^ p + y₀ ^ p) * (k : ℤ) ^ p = z ^ p := hscaled
      _ = z₀ ^ p * (k : ℤ) ^ p := by rw [hzk, mul_pow]; ring
  have hxyz₀ : ¬(p : ℤ) ∣ x₀ * y₀ * z₀ := by
    intro hpdiv
    apply hxyz
    apply hpdiv.trans
    refine ⟨(k : ℤ) ^ 3, ?_⟩
    rw [hxk, hyk, hzk]
    ring
  exact no_case_primitive hzeta hpodd hxy₀ hxyz₀ hclass hFermat₀

end Towers.NumberTheory.Milne
