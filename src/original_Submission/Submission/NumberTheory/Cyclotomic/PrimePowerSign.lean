import Submission.NumberTheory.Cyclotomic.PrimePowerCyclotomic

/-!
# The sign in a prime-power cyclotomic discriminant

This file formalizes the parity classification in Milne's Remark 6.3(a).
-/

namespace Submission.NumberTheory.Milne

private theorem odd_pred_div {n : ℕ} (hn : Odd n) :
    Odd ((n - 1) / 2) ↔ n % 4 = 3 := by
  rw [Nat.odd_iff] at hn ⊢
  rcases Nat.odd_mod_four_iff.mp hn with hn4 | hn4
  · have hdecomp := Nat.mod_add_div n 4
    rw [hn4] at hdecomp
    omega
  · have hdecomp := Nat.mod_add_div n 4
    rw [hn4] at hdecomp
    omega

/-- Milne, Remark 6.3(a): for a prime-power conductor greater than two, half
the cyclotomic degree is odd exactly for conductor four or for a prime that is
three modulo four. -/
theorem cyclotomic_half_odd
    {p k : ℕ} (hp : p.Prime) (hconductor : 2 < p ^ (k + 1)) :
    Odd (p ^ k * (p - 1) / 2) ↔ p ^ (k + 1) = 4 ∨ p % 4 = 3 := by
  rcases hp.eq_two_or_odd with rfl | hpodd
  · rcases k with _ | k
    · norm_num at hconductor
    · rcases k with _ | k
      · norm_num
      · simp only [Nat.reduceSubDiff, mul_one]
        constructor
        · intro hodd
          have heven : Even (2 ^ (k + 2) / 2) := by
            rw [pow_succ, Nat.mul_div_left _ (by norm_num : 0 < 2)]
            refine ⟨2 ^ k, ?_⟩
            rw [pow_succ]
            omega
          exact (Nat.not_odd_iff_even.mpr heven hodd).elim
        · rintro (hfour | hmod)
          · have hgt : 4 < 2 ^ (k + 2 + 1) := by
              calc
                4 = 2 ^ 2 := by norm_num
                _ < 2 ^ (k + 2 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
            omega
          · norm_num at hmod
  · have hpne : p ≠ 2 := by
      intro h
      subst p
      norm_num at hpodd
    have hpodd' : Odd p := Nat.odd_iff.mpr hpodd
    have hp_even_pred : 2 ∣ p - 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rw [Nat.mul_div_assoc _ hp_even_pred]
    rw [Nat.odd_mul]
    have hpk : Odd (p ^ k) := hpodd'.pow
    rw [and_iff_right hpk, odd_pred_div hpodd']
    constructor
    · intro hpmod
      exact Or.inr hpmod
    · rintro (hfour | hpmod)
      · have hoddpow : Odd (p ^ (k + 1)) := hpodd'.pow
        rw [hfour] at hoddpow
        exact ((by decide : ¬Odd 4) hoddpow).elim
      · exact hpmod

open NumberField

open scoped NumberField

variable {p k : ℕ} {K : Type*} [Field K] [CharZero K] [hp : Fact p.Prime]
variable [hK : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]

/-- Milne, Remark 6.3(a), in discriminant-sign form: a nontrivial
prime-power cyclotomic field has negative discriminant exactly for conductor
four or for an odd prime congruent to three modulo four. -/
theorem cyclotomic_discriminant_neg
    (hconductor : 2 < p ^ (k + 1)) :
    letI : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
    NumberField.discr K < 0 ↔ p ^ (k + 1) = 4 ∨ p % 4 = 3 := by
  letI : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  rw [← cyclotomic_half_odd hp.out hconductor]
  rw [prime_cyclotomic_discriminant (p := p) (k := k) (K := K)]
  constructor
  · intro hneg
    by_contra hnotodd
    have heven : Even (p ^ k * (p - 1) / 2) :=
      Nat.not_odd_iff_even.mp hnotodd
    rw [Even.neg_one_pow heven, one_mul] at hneg
    have hpnonneg : (0 : ℤ) ≤ p := by positivity
    exact (not_lt_of_ge (pow_nonneg hpnonneg _) hneg)
  · intro hodd
    rw [Odd.neg_one_pow hodd]
    have hppos : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    have hpowpos : (0 : ℤ) <
        (p : ℤ) ^ (p ^ k * (p * (k + 1) - (k + 1) - 1)) :=
      pow_pos hppos _
    omega

end Submission.NumberTheory.Milne
