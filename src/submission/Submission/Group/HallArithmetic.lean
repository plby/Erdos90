import Mathlib

/-!
# Arithmetic input for Hall collection

These lemmas contain the prime-power divisibility arithmetic used by the pure
Hall collector.  They do not depend on any completed Zassenhaus-series laws.
-/

namespace Submission

/-- The exact prime-power binomial valuation gives the corresponding
prime-power divisibility bound. -/
lemma multiplicity_dvd_choose
    {p a k : ℕ} [Fact p.Prime]
    (hk : k ≤ p ^ a)
    (hk0 : k ≠ 0) :
    p ^ (a - multiplicity p k) ∣ Nat.choose (p ^ a) k := by
  apply pow_dvd_of_le_emultiplicity
  rw [(Fact.out : Nat.Prime p).emultiplicity_choose_prime_pow hk hk0]

/-- Removing the `p`-adic valuation of a positive index from the exponent of a
prime power leaves enough room to recover the original prime power after
multiplying by that index. -/
lemma prime_sub_multiplicity
    {p a k : ℕ} [Fact p.Prime]
    (hk : k ≤ p ^ a)
    (hk0 : k ≠ 0) :
    p ^ a ≤ k * p ^ (a - multiplicity p k) := by
  have hpow_le :
      p ^ multiplicity p k ≤ k :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (pow_multiplicity_dvd p k)
  have hmult_le : multiplicity p k ≤ a := by
    exact
      (Nat.pow_le_pow_iff_right (Fact.out : Nat.Prime p).one_lt).mp
        (hpow_le.trans hk)
  calc
    p ^ a = p ^ multiplicity p k * p ^ (a - multiplicity p k) := by
      rw [← pow_add, Nat.add_sub_of_le hmult_le]
    _ ≤ k * p ^ (a - multiplicity p k) :=
      Nat.mul_le_mul_right (p ^ (a - multiplicity p k)) hpow_le

/-- The binomial valuation attached to an iterated commutator factor is strong
enough for the weighted Hall target. -/
lemma add_sub_multiplicity
    {p a k : ℕ} [Fact p.Prime]
    (A B : ℕ)
    (hk : k ≤ p ^ a)
    (hk0 : k ≠ 0) :
    A * p ^ a + B ≤
      (k * A + B) * p ^ (a - multiplicity p k) := by
  have hprimePow :
      p ^ a ≤ k * p ^ (a - multiplicity p k) :=
    prime_sub_multiplicity hk hk0
  have hpow_one :
      1 ≤ p ^ (a - multiplicity p k) :=
    (pow_pos (Fact.out : Nat.Prime p).pos _)
  calc
    A * p ^ a + B ≤
        A * (k * p ^ (a - multiplicity p k)) +
          B * p ^ (a - multiplicity p k) := by
      exact
        Nat.add_le_add
          (Nat.mul_le_mul_left A hprimePow)
          (by simpa using Nat.mul_le_mul_left B hpow_one)
    _ = (k * A + B) * p ^ (a - multiplicity p k) := by
      ring

end Submission
