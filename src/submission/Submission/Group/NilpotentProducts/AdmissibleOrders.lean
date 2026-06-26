import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas


/-!
# Residue arithmetic for Struik's well-behaved case

Theorem 2 permits cyclic orders that are odd or zero.  The only
non-polynomial coordinate operation in equation (18) is `choose x 2`;
this file proves that it descends modulo every permitted order.
-/

namespace Struik
namespace P1960

/-- Struik's permitted class-three orders: odd finite orders and `0` for
an infinite cyclic factor. -/
def AOrd (n : ℕ) : Prop :=
  n = 0 ∨ Odd n

lemma admissibleOrder_zero : AOrd 0 :=
  Or.inl rfl

lemma AOrd.of_odd {n : ℕ} (hn : Odd n) :
    AOrd n :=
  Or.inr hn

/-- The gcd convention used throughout Theorems 1 and 2 preserves
admissible orders. -/
lemma AOrd.gcd
    {m n : ℕ}
    (hm : AOrd m)
    (hn : AOrd n) :
    AOrd (Nat.gcd m n) := by
  rcases hm with rfl | hm
  · rcases hn with rfl | hn
    · exact admissibleOrder_zero
    · exact Or.inr (by simpa using hn)
  · rcases hn with rfl | hn
    · exact Or.inr (by simpa using hm)
    · exact Or.inr (hm.of_dvd_nat (Nat.gcd_dvd_left m n))

private lemma factorial_choose_prod (A : ℤ) (k : ℕ) :
    (k.factorial : ℤ) * Ring.choose A k =
      ∏ j ∈ Finset.range k, (A - (j : ℤ)) := by
  rw [← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose]
  rw [← Polynomial.eval_eq_smeval]
  exact descPochhammer_eval_eq_prod_range k A

/-- The degree-two binomial polynomial has the usual integral formula
after clearing its denominator. -/
lemma two_mul_choose (A : ℤ) :
    2 * Ring.choose A 2 = A * (A - 1) := by
  simpa [Finset.prod_range_succ] using
    (factorial_choose_prod A 2)

lemma choose_coprime_factorial
    {m k : ℕ} {A B : ℤ}
    (hcop : m.Coprime k.factorial)
    (hAB : A ≡ B [ZMOD (m : ℤ)]) :
    Ring.choose A k ≡ Ring.choose B k [ZMOD (m : ℤ)] := by
  have hprod :
      (∏ j ∈ Finset.range k, (A - (j : ℤ))) ≡
        (∏ j ∈ Finset.range k, (B - (j : ℤ))) [ZMOD (m : ℤ)] := by
    apply Int.ModEq.prod
    intro j hj
    exact hAB.sub (Int.ModEq.refl (j : ℤ))
  rw [← factorial_choose_prod,
    ← factorial_choose_prod] at hprod
  rw [Int.modEq_iff_dvd] at hprod ⊢
  have hdiv :
      (m : ℤ) ∣ (k.factorial : ℤ) *
        (Ring.choose B k - Ring.choose A k) := by
    convert hprod using 1 ; ring
  have hcop_int : IsCoprime (m : ℤ) (k.factorial : ℤ) := by
    exact hcop.cast
  exact hcop_int.dvd_of_dvd_mul_left hdiv

/-- `choose x 2` is well-defined modulo an odd modulus, and equality is
the order-zero case. -/
theorem choose_admissible_order
    {m : ℕ} (hm : AOrd m)
    {A B : ℤ} (hAB : A ≡ B [ZMOD (m : ℤ)]) :
    Ring.choose A 2 ≡ Ring.choose B 2 [ZMOD (m : ℤ)] := by
  rcases hm with rfl | hm
  · have hEq : A = B := by
      simpa [Int.ModEq] using hAB
    simp [hEq]
  · exact choose_coprime_factorial
      (by simpa using hm.coprime_two_right) hAB

/-- Lowering an integer congruence modulus along a natural divisibility
relation. -/
lemma mod_dvd_nat
    {a b : ℤ} {m n : ℕ}
    (h : a ≡ b [ZMOD (m : ℤ)])
    (hd : n ∣ m) :
    a ≡ b [ZMOD (n : ℤ)] := by
  apply h.of_dvd
  exact_mod_cast hd

end P1960
end Struik
