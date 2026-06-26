import Towers.ClassField.HigherReciprocity.Wieferich
import Mathlib.FieldTheory.Finite.Basic

/-! # Chapter VIII, Section 5, Theorem 5.14 -/

namespace Towers.CField.HRecip

/-- The arithmetic output of the explicit cyclotomic Hilbert-symbol
calculation in the proof: the trace computation shows that the Fermat
quotient `(q^(p-1) - 1) / p` is itself divisible by `p`. -/
def FurtwanglerCyclotomicConclusion (p q : ℕ) : Prop :=
  p ∣ (q ^ (p - 1) - 1) / p

/-- The one unavailable input in the source proof.  This records only the
output of applying power reciprocity to
`alpha = (x + zeta*y)/(x+y)` and `beta = q^(p-1)`; the passage from this
trace divisibility to the stated congruence is proved below. -/
def CyclotomicHilbertBridge : Prop :=
  ∀ (p x y z q : ℕ),
    p.Prime → p ≠ 2 → 0 < x → 0 < y → 0 < z →
    Nat.gcd (Nat.gcd x y) z = 1 → (¬ p ∣ x * y * z) →
    x ^ p + y ^ p = z ^ p →
    q.Prime → q ∣ x * y * z →
    FurtwanglerCyclotomicConclusion p q

/-- The elementary last step of Furtwängler's proof: Fermat's little theorem
gives one factor of `p`, while the cyclotomic trace calculation gives the
second. -/
theorem furtwangler_mod_conclusion
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (htrace : FurtwanglerCyclotomicConclusion p q) :
    q ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hcoprime : Nat.Coprime q p :=
    ((Nat.coprime_primes hp hq).2 hpq).symm
  have hfermat : q ^ (p - 1) ≡ 1 [MOD p] := by
    simpa [Nat.totient_prime hp] using
      Nat.ModEq.pow_totient hcoprime
  have hone : 1 ≤ q ^ (p - 1) := one_le_pow₀ hq.one_le
  have hpDvd : p ∣ q ^ (p - 1) - 1 :=
    (Nat.modEq_iff_dvd' hone).1 hfermat.symm
  have hpSqDvd : p ^ 2 ∣ q ^ (p - 1) - 1 := by
    rw [pow_two]
    exact (Nat.dvd_div_iff_mul_dvd hpDvd).1 htrace
  exact ((Nat.modEq_iff_dvd' hone).2 hpSqDvd).symm

/-- The bridge is deliberately limited to the missing Hilbert-symbol trace
calculation; all remaining arithmetic is formalized. -/
theorem of_cyclotomicHilbert
    (h : CyclotomicHilbertBridge) :
    (∀ (p x y z : ℕ),
          p.Prime → p ≠ 2 → 0 < x → 0 < y → 0 < z →
          Nat.gcd (Nat.gcd x y) z = 1 → (¬ p ∣ x * y * z) →
          x ^ p + y ^ p = z ^ p →
          ∀ q : ℕ, q.Prime → q ∣ x * y * z →
            q ^ (p - 1) ≡ 1 [MOD p ^ 2]) := by
  intro p x y z hp hp2 hx hy hz hcoprime hpxyz hFermat q hq hqDvd
  apply furtwangler_mod_conclusion hp hq
  · intro hpq
    apply hpxyz
    exact (hpq ▸ hqDvd)
  · exact h p x y z q hp hp2 hx hy hz hcoprime hpxyz hFermat hq hqDvd

end Towers.CField.HRecip
