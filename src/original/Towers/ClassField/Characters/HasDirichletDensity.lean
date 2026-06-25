import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Chapter V, Section 2, Theorem 2.2

We define the Dirichlet density used in the text.  Mathlib proves Dirichlet's
theorem that every reduced residue class contains infinitely many primes,
but it does not currently package the sharper density computation
`1 / phi(m)`.  The theorem below records the available consequence without
weakening the definition of density.
-/

namespace Towers.CField.Charac

open Filter Set Topology

/-- A set of natural-number primes has Dirichlet density `delta` when its
prime reciprocal-power sum has the indicated normalized limit as the real
variable tends to `1` from above. -/
def HasDirichletDensity (T : Set ℕ) (delta : ℝ) : Prop :=
  Tendsto
    (fun s : ℝ ↦
      (∑' p : {p : ℕ // p ∈ T ∧ p.Prime},
        1 / (p.1 : ℝ) ^ s) /
        Real.log (1 / (s - 1)))
    (𝓝[>] 1) (𝓝 delta)

/-- The proved infinitude consequence of Theorem 2.2: every unit residue
class modulo a nonzero modulus contains infinitely many primes. -/
theorem primes_arithmetic_progression
    {m : ℕ} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod m) = a}.Infinite :=
  Nat.infinite_setOf_prime_and_eq_mod ha

/-- Integer form of the infinitude consequence of Theorem 2.2. -/
theorem prime_above_progression
    (bound : ℕ) {m : ℕ} {a : ℤ} (hm : m ≠ 0)
    (ha : IsCoprime a m) :
    ∃ p > bound, p.Prime ∧ p ≡ a [ZMOD m] :=
  Nat.forall_exists_prime_gt_and_zmodEq bound hm ha

end Towers.CField.Charac
