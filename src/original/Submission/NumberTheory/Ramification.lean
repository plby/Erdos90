import Mathlib


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Ideal

/-- The ideal `(q)` of `ℤ`. -/
def rationalPrimeIdeal (q : ℕ) : Ideal ℤ :=
  Ideal.span ({(q : ℤ)} : Set ℤ)

/--
A rational prime `q` is tamely ramified in a `ℤ`-algebra `S`
if every prime ideal above `(q)` has ramification index coprime to `q`.
-/
noncomputable def RationalTamelyRamified
    {S : Type*} [CommRing S] [Algebra ℤ S]
    (q : ℕ) : Prop :=
  ∀ P : Ideal S,
    P.LiesOver (rationalPrimeIdeal q) →
      Nat.Coprime q
        (Ideal.ramificationIdx (rationalPrimeIdeal q) P)

end Ideal

namespace Submission

def absDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

/-- The root discriminant `D_K^(1 / [K : ℚ])` of a number field. -/
def rootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.rpow (absDiscriminant K) (1 / (Module.finrank ℚ K : ℝ))

/--
A rational prime `p` splits completely in `K` when the ideal `(p)` in `ℤ`
factors in the ring of integers of `K` as a product of `[K : ℚ]` distinct prime
ideals, equivalently: there are exactly `[K : ℚ]` prime ideals above `(p)`, and
each has ramification index `1` and inertia degree `1`.
-/
def splitsCompletely (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  (Ideal.primesOver (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard =
      Module.finrank ℚ K ∧
    ∀ P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers K),
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal p) P = 1 ∧
        Ideal.inertiaDeg (Ideal.rationalPrimeIdeal p) P = 1

-- Lemma 1

/--
A rational prime `q` has ramification index exactly `e` in a `ℤ`-algebra `S`
if every prime ideal above `(q)` has ramification index `e`.
-/
noncomputable def RationalRamificationIdx
    {S : Type*} [CommRing S] [Algebra ℤ S]
    (q e : ℕ) : Prop :=
  ∀ P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) S,
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P = e

/--
A rational prime `q` is unramified in a `ℤ`-algebra `S`
if every prime ideal above `(q)` has ramification index `1`.
-/
noncomputable def RationalPrimeUnramified
    {S : Type*} [CommRing S] [Algebra ℤ S]
    (q : ℕ) : Prop :=
  RationalRamificationIdx (S := S) q 1

lemma rational_ne_bot {q : ℕ} (hq : Nat.Prime q) :
    Ideal.rationalPrimeIdeal q ≠ ⊥ := by
  simpa [Ideal.rationalPrimeIdeal, Ideal.span_singleton_eq_bot] using
    (show (q : ℤ) ≠ 0 by exact_mod_cast hq.ne_zero)

lemma rational_prime_ideal {q : ℕ} (hq : Nat.Prime q) :
    (Ideal.rationalPrimeIdeal q).IsPrime := by
  have hqIntPrime : Prime (q : ℤ) := by
    exact (Int.prime_iff_natAbs_prime).2 (by simpa using hq)
  exact (Ideal.span_singleton_prime
    (show (q : ℤ) ≠ 0 by exact_mod_cast hq.ne_zero)).2 hqIntPrime

lemma rational_ideal_maximal {q : ℕ} (hq : Nat.Prime q) :
    (Ideal.rationalPrimeIdeal q).IsMaximal :=
  Ideal.IsPrime.isMaximal
    (rational_prime_ideal hq) (rational_ne_bot hq)


end Submission
