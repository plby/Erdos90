import Mathlib

/-!
# Milne, Algebraic Number Theory, Proposition 3.28

The approximation theorem for finitely many distinct prime ideals is the Chinese
Remainder Theorem applied to equal powers of those primes.
-/

namespace Towers.NumberTheory.Milne

open IsDedekindDomain

/-- Proposition 3.28, in its congruence form: given prescribed residues at finitely many
distinct nonzero primes, one can realize them simultaneously modulo the `(n+1)`st powers.
This is equivalent to `ord_(p_i)(x-x_i) > n`. -/
theorem approximation_distinct
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {ι : Type*} [Finite ι]
    (P : ι → HeightOneSpectrum A) (hP : Function.Injective P)
    (x : ι → A) (n : ℕ) :
    ∃ y : A, ∀ i, y - x i ∈ (P i).asIdeal ^ (n + 1) := by
  apply Ideal.exists_forall_sub_mem_ideal
  intro i j hij
  exact HeightOneSpectrum.isCoprime_pow_of_ne
    (P i) (P j) (fun h => hij (hP h)) (n + 1) (n + 1)

/-- Proposition 3.28 in valuation form for a natural bound.  Since Mathlib's
`intValuation` is multiplicative, Milne's inequality
`ord_(P i) (y - x i) > n` is written as
`intValuation (y - x i) < exp (-n)`. -/
theorem approximation_distinct_primes
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {ι : Type*} [Finite ι]
    (P : ι → HeightOneSpectrum A) (hP : Function.Injective P)
    (x : ι → A) (n : ℕ) :
    ∃ y : A, ∀ i,
      (P i).intValuation (y - x i) < WithZero.exp (-(n : ℤ)) := by
  obtain ⟨y, hy⟩ := approximation_distinct A P hP x n
  refine ⟨y, fun i => ?_⟩
  exact ((P i).intValuation_le_pow_iff_mem (y - x i) (n + 1)).2 (hy i) |>.trans_lt <| by
    rw [WithZero.exp_lt_exp]
    omega

/-- Proposition 3.28 with Milne's integer-valued bound. For `n < 0` the exponent
`(n + 1).toNat` is zero, as expected because every integral element has nonnegative order. -/
theorem approximation_distinct_int
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {ι : Type*} [Finite ι]
    (P : ι → HeightOneSpectrum A) (hP : Function.Injective P)
    (x : ι → A) (n : ℤ) :
    ∃ y : A, ∀ i, y - x i ∈ (P i).asIdeal ^ (n + 1).toNat := by
  apply Ideal.exists_forall_sub_mem_ideal
  intro i j hij
  exact HeightOneSpectrum.isCoprime_pow_of_ne
    (P i) (P j) (fun h ↦ hij (hP h)) (n + 1).toNat (n + 1).toNat

/-- Proposition 3.28 with Milne's literal integer-valued bound, stated as a
strict inequality for the normalized prime valuations. -/
theorem approximation_distinct_valuation
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {ι : Type*} [Finite ι]
    (P : ι → HeightOneSpectrum A) (hP : Function.Injective P)
    (x : ι → A) (n : ℤ) :
    ∃ y : A, ∀ i,
      (P i).intValuation (y - x i) < WithZero.exp (-n) := by
  obtain ⟨y, hy⟩ := approximation_distinct_int A P hP x n
  refine ⟨y, fun i => ?_⟩
  by_cases hn : 0 ≤ n
  · exact ((P i).intValuation_le_pow_iff_mem
      (y - x i) (n + 1).toNat).2 (hy i) |>.trans_lt <| by
      rw [WithZero.exp_lt_exp]
      omega
  · exact ((P i).intValuation_le_one (y - x i)).trans_lt <| by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega

end Towers.NumberTheory.Milne
