import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic


/-!
# Auxiliary lemmas for Kummer's proof of Fermat's last theorem

This file formalizes Lemmas 6.10 and 6.11 of Milne's *Algebraic Number
Theory* notes.
-/

namespace Towers.NumberTheory.Milne

open Algebra Module NumberField
open scoped Cyclotomic

variable {p : ℕ} {K : Type*} [Field K] [NumberField K] [hp : Fact p.Prime]
variable [IsCyclotomicExtension {p} ℚ K]

private theorem dvd_coeff_smul {d : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℤ M] (B : Basis (Fin d) ℤ M)
    (c : Fin d → ℤ) (n : ℤ) (β : M)
    (h : ∑ i, c i • B i = n • β) :
    ∀ i, n ∣ c i := by
  classical
  intro i
  have hcoord : B.coord i (∑ j, c j • B j) = c i := by
    rw [map_sum, Finset.sum_eq_single i]
    · simp [Basis.coord_apply]
    · intro j hj hji
      simp [Basis.coord_apply, hji]
    · simp
  refine ⟨B.coord i β, ?_⟩
  have heq := congrArg (B.coord i) h
  rw [hcoord] at heq
  simpa using heq

/-- **Milne, Lemma 6.10.** In a prime cyclotomic ring, the `p`th power of
every algebraic integer is congruent to an ordinary integer modulo `p`.
-/
theorem cyclotomic_integer_add
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) (α : NumberField.RingOfIntegers K) :
    ∃ a : ℤ, ∃ β : NumberField.RingOfIntegers K,
      α ^ p = algebraMap ℤ (NumberField.RingOfIntegers K) a +
        algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) * β := by
  have hadjoin : Algebra.adjoin ℤ
      ({hzeta.toInteger} : Set (NumberField.RingOfIntegers K)) = ⊤ := by
    rw [← hzeta.integralPowerBasis.adjoin_gen_eq_top, hzeta.integralPowerBasis_gen]
  have hα : α ∈ Algebra.adjoin ℤ
      ({hzeta.toInteger} : Set (NumberField.RingOfIntegers K)) := by
    simp [hadjoin]
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
      simp only [Set.mem_singleton_iff] at hx
      subst x
      refine ⟨1, 0, ?_⟩
      simp [hzeta.toInteger_isPrimitiveRoot.pow_eq_one]
  | algebraMap a =>
      refine ⟨a ^ p, 0, ?_⟩
      simp
  | add x y hx hy ihx ihy =>
      obtain ⟨a, β, hβ⟩ := ihx
      obtain ⟨b, γ, hγ⟩ := ihy
      refine ⟨a + b, β + γ + x * y *
        ∑ k ∈ Finset.Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) *
          ((p.choose k / p : ℕ) : NumberField.RingOfIntegers K), ?_⟩
      rw [Commute.add_pow_prime_eq hp.out (Commute.all x y), hβ, hγ]
      push_cast
      ring
  | mul x y hx hy ihx ihy =>
      obtain ⟨a, β, hβ⟩ := ihx
      obtain ⟨b, γ, hγ⟩ := ihy
      refine ⟨a * b, algebraMap ℤ (NumberField.RingOfIntegers K) a * γ +
        algebraMap ℤ (NumberField.RingOfIntegers K) b * β +
        algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) * β * γ, ?_⟩
      rw [mul_pow, hβ, hγ, map_mul]
      ring

/-- **Milne, Lemma 6.11.** Write an algebraic integer as a linear
combination of all `p` powers `1, ζ, ..., ζ^(p-1)`, with at least one zero
coefficient. If the resulting integer is divisible by `n` in the cyclotomic
integer ring, then every coefficient is divisible by `n` in `ℤ`.

The coefficient family is indexed by `ℕ`, but only its values below `p` occur.
-/
theorem cyclotomic_coefficients_dvd
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) (a : ℕ → ℤ) (n : ℤ)
    (hzero : ∃ i < p, a i = 0)
    (hdiv : ∃ β : NumberField.RingOfIntegers K,
      ∑ i ∈ Finset.range p,
          algebraMap ℤ (NumberField.RingOfIntegers K) (a i) * hzeta.toInteger ^ i =
        algebraMap ℤ (NumberField.RingOfIntegers K) n * β) :
    ∀ i < p, n ∣ a i := by
  let B := hzeta.integralPowerBasis
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1 : 1 ≤ p := hp2.trans' (by omega)
  have hdim : B.dim = p - 1 := by
    simp [B, Nat.totient_prime hp.out]
  let B' : Basis (Fin (p - 1)) ℤ (NumberField.RingOfIntegers K) :=
    B.basis.reindex (finCongr hdim)
  have hB' (i : Fin (p - 1)) : B' i = hzeta.toInteger ^ (i : ℕ) := by
    simp [B', B, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have hgeom : hzeta.toInteger ^ (p - 1) =
      -∑ i ∈ Finset.range (p - 1), hzeta.toInteger ^ i := by
    simpa [Nat.pred_eq_sub_one] using
      hzeta.toInteger_isPrimitiveRoot.pow_sub_one_eq (by omega : 1 < p)
  have hrewrite :
      (∑ i ∈ Finset.range p,
          algebraMap ℤ (NumberField.RingOfIntegers K) (a i) * hzeta.toInteger ^ i) =
        ∑ i ∈ Finset.range (p - 1),
          algebraMap ℤ (NumberField.RingOfIntegers K) (a i - a (p - 1)) *
            hzeta.toInteger ^ i := by
    rw [show Finset.range p = Finset.range (p - 1 + 1) by
      rw [Nat.sub_add_cancel hp1]]
    rw [Finset.sum_range_succ, hgeom, mul_neg, Finset.mul_sum,
      ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [map_sub]
    ring
  obtain ⟨β, hβ⟩ := hdiv
  rw [hrewrite] at hβ
  have hbasis :
      (∑ i : Fin (p - 1), (a i - a (p - 1)) • B' i) = n • β := by
    simpa [Finset.sum_range, hB', Algebra.smul_def] using hβ
  have hdiff : ∀ i < p - 1, n ∣ a i - a (p - 1) := by
    intro i hi
    exact dvd_coeff_smul B'
      (fun j ↦ a j - a (p - 1)) n β hbasis ⟨i, hi⟩
  obtain ⟨k, hk, hak⟩ := hzero
  have hlast : n ∣ a (p - 1) := by
    by_cases hklast : k = p - 1
    · simp [← hklast, hak]
    · have hk' : k < p - 1 := by omega
      have := hdiff k hk'
      simpa [hak] using this
  intro i hi
  by_cases hilast : i = p - 1
  · simpa [hilast] using hlast
  · have hi' : i < p - 1 := by omega
    have := (hdiff i hi').add hlast
    convert this using 1 ; ring

end Towers.NumberTheory.Milne
