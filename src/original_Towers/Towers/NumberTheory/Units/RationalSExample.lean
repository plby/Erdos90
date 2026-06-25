import Towers.NumberTheory.Units.SUnits
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Milne, Algebraic Number Theory, rational S-unit example

For `K = ℚ` and the finite primes above `2`, `3`, and `5`, the group of `S`-units consists
exactly of the rational numbers `±2^k 3^m 5^n` with integral exponents.
-/

namespace Towers.NumberTheory.Milne

open IsDedekindDomain
open scoped NumberField

noncomputable section

/-- The finite primes of `ℚ` above `2`, `3`, and `5`. -/
def rational235Primes : Set (FinitePrime ℚ) :=
  {v | ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = 2 ∨
    ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = 3 ∨
    ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = 5}

theorem rational_235_val (x : ℚˣ) :
    x ∈ SUnits ℚ rational235Primes ↔
      ∀ p : Nat.Primes, (p : ℕ) ≠ 2 → (p : ℕ) ≠ 3 → (p : ℕ) ≠ 5 →
        padicValRat p (x : ℚ) = 0 := by
  constructor
  · intro hx p hp2 hp3 hp5
    letI : Fact p.1.Prime := ⟨p.2⟩
    let v : FinitePrime ℚ := Rat.HeightOneSpectrum.primesEquiv.symm p
    have hvnot : v ∉ rational235Primes := by
      intro hv
      change ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = 2 ∨
        ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = 3 ∨
        ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = 5 at hv
      simp [v, hp2, hp3, hp5] at hv
    have hvone : v.valuation ℚ (x : ℚˣ) = 1 := hx v hvnot
    have hpone : Rat.padicValuation p (x : ℚ) = 1 := by
      simpa [v] using
        (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).eq_one_iff_eq_one.mp hvone
    simpa [Rat.padicValuation, x.ne_zero] using hpone
  · intro hx v hvnot
    let p : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v
    letI : Fact p.1.Prime := ⟨p.2⟩
    have hp2 : (p : ℕ) ≠ 2 := by
      intro h
      exact hvnot (Or.inl h)
    have hp3 : (p : ℕ) ≠ 3 := by
      intro h
      exact hvnot (Or.inr (Or.inl h))
    have hp5 : (p : ℕ) ≠ 5 := by
      intro h
      exact hvnot (Or.inr (Or.inr h))
    have hpzero := hx p hp2 hp3 hp5
    have hpone : Rat.padicValuation p (x : ℚ) = 1 := by
      simp [Rat.padicValuation, x.ne_zero, hpzero]
    exact (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).eq_one_iff_eq_one.mpr hpone

private theorem nat_two_five
    (n : ℕ) (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3 ∨ p = 5) :
    n = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 * 5 ^ n.factorization 5 := by
  have hfactorization : n.factorization =
      Finsupp.single 2 (n.factorization 2) +
        Finsupp.single 3 (n.factorization 3) +
          Finsupp.single 5 (n.factorization 5) := by
    ext p
    by_cases hp2 : p = 2
    · subst p
      simp
    by_cases hp3 : p = 3
    · subst p
      simp [hp2]
    by_cases hp5 : p = 5
    · subst p
      simp [hp2, hp3]
    have hpzero : n.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff]
      intro hp
      have hp' : p ∈ n.primeFactors := by simpa using hp
      rcases hfac p hp' with h | h | h <;> contradiction
    simp [hp2, hp3, hp5, hpzero]
  calc
    n = n.factorization.prod (fun p k ↦ p ^ k) :=
      (Nat.prod_factorization_pow_eq_self hn).symm
    _ = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 *
        5 ^ n.factorization 5 := by
      conv_lhs => rw [hfactorization]
      rw [Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
      rw [Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
      simp

private theorem numerator_subset_235 (x : ℚˣ)
    (hx : ∀ p : Nat.Primes, (p : ℕ) ≠ 2 → (p : ℕ) ≠ 3 → (p : ℕ) ≠ 5 →
      padicValRat p (x : ℚ) = 0) :
    ∀ p ∈ (x : ℚ).num.natAbs.primeFactors, p = 2 ∨ p = 3 ∨ p = 5 := by
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  by_contra hout
  push Not at hout
  have hval := hx ⟨p, hpprime⟩ hout.1 hout.2.1 hout.2.2
  have hpnum : p ∣ (x : ℚ).num.natAbs := Nat.dvd_of_mem_primeFactors hp
  have hpden : ¬ p ∣ (x : ℚ).den := by
    exact hpprime.coprime_iff_not_dvd.mp ((x : ℚ).reduced.of_dvd_left hpnum)
  have hdenval : padicValNat p (x : ℚ).den = 0 :=
    padicValNat.eq_zero_of_not_dvd hpden
  letI : Fact p.Prime := ⟨hpprime⟩
  have hnumval : padicValInt p (x : ℚ).num ≠ 0 := by
    rw [padicValInt]
    exact (dvd_iff_padicValNat_ne_zero (p := p)
      (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.2 x.ne_zero))).mp hpnum
  rw [padicValRat_def, hdenval, Nat.cast_zero, sub_zero] at hval
  exact hnumval (Int.ofNat_inj.mp hval)

private theorem denominator_subset_235 (x : ℚˣ)
    (hx : ∀ p : Nat.Primes, (p : ℕ) ≠ 2 → (p : ℕ) ≠ 3 → (p : ℕ) ≠ 5 →
      padicValRat p (x : ℚ) = 0) :
    ∀ p ∈ (x : ℚ).den.primeFactors, p = 2 ∨ p = 3 ∨ p = 5 := by
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  by_contra hout
  push Not at hout
  have hval := hx ⟨p, hpprime⟩ hout.1 hout.2.1 hout.2.2
  have hpden : p ∣ (x : ℚ).den := Nat.dvd_of_mem_primeFactors hp
  have hpnum : ¬ p ∣ (x : ℚ).num.natAbs := by
    exact hpprime.coprime_iff_not_dvd.mp ((x : ℚ).reduced.symm.of_dvd_left hpden)
  have hnumval : padicValInt p (x : ℚ).num = 0 := by
    rw [padicValInt]
    exact padicValNat.eq_zero_of_not_dvd hpnum
  letI : Fact p.Prime := ⟨hpprime⟩
  have hdenval : padicValNat p (x : ℚ).den ≠ 0 :=
    (dvd_iff_padicValNat_ne_zero (p := p) (x : ℚ).den_ne_zero).mp hpden
  rw [padicValRat_def, hnumval, Nat.cast_zero, zero_sub, neg_eq_zero] at hval
  exact hdenval (Int.ofNat_inj.mp hval)

theorem rational_sunit_form (x : ℚˣ)
    (hx : ∀ p : Nat.Primes, (p : ℕ) ≠ 2 → (p : ℕ) ≠ 3 → (p : ℕ) ≠ 5 →
      padicValRat p (x : ℚ) = 0) :
    ∃ s : ℤˣ, (x : ℚ) = ((s : ℤ) : ℚ) *
      (2 : ℚ) ^ (((x : ℚ).num.natAbs.factorization 2 : ℤ) -
        ((x : ℚ).den.factorization 2 : ℤ)) *
      (3 : ℚ) ^ (((x : ℚ).num.natAbs.factorization 3 : ℤ) -
        ((x : ℚ).den.factorization 3 : ℤ)) *
      (5 : ℚ) ^ (((x : ℚ).num.natAbs.factorization 5 : ℤ) -
        ((x : ℚ).den.factorization 5 : ℤ)) := by
  have hnumne : (x : ℚ).num ≠ 0 := Rat.num_ne_zero.2 x.ne_zero
  have hnumabsne : (x : ℚ).num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnumne
  have hnumabs := nat_two_five
    (x : ℚ).num.natAbs hnumabsne (numerator_subset_235 x hx)
  have hden := nat_two_five
    (x : ℚ).den (x : ℚ).den_ne_zero (denominator_subset_235 x hx)
  have hsign : IsUnit (x : ℚ).num.sign :=
    Int.isUnit_iff_abs_eq.mpr (Int.abs_sign_of_ne_zero hnumne)
  let s : ℤˣ := hsign.unit
  refine ⟨s, ?_⟩
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
    zpow_sub₀ (by norm_num : (3 : ℚ) ≠ 0),
    zpow_sub₀ (by norm_num : (5 : ℚ) ≠ 0)]
  simp only [zpow_natCast]
  nth_rewrite 1 [← (x : ℚ).num_div_den]
  conv_lhs =>
    rw [← (x : ℚ).num.sign_mul_natAbs]
    rw [hnumabs, hden]
  simp only [Int.cast_mul, Int.cast_natCast]
  dsimp only [s]
  rw [hsign.unit_spec]
  field_simp
  push_cast
  ring

private theorem val_rat_zpow (p : Nat.Primes) (q : ℚ) (hq : q ≠ 0) (n : ℤ) :
    padicValRat p (q ^ n) = n * padicValRat p q := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  cases n with
  | ofNat n =>
      simpa only [zpow_natCast, Int.ofNat_eq_natCast, Int.natCast_mul, Int.cast_ofNat] using
        (padicValRat.pow (p := (p : ℕ)) hq (k := n))
  | negSucc n =>
      rw [zpow_negSucc, padicValRat.inv, padicValRat.pow hq]
      simp only [Int.negSucc_eq]
      push_cast
      ring

private theorem padic_val_rat (p : Nat.Primes) (hp : (p : ℕ) ≠ 2) :
    padicValRat p (2 : ℚ) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  change padicValRat (p : ℕ) ((2 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (by
    intro hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact p.2.ne_one h
    · exact hp h)

private theorem val_rat_ne (p : Nat.Primes) (hp : (p : ℕ) ≠ 3) :
    padicValRat p (3 : ℚ) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  change padicValRat (p : ℕ) ((3 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (by
    intro hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact p.2.ne_one h
    · exact hp h)

private theorem val_rat_five (p : Nat.Primes) (hp : (p : ℕ) ≠ 5) :
    padicValRat p (5 : ℚ) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  change padicValRat (p : ℕ) ((5 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (by
    intro hdvd
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exact p.2.ne_one h
    · exact hp h)

/-- Milne's example following Theorem 5.11:
`U({(2), (3), (5)}) = {±2^k 3^m 5^n | k, m, n ∈ ℤ}`. -/
theorem rational_235_s (x : ℚˣ) :
    x ∈ SUnits ℚ rational235Primes ↔
      ∃ (s : ℤˣ) (k m n : ℤ),
        (x : ℚ) = ((s : ℤ) : ℚ) * (2 : ℚ) ^ k * (3 : ℚ) ^ m * (5 : ℚ) ^ n := by
  rw [rational_235_val]
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := rational_sunit_form x hx
    exact ⟨s, _, _, _, hs⟩
  · rintro ⟨s, k, m, n, hx⟩ p hp2 hp3 hp5
    letI : Fact p.1.Prime := ⟨p.2⟩
    rw [hx]
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp only [Units.val_one, Int.cast_one, one_mul]
      rw [padicValRat.mul
          (mul_ne_zero (zpow_ne_zero k (by norm_num)) (zpow_ne_zero m (by norm_num)))
          (zpow_ne_zero n (by norm_num)),
        padicValRat.mul (zpow_ne_zero k (by norm_num)) (zpow_ne_zero m (by norm_num)),
        val_rat_zpow p 2 (by norm_num) k,
        val_rat_zpow p 3 (by norm_num) m,
        val_rat_zpow p 5 (by norm_num) n,
        padic_val_rat p hp2,
        val_rat_ne p hp3,
        val_rat_five p hp5]
      ring
    · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      simp only [neg_mul]
      rw [padicValRat.neg]
      simp only [one_mul]
      rw [padicValRat.mul
          (mul_ne_zero (zpow_ne_zero k (by norm_num)) (zpow_ne_zero m (by norm_num)))
          (zpow_ne_zero n (by norm_num)),
        padicValRat.mul (zpow_ne_zero k (by norm_num)) (zpow_ne_zero m (by norm_num)),
        val_rat_zpow p 2 (by norm_num) k,
        val_rat_zpow p 3 (by norm_num) m,
        val_rat_zpow p 5 (by norm_num) n,
        padic_val_rat p hp2,
        val_rat_ne p hp3,
        val_rat_five p hp5]
      ring

end

end Towers.NumberTheory.Milne
