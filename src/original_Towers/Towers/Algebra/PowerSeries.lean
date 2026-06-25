import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

/-!
# Power series lemmas

This file records small formal-power-series facts used by the Towers project.
-/

namespace PowerSeries

open Polynomial

open scoped PowerSeries

noncomputable section

lemma binomial_series_int (A : Type*) [CommRing A] (n : ℕ) (u : ℤ) :
    PowerSeries.binomialSeries A ((n : ℤ) * u) =
      (PowerSeries.binomialSeries A u) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        PowerSeries.binomialSeries A (((n + 1 : ℕ) : ℤ) * u)
            = PowerSeries.binomialSeries A ((n : ℤ) * u + u) := by
                congr 1
                push_cast
                ring
        _ = PowerSeries.binomialSeries A ((n : ℤ) * u) *
              PowerSeries.binomialSeries A u := by
                rw [PowerSeries.binomialSeries_add]
        _ = (PowerSeries.binomialSeries A u) ^ n *
              PowerSeries.binomialSeries A u := by
                rw [ih]
        _ = (PowerSeries.binomialSeries A u) ^ (n + 1) := by
                rw [pow_succ]

lemma iterateFrobenius_zmod (p v : ℕ) [Fact p.Prime] (a : ZMod p) :
    iterateFrobenius (ZMod p) p v a = a := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  simp

lemma iterate_zmod_series (p v : ℕ) [Fact p.Prime]
    (f : (ZMod p)⟦X⟧) :
    PowerSeries.map (iterateFrobenius (ZMod p) p v) f = f := by
  ext n
  simp [iterateFrobenius_zmod]

lemma pow_expand_zmod {p : ℕ} (hp : p.Prime) (v : ℕ)
    (f : (ZMod p)⟦X⟧) :
    f ^ p ^ v = PowerSeries.expand (p ^ v) (pow_ne_zero v hp.ne_zero) f := by
  letI : Fact p.Prime := ⟨hp⟩
  have h :=
    MvPowerSeries.map_iterateFrobenius_expand
      (p := p) (hp := hp.ne_zero) (R := ZMod p) (f := f) v
  rw [← h]
  exact iterate_zmod_series p v _

lemma binomial_int_expand {p : ℕ} (hp : p.Prime)
    (v : ℕ) (u : ℤ) :
    PowerSeries.binomialSeries (ZMod p) (((p ^ v : ℕ) : ℤ) * u) =
      PowerSeries.expand (p ^ v) (pow_ne_zero v hp.ne_zero)
        (PowerSeries.binomialSeries (ZMod p) u) := by
  rw [binomial_series_int]
  exact pow_expand_zmod hp v _

theorem coeff_int_self {p : ℕ} (hp : p.Prime)
    (v : ℕ) (u : ℤ) :
    PowerSeries.coeff (p ^ v)
        (PowerSeries.binomialSeries (ZMod p) (((p ^ v : ℕ) : ℤ) * u)) =
      (u : ZMod p) := by
  let q := p ^ v
  have hqpos : 0 < q := pow_pos hp.pos v
  have hseries :
      PowerSeries.binomialSeries (ZMod p) ((q : ℤ) * u) =
        PowerSeries.expand q hqpos.ne' (PowerSeries.binomialSeries (ZMod p) u) := by
    simpa [q] using binomial_int_expand hp v u
  rw [hseries]
  rw [PowerSeries.coeff_expand, if_pos (dvd_refl q), Nat.div_self hqpos]
  simp [PowerSeries.binomialSeries_coeff]

theorem binomial_int_pos {p : ℕ} (hp : p.Prime)
    {v m : ℕ} {u : ℤ} (hm0 : 0 < m) (hm : m < p ^ v) :
    PowerSeries.coeff m
        (PowerSeries.binomialSeries (ZMod p) (((p ^ v : ℕ) : ℤ) * u)) =
      0 := by
  let q := p ^ v
  have hqpos : 0 < q := pow_pos hp.pos v
  have hseries :
      PowerSeries.binomialSeries (ZMod p) ((q : ℤ) * u) =
        PowerSeries.expand q hqpos.ne' (PowerSeries.binomialSeries (ZMod p) u) := by
    simpa [q] using binomial_int_expand hp v u
  have hnotdvd : ¬ q ∣ m := Nat.not_dvd_of_pos_of_lt hm0 (by simpa [q] using hm)
  rw [hseries]
  rw [PowerSeries.coeff_expand, if_neg hnotdvd]

/--
If `e = p^v u`, then the formal binomial series `(1 + X)^e` over `ZMod p`
has expansion

`1 + u X^(p^v) + O(X^(p^v + 1))`.

Here `PowerSeries.binomialSeries (ZMod p) e` is Mathlib's formal
`(1 + X)^e`, valid for positive and negative integer exponents, and truncating
at `p^v + 1` keeps exactly the coefficients through degree `p^v`.
-/
theorem trunc_binomial_series {p : ℕ} (hp : p.Prime)
    (v : ℕ) (u : ℤ) :
    PowerSeries.trunc (p ^ v + 1)
        (PowerSeries.binomialSeries (ZMod p) (((p ^ v : ℕ) : ℤ) * u)) =
      (Polynomial.C 1 + Polynomial.C (u : ZMod p) * Polynomial.X ^ (p ^ v) :
        (ZMod p)[X]) := by
  let q := p ^ v
  have hqpos : 0 < q := pow_pos hp.pos v
  have hpv_ne : p ^ v ≠ 0 := pow_ne_zero v hp.ne_zero
  ext m
  rw [PowerSeries.coeff_trunc]
  by_cases hm_lt : m < q + 1
  · rw [if_pos hm_lt]
    have hm_le_q : m ≤ q := Nat.lt_succ_iff.mp hm_lt
    by_cases hm0 : m = 0
    · subst m
      rw [Polynomial.coeff_add, Polynomial.coeff_C, if_pos rfl,
        Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hpv_ne)]
      simp [PowerSeries.binomialSeries_coeff]
    · by_cases hmq : m = q
      · subst m
        rw [coeff_int_self hp v u]
        rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg hqpos.ne',
          Polynomial.coeff_C_mul_X_pow]
        simp [q]
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        have hm_lt_q : m < q := lt_of_le_of_ne hm_le_q hmq
        rw [binomial_int_pos hp hm_pos (by simpa [q] using hm_lt_q)]
        have hmpv : m ≠ p ^ v := by simpa [q] using hmq
        rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg hm0,
          Polynomial.coeff_C_mul_X_pow, if_neg hmpv]
        simp
  · rw [if_neg hm_lt]
    have hm_ge : q + 1 ≤ m := le_of_not_gt hm_lt
    have hm0 : m ≠ 0 := by omega
    have hmq : m ≠ q := by omega
    have hmpv : m ≠ p ^ v := by simpa [q] using hmq
    rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg hm0,
      Polynomial.coeff_C_mul_X_pow, if_neg hmpv]
    simp

/--
The same leading-term statement with a separate integer exponent `e`.
If `e = p^v u`, then `(1 + X)^e` over `ZMod p` is
`1 + ū X^(p^v)` modulo terms of degree at least `p^v + 1`.
-/
theorem trunc_binomial_int {p : ℕ} (hp : p.Prime)
    {e u : ℤ} {v : ℕ}
    (he : e = (((p ^ v : ℕ) : ℤ) * u)) :
    PowerSeries.trunc (p ^ v + 1)
        (PowerSeries.binomialSeries (ZMod p) e) =
      (Polynomial.C 1 + Polynomial.C (u : ZMod p) * Polynomial.X ^ (p ^ v) :
        (ZMod p)[X]) := by
  subst e
  exact trunc_binomial_series hp v u

/-- In the decomposition `e = p^v u`, the coefficient of `X^(p^v)` is `ū`. -/
theorem binomial_int_self {p : ℕ} (hp : p.Prime)
    {e u : ℤ} {v : ℕ}
    (he : e = (((p ^ v : ℕ) : ℤ) * u)) :
    PowerSeries.coeff (p ^ v)
        (PowerSeries.binomialSeries (ZMod p) e) =
      (u : ZMod p) := by
  subst e
  exact coeff_int_self hp v u

/-- In the decomposition `e = p^v u`, all positive coefficients before
`X^(p^v)` vanish. -/
theorem coeff_binomial_pos {p : ℕ}
    (hp : p.Prime) {e u : ℤ} {v m : ℕ}
    (he : e = (((p ^ v : ℕ) : ℤ) * u)) (hm0 : 0 < m) (hm : m < p ^ v) :
    PowerSeries.coeff m
        (PowerSeries.binomialSeries (ZMod p) e) =
      0 := by
  subst e
  exact binomial_int_pos hp hm0 hm

theorem cast_zmod_dvd {p : ℕ} {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    (u : ZMod p) ≠ 0 := by
  simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hu

theorem coeff_binomial_ne {p : ℕ} (hp : p.Prime)
    {v : ℕ} {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    PowerSeries.coeff (p ^ v)
        (PowerSeries.binomialSeries (ZMod p) (((p ^ v : ℕ) : ℤ) * u)) ≠
      0 := by
  rw [coeff_int_self hp v u]
  exact cast_zmod_dvd hu

/--
If `e = p^v u` and `p ∤ u`, the leading coefficient `ū` in the previous
truncation statement is nonzero.
-/
theorem coeff_binomial_self {p : ℕ}
    (hp : p.Prime) {e u : ℤ} {v : ℕ}
    (he : e = (((p ^ v : ℕ) : ℤ) * u)) (hu : ¬ (p : ℤ) ∣ u) :
    PowerSeries.coeff (p ^ v)
        (PowerSeries.binomialSeries (ZMod p) e) ≠
      0 := by
  subst e
  exact coeff_binomial_ne hp hu

end

end PowerSeries
