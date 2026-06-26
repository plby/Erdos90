import Mathlib

/-!
# Milne, Algebraic Number Theory, Examples 1.10 and 1.13

This file realizes two elementary localizations of `ℤ` as explicit subrings of `ℚ`, using
the reduced denominator of a rational number.
-/

namespace Towers.NumberTheory.Milne

/-- The subring of rational numbers whose reduced denominator divides a power of `d`.
This is Milne's concrete model of `ℤ_d`. -/
def integersAway (d : ℤ) : Subring ℚ where
  carrier := {q | ∃ n : ℕ, q.den ∣ d.natAbs ^ n}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, (Rat.add_den_dvd x y).trans ?_⟩
    calc
      x.den * y.den ∣ d.natAbs ^ m * d.natAbs ^ n := Nat.mul_dvd_mul hm hn
      _ = d.natAbs ^ (m + n) := (pow_add _ m n).symm
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, (Rat.mul_den_dvd x y).trans ?_⟩
    calc
      x.den * y.den ∣ d.natAbs ^ m * d.natAbs ^ n := Nat.mul_dvd_mul hm hn
      _ = d.natAbs ^ (m + n) := (pow_add _ m n).symm
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, by simpa using hn⟩

/-- A rational lies in `ℤ_d` exactly when it can be written with denominator a power of `d`.
This is the concrete description in Example 1.10(a). -/
theorem integers_away_div {d : ℤ} (hd : d ≠ 0) (q : ℚ) :
    q ∈ integersAway d ↔
      ∃ (a : ℤ) (n : ℕ), q = (a : ℚ) / (d : ℚ) ^ n := by
  constructor
  · rintro ⟨n, hn⟩
    have hnInt : (q.den : ℤ) ∣ (d : ℤ) ^ n := by
      apply (Int.dvd_natAbs).mp
      rw [Int.natAbs_pow]
      exact Int.natCast_dvd_natCast.mpr hn
    obtain ⟨c, hc⟩ := hnInt
    refine ⟨q.num * c, n, ?_⟩
    calc
      q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      _ = (q.num * c : ℤ) / (d : ℚ) ^ n := by
        apply (div_eq_div_iff
          (by exact_mod_cast q.den_ne_zero) (by exact_mod_cast Int.pow_ne_zero hd)).mpr
        norm_cast
        rw [hc]
        ring
  · rintro ⟨a, n, rfl⟩
    refine ⟨n, ?_⟩
    have hdenInt :
        ((((a : ℚ) / (d : ℚ) ^ n).den : ℕ) : ℤ) ∣ (d : ℤ) ^ n := by
      have hdiv : (a : ℚ) / (d : ℚ) ^ n = Rat.divInt a (d ^ n) := by
        calc
          (a : ℚ) / (d : ℚ) ^ n = (a : ℚ) / ((d ^ n : ℤ) : ℚ) := by
            rw [Int.cast_pow]
          _ = Rat.divInt a (d ^ n) := Rat.intCast_div_eq_divInt _ _
      rw [hdiv]
      exact Rat.den_dvd a (d ^ n)
    have hdenAbs :
        ((((a : ℚ) / (d : ℚ) ^ n).den : ℕ) : ℤ) ∣
          (((d : ℤ) ^ n).natAbs : ℤ) :=
      (Int.dvd_natAbs).mpr hdenInt
    rw [Int.natAbs_pow] at hdenAbs
    exact Int.natCast_dvd_natCast.mp hdenAbs

/-- The subring of rational numbers whose reduced denominator is not divisible by `p`.
For prime `p`, this is Milne's concrete model of `ℤ_(p)`. -/
def integersAtPrime (p : ℕ) (hp : p.Prime) : Subring ℚ where
  carrier := {q | ¬p ∣ q.den}
  zero_mem' := by simpa using hp.not_dvd_one
  one_mem' := by simpa using hp.not_dvd_one
  add_mem' := by
    intro x y hx hy hxy
    have : p ∣ x.den * y.den := hxy.trans (Rat.add_den_dvd x y)
    exact (hp.dvd_mul.mp this).elim hx hy
  mul_mem' := by
    intro x y hx hy hxy
    have : p ∣ x.den * y.den := hxy.trans (Rat.mul_den_dvd x y)
    exact (hp.dvd_mul.mp this).elim hx hy
  neg_mem' := by
    intro x hx
    simpa using hx

/-- A rational lies in `ℤ_(p)` exactly when it has a presentation whose denominator is not
divisible by `p`. This is Example 1.10(b). -/
theorem integers_prime_fraction
    {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ integersAtPrime p hp ↔
      ∃ (a : ℤ) (b : ℕ), ¬p ∣ b ∧ q = (a : ℚ) / (b : ℚ) := by
  constructor
  · intro hq
    exact ⟨q.num, q.den, hq, (Rat.num_div_den q).symm⟩
  · rintro ⟨a, b, hpb, rfl⟩ hpden
    apply hpb
    apply hpden.trans
    have hdenInt :
        (((((a : ℚ) / (b : ℚ)).den : ℕ) : ℤ) ∣ (b : ℤ)) := by
      have hdiv : (a : ℚ) / (b : ℚ) = Rat.divInt a (b : ℤ) := by
        calc
          (a : ℚ) / (b : ℚ) = (a : ℚ) / (((b : ℤ) : ℚ)) := by
            rw [Int.cast_natCast]
          _ = Rat.divInt a (b : ℤ) := Rat.intCast_div_eq_divInt _ _
      rw [hdiv]
      exact Rat.den_dvd a (b : ℤ)
    exact Int.natCast_dvd_natCast.mp hdenInt

end Towers.NumberTheory.Milne
