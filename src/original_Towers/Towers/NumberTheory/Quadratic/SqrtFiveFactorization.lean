import Mathlib

/-!
# Milne, Algebraic Number Theory, Exercise 2-1

The order `ℤ[√5]` has two distinct factorizations of `4` into irreducibles.
-/

namespace Towers.NumberTheory.Milne

abbrev SqrtFive := ℤ√5

namespace SqrtFive

private lemma norm_formula (x : SqrtFive) :
    x.norm = x.re ^ 2 - 5 * x.im ^ 2 := by
  simp [Zsqrtd.norm_def, pow_two]
  ring

private lemma abs_ne_two (x : SqrtFive) : x.norm.natAbs ≠ 2 := by
  intro h
  have hnorm : x.norm = 2 ∨ x.norm = -2 := (Int.natAbs_eq_iff).mp h
  rcases hnorm with hnorm | hnorm
  · have hsquare : (x.re : ZMod 5) ^ 2 = 2 := by
      rw [norm_formula] at hnorm
      have hcast := congrArg (fun z : ℤ ↦ (z : ZMod 5)) hnorm
      have hfive : (5 : ZMod 5) = 0 := by decide
      simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, hfive, zero_mul,
        sub_zero] at hcast
      simpa using hcast
    have : ∀ a : ZMod 5, a ^ 2 ≠ 2 := by decide
    exact this x.re hsquare
  · have hsquare : (x.re : ZMod 5) ^ 2 = -2 := by
      rw [norm_formula] at hnorm
      have hcast := congrArg (fun z : ℤ ↦ (z : ZMod 5)) hnorm
      have hfive : (5 : ZMod 5) = 0 := by decide
      simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, hfive, zero_mul,
        sub_zero] at hcast
      simpa using hcast
    have : ∀ a : ZMod 5, a ^ 2 ≠ -2 := by decide
    exact this x.re hsquare

private lemma irreducible_abs_four
    {x : SqrtFive} (hnorm : x.norm.natAbs = 4) : Irreducible x := by
  rw [irreducible_iff]
  constructor
  · intro hx
    have hone : x.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hx
    omega
  · intro a b hab
    by_contra h
    push Not at h
    have ha1 : a.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.1
    have hb1 : b.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.2
    have hprod : a.norm.natAbs * b.norm.natAbs = 2 ^ 2 := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, hnorm]
      norm_num
    have haval := (Nat.prime_two.mul_eq_prime_sq_iff ha1 hb1).mp hprod
    exact abs_ne_two a haval.1

/-- The two displayed factorizations of `4` in `ℤ[√5]`. -/
theorem four_factorizations :
    (2 : SqrtFive) * 2 =
      (⟨1, 1⟩ : SqrtFive) * (⟨-1, 1⟩ : SqrtFive) := by
  ext <;> norm_num

theorem irreducible_two : Irreducible (2 : SqrtFive) := by
  apply irreducible_abs_four
  norm_num [Zsqrtd.norm_def]

theorem irreducible_add_sqrtd :
    Irreducible (⟨1, 1⟩ : SqrtFive) := by
  apply irreducible_abs_four
  norm_num [Zsqrtd.norm_def]

theorem irreducible_neg_sqrtd :
    Irreducible (⟨-1, 1⟩ : SqrtFive) := by
  apply irreducible_abs_four
  norm_num [Zsqrtd.norm_def]

private lemma sqrtd_dvd_two :
    ¬(⟨1, 1⟩ : SqrtFive) ∣ (2 : SqrtFive) := by
  rintro ⟨c, hc⟩
  have him := congrArg Zsqrtd.im hc
  have hre := congrArg Zsqrtd.re hc
  norm_num [Zsqrtd.im_mul] at him
  norm_num [Zsqrtd.re_mul] at hre
  omega

/-- The factorization through `1 + √5` is not obtained from `2 · 2` by replacing factors with
associates. -/
theorem not_associated_sqrtd :
    ¬Associated (2 : SqrtFive) (⟨1, 1⟩ : SqrtFive) := by
  intro h
  exact sqrtd_dvd_two h.symm.dvd

end SqrtFive

end Towers.NumberTheory.Milne
