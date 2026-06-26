import Submission.NumberTheory.Quadratic.SqrtNegFive

/-!
# Milne, Algebraic Number Theory, introduction: three factorizations of 21

Milne displays three distinct length-two factorizations in `Z[sqrt(-5)]`:

`21 = 3 * 7 = (4 + sqrt(-5)) * (4 - sqrt(-5))
    = (1 + 2 sqrt(-5)) * (1 - 2 sqrt(-5))`.

This file records the equalities and verifies that every displayed factor is irreducible.
-/

namespace Submission.NumberTheory.SNFive

private lemma norm_formula (x : SNFive) :
    x.norm = x.re ^ 2 + 5 * x.im ^ 2 := by
  simp [Zsqrtd.norm_def, pow_two]
  ring

private lemma norm_nonnegative (x : SNFive) : 0 ≤ x.norm := by
  rw [norm_formula]
  positivity

private lemma norm_ne_three (x : SNFive) : x.norm.natAbs ≠ 3 := by
  intro h
  have hnorm : x.norm = 3 := by
    rw [← Int.natAbs_of_nonneg (norm_nonnegative x)]
    exact_mod_cast h
  rw [norm_formula] at hnorm
  have him : x.im = 0 := by
    have himLower : -1 < x.im := by
      nlinarith [sq_nonneg x.re, sq_nonneg (x.im + 1)]
    have himUpper : x.im < 1 := by
      nlinarith [sq_nonneg x.re, sq_nonneg (x.im - 1)]
    omega
  rw [him] at hnorm
  have hsquare : IsSquare (3 : ℤ) :=
    ⟨x.re, by simpa [pow_two] using hnorm.symm⟩
  norm_num at hsquare

private lemma norm_ne_seven (x : SNFive) : x.norm.natAbs ≠ 7 := by
  intro h
  have hnorm : x.norm = 7 := by
    rw [← Int.natAbs_of_nonneg (norm_nonnegative x)]
    exact_mod_cast h
  rw [norm_formula] at hnorm
  have himLower : -2 < x.im := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im + 2)]
  have himUpper : x.im < 2 := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im - 2)]
  have hreLower : -3 < x.re := by
    nlinarith [sq_nonneg x.im, sq_nonneg (x.re + 3)]
  have hreUpper : x.re < 3 := by
    nlinarith [sq_nonneg x.im, sq_nonneg (x.re - 3)]
  interval_cases x.im <;> interval_cases x.re <;> norm_num at hnorm

private lemma irreducible_twenty_one
    {x : SNFive} (hnorm : x.norm.natAbs = 21) : Irreducible x := by
  rw [irreducible_iff]
  constructor
  · intro hx
    have hone : x.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hx
    omega
  · intro a b hab
    by_contra h
    push Not at h
    have haOne : a.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.1
    have hbOne : b.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.2
    have hprod : a.norm.natAbs * b.norm.natAbs = 3 * 7 := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, hnorm]
    have hdiv : a.norm.natAbs ∣ 3 * 7 := ⟨b.norm.natAbs, hprod.symm⟩
    obtain ⟨u, v, hu, hv, huv⟩ := Nat.dvd_mul.mp hdiv
    rcases (Nat.dvd_prime Nat.prime_three).mp hu with rfl | rfl <;>
      rcases (Nat.dvd_prime Nat.prime_seven).mp hv with rfl | rfl
    · exact haOne (by simpa using huv.symm)
    · exact norm_ne_seven a (by simpa using huv.symm)
    · exact norm_ne_three a (by simpa using huv.symm)
    · apply hbOne
      have haTwentyOne : a.norm.natAbs = 21 := by simpa using huv.symm
      rw [haTwentyOne] at hprod
      omega

/-- The three displayed products in Milne's introduction all equal `21`. -/
theorem twenty_three_factorizations :
    (3 : SNFive) * 7 =
        (⟨4, 1⟩ : SNFive) * (⟨4, -1⟩ : SNFive) ∧
      (3 : SNFive) * 7 =
        (⟨1, 2⟩ : SNFive) * (⟨1, -2⟩ : SNFive) := by
  constructor <;> ext <;> norm_num

theorem irreducible_four_sqrtd :
    Irreducible (⟨4, 1⟩ : SNFive) := by
  apply irreducible_twenty_one
  norm_num [Zsqrtd.norm_def]

theorem four_sub_sqrtd :
    Irreducible (⟨4, -1⟩ : SNFive) := by
  apply irreducible_twenty_one
  norm_num [Zsqrtd.norm_def]

/-- Every factor occurring in the three displayed factorizations of `21` is irreducible. -/
theorem twenty_factors_irreducible :
    Irreducible (3 : SNFive) ∧
      Irreducible (7 : SNFive) ∧
      Irreducible (⟨4, 1⟩ : SNFive) ∧
      Irreducible (⟨4, -1⟩ : SNFive) ∧
      Irreducible (⟨1, 2⟩ : SNFive) ∧
      Irreducible (⟨1, -2⟩ : SNFive) :=
  ⟨irreducible_three, irreducible_seven,
    irreducible_four_sqrtd, four_sub_sqrtd,
    irreducible_two_sqrtd, irreducible_sub_sqrtd⟩

private theorem associated_or_neg (x y : SNFive) :
    Associated x y ↔ x = y ∨ x = -y := by
  constructor
  · rintro ⟨u, hu⟩
    rcases (unit_or_neg (u : SNFive)).mp u.isUnit with h | h
    · left
      simpa [h] using hu
    · right
      simpa [h, neg_eq_iff_eq_neg] using hu
  · rintro (h | h)
    · subst x
      exact Associated.refl y
    · refine ⟨-1, ?_⟩
      simpa [neg_eq_iff_eq_neg] using h

/-- No factor in one displayed pair is associated to a factor in either other pair. -/
theorem twenty_pairs_distinct :
    ¬Associated (3 : SNFive) (⟨4, 1⟩ : SNFive) ∧
      ¬Associated (3 : SNFive) (⟨4, -1⟩ : SNFive) ∧
      ¬Associated (3 : SNFive) (⟨1, 2⟩ : SNFive) ∧
      ¬Associated (3 : SNFive) (⟨1, -2⟩ : SNFive) ∧
      ¬Associated (7 : SNFive) (⟨4, 1⟩ : SNFive) ∧
      ¬Associated (7 : SNFive) (⟨4, -1⟩ : SNFive) ∧
      ¬Associated (7 : SNFive) (⟨1, 2⟩ : SNFive) ∧
      ¬Associated (7 : SNFive) (⟨1, -2⟩ : SNFive) ∧
      ¬Associated (⟨4, 1⟩ : SNFive) (⟨1, 2⟩ : SNFive) ∧
      ¬Associated (⟨4, 1⟩ : SNFive) (⟨1, -2⟩ : SNFive) ∧
      ¬Associated (⟨4, -1⟩ : SNFive) (⟨1, 2⟩ : SNFive) ∧
      ¬Associated (⟨4, -1⟩ : SNFive) (⟨1, -2⟩ : SNFive) := by
  simp only [associated_or_neg]
  norm_num [Zsqrtd.ext_iff]

end Submission.NumberTheory.SNFive
