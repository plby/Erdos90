import Towers.NumberTheory.Quadratic.NonUniqueFactorization

/-!
# Milne, Algebraic Number Theory, introduction: `ℤ[√-5]`

This file formalizes the first explicit failure of unique factorization in the book:

`6 = 2 * 3 = (1 + √-5) * (1 - √-5)`.
-/

namespace Towers.NumberTheory.SNFive

private lemma norm_formula (x : SNFive) :
    x.norm = x.re ^ 2 + 5 * x.im ^ 2 := by
  simp [Zsqrtd.norm_def, pow_two]
  ring

private lemma norm_nonnegative (x : SNFive) : 0 ≤ x.norm := by
  rw [norm_formula]
  positivity

private lemma norm_ne_two (x : SNFive) : x.norm.natAbs ≠ 2 := by
  intro h
  have h' : x.norm = 2 := by
    rw [← Int.natAbs_of_nonneg (norm_nonnegative x)]
    exact_mod_cast h
  rw [norm_formula] at h'
  have him_lower : -1 < x.im := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im + 1)]
  have him_upper : x.im < 1 := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im - 1)]
  have him : x.im = 0 := by omega
  rw [him] at h'
  have hsquare : IsSquare (2 : ℤ) := ⟨x.re, by simpa [pow_two] using h'.symm⟩
  norm_num at hsquare

private lemma norm_ne_three (x : SNFive) : x.norm.natAbs ≠ 3 := by
  intro h
  have h' : x.norm = 3 := by
    rw [← Int.natAbs_of_nonneg (norm_nonnegative x)]
    exact_mod_cast h
  rw [norm_formula] at h'
  have him_lower : -1 < x.im := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im + 1)]
  have him_upper : x.im < 1 := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im - 1)]
  have him : x.im = 0 := by omega
  rw [him] at h'
  have hsquare : IsSquare (3 : ℤ) := ⟨x.re, by simpa [pow_two] using h'.symm⟩
  norm_num at hsquare

private lemma irreducible_norm_sq
    {x : SNFive} {p : ℕ} (hp : p.Prime)
    (hnorm : x.norm.natAbs = p ^ 2)
    (hnoNorm : ∀ y : SNFive, y.norm.natAbs ≠ p) :
    Irreducible x := by
  rw [irreducible_iff]
  constructor
  · intro hx
    have hone : x.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hx
    rw [hnorm] at hone
    exact hp.ne_one (Nat.pow_left_injective (by omega) hone)
  · intro a b hab
    by_contra h
    push Not at h
    have ha1 : a.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.1
    have hb1 : b.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.2
    have hprod : a.norm.natAbs * b.norm.natAbs = p ^ 2 := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, hnorm]
    have haval := (hp.mul_eq_prime_sq_iff ha1 hb1).mp hprod
    exact hnoNorm a haval.1

private lemma irreducible_norm_six
    {x : SNFive} (hnorm : x.norm.natAbs = 6) : Irreducible x := by
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
    have hprod : a.norm.natAbs * b.norm.natAbs = 2 * 3 := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, hnorm]
    have hdiv : a.norm.natAbs ∣ 2 * 3 := ⟨b.norm.natAbs, hprod.symm⟩
    obtain ⟨u, v, hu, hv, huv⟩ := Nat.dvd_mul.mp hdiv
    rcases (Nat.dvd_prime Nat.prime_two).mp hu with rfl | rfl <;>
      rcases (Nat.dvd_prime Nat.prime_three).mp hv with rfl | rfl
    · exact ha1 (by simpa using huv.symm)
    · exact norm_ne_three a (by simpa using huv.symm)
    · exact norm_ne_two a (by simpa using huv.symm)
    · apply hb1
      have ha6 : a.norm.natAbs = 6 := by simpa using huv.symm
      rw [ha6] at hprod
      omega

/-- Milne's displayed pair of factorizations of `6` in `ℤ[√-5]`. -/
theorem six_factorizations :
    (2 : SNFive) * 3 =
      (⟨1, 1⟩ : SNFive) * (⟨1, -1⟩ : SNFive) := by
  ext <;> norm_num

theorem irreducible_two : Irreducible (2 : SNFive) := by
  apply irreducible_norm_sq Nat.prime_two
  · norm_num [Zsqrtd.norm_def]
  · exact norm_ne_two

theorem irreducible_add_sqrtd :
    Irreducible (⟨1, 1⟩ : SNFive) := by
  apply irreducible_norm_six
  norm_num [Zsqrtd.norm_def]

theorem irreducible_one_sqrtd :
    Irreducible (⟨1, -1⟩ : SNFive) := by
  apply irreducible_norm_six
  norm_num [Zsqrtd.norm_def]

private lemma not_associated_ne {x y : SNFive} (hxy : x.norm ≠ y.norm) :
    ¬Associated x y := by
  intro h
  exact hxy (Zsqrtd.norm_eq_of_associated (by norm_num : (-5 : ℤ) ≤ 0) h)

private lemma not_associated_sub :
    ¬Associated (⟨1, 1⟩ : SNFive) (⟨1, -1⟩ : SNFive) := by
  rintro ⟨u, hu⟩
  rcases (unit_or_neg (u : SNFive)).mp u.isUnit with h | h
  · rw [h, mul_one] at hu
    have him := congrArg Zsqrtd.im hu
    norm_num at him
  · rw [h, mul_neg, mul_one] at hu
    have hre := congrArg Zsqrtd.re hu
    norm_num at hre

/-- The four irreducibles in Milne's factorization are pairwise nonassociate. -/
theorem six_pairwise_nonassociated :
    ¬Associated (2 : SNFive) 3 ∧
    ¬Associated (2 : SNFive) (⟨1, 1⟩ : SNFive) ∧
    ¬Associated (2 : SNFive) (⟨1, -1⟩ : SNFive) ∧
    ¬Associated (3 : SNFive) (⟨1, 1⟩ : SNFive) ∧
    ¬Associated (3 : SNFive) (⟨1, -1⟩ : SNFive) ∧
    ¬Associated (⟨1, 1⟩ : SNFive) (⟨1, -1⟩ : SNFive) := by
  refine ⟨not_associated_ne ?_, not_associated_ne ?_,
    not_associated_ne ?_, not_associated_ne ?_,
    not_associated_ne ?_, not_associated_sub⟩ <;>
    norm_num [Zsqrtd.norm_def]

private lemma sqrtd_dvd_two :
    ¬(⟨1, 1⟩ : SNFive) ∣ (2 : SNFive) := by
  rintro ⟨c, hc⟩
  have hn : (4 : ℤ) = 6 * c.norm := by
    calc
      4 = (2 : SNFive).norm := by norm_num [Zsqrtd.norm_def]
      _ = ((⟨1, 1⟩ : SNFive) * c).norm := congrArg Zsqrtd.norm hc
      _ = 6 * c.norm := by rw [Zsqrtd.norm_mul]; norm_num [Zsqrtd.norm_def]
  omega

private lemma sqrtd_not_dvd :
    ¬(⟨1, 1⟩ : SNFive) ∣ (3 : SNFive) := by
  rintro ⟨c, hc⟩
  have hn : (9 : ℤ) = 6 * c.norm := by
    calc
      9 = (3 : SNFive).norm := by norm_num [Zsqrtd.norm_def]
      _ = ((⟨1, 1⟩ : SNFive) * c).norm := congrArg Zsqrtd.norm hc
      _ = 6 * c.norm := by rw [Zsqrtd.norm_mul]; norm_num [Zsqrtd.norm_def]
  omega

/-- The irreducible `1 + √-5` is not prime: it divides `2 * 3` but neither factor. -/
theorem irreducible_not_sqrtd :
    Irreducible (⟨1, 1⟩ : SNFive) ∧
      ¬Prime (⟨1, 1⟩ : SNFive) := by
  refine ⟨irreducible_add_sqrtd, ?_⟩
  intro hprime
  have hdvd : (⟨1, 1⟩ : SNFive) ∣ (2 : SNFive) * 3 :=
    ⟨(⟨1, -1⟩ : SNFive), six_factorizations⟩
  exact (hprime.dvd_mul.mp hdvd).elim sqrtd_dvd_two sqrtd_not_dvd

end Towers.NumberTheory.SNFive
