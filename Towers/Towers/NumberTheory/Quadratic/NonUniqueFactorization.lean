import Mathlib

namespace Towers.NumberTheory

abbrev SNFive := ℤ√(-5)

namespace SNFive

private lemma norm_formula (x : SNFive) :
    x.norm = x.re ^ 2 + 5 * x.im ^ 2 := by
  simp [Zsqrtd.norm_def, pow_two]
  ring

private lemma norm_nonnegative (x : SNFive) : 0 ≤ x.norm := by
  rw [norm_formula]
  positivity

theorem unit_or_neg (x : SNFive) :
    IsUnit x ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    have hn : x.norm = 1 :=
      (Zsqrtd.norm_eq_one_iff' (by norm_num : (-5 : ℤ) ≤ 0) x).mpr hx
    rw [norm_formula] at hn
    have him : x.im = 0 := by
      nlinarith [sq_nonneg x.re, sq_nonneg x.im]
    have hre : x.re ^ 2 = 1 := by
      nlinarith
    rcases sq_eq_one_iff.mp hre with hre | hre
    · exact Or.inl (Zsqrtd.ext_iff.mpr ⟨by simpa using hre, by simpa using him⟩)
    · exact Or.inr (Zsqrtd.ext_iff.mpr ⟨by simpa using hre, by simpa using him⟩)
  · rintro (rfl | rfl) <;> simp

private lemma norm_ne_three (x : SNFive) : x.norm.natAbs ≠ 3 := by
  intro h
  have h' : x.norm = 3 := by
    rw [← Int.natAbs_of_nonneg (norm_nonnegative x)]
    exact_mod_cast h
  rw [norm_formula] at h'
  have him_lower : -1 < x.im := by nlinarith [sq_nonneg x.re, sq_nonneg (x.im + 1)]
  have him_upper : x.im < 1 := by nlinarith [sq_nonneg x.re, sq_nonneg (x.im - 1)]
  have him : x.im = 0 := by omega
  rw [him] at h'
  have hsquare : IsSquare (3 : ℤ) := ⟨x.re, by simpa [pow_two] using h'.symm⟩
  norm_num at hsquare

private lemma norm_ne_seven (x : SNFive) : x.norm.natAbs ≠ 7 := by
  intro h
  have h' : x.norm = 7 := by
    rw [← Int.natAbs_of_nonneg (norm_nonnegative x)]
    exact_mod_cast h
  rw [norm_formula] at h'
  have him_lower : -2 < x.im := by nlinarith [sq_nonneg x.re, sq_nonneg (x.im + 2)]
  have him_upper : x.im < 2 := by nlinarith [sq_nonneg x.re, sq_nonneg (x.im - 2)]
  have hre_lower : -3 < x.re := by nlinarith [sq_nonneg x.im, sq_nonneg (x.re + 3)]
  have hre_upper : x.re < 3 := by nlinarith [sq_nonneg x.im, sq_nonneg (x.re - 3)]
  interval_cases x.im <;> interval_cases x.re <;> norm_num at h'

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

theorem irreducible_three : Irreducible (3 : SNFive) := by
  apply irreducible_norm_sq Nat.prime_three
  · norm_num [Zsqrtd.norm_def]
  · exact norm_ne_three

theorem irreducible_seven : Irreducible (7 : SNFive) := by
  apply irreducible_norm_sq Nat.prime_seven
  · norm_num [Zsqrtd.norm_def]
  · exact norm_ne_seven

private lemma irreducible_or_sqrtd (sign : ℤ) (hsign : sign = 1 ∨ sign = -1) :
    Irreducible (⟨1, sign * 2⟩ : SNFive) := by
  rw [irreducible_iff]
  constructor
  · intro hx
    have hone := Zsqrtd.norm_eq_one_iff.mpr hx
    rcases hsign with rfl | rfl <;> norm_num [Zsqrtd.norm_def] at hone
  · intro a b hab
    by_contra h
    push Not at h
    have ha1 : a.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.1
    have hb1 : b.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.2
    have hprod : a.norm.natAbs * b.norm.natAbs = 3 * 7 := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab]
      rcases hsign with rfl | rfl <;> norm_num [Zsqrtd.norm_def]
    have hdiv : a.norm.natAbs ∣ 3 * 7 := ⟨b.norm.natAbs, hprod.symm⟩
    obtain ⟨u, v, hu, hv, huv⟩ := Nat.dvd_mul.mp hdiv
    rcases (Nat.dvd_prime Nat.prime_three).mp hu with rfl | rfl <;>
      rcases (Nat.dvd_prime Nat.prime_seven).mp hv with rfl | rfl
    · exact ha1 (by simpa using huv.symm)
    · exact norm_ne_seven a (by simpa using huv.symm)
    · exact norm_ne_three a (by simpa using huv.symm)
    · apply hb1
      have ha21 : a.norm.natAbs = 21 := by simpa using huv.symm
      rw [ha21] at hprod
      omega

theorem irreducible_two_sqrtd :
    Irreducible (⟨1, 2⟩ : SNFive) := by
  simpa using irreducible_or_sqrtd 1 (Or.inl rfl)

theorem irreducible_sub_sqrtd :
    Irreducible (⟨1, -2⟩ : SNFive) := by
  simpa using irreducible_or_sqrtd (-1) (Or.inr rfl)

theorem twenty_one_factorizations :
    (3 : SNFive) * 7 = (⟨1, 2⟩ : SNFive) * ⟨1, -2⟩ := by
  ext <;> norm_num

theorem unique_facto_monoi : ¬ UniqueFactorizationMonoid SNFive := by
  intro hUFD
  letI : UniqueFactorizationMonoid SNFive := hUFD
  have hprime : Prime (3 : SNFive) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp irreducible_three
  have hdvd : (3 : SNFive) ∣ (⟨1, 2⟩ : SNFive) * ⟨1, -2⟩ := by
    refine ⟨7, ?_⟩
    exact twenty_one_factorizations.symm
  rcases hprime.dvd_mul.mp hdvd with hleft | hright
  · obtain ⟨c, hc⟩ := hleft
    have hn : (21 : ℤ) = 9 * c.norm := by
      calc
        21 = (⟨1, 2⟩ : SNFive).norm := by norm_num [Zsqrtd.norm_def]
        _ = ((3 : SNFive) * c).norm := congrArg Zsqrtd.norm hc
        _ = 9 * c.norm := by rw [Zsqrtd.norm_mul]; norm_num [Zsqrtd.norm_def]
    omega
  · obtain ⟨c, hc⟩ := hright
    have hn : (21 : ℤ) = 9 * c.norm := by
      calc
        21 = (⟨1, -2⟩ : SNFive).norm := by norm_num [Zsqrtd.norm_def]
        _ = ((3 : SNFive) * c).norm := congrArg Zsqrtd.norm hc
        _ = 9 * c.norm := by rw [Zsqrtd.norm_mul]; norm_num [Zsqrtd.norm_def]
    omega

end SNFive

end Towers.NumberTheory
