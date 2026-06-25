import Towers.NumberTheory.Quadratic.SqrtFiveIdeals

/-!
# Milne, Algebraic Number Theory, introduction: ideals underlying the factorizations of `21`

Milne uses the four ideals `(3, 1 plus or minus sqrt(-5))` and
`(7, 3 plus or minus sqrt(-5))`.
This file verifies that they are prime and nonprincipal.
-/

namespace Towers.NumberTheory.SNFive

open Ideal

/-- The prime ideal `(7, 3 + sqrt(-5))`. -/
abbrev primeSevenPlus : Ideal SNFive :=
  (QOrd.rootIdeal (-5) 0 7 (-3)).map quadraticOrderEquiv

/-- The prime ideal `(7, 3 - sqrt(-5))`. -/
abbrev primeSevenMinus : Ideal SNFive :=
  (QOrd.rootIdeal (-5) 0 7 3).map quadraticOrderEquiv

theorem seven_plus_pair :
    primeSevenPlus =
      span {(7 : SNFive), (⟨3, 1⟩ : SNFive)} := by
  have hseven : quadraticOrderEquiv (7 : QOrd (-5) 0) =
      (7 : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]
  have hroot : quadraticOrderEquiv
      (QuadraticAlgebra.omega - (-3 : QOrd (-5) 0)) =
      (⟨3, 1⟩ : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, QuadraticAlgebra.omega_re,
      QuadraticAlgebra.omega_im]
  change (span {(7 : QOrd (-5) 0),
    QuadraticAlgebra.omega - (-3 : QOrd (-5) 0)}).map
      quadraticOrderEquiv = _
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hseven, hroot]

theorem seven_minus_pair :
    primeSevenMinus =
      span {(7 : SNFive), (⟨3, -1⟩ : SNFive)} := by
  have hseven : quadraticOrderEquiv (7 : QOrd (-5) 0) =
      (7 : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]
  have hroot : quadraticOrderEquiv
      (QuadraticAlgebra.omega - (3 : QOrd (-5) 0)) =
      -(⟨3, -1⟩ : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, QuadraticAlgebra.omega_re,
      QuadraticAlgebra.omega_im]
  change (span {(7 : QOrd (-5) 0),
    QuadraticAlgebra.omega - (3 : QOrd (-5) 0)}).map
      quadraticOrderEquiv = _
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hseven, hroot]
  exact Ideal.span_pair_neg (7 : SNFive) (⟨3, -1⟩ : SNFive)

theorem prime_seven_plus : primeSevenPlus.IsPrime := by
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : (QOrd.rootIdeal (-5) 0 7 (-3)).IsPrime :=
    QOrd.root_ideal_prime (-5) 0 7 (-3) (by decide)
  exact Ideal.map_isPrime_of_equiv quadraticOrderEquiv

theorem prime_seven_minus : primeSevenMinus.IsPrime := by
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : (QOrd.rootIdeal (-5) 0 7 3).IsPrime :=
    QOrd.root_ideal_prime (-5) 0 7 3 (by decide)
  exact Ideal.map_isPrime_of_equiv quadraticOrderEquiv

private lemma norm_nonnegative (x : SNFive) : 0 ≤ x.norm :=
  Zsqrtd.norm_nonneg (by norm_num) x

private lemma norm_ne_three (x : SNFive) : x.norm.natAbs ≠ 3 := by
  intro h
  have hnorm : x.norm = 3 := by
    rw [← Int.natAbs_of_nonneg (norm_nonnegative x)]
    exact_mod_cast h
  rw [Zsqrtd.norm_def] at hnorm
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
  rw [Zsqrtd.norm_def] at hnorm
  have himLower : -2 < x.im := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im + 2)]
  have himUpper : x.im < 2 := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im - 2)]
  have hreLower : -3 < x.re := by
    nlinarith [sq_nonneg x.im, sq_nonneg (x.re + 3)]
  have hreUpper : x.re < 3 := by
    nlinarith [sq_nonneg x.im, sq_nonneg (x.re - 3)]
  interval_cases x.im <;> interval_cases x.re <;> norm_num at hnorm

private lemma not_principal_norm
    (I : Ideal SNFive) (p pNorm yNorm : ℕ) (y : SNFive)
    (hp : Nat.Prime p) (hprime : I.IsPrime)
    (hpMem : (p : SNFive) ∈ I) (hyMem : y ∈ I)
    (hpNormEq : (p : SNFive).norm.natAbs = pNorm)
    (hyNormEq : y.norm.natAbs = yNorm)
    (hgcd : Nat.gcd pNorm yNorm = p)
    (hnorm : ∀ x : SNFive, x.norm.natAbs ≠ p) :
    ¬ I.IsPrincipal := by
  intro hprincipal
  obtain ⟨x, hx⟩ := hprincipal.principal
  have hxIdeal : I = span {x} := by
    ext z
    change z ∈ (I : Submodule SNFive SNFive) ↔
      z ∈ Submodule.span SNFive {x}
    rw [hx]
  have hpMem' : (p : SNFive) ∈ span ({x} : Set SNFive) := by
    rw [← hxIdeal]
    exact hpMem
  have hyMem' : y ∈ span ({x} : Set SNFive) := by
    rw [← hxIdeal]
    exact hyMem
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hpMem'
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hyMem'
  have hxNormDvdP : x.norm.natAbs ∣ pNorm := by
    refine ⟨a.norm.natAbs, ?_⟩
    calc
      pNorm = (p : SNFive).norm.natAbs := hpNormEq.symm
      _ = (x * a).norm.natAbs := congrArg (fun z : SNFive => z.norm.natAbs) ha
      _ = x.norm.natAbs * a.norm.natAbs := by
        rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have hxNormDvdY : x.norm.natAbs ∣ yNorm := by
    refine ⟨b.norm.natAbs, ?_⟩
    calc
      yNorm = y.norm.natAbs := hyNormEq.symm
      _ = (x * b).norm.natAbs := congrArg (fun z : SNFive => z.norm.natAbs) hb
      _ = x.norm.natAbs * b.norm.natAbs := by
        rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have hxNormDvd : x.norm.natAbs ∣ p := by
    rw [← hgcd]
    exact Nat.dvd_gcd hxNormDvdP hxNormDvdY
  have hxNormNeOne : x.norm.natAbs ≠ 1 := by
    intro hone
    have hxUnit : IsUnit x := Zsqrtd.norm_eq_one_iff.mp hone
    exact hprime.ne_top (hxIdeal.trans (Ideal.span_singleton_eq_top.mpr hxUnit))
  rcases (Nat.dvd_prime hp).mp hxNormDvd with hone | hpNorm
  · exact hxNormNeOne hone
  · exact hnorm x hpNorm

theorem plus_not_principal : ¬ primeIdealPlus.IsPrincipal := by
  apply not_principal_norm primeIdealPlus 3 9 6
      (⟨1, 1⟩ : SNFive) Nat.prime_three prime_three_plus
  · rw [plus_span_pair]
    exact Ideal.subset_span (by simp)
  · rw [plus_span_pair]
    exact Ideal.subset_span (by simp)
  · norm_num [Zsqrtd.norm_def]
  · norm_num [Zsqrtd.norm_def]
  · decide
  · exact norm_ne_three

theorem minus_not_principal : ¬ primeIdealMinus.IsPrincipal := by
  apply not_principal_norm primeIdealMinus 3 9 6
      (⟨1, -1⟩ : SNFive) Nat.prime_three prime_three_minus
  · rw [minus_span_pair]
    exact Ideal.subset_span (by simp)
  · rw [minus_span_pair]
    exact Ideal.subset_span (by simp)
  · norm_num [Zsqrtd.norm_def]
  · norm_num [Zsqrtd.norm_def]
  · decide
  · exact norm_ne_three

theorem seven_plus_principal : ¬ primeSevenPlus.IsPrincipal := by
  apply not_principal_norm primeSevenPlus 7 49 14
      (⟨3, 1⟩ : SNFive) Nat.prime_seven prime_seven_plus
  · rw [seven_plus_pair]
    exact Ideal.subset_span (by simp)
  · rw [seven_plus_pair]
    exact Ideal.subset_span (by simp)
  · norm_num [Zsqrtd.norm_def]
  · norm_num [Zsqrtd.norm_def]
  · decide
  · exact norm_ne_seven

theorem seven_minus_principal : ¬ primeSevenMinus.IsPrincipal := by
  apply not_principal_norm primeSevenMinus 7 49 14
      (⟨3, -1⟩ : SNFive) Nat.prime_seven prime_seven_minus
  · rw [seven_minus_pair]
    exact Ideal.subset_span (by simp)
  · rw [seven_minus_pair]
    exact Ideal.subset_span (by simp)
  · norm_num [Zsqrtd.norm_def]
  · norm_num [Zsqrtd.norm_def]
  · decide
  · exact norm_ne_seven

/-- The four ideals used for Milne's three factorizations of `21` are prime and nonprincipal. -/
theorem twenty_ideals_nonprincipal :
    primeIdealPlus.IsPrime ∧ ¬primeIdealPlus.IsPrincipal ∧
      primeIdealMinus.IsPrime ∧ ¬primeIdealMinus.IsPrincipal ∧
      primeSevenPlus.IsPrime ∧ ¬primeSevenPlus.IsPrincipal ∧
      primeSevenMinus.IsPrime ∧ ¬primeSevenMinus.IsPrincipal :=
  ⟨prime_three_plus, plus_not_principal,
    prime_three_minus, minus_not_principal,
    prime_seven_plus, seven_plus_principal,
    prime_seven_minus, seven_minus_principal⟩

end Towers.NumberTheory.SNFive
