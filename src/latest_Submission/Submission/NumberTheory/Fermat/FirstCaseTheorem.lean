import Submission.NumberTheory.Fermat.FermatFirstCase
import Submission.NumberTheory.Fermat.FermatPairwiseCoprime
import Submission.NumberTheory.Fermat.PairwisePowerFactors

/-!
# Milne, Algebraic Number Theory, Theorem 6.8

The first case of Fermat's last theorem for regular primes.
-/

namespace Submission.NumberTheory.Milne

open Algebra Function Ideal IsCyclotomicExtension NumberField
open scoped BigOperators Cyclotomic

variable {p : ℕ} {K : Type*} [Field K] [CharZero K] [hp : Fact p.Prime]
variable [hK : IsCyclotomicExtension {p} ℚ K]

private theorem coprime_third_add
    {n : ℕ} (hn : 0 < n) {x y z : ℤ} (hxy : IsCoprime x y)
    (h : x ^ n + y ^ n = z ^ n) : IsCoprime x z := by
  rcases hxy.pow_right (n := n) with ⟨a, b, hab⟩
  have hxzpow : IsCoprime x (z ^ n) := by
    refine ⟨a - b * x ^ (n - 1), b, ?_⟩
    rw [← h, mul_add]
    calc
      (a - b * x ^ (n - 1)) * x + (b * x ^ n + b * y ^ n) =
          a * x + b * y ^ n := by
        rw [sub_mul, mul_assoc, pow_sub_one_mul hn.ne' x]
        ring
      _ = 1 := hab
  exact (IsCoprime.pow_right_iff hn).mp hxzpow

/-- The `p > 5` part of Theorem 6.8, after the elementary relabeling has arranged
`p ∤ x - y` and the solution has been made primitive. -/
theorem no_case_relabelled
    [NumberField K] [NumberField.IsCMField K] {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (hp5 : 5 < p) {x y z : ℤ} (hxy : IsCoprime x y)
    (hpx : ¬(p : ℤ) ∣ x) (hpy : ¬(p : ℤ) ∣ y) (hpz : ¬(p : ℤ) ∣ z)
    (hpxy : ¬(p : ℤ) ∣ x - y) (hclass : ¬p ∣ NumberField.classNumber K)
    (hFermat : x ^ p + y ^ p = z ^ p) : False := by
  let O := NumberField.RingOfIntegers K
  let zetaO : O := hzeta.toInteger
  let xO : O := algebraMap ℤ O x
  let yO : O := algebraMap ℤ O y
  let zO : O := algebraMap ℤ O z
  let F : Fin p → Ideal O := fun i ↦
    Ideal.span {xO + zetaO ^ (i : ℕ) * yO}
  let J : Ideal O := Ideal.span {zO}
  have hpodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hpair : Pairwise (IsCoprime on F) := by
    simpa [F, O, zetaO, xO, yO] using
      fermat_pairwise_coprime hzeta hxy hFermat hpz
  have hfactorK :
      ∏ i : Fin p,
        (algebraMap ℤ K x + zeta ^ (i : ℕ) * algebraMap ℤ K y) =
          (algebraMap ℤ K z) ^ p := by
    have hcyclo := primitive_root_powers
      (x := algebraMap ℤ K x) (y := algebraMap ℤ K y) hzeta hpodd
    have hfermatK :
        (algebraMap ℤ K x) ^ p + (algebraMap ℤ K y) ^ p =
          (algebraMap ℤ K z) ^ p := by
      simpa only [map_add, map_pow] using congrArg (algebraMap ℤ K) hFermat
    rw [hfermatK] at hcyclo
    calc
      ∏ i : Fin p,
          (algebraMap ℤ K x + zeta ^ (i : ℕ) * algebraMap ℤ K y) =
          ∏ i ∈ Finset.range p,
            (algebraMap ℤ K x + zeta ^ i * algebraMap ℤ K y) := by
        rw [Finset.prod_fin_eq_prod_range]
        apply Finset.prod_congr rfl
        intro i hi
        simp [Finset.mem_range.mp hi]
      _ = (algebraMap ℤ K z) ^ p := by simpa using hcyclo.symm
  have hfactor : ∏ i : Fin p, (xO + zetaO ^ (i : ℕ) * yO) = zO ^ p := by
    apply Subtype.ext
    change
      (↑(∏ i : Fin p, (xO + zetaO ^ (i : ℕ) * yO)) : K) =
        ↑(zO ^ p)
    simpa [xO, yO, zO, zetaO, hzeta.coe_toInteger] using hfactorK
  have hprod : ∏ i, F i = J ^ p := by
    calc
      ∏ i, F i = Ideal.span {∏ i : Fin p, (xO + zetaO ^ (i : ℕ) * yO)} := by
        simpa [F] using Ideal.prod_span_singleton Finset.univ
          (fun i : Fin p ↦ xO + zetaO ^ (i : ℕ) * yO)
      _ = Ideal.span {zO ^ p} := by rw [hfactor]
      _ = J ^ p := by
        change Ideal.span {zO ^ p} = Ideal.span {zO} ^ p
        rw [Ideal.span_singleton_pow]
  have hz : z ≠ 0 := by
    intro hz
    apply hpz
    rw [hz]
    exact dvd_zero _
  have hzO : zO ≠ 0 := by
    simpa [zO] using (Int.cast_ne_zero.mpr hz : (z : O) ≠ 0)
  have hJ0 : J ≠ 0 := by
    exact (Ideal.span_singleton_eq_bot.not.mpr hzO)
  let one : Fin p := ⟨1, by omega⟩
  obtain ⟨I, hI⟩ :=
    pairwise_coprime_ne F hpair hJ0 hprod one
  have hfactorOne :
      Ideal.span {xO + zetaO * yO} = I ^ p := by
    simpa [F, one] using hI
  have hFone0 : F one ≠ 0 := by
    intro hzero
    have hzprod : ∏ i, F i = 0 := Finset.prod_eq_zero (Finset.mem_univ one) hzero
    rw [hprod] at hzprod
    exact (pow_ne_zero p hJ0) hzprod
  have hI0 : I ≠ 0 := by
    intro hzero
    apply hFone0
    rw [hI, hzero, zero_pow hp.out.ne_zero]
  exact no_first_case hzeta hp5 x y hpx hpy hpxy hclass I hI0
    (by simpa [O, zetaO, xO, yO] using hfactorOne)

/-- Milne, Theorem 6.8 for a primitive solution.  The source first removes a common factor;
this formulation records the resulting coprimality explicitly and includes the small-prime and
variable-relabeling steps. -/
theorem no_case_primitive
    [NumberField K] [NumberField.IsCMField K] {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (hpodd : Odd p) {x y z : ℤ} (hxy : IsCoprime x y)
    (hxyz : ¬(p : ℤ) ∣ x * y * z) (hclass : ¬p ∣ NumberField.classNumber K)
    (hFermat : x ^ p + y ^ p = z ^ p) : False := by
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpx : ¬(p : ℤ) ∣ x := by
    intro hx
    exact hxyz (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hx y) z)
  have hpy : ¬(p : ℤ) ∣ y := by
    intro hy
    exact hxyz (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hy x) z)
  have hpz : ¬(p : ℤ) ∣ z := by
    intro hz
    exact hxyz (dvd_mul_of_dvd_right hz (x * y))
  by_cases hp3 : p = 3
  · subst p
    exact (fermat_first_case hxyz) hFermat
  by_cases hp5eq : p = 5
  · subst p
    exact (fermat_five_case hxyz) hFermat
  have hp5 : 5 < p := by
    obtain ⟨k, hk⟩ := hpodd
    have hpge2 := hp.out.two_le
    omega
  by_cases hpxyGood : ¬(p : ℤ) ∣ x - y
  · exact no_case_relabelled hzeta hp5 hxy hpx hpy hpz hpxyGood
      hclass hFermat
  have hxyDiv : (p : ℤ) ∣ x - y := Classical.not_not.mp hpxyGood
  have hxzCoprime : IsCoprime x z :=
    coprime_third_add hp.out.pos hxy hFermat
  by_cases hpxzGood : ¬(p : ℤ) ∣ x + z
  · apply no_case_relabelled
      (x := x) (y := -z) (z := -y) hzeta hp5
      ((IsCoprime.neg_right_iff x z).mpr hxzCoprime) hpx
      (by simpa only [dvd_neg] using hpz) (by simpa only [dvd_neg] using hpy)
      (by simpa [sub_neg_eq_add] using hpxzGood) hclass
    show x ^ p + (-z) ^ p = (-y) ^ p
    rw [hpodd.neg_pow, hpodd.neg_pow]
    linear_combination hFermat
  have hxzDiv : (p : ℤ) ∣ x + z := Classical.not_not.mp hpxzGood
  have hxpow := Int.ModEq.pow_prime_eq_self hp.out x
  have hypow := Int.ModEq.pow_prime_eq_self hp.out y
  have hzpow := Int.ModEq.pow_prime_eq_self hp.out z
  have hpowEq : x ^ p + y ^ p ≡ z ^ p [ZMOD (p : ℤ)] := by
    rw [hFermat]
  have hlinear : x + y ≡ z [ZMOD (p : ℤ)] :=
    (hxpow.add hypow).symm.trans (hpowEq.trans hzpow)
  have hxyMod : x ≡ y [ZMOD (p : ℤ)] :=
    Int.modEq_iff_dvd.mpr (by simpa only [neg_sub] using dvd_neg.mpr hxyDiv)
  have hxzMod : x ≡ -z [ZMOD (p : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    simpa [neg_sub] using dvd_neg.mpr hxzDiv
  have hyzMod : y ≡ -z [ZMOD (p : ℤ)] := hxyMod.symm.trans hxzMod
  have hthree : (p : ℤ) ∣ 3 * z := by
    have hmod := (hxzMod.add hyzMod).symm.trans hlinear
    convert hmod.dvd using 1 ; ring
  rcases hpInt.dvd_mul.mp hthree with hp3 | hpz'
  · have hp3Nat : p ∣ 3 := by exact_mod_cast hp3
    have := Nat.le_of_dvd (by norm_num : 0 < 3) hp3Nat
    omega
  · exact hpz hpz'

end Submission.NumberTheory.Milne
