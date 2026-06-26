import Submission.NumberTheory.Quadratic.SqrtNegFive
import Submission.NumberTheory.Quadratic.PrimeDecomposition

/-!
# Milne, Algebraic Number Theory, introduction and Exercise 0-2

This file gives the prime-ideal factorization underlying the two factorizations of `6` in
`ℤ[√-5]`.
-/

namespace Submission.NumberTheory.SNFive

open Ideal

/-- The coordinate-preserving equivalence between Mathlib's `ℤ√d` model and the quadratic
algebra model used by the general prime-decomposition theorems. -/
def quadraticOrderEquiv : QOrd (-5) 0 ≃+* SNFive where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

/-- The prime ideal `(2, 1 + √-5)`. -/
abbrev primeIdealTwo : Ideal SNFive :=
  (QOrd.rootIdeal (-5) 0 2 (-1)).map quadraticOrderEquiv

/-- The prime ideal `(3, 1 + √-5)`. -/
abbrev primeIdealPlus : Ideal SNFive :=
  (QOrd.rootIdeal (-5) 0 3 (-1)).map quadraticOrderEquiv

/-- The prime ideal `(3, 1 - √-5)`, represented equivalently by `(3, √-5 - 1)`. -/
abbrev primeIdealMinus : Ideal SNFive :=
  (QOrd.rootIdeal (-5) 0 3 1).map quadraticOrderEquiv

theorem prime_span_pair :
    primeIdealTwo = span {(2 : SNFive), (⟨1, 1⟩ : SNFive)} := by
  have htwo : quadraticOrderEquiv (2 : QOrd (-5) 0) =
      (2 : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]
  have hroot : quadraticOrderEquiv
      (QuadraticAlgebra.omega - (-1 : QOrd (-5) 0)) =
      (⟨1, 1⟩ : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
  change (span {(2 : QOrd (-5) 0),
    QuadraticAlgebra.omega - (-1 : QOrd (-5) 0)}).map quadraticOrderEquiv = _
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, htwo, hroot]

theorem plus_span_pair :
    primeIdealPlus = span {(3 : SNFive), (⟨1, 1⟩ : SNFive)} := by
  have hthree : quadraticOrderEquiv (3 : QOrd (-5) 0) =
      (3 : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]
  have hroot : quadraticOrderEquiv
      (QuadraticAlgebra.omega - (-1 : QOrd (-5) 0)) =
      (⟨1, 1⟩ : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
  change (span {(3 : QOrd (-5) 0),
    QuadraticAlgebra.omega - (-1 : QOrd (-5) 0)}).map quadraticOrderEquiv = _
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hthree, hroot]

theorem minus_span_pair :
    primeIdealMinus = span {(3 : SNFive), (⟨1, -1⟩ : SNFive)} := by
  have hthree : quadraticOrderEquiv (3 : QOrd (-5) 0) =
      (3 : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]
  have hroot : quadraticOrderEquiv
      (QuadraticAlgebra.omega - (1 : QOrd (-5) 0)) =
      -(⟨1, -1⟩ : SNFive) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
  change (span {(3 : QOrd (-5) 0),
    QuadraticAlgebra.omega - (1 : QOrd (-5) 0)}).map quadraticOrderEquiv = _
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hthree, hroot]
  exact Ideal.span_pair_neg (3 : SNFive) (⟨1, -1⟩ : SNFive)

theorem prime_ideal_two : primeIdealTwo.IsPrime := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (QOrd.rootIdeal (-5) 0 2 (-1)).IsPrime :=
    QOrd.root_ideal_prime (-5) 0 2 (-1) (by decide)
  exact Ideal.map_isPrime_of_equiv quadraticOrderEquiv

theorem prime_three_plus : primeIdealPlus.IsPrime := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : (QOrd.rootIdeal (-5) 0 3 (-1)).IsPrime :=
    QOrd.root_ideal_prime (-5) 0 3 (-1) (by decide)
  exact Ideal.map_isPrime_of_equiv quadraticOrderEquiv

theorem prime_three_minus : primeIdealMinus.IsPrime := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : (QOrd.rootIdeal (-5) 0 3 1).IsPrime :=
    QOrd.root_ideal_prime (-5) 0 3 1 (by decide)
  exact Ideal.map_isPrime_of_equiv quadraticOrderEquiv

/-- `(2, 1 + √-5)² = (2)`. -/
theorem prime_ideal_sq :
    primeIdealTwo ^ 2 = span {(2 : SNFive)} := by
  rw [pow_two]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Ideal.map_mul]
  rw [(QOrd.ramifies_at_root (-5) 0 2 (-1)
    ⟨-3, by norm_num⟩
    ⟨1, by norm_num⟩
    (by
      intro q hq
      have hq' : q = -3 := by omega
      subst q
      exact ⟨-1, -1, by norm_num⟩)).2]
  have hmap : quadraticOrderEquiv (2 : QOrd (-5) 0) =
      (2 : SNFive) := by
    ext <;> simp [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]
  simp [Ideal.map_span, hmap]

/-- `(3, 1 + √-5)(3, 1 - √-5) = (3)`. -/
theorem prime_plus_minus :
    primeIdealPlus * primeIdealMinus =
      span {(3 : SNFive)} := by
  rw [← Ideal.map_mul]
  have hprod :
      QOrd.rootIdeal (-5) 0 3 (-1) *
          QOrd.rootIdeal (-5) 0 3 1 =
        span {(3 : QOrd (-5) 0)} := by
    simpa using QOrd.root_ideal_conjugate (-5) 0 3 (-1)
      ⟨2, by norm_num⟩ ⟨1, 1, by norm_num⟩
  rw [hprod]
  have hmap : quadraticOrderEquiv (3 : QOrd (-5) 0) =
      (3 : SNFive) := by
    ext <;> simp [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]
  simp [Ideal.map_span, hmap]

/-- `(2, 1 + sqrt(-5))(3, 1 + sqrt(-5)) = (1 + sqrt(-5))`. -/
theorem prime_ideal_plus :
    primeIdealTwo * primeIdealPlus =
      span {(⟨1, 1⟩ : SNFive)} := by
  rw [prime_span_pair, plus_span_pair,
    Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton'.2
        ⟨(⟨1, -1⟩ : SNFive), by ext <;> norm_num⟩
    · exact Ideal.mem_span_singleton'.2
        ⟨(2 : SNFive), by ext <;> norm_num⟩
    · exact Ideal.mem_span_singleton'.2
        ⟨(3 : SNFive), by ext <;> norm_num⟩
    · exact Ideal.mem_span_singleton'.2
        ⟨(⟨1, 1⟩ : SNFive), by ext <;> norm_num⟩
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    have htwo :
        (2 : SNFive) * (⟨1, 1⟩ : SNFive) ∈
          span ({(2 : SNFive) * 3,
            (2 : SNFive) * (⟨1, 1⟩ : SNFive),
            (⟨1, 1⟩ : SNFive) * 3,
            (⟨1, 1⟩ : SNFive) * (⟨1, 1⟩ : SNFive)} :
              Set SNFive) :=
      Ideal.subset_span (by simp)
    have hthree :
        (⟨1, 1⟩ : SNFive) * 3 ∈
          span ({(2 : SNFive) * 3,
            (2 : SNFive) * (⟨1, 1⟩ : SNFive),
            (⟨1, 1⟩ : SNFive) * 3,
            (⟨1, 1⟩ : SNFive) * (⟨1, 1⟩ : SNFive)} :
              Set SNFive) :=
      Ideal.subset_span (by simp)
    have hresult :=
      (span ({(2 : SNFive) * 3,
        (2 : SNFive) * (⟨1, 1⟩ : SNFive),
        (⟨1, 1⟩ : SNFive) * 3,
        (⟨1, 1⟩ : SNFive) * (⟨1, 1⟩ : SNFive)} :
          Set SNFive)).sub_mem hthree htwo
    convert hresult using 1

/-- `(2, 1 + sqrt(-5))(3, 1 - sqrt(-5)) = (1 - sqrt(-5))`. -/
theorem prime_ideal_minus :
    primeIdealTwo * primeIdealMinus =
      span {(⟨1, -1⟩ : SNFive)} := by
  rw [prime_span_pair, minus_span_pair,
    Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton'.2
        ⟨(⟨1, 1⟩ : SNFive), by ext <;> norm_num⟩
    · exact Ideal.mem_span_singleton'.2
        ⟨(2 : SNFive), by ext <;> norm_num⟩
    · exact Ideal.mem_span_singleton'.2
        ⟨(⟨-2, 1⟩ : SNFive), by ext <;> norm_num⟩
    · exact Ideal.mem_span_singleton'.2
        ⟨(⟨1, 1⟩ : SNFive), by ext <;> norm_num⟩
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    let J : Ideal SNFive :=
      span ({(2 : SNFive) * 3,
        (2 : SNFive) * (⟨1, -1⟩ : SNFive),
        (⟨1, 1⟩ : SNFive) * 3,
        (⟨1, 1⟩ : SNFive) * (⟨1, -1⟩ : SNFive)} :
          Set SNFive)
    have hsix : (2 : SNFive) * 3 ∈ J :=
      Ideal.subset_span (by simp)
    have htwo :
        (2 : SNFive) * (⟨1, -1⟩ : SNFive) ∈ J :=
      Ideal.subset_span (by simp)
    have hthree : (⟨1, 1⟩ : SNFive) * 3 ∈ J :=
      Ideal.subset_span (by simp)
    have hthreeMinus :
        (2 : SNFive) * 3 - (⟨1, 1⟩ : SNFive) * 3 ∈ J :=
      J.sub_mem hsix hthree
    have hresult :
        ((2 : SNFive) * 3 - (⟨1, 1⟩ : SNFive) * 3) -
            (2 : SNFive) * (⟨1, -1⟩ : SNFive) ∈ J :=
      J.sub_mem hthreeMinus htwo
    change (⟨1, -1⟩ : SNFive) ∈ J
    convert hresult using 1

/-- Exercise 0-2: the factorization of `(6)` into prime ideals in `ℤ[√-5]`. -/
theorem span_six_factorization :
    span {(6 : SNFive)} =
      primeIdealTwo ^ 2 * primeIdealPlus * primeIdealMinus := by
  rw [mul_assoc, prime_ideal_sq,
    prime_plus_minus,
    Ideal.span_singleton_mul_span_singleton]
  norm_num

end Submission.NumberTheory.SNFive
