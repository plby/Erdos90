import Towers.NumberTheory.Quadratic.SqrtNegThree
import Towers.NumberTheory.Quadratic.PrimeDecomposition

/-!
# Milne, Algebraic Number Theory, Exercise 2-4

The prime ideal `(2, 1 + √-3)` does not satisfy ideal cancellation. This prevents ideals in
`ℤ[√-3]` from having unique factorization into prime ideals.
-/

namespace Towers.NumberTheory.Milne.SNThree

open Ideal

/-- The coordinate-preserving equivalence with the quadratic-algebra model used by the general
prime-decomposition theorems. -/
def quadraticOrderEquiv : QOrd (-3) 0 ≃+* SNThree where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

/-- Milne's ideal `a = (2, 1 + √-3)`. -/
abbrev badIdeal : Ideal SNThree :=
  (QOrd.rootIdeal (-3) 0 2 (-1)).map quadraticOrderEquiv

theorem bad_span_pair :
    badIdeal = span {(2 : SNThree), (⟨1, 1⟩ : SNThree)} := by
  have htwo : quadraticOrderEquiv (2 : QOrd (-3) 0) =
      (2 : SNThree) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]
  have hroot : quadraticOrderEquiv
      (QuadraticAlgebra.omega - (-1 : QOrd (-3) 0)) =
      (⟨1, 1⟩ : SNThree) := by
    ext <;> norm_num [quadraticOrderEquiv, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
  change (span {(2 : QOrd (-3) 0),
    QuadraticAlgebra.omega - (-1 : QOrd (-3) 0)}).map quadraticOrderEquiv = _
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, htwo, hroot]

theorem bad_ideal_prime : badIdeal.IsPrime := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (QOrd.rootIdeal (-3) 0 2 (-1)).IsPrime :=
    QOrd.root_ideal_prime (-3) 0 2 (-1) (by decide)
  exact Ideal.map_isPrime_of_equiv quadraticOrderEquiv

/-- The ideal `(2, 1 + √-3)` is strictly larger than `(2)`. -/
theorem bad_ne_two :
    badIdeal ≠ span {(2 : SNThree)} := by
  rw [bad_span_pair, Ne, Ideal.span_pair_eq_span_left_iff_dvd]
  rintro ⟨c, hc⟩
  have him := congrArg Zsqrtd.im hc
  norm_num [Zsqrtd.im_mul] at him
  omega

theorem bad_ne_bot : badIdeal ≠ ⊥ := by
  intro h
  have htwo : (2 : SNThree) ∈ badIdeal := by
    rw [bad_span_pair]
    exact Ideal.subset_span (Set.mem_insert _ _)
  rw [h] at htwo
  change (2 : SNThree) = 0 at htwo
  norm_num at htwo

/-- Milne's identity `a² = (2)a`. -/
theorem badIdeal_sq :
    badIdeal ^ 2 = span {(2 : SNThree)} * badIdeal := by
  rw [bad_span_pair, pow_two, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_mul
        (Ideal.mem_span_singleton_self (2 : SNThree))
        (Ideal.subset_span (Set.mem_insert _ _))
    · exact Ideal.mul_mem_mul
        (Ideal.mem_span_singleton_self (2 : SNThree))
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · have hmem :
          (2 : SNThree) * (⟨1, 1⟩ : SNThree) ∈
            span {(2 : SNThree)} *
              span {(2 : SNThree), (⟨1, 1⟩ : SNThree)} :=
        Ideal.mul_mem_mul
          (Ideal.mem_span_singleton_self (2 : SNThree))
          (Ideal.subset_span
            (Set.mem_insert_of_mem (2 : SNThree) (Set.mem_singleton _)))
      simpa only [mul_comm (2 : SNThree) (⟨1, 1⟩ : SNThree)] using hmem
    · apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨(⟨1, 1⟩ : SNThree) - 2, ?_, ?_⟩
      · exact (span {(2 : SNThree), (⟨1, 1⟩ : SNThree)}).sub_mem
          (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
          (Ideal.subset_span (Set.mem_insert _ _))
      · ext <;> norm_num
  · rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, rfl⟩ := hz
    have hleft :
        a * ((2 : SNThree) * 2) ∈
          span ({(2 : SNThree) * 2,
            (2 : SNThree) * (⟨1, 1⟩ : SNThree),
            (⟨1, 1⟩ : SNThree) * 2,
            (⟨1, 1⟩ : SNThree) * (⟨1, 1⟩ : SNThree)} :
              Set SNThree) :=
      (span _).mul_mem_left a (Ideal.subset_span (Set.mem_insert _ _))
    have hright :
        b * ((2 : SNThree) * (⟨1, 1⟩ : SNThree)) ∈
          span ({(2 : SNThree) * 2,
            (2 : SNThree) * (⟨1, 1⟩ : SNThree),
            (⟨1, 1⟩ : SNThree) * 2,
            (⟨1, 1⟩ : SNThree) * (⟨1, 1⟩ : SNThree)} :
              Set SNThree) :=
      (span _).mul_mem_left b
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    have hsum := (span _).add_mem hleft hright
    convert hsum using 1
    all_goals ring

/-- The multiplicative monoid of ideals of `ℤ[√-3]` cannot be a unique-factorization monoid:
the identity `a² = (2)a` would cancel to the false equality `a = (2)`. -/
theorem ideals_unique_monoid :
    ¬Nonempty (UniqueFactorizationMonoid (Ideal SNThree)) := by
  rintro ⟨hufm⟩
  letI : UniqueFactorizationMonoid (Ideal SNThree) := hufm
  have hsq : badIdeal * badIdeal = span {(2 : SNThree)} * badIdeal := by
    simpa only [pow_two] using badIdeal_sq
  have hcancel : badIdeal = span {(2 : SNThree)} :=
    mul_right_cancel₀ (by simpa only [Ideal.zero_eq_bot] using bad_ne_bot) hsq
  exact bad_ne_two hcancel

end Towers.NumberTheory.Milne.SNThree
