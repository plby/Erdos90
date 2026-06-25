import Mathlib.Algebra.Polynomial.Splits
import Mathlib.NumberTheory.SumTwoSquares
import Submission.NumberTheory.Quadratic.PrimeDecomposition


/-!
# Milne, Algebraic Number Theory, Example 3.45

For an odd rational prime `p`, this file relates the congruence `p = 1 (mod 4)` to a
square root of `-1` modulo `p`, splitting of `X^2 + 1`, non-primality in the Gaussian
integers, and representation by two squares.  It also records the corresponding
factorization of `(p)` into two distinct prime ideals of `GaussianInt`.
-/

namespace Submission.NumberTheory.Milne

open Ideal Polynomial
open Submission.NumberTheory

noncomputable section

/-- The polynomial obtained by reducing the Gaussian minimal polynomial modulo `p`. -/
def gaussianReductionPolynomial (p : ℕ) : (ZMod p)[X] :=
  X ^ 2 + 1

/-- A square root of `-1` gives the two linear factors of `X^2 + 1`, and conversely a
splitting of this quadratic supplies such a root. -/
theorem gaussian_splits_sq
    (p : ℕ) [Fact p.Prime] :
    (gaussianReductionPolynomial p).Splits ↔
      ∃ x : ZMod p, x ^ 2 = -1 := by
  constructor
  · intro hsplit
    have hdeg : (gaussianReductionPolynomial p).degree = 2 := by
      simpa [gaussianReductionPolynomial] using
        (degree_X_pow_add_C (R := ZMod p) (by omega : 0 < 2) (1 : ZMod p))
    obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero (by rw [hdeg]; simp)
    refine ⟨x, ?_⟩
    exact add_eq_zero_iff_eq_neg.mp (by simpa [gaussianReductionPolynomial] using hx)
  · rintro ⟨x, hx⟩
    have hfactor : gaussianReductionPolynomial p =
        (X - C x) * (X + C x) := by
      calc
        gaussianReductionPolynomial p = X ^ 2 - C (x ^ 2) := by
          rw [gaussianReductionPolynomial, hx]
          simp
        _ = (X - C x) * (X + C x) := by
          rw [map_pow]
          ring
    rw [hfactor]
    exact (Splits.X_sub_C x).mul (Splits.X_add_C x)

/-- For an odd prime, the residue `1` modulo `4` is equivalent to the existence of a
square root of `-1` modulo `p`. -/
theorem mod_sq_neg
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    p % 4 = 1 ↔ ∃ x : ZMod p, x ^ 2 = -1 := by
  have hodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).2 hp2
  have hres : p % 4 = 1 ∨ p % 4 = 3 := Nat.odd_mod_four_iff.mp hodd
  have hsquare : IsSquare (-1 : ZMod p) ↔ ∃ x : ZMod p, x ^ 2 = -1 := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simpa [pow_two] using hx.symm⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by simpa [pow_two] using hx.symm⟩
  rw [← hsquare, ZMod.exists_sq_eq_neg_one_iff]
  constructor
  · exact fun hp1 hp3 ↦ by omega
  · intro hp3
    exact hres.resolve_right hp3

/-- The reduced Gaussian polynomial splits exactly for primes congruent to `1` modulo `4`. -/
theorem gaussian_splits_four
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (gaussianReductionPolynomial p).Splits ↔ p % 4 = 1 := by
  rw [gaussian_splits_sq,
    ← mod_sq_neg p hp2]

/-- An odd rational prime is reducible in the Gaussian integers exactly when it is `1`
modulo `4`. -/
theorem gaussian_int_four
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ Prime (p : GaussianInt) ↔ p % 4 = 1 := by
  rw [GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime]
  have hodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).2 hp2
  rcases Nat.odd_mod_four_iff.mp hodd with hp1 | hp3
  · simp [hp1]
  · simp [hp3]

/-- Fermat's two-square theorem, with the converse specialized to odd primes. -/
theorem int_sq_four
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2) ↔ p % 4 = 1 := by
  constructor
  · rintro ⟨a, b, hab⟩
    have hodd : p % 2 = 1 :=
      (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).2 hp2
    rcases Nat.odd_mod_four_iff.mp hodd with hp1 | hp3
    · exact hp1
    · exfalso
      have hbad : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 ≠ 3 := by decide
      apply hbad (a : ZMod 4) (b : ZMod 4)
      have hcast := congrArg (fun z : ℤ ↦ (z : ZMod 4)) hab
      simpa [← ZMod.natCast_mod p 4, hp3] using hcast.symm
  · intro hp1
    obtain ⟨a, b, hab⟩ :=
      Nat.Prime.sq_add_sq (p := p) (by omega : p % 4 ≠ 3)
    exact ⟨a, b, by exact_mod_cast hab.symm⟩

/-- The coordinate model `QOrd (-1) 0` is the Gaussian integer ring. -/
def gaussianQuadraticOrder :
    GaussianInt ≃+* QOrd (-1) 0 where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_mul' x y := by ext <;> simp

/-- Coordinatewise reduction of a Gaussian integer modulo `p`. -/
def gaussianReduceMod (p : ℕ) :
    GaussianInt →+*
      QuadraticAlgebra (ZMod p) ((-1 : ℤ) : ZMod p) ((0 : ℤ) : ZMod p) :=
  (QOrd.reduceMod (-1) 0 p).comp
    gaussianQuadraticOrder.toRingHom

@[simp]
theorem gaussian_reduce_re (p : ℕ) (z : GaussianInt) :
    (gaussianReduceMod p z).re = (z.re : ZMod p) := rfl

@[simp]
theorem gaussian_reduce_im (p : ℕ) (z : GaussianInt) :
    (gaussianReduceMod p z).im = (z.im : ZMod p) := rfl

theorem gaussian_reduce_surjective (p : ℕ) :
    Function.Surjective (gaussianReduceMod p) := by
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := ZMod.ringHom_surjective (Int.castRingHom (ZMod p)) x
  obtain ⟨b, rfl⟩ := ZMod.ringHom_surjective (Int.castRingHom (ZMod p)) y
  exact ⟨(⟨a, b⟩ : GaussianInt), rfl⟩

/-- Reduction modulo `p` has kernel the principal ideal `(p)`. -/
theorem gaussian_reduce_ker (p : ℕ) :
    span {(p : GaussianInt)} = RingHom.ker (gaussianReduceMod p) := by
  apply le_antisymm
  · rw [span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    apply QuadraticAlgebra.ext
    · simp
    · simp
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have hre : (z.re : ZMod p) = 0 := by
      simpa using congrArg QuadraticAlgebra.re hz
    have him : (z.im : ZMod p) = 0 := by
      simpa using congrArg QuadraticAlgebra.im hz
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z.re p).mp hre
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z.im p).mp him
    apply mem_span_singleton.mpr
    refine ⟨(⟨a, b⟩ : GaussianInt), ?_⟩
    apply Zsqrtd.ext
    · simpa [mul_comm] using ha
    · simpa [mul_comm] using hb

/-- The residue ring of the Gaussian integers modulo `(p)` is the quadratic algebra
over `ZMod p` defined by `X² + 1`. -/
noncomputable def gaussianQuadraticAlgebra (p : ℕ) :
    GaussianInt ⧸ span {(p : GaussianInt)} ≃+*
      QuadraticAlgebra (ZMod p) ((-1 : ℤ) : ZMod p) ((0 : ℤ) : ZMod p) :=
  (Ideal.quotEquivOfEq (gaussian_reduce_ker p)).trans
    (RingHom.quotientKerEquivOfSurjective (gaussian_reduce_surjective p))

/-- The concrete ramification identity `(2) = (1+i)²` in the Gaussian integers. -/
theorem gaussian_two_ramifies :
    span {(2 : GaussianInt)} = span {(⟨1, 1⟩ : GaussianInt)} ^ 2 := by
  have hi : IsUnit (⟨0, 1⟩ : GaussianInt) := by
    rw [Zsqrtd.isUnit_iff_norm_isUnit]
    norm_num [Zsqrtd.norm]
  rw [pow_two, Ideal.span_singleton_mul_span_singleton]
  have hmul :
      (⟨1, 1⟩ : GaussianInt) * ⟨1, 1⟩ =
        (2 : GaussianInt) * ⟨0, 1⟩ := by
    ext <;> norm_num
  rw [hmul, Ideal.span_singleton_mul_right_unit hi]

/-- The rational prime `3` remains prime in the Gaussian integers. -/
theorem gaussian_three_prime : Prime (3 : GaussianInt) := by
  exact GaussianInt.prime_of_nat_prime_of_mod_four_eq_three 3 (by norm_num)

/-- The ideal `(3)` is maximal, i.e. `3` is inert in the Gaussian integers. -/
theorem gaussian_three_inert : (span {(3 : GaussianInt)}).IsMaximal := by
  have hprime : (span {(3 : GaussianInt)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).2 gaussian_three_prime
  exact hprime.isMaximal (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))

/-- The quotient by `(3)` is a field. -/
theorem gaussian_residue_field :
    IsField (GaussianInt ⧸ span {(3 : GaussianInt)}) := by
  letI : (span {(3 : GaussianInt)}).IsMaximal := gaussian_three_inert
  exact (Ideal.Quotient.field (span {(3 : GaussianInt)})).toIsField

/-- The residue field in the inert example has nine elements, so it is a model of
the finite field `𝔽₉`. -/
theorem gaussian_residue_card :
    Nat.card (GaussianInt ⧸ span {(3 : GaussianInt)}) = 9 := by
  calc
    Nat.card (GaussianInt ⧸ span {(3 : GaussianInt)}) =
        Nat.card (QuadraticAlgebra (ZMod 3)
          ((-1 : ℤ) : ZMod 3) ((0 : ℤ) : ZMod 3)) :=
      Nat.card_congr (gaussianQuadraticAlgebra 3).toEquiv
    _ = Nat.card (ZMod 3 × ZMod 3) :=
      Nat.card_congr (QuadraticAlgebra.equivProd
        ((-1 : ℤ) : ZMod 3) ((0 : ℤ) : ZMod 3))
    _ = 9 := by norm_num [Nat.card_prod]

/-- The concrete splitting identity `(5) = (2+i)(2-i)` in the Gaussian integers. -/
theorem gaussian_five_splits :
    span {(5 : GaussianInt)} =
      span {(⟨2, 1⟩ : GaussianInt)} * span {(⟨2, -1⟩ : GaussianInt)} := by
  rw [Ideal.span_singleton_mul_span_singleton]
  have hmul :
      (⟨2, 1⟩ : GaussianInt) * ⟨2, -1⟩ = 5 := by
    ext <;> norm_num
  rw [hmul]

/-- A rational prime splits in the Gaussian integers when its principal ideal is the
product of two distinct prime ideals. -/
def GaussianIdealSplits (p : ℕ) : Prop :=
  ∃ P Q : Ideal GaussianInt,
    P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      P * Q = span {(p : GaussianInt)}

/-- The ideal-theoretic splitting asserted in Example 3.45: if `p = 1 (mod 4)`, then
`(p)` is a product of two distinct prime ideals in the Gaussian integers. -/
theorem gaussian_ideal_splits
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp1 : p % 4 = 1) :
    GaussianIdealSplits p := by
  obtain ⟨r, hr⟩ :=
    (mod_sq_neg p hp2).mp hp1
  obtain ⟨a, rfl⟩ :=
    ZMod.ringHom_surjective (Int.castRingHom (ZMod p)) r
  have hroot : (p : ℤ) ∣ a ^ 2 - (-1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simpa using sub_eq_zero.mpr hr
  have hpm : ¬(p : ℤ) ∣ (-1) := by
    intro h
    have hpunit : IsUnit (p : ℤ) := (isUnit_iff_dvd_one).2 (by simpa using h)
    exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_unit hpunit
  obtain ⟨hP, hQ, hne, hmul⟩ :=
    QOrd.odd_splits_order (-1) a p hp2 hpm hroot
  let e := gaussianQuadraticOrder
  let I := QOrd.rootIdeal (-1) 0 p a
  let J := QOrd.rootIdeal (-1) 0 p (-a)
  let P : Ideal GaussianInt := I.map e.symm.toRingHom
  let Q : Ideal GaussianInt := J.map e.symm.toRingHom
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · letI : I.IsPrime := hP
    exact Ideal.map_isPrime_of_surjective e.symm.surjective (by simp)
  · letI : J.IsPrime := hQ
    exact Ideal.map_isPrime_of_surjective e.symm.surjective (by simp)
  · intro hPQ
    apply hne
    exact (e.symm.idealComapOrderIso.symm.injective hPQ)
  · simpa [P, Q, I, J, e, Ideal.map_mul, Ideal.map_span, Set.image_singleton] using
      congrArg (Ideal.map e.symm.toRingHom) hmul

/-- The principal ideal `(p)` splits in the Gaussian integers exactly when `p` is `1`
modulo `4`. -/
theorem gaussian_splits_mod
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    GaussianIdealSplits p ↔ p % 4 = 1 := by
  constructor
  · rintro ⟨P, Q, hP, hQ, hne, hmul⟩
    have hnot3 : p % 4 ≠ 3 := by
      intro hp3
      have hp0 : (p : GaussianInt) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      have hspan : (span {(p : GaussianInt)}).IsPrime :=
        (Ideal.span_singleton_prime hp0).2
          (GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p hp3)
      have hP0 : P ≠ ⊥ := by
        intro hzero
        have : span {(p : GaussianInt)} = ⊥ := by
          rw [← hmul, hzero]
          simp
        exact (Ideal.span_singleton_eq_bot.not.mpr hp0) this
      have hQ0 : Q ≠ ⊥ := by
        intro hzero
        have : span {(p : GaussianInt)} = ⊥ := by
          rw [← hmul, hzero]
          simp
        exact (Ideal.span_singleton_eq_bot.not.mpr hp0) this
      rcases hspan.mul_le.mp (le_of_eq hmul) with hP_le | hQ_le
      · have hPQ : P ≤ Q := hP_le.trans (by rw [← hmul]; exact Ideal.mul_le_left)
        exact hne ((hP.isMaximal hP0).eq_of_le hQ.ne_top hPQ)
      · have hQP : Q ≤ P := hQ_le.trans (by rw [← hmul]; exact Ideal.mul_le_right)
        exact hne ((hQ.isMaximal hQ0).eq_of_le hP.ne_top hQP).symm
    have hodd : p % 2 = 1 :=
      (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).2 hp2
    exact (Nat.odd_mod_four_iff.mp hodd).resolve_right hnot3
  · exact gaussian_ideal_splits p hp2

/-- The five elementary formulations of Example 3.45, bundled as a single equivalence. -/
theorem gaussian_prime_equivalences
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    p % 4 = 1 ↔
      (∃ x : ZMod p, x ^ 2 = -1) ∧
      (gaussianReductionPolynomial p).Splits ∧
      GaussianIdealSplits p ∧
      ¬ Prime (p : GaussianInt) ∧
      ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 := by
  constructor
  · intro hp1
    exact ⟨(mod_sq_neg p hp2).mp hp1,
      (gaussian_splits_four p hp2).2 hp1,
      (gaussian_splits_mod p hp2).2 hp1,
      (gaussian_int_four p hp2).2 hp1,
      (int_sq_four p hp2).2 hp1⟩
  · rintro ⟨_, _, _, _, hsum⟩
    exact (int_sq_four p hp2).1 hsum

end

end Submission.NumberTheory.Milne
