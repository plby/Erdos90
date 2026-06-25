import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Towers.NumberTheory.Quadratic.IntegralElements

attribute [-instance] DivisionRing.toRatAlgebra

namespace Towers.NumberTheory

open scoped NumberField

namespace CNOne

open RingOfIntegers

/-- The conductors in the Masley--Montgomery class-number-one classification. -/
def masleyMontgomeryConductors : Finset ℕ :=
  {3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 17, 19, 20, 21, 24, 25, 27, 28,
    32, 33, 35, 36, 40, 44, 45, 48, 60, 84}

/-- The Heegner radicands in the Baker--Heegner--Stark classification. -/
def heegnerRadicands : Finset ℤ :=
  {-1, -2, -3, -7, -11, -19, -43, -67, -163}

/-- Class number one for the canonical cyclotomic field of conductor `m`. -/
def CyclotomicClassNumber (m : ℕ) : Prop :=
  NumberField.classNumber (CyclotomicField m ℚ) = 1

/-- A precise Lean statement of Wright's Theorem 72.  Wright cites this theorem
without proof; the predicate lets subsequent deductions use exactly that statement. -/
def MasleyMontgomeryStatement : Prop :=
  ∀ m : ℕ, 3 ≤ m →
    (CyclotomicClassNumber m ↔ m ∈ masleyMontgomeryConductors)

private theorem negative_quadratic_nonsquare (m : ℤ) (hm : m < 0) :
    ∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r := by
  intro r hr
  have hmQ : (m : ℚ) < 0 := by exact_mod_cast hm
  have hsquare : 0 ≤ r ^ 2 := sq_nonneg r
  norm_num at hr
  linarith

/-- The class number of `ℚ(√m)` for a negative radicand, using the coordinate
model from Chapter 6. -/
noncomputable def negativeQuadraticNumber (m : ℤ) (hm : m < 0) : ℕ := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨negative_quadratic_nonsquare m hm⟩
  letI : NumberField (QFModel m) :=
    NumberField.of_module_finite ℚ (QFModel m)
  exact NumberField.classNumber (QFModel m)

/-- A precise Lean statement of Wright's Theorem 74. -/
def BakerHeegnerStark : Prop :=
  ∀ (m : ℤ) (hm : m < 0), Squarefree m →
    (negativeQuadraticNumber m hm = 1 ↔ m ∈ heegnerRadicands)

private abbrev GaussianOrder := QuadraticAlgebra ℤ (-1) 0

private def gaussianOrderEquiv : GaussianInt ≃+* GaussianOrder where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_mul' x y := by ext <;> simp

private theorem gaussian_principal_ring :
    IsPrincipalIdealRing GaussianOrder := by
  exact IsPrincipalIdealRing.of_surjective gaussianOrderEquiv.toRingHom
    gaussianOrderEquiv.surjective

private def gaussianOrderEmbedding :
    GaussianOrder →+* QFModel (-1) where
  toFun z := ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> norm_num
  map_one' := by apply QuadraticAlgebra.ext <;> norm_num [QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one]
  map_add' x y := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;> norm_cast
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul]
      push_cast
      ring
    · simp only [QuadraticAlgebra.im_mul]
      push_cast
      ring

private theorem gaussian_embedding_injective :
    Function.Injective gaussianOrderEmbedding := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · have h := congrArg QuadraticAlgebra.re hxy
    change (x.re : ℚ) = (y.re : ℚ) at h
    exact Rat.intCast_injective h
  · have h := congrArg QuadraticAlgebra.im hxy
    change (x.im : ℚ) = (y.im : ℚ) at h
    exact Rat.intCast_injective h

private local instance : Algebra GaussianOrder (QFModel (-1)) :=
  gaussianOrderEmbedding.toAlgebra

private local instance : IsScalarTower ℤ GaussianOrder (QFModel (-1)) :=
  IsScalarTower.of_algebraMap_eq' rfl

@[reducible] private def gaussianIntegralClosure :
    IsIntegralClosure GaussianOrder ℤ (QFModel (-1)) where
  algebraMap_injective := gaussian_embedding_injective
  isIntegral_iff {x} := by
    rw [QFModel.gaussian_integer_coordinates]
    constructor
    · rintro ⟨a, b, ha, hb⟩
      refine ⟨(⟨a, b⟩ : GaussianOrder), ?_⟩
      change gaussianOrderEmbedding (⟨a, b⟩ : GaussianOrder) = x
      apply QuadraticAlgebra.ext
      · exact ha.symm
      · exact hb.symm
    · rintro ⟨y, rfl⟩
      refine ⟨y.re, y.im, ?_, ?_⟩
      · change (gaussianOrderEmbedding y).re = (y.re : ℚ)
        rfl
      · change (gaussianOrderEmbedding y).im = (y.im : ℚ)
        rfl

/-- The Gaussian positive case in Theorem 74. -/
theorem negative_quadratic_number :
    negativeQuadraticNumber (-1) (by norm_num) = 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ ((-1 : ℤ) : ℚ) + 0 * r) :=
    ⟨negative_quadratic_nonsquare (-1) (by norm_num)⟩
  letI : NumberField (QFModel (-1)) :=
    NumberField.of_module_finite ℚ (QFModel (-1))
  letI : Algebra GaussianOrder (QFModel (-1)) :=
    gaussianOrderEmbedding.toAlgebra
  letI : IsScalarTower ℤ GaussianOrder (QFModel (-1)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure GaussianOrder ℤ (QFModel (-1)) :=
    gaussianIntegralClosure
  letI : IsPrincipalIdealRing GaussianOrder := gaussian_principal_ring
  change NumberField.classNumber (QFModel (-1)) = 1
  rw [NumberField.classNumber_eq_one_iff]
  let e : 𝓞 (QFModel (-1)) ≃+* GaussianOrder :=
    @NumberField.RingOfIntegers.equiv (QFModel (-1)) inferInstance
      GaussianOrder inferInstance gaussianOrderEmbedding.toAlgebra
      gaussianIntegralClosure
  exact IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective

/-- For a number ring, unique factorization is equivalent to class number one. -/
theorem integers_unique_monoid
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (UniqueFactorizationMonoid (𝓞 K)) ↔
      NumberField.classNumber K = 1 := by
  constructor
  · rintro ⟨hufd⟩
    letI : UniqueFactorizationMonoid (𝓞 K) := hufd
    rw [NumberField.classNumber_eq_one_iff]
    exact IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid (𝓞 K)
  · intro hclass
    letI : IsPrincipalIdealRing (𝓞 K) :=
      NumberField.classNumber_eq_one_iff.mp hclass
    exact ⟨inferInstance⟩

/-- Among odd primes, membership in the Masley--Montgomery list is equivalent
to being at most `19`. -/
theorem masley_montgomery_nineteen
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    p ∈ masleyMontgomeryConductors ↔ p ≤ 19 := by
  constructor
  · intro hmem
    have hp2 : 2 ≤ p := hp.two_le
    have hp84 : p ≤ 84 := by
      simp only [masleyMontgomeryConductors, Finset.mem_insert,
        Finset.mem_singleton] at hmem
      omega
    interval_cases p <;> norm_num [masleyMontgomeryConductors] at *
  · intro hp19
    have hp2 : 2 ≤ p := hp.two_le
    interval_cases p <;> norm_num [masleyMontgomeryConductors] at *

/-- Corollary 73 is the prime-conductor specialization of Theorem 72. -/
theorem conjecture_masley_montgomery
    (hMM : MasleyMontgomeryStatement) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) :
    CyclotomicClassNumber p ↔ p ≤ 19 := by
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    have hp_ne_two : p ≠ 2 := by
      intro hp_eq
      subst p
      norm_num at hodd
    omega
  rw [hMM p hp3, masley_montgomery_nineteen hp hodd]

/-- The conductor `3` positive case of Theorem 72, already proved in Mathlib. -/
theorem cyclotomic_number_one :
    CyclotomicClassNumber 3 := by
  letI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  rw [CyclotomicClassNumber, NumberField.classNumber_eq_one_iff]
  exact @IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
    inferInstance inferInstance (CyclotomicField.isCyclotomicExtension 3 ℚ)

/-- The conductor `4` positive case of Theorem 72. -/
theorem cyclotomic_four_number :
    CyclotomicClassNumber 4 := by
  letI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (4 : ℚ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have hcycloPow : IsCyclotomicExtension {2 ^ 2} ℚ (CyclotomicField 4 ℚ) := by
    norm_num
    exact CyclotomicField.isCyclotomicExtension 4 ℚ
  have hdiscr : NumberField.discr (CyclotomicField 4 ℚ) = -4 := by
    simpa using
      (@IsCyclotomicExtension.Rat.discr_prime_pow 2 2 (CyclotomicField 4 ℚ)
        inferInstance inferInstance inferInstance hcycloPow)
  have hfinrank : Module.finrank ℚ (CyclotomicField 4 ℚ) = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 4) (CyclotomicField 4 ℚ)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  have hfinrank_numberField :
      @Module.finrank ℚ (CyclotomicField 4 ℚ) inferInstance inferInstance
        (@Algebra.toModule ℚ (CyclotomicField 4 ℚ) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (CyclotomicField 4 ℚ) inferInstance
            inferInstance)) = 2 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (CyclotomicField 4 ℚ)) =
          @DivisionRing.toRatAlgebra (CyclotomicField 4 ℚ) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces
      (CyclotomicField 4 ℚ) = 1 := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
      (CyclotomicField 4 ℚ)
    have hcard2 : NumberField.InfinitePlace.nrRealPlaces
          (CyclotomicField 4 ℚ) +
          2 * NumberField.InfinitePlace.nrComplexPlaces
            (CyclotomicField 4 ℚ) = 2 :=
      hcard.trans hfinrank_numberField
    have hsle : NumberField.InfinitePlace.nrComplexPlaces
        (CyclotomicField 4 ℚ) ≤ 1 := by omega
    have hsign := NumberField.sign_discr (K := CyclotomicField 4 ℚ)
    rw [hdiscr] at hsign
    interval_cases hC : NumberField.InfinitePlace.nrComplexPlaces
        (CyclotomicField 4 ℚ)
    · have hsignD : ((-4 : ℤ).sign) = -1 := Int.sign_eq_neg_one_of_neg (by norm_num)
      rw [hsignD] at hsign
      norm_num at hsign
    · rfl
  rw [CyclotomicClassNumber, NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [hdiscr, hfinrank_numberField, hcomplex]
  norm_num
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  nlinarith

/-- The conductor `5` positive case of Theorem 72, already proved in Mathlib. -/
theorem cyclotomic_five_number :
    CyclotomicClassNumber 5 := by
  letI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (5 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  rw [CyclotomicClassNumber, NumberField.classNumber_eq_one_iff]
  exact @IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)
    inferInstance inferInstance (CyclotomicField.isCyclotomicExtension 5 ℚ)

/-- The conductor `7` positive case of Theorem 72. -/
theorem cyclotomic_seven_number :
    CyclotomicClassNumber 7 := by
  letI : NeZero (7 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (7 : ℚ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let hcyclo : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) :=
    CyclotomicField.isCyclotomicExtension 7 ℚ
  letI : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) := hcyclo
  have hdiscr : NumberField.discr (CyclotomicField 7 ℚ) = -16807 := by
    simpa using
      (@IsCyclotomicExtension.Rat.discr_prime 7 (CyclotomicField 7 ℚ)
        inferInstance inferInstance inferInstance hcyclo)
  have hfinrank : Module.finrank ℚ (CyclotomicField 7 ℚ) = 6 := by
    rw [IsCyclotomicExtension.finrank (n := 7) (CyclotomicField 7 ℚ)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    rw [Nat.totient_prime (by norm_num)]
  have hfinrank_numberField :
      @Module.finrank ℚ (CyclotomicField 7 ℚ) inferInstance inferInstance
        (@Algebra.toModule ℚ (CyclotomicField 7 ℚ) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (CyclotomicField 7 ℚ) inferInstance
            inferInstance)) = 6 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (CyclotomicField 7 ℚ)) =
          @DivisionRing.toRatAlgebra (CyclotomicField 7 ℚ) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces
      (CyclotomicField 7 ℚ) = 3 := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
      (CyclotomicField 7 ℚ)
    have hcard6 : NumberField.InfinitePlace.nrRealPlaces
          (CyclotomicField 7 ℚ) +
          2 * NumberField.InfinitePlace.nrComplexPlaces
            (CyclotomicField 7 ℚ) = 6 :=
      hcard.trans hfinrank_numberField
    have hreal : NumberField.InfinitePlace.nrRealPlaces
        (CyclotomicField 7 ℚ) = 0 :=
      @IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero 7 inferInstance
        (CyclotomicField 7 ℚ) inferInstance inferInstance hcyclo (by norm_num)
    omega
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (CyclotomicField 7 ℚ) *
        (Nat.factorial
            (@Module.finrank ℚ (CyclotomicField 7 ℚ) inferInstance inferInstance
              (@Algebra.toModule ℚ (CyclotomicField 7 ℚ) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (CyclotomicField 7 ℚ) inferInstance
                  inferInstance))) /
          (@Module.finrank ℚ (CyclotomicField 7 ℚ) inferInstance inferInstance
              (@Algebra.toModule ℚ (CyclotomicField 7 ℚ) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (CyclotomicField 7 ℚ) inferInstance
                  inferInstance))) ^
            (@Module.finrank ℚ (CyclotomicField 7 ℚ) inferInstance inferInstance
              (@Algebra.toModule ℚ (CyclotomicField 7 ℚ) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (CyclotomicField 7 ℚ) inferInstance
                  inferInstance))) *
          √|NumberField.discr (CyclotomicField 7 ℚ)|)⌋₊ = 4 := by
    rw [hcomplex, hfinrank_numberField, hdiscr]
    norm_num
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hsqrt : (2.64 : ℝ) < √7 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have hsqrt16807 : √(16807 : ℝ) = 49 * √7 := by
        calc
          √(16807 : ℝ) = √((2401 : ℝ) * 7) := by norm_num
          _ = √(2401 : ℝ) * √7 := by rw [Real.sqrt_mul (by norm_num)]
          _ = 49 * √7 := by norm_num
      rw [hsqrt16807]
      rw [show (4 / Real.pi) ^ 3 * (5 / 324 * (49 * √7)) =
        3920 * √7 / (81 * Real.pi ^ 3) by ring]
      rw [le_div_iff₀ (by positivity)]
      have hpi3 : Real.pi ^ 3 < (3.15 : ℝ) ^ 3 := by gcongr
      norm_num at hpi3 ⊢
      nlinarith
    · have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hsqrt : √(7 : ℝ) < 2.65 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have hsqrt16807 : √(16807 : ℝ) = 49 * √7 := by
        calc
          √(16807 : ℝ) = √((2401 : ℝ) * 7) := by norm_num
          _ = √(2401 : ℝ) * √7 := by rw [Real.sqrt_mul (by norm_num)]
          _ = 49 * √7 := by norm_num
      rw [hsqrt16807]
      rw [show (4 / Real.pi) ^ 3 * (5 / 324 * (49 * √7)) =
        3920 * √7 / (81 * Real.pi ^ 3) by ring]
      norm_num
      rw [div_lt_iff₀ (by positivity)]
      have hpi3 : (3 : ℝ) ^ 3 < Real.pi ^ 3 := by gcongr
      norm_num at hpi3 ⊢
      nlinarith
  have horderTwo : orderOf (2 : ZMod 7) = 3 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderThree : orderOf (3 : ZMod 7) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  rw [CyclotomicClassNumber, NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  rw [hfloor]
  intro p hp hpprime P hP hpow
  have hp_le : p ≤ 4 := (Finset.mem_Icc.mp hp).2
  have hp_ge : 2 ≤ p := hpprime.two_le
  have hp_cases : p = 2 ∨ p = 3 := by
    by_cases hp_two : p = 2
    · exact Or.inl hp_two
    · right
      have hp_ne_four : p ≠ 4 := by
        intro hp_four
        subst p
        norm_num at hpprime
      omega
  rcases hp_cases with rfl | rfl
  · letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
    have hinertia : (Ideal.span {(2 : ℤ)}).inertiaDeg P =
        orderOf (2 : ZMod 7) :=
      @IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 7 2 inferInstance
        (CyclotomicField 7 ℚ) inferInstance inferInstance P inferInstance inferInstance
        inferInstance hcyclo (by norm_num)
    change 2 ^ (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P ≤ 4 at hpow
    rw [hinertia, horderTwo] at hpow
    norm_num at hpow
  · letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
    have hinertia : (Ideal.span {(3 : ℤ)}).inertiaDeg P =
        orderOf (3 : ZMod 7) :=
      @IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 7 3 inferInstance
        (CyclotomicField 7 ℚ) inferInstance inferInstance P inferInstance inferInstance
        inferInstance hcyclo (by norm_num)
    change 3 ^ (Ideal.span ({(3 : ℤ)} : Set ℤ)).inertiaDeg P ≤ 4 at hpow
    rw [hinertia, horderThree] at hpow
    norm_num at hpow

/-- The conductor `8` positive case of Theorem 72. -/
theorem cyclotomic_eight_number :
    CyclotomicClassNumber 8 := by
  letI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (8 : ℚ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hcyclo : IsCyclotomicExtension {8} ℚ (CyclotomicField 8 ℚ) :=
    CyclotomicField.isCyclotomicExtension 8 ℚ
  letI : IsCyclotomicExtension {8} ℚ (CyclotomicField 8 ℚ) := hcyclo
  have hcycloPow : IsCyclotomicExtension {2 ^ (2 + 1)} ℚ
      (CyclotomicField 8 ℚ) := by
    norm_num
    exact hcyclo
  letI : IsCyclotomicExtension {2 ^ (2 + 1)} ℚ
      (CyclotomicField 8 ℚ) := hcycloPow
  have hdiscr : NumberField.discr (CyclotomicField 8 ℚ) = 256 := by
    simpa using
      (@IsCyclotomicExtension.Rat.discr_prime_pow_succ 2 2
        (CyclotomicField 8 ℚ) inferInstance inferInstance inferInstance hcycloPow)
  have hfinrank : Module.finrank ℚ (CyclotomicField 8 ℚ) = 4 := by
    rw [IsCyclotomicExtension.finrank (n := 8) (CyclotomicField 8 ℚ)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  have hfinrank_numberField :
      @Module.finrank ℚ (CyclotomicField 8 ℚ) inferInstance inferInstance
        (@Algebra.toModule ℚ (CyclotomicField 8 ℚ) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (CyclotomicField 8 ℚ) inferInstance
            inferInstance)) = 4 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (CyclotomicField 8 ℚ)) =
          @DivisionRing.toRatAlgebra (CyclotomicField 8 ℚ) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces
      (CyclotomicField 8 ℚ) = 2 := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
      (CyclotomicField 8 ℚ)
    have hcard4 : NumberField.InfinitePlace.nrRealPlaces
          (CyclotomicField 8 ℚ) +
          2 * NumberField.InfinitePlace.nrComplexPlaces
            (CyclotomicField 8 ℚ) = 4 :=
      hcard.trans hfinrank_numberField
    have hreal : NumberField.InfinitePlace.nrRealPlaces
        (CyclotomicField 8 ℚ) = 0 :=
      @IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero 8 inferInstance
        (CyclotomicField 8 ℚ) inferInstance inferInstance hcyclo (by norm_num)
    omega
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (CyclotomicField 8 ℚ) *
        (Nat.factorial
            (@Module.finrank ℚ (CyclotomicField 8 ℚ) inferInstance inferInstance
              (@Algebra.toModule ℚ (CyclotomicField 8 ℚ) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (CyclotomicField 8 ℚ) inferInstance
                  inferInstance))) /
          (@Module.finrank ℚ (CyclotomicField 8 ℚ) inferInstance inferInstance
              (@Algebra.toModule ℚ (CyclotomicField 8 ℚ) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (CyclotomicField 8 ℚ) inferInstance
                  inferInstance))) ^
            (@Module.finrank ℚ (CyclotomicField 8 ℚ) inferInstance inferInstance
              (@Algebra.toModule ℚ (CyclotomicField 8 ℚ) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (CyclotomicField 8 ℚ) inferInstance
                  inferInstance))) *
          √|NumberField.discr (CyclotomicField 8 ℚ)|)⌋₊ = 2 := by
    rw [hcomplex, hfinrank_numberField, hdiscr]
    norm_num
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · change (2 : ℝ) ≤ (4 / Real.pi) ^ 2 * (3 / 2)
      rw [show (4 / Real.pi) ^ 2 * (3 / 2) = 24 / Real.pi ^ 2 by
        field_simp [Real.pi_ne_zero]
        ring]
      rw [le_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
      have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hpi2 : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by gcongr
      norm_num at hpi2 ⊢
      nlinarith
    · norm_num
      change (4 / Real.pi) ^ 2 * (3 / 2) < (3 : ℝ)
      rw [show (4 / Real.pi) ^ 2 * (3 / 2) = 24 / Real.pi ^ 2 by
        field_simp [Real.pi_ne_zero]
        ring]
      rw [div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)]
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hpi2 : (3 : ℝ) ^ 2 < Real.pi ^ 2 :=
        (sq_lt_sq₀ (by norm_num) Real.pi_pos.le).2 hpi
      nlinarith
  rw [CyclotomicClassNumber, NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  rw [hfloor]
  intro p hp hpprime P hP hpow
  have hp_le : p ≤ 2 := (Finset.mem_Icc.mp hp).2
  have hp_ge : 2 ≤ p := hpprime.two_le
  have hp_eq : p = 2 := by omega
  subst p
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  have hζ : IsPrimitiveRoot
      (IsCyclotomicExtension.zeta (2 ^ (2 + 1)) ℚ (CyclotomicField 8 ℚ))
      (2 ^ (2 + 1)) :=
    @IsCyclotomicExtension.zeta_spec (2 ^ (2 + 1)) inferInstance ℚ
      (CyclotomicField 8 ℚ) inferInstance inferInstance inferInstance hcycloPow
  rw [@IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver
    2 2 inferInstance (CyclotomicField 8 ℚ) inferInstance inferInstance hcycloPow
      _ hζ P inferInstance inferInstance]
  exact ⟨hζ.toInteger - 1, rfl⟩

/-- The conductor `9` positive case of Theorem 72. -/
theorem cyclotomic_nine_number :
    CyclotomicClassNumber 9 := by
  letI : NeZero (9 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (9 : ℚ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let hcyclo : IsCyclotomicExtension {9} ℚ (CyclotomicField 9 ℚ) :=
    CyclotomicField.isCyclotomicExtension 9 ℚ
  letI : IsCyclotomicExtension {9} ℚ (CyclotomicField 9 ℚ) := hcyclo
  have hcycloPow : IsCyclotomicExtension {3 ^ (1 + 1)} ℚ
      (CyclotomicField 9 ℚ) := by
    norm_num
    exact hcyclo
  have hdiscr : NumberField.discr (CyclotomicField 9 ℚ) = -19683 := by
    simpa using
      (@IsCyclotomicExtension.Rat.discr_prime_pow_succ 3 1
        (CyclotomicField 9 ℚ) inferInstance inferInstance inferInstance hcycloPow)
  have hfinrank : Module.finrank ℚ (CyclotomicField 9 ℚ) = 6 := by
    rw [IsCyclotomicExtension.finrank (n := 9) (CyclotomicField 9 ℚ)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  have hfinrank_numberField :
      @Module.finrank ℚ (CyclotomicField 9 ℚ) inferInstance inferInstance
        (@Algebra.toModule ℚ (CyclotomicField 9 ℚ) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (CyclotomicField 9 ℚ) inferInstance
            inferInstance)) = 6 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (CyclotomicField 9 ℚ)) =
          @DivisionRing.toRatAlgebra (CyclotomicField 9 ℚ) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces
      (CyclotomicField 9 ℚ) = 3 := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
      (CyclotomicField 9 ℚ)
    have hcard6 : NumberField.InfinitePlace.nrRealPlaces
          (CyclotomicField 9 ℚ) +
          2 * NumberField.InfinitePlace.nrComplexPlaces
            (CyclotomicField 9 ℚ) = 6 :=
      hcard.trans hfinrank_numberField
    have hreal : NumberField.InfinitePlace.nrRealPlaces
        (CyclotomicField 9 ℚ) = 0 :=
      @IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero 9 inferInstance
        (CyclotomicField 9 ℚ) inferInstance inferInstance hcyclo (by norm_num)
    omega
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (CyclotomicField 9 ℚ) *
        (Nat.factorial
            (@Module.finrank ℚ (CyclotomicField 9 ℚ) inferInstance inferInstance
              (@Algebra.toModule ℚ (CyclotomicField 9 ℚ) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (CyclotomicField 9 ℚ) inferInstance
                  inferInstance))) /
          (@Module.finrank ℚ (CyclotomicField 9 ℚ) inferInstance inferInstance
              (@Algebra.toModule ℚ (CyclotomicField 9 ℚ) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (CyclotomicField 9 ℚ) inferInstance
                  inferInstance))) ^
            (@Module.finrank ℚ (CyclotomicField 9 ℚ) inferInstance inferInstance
              (@Algebra.toModule ℚ (CyclotomicField 9 ℚ) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (CyclotomicField 9 ℚ) inferInstance
                  inferInstance))) *
          √|NumberField.discr (CyclotomicField 9 ℚ)|)⌋₊ = 4 := by
    rw [hcomplex, hfinrank_numberField, hdiscr]
    norm_num
    have hsqrt19683 : √(19683 : ℝ) = 81 * √3 := by
      calc
        √(19683 : ℝ) = √((6561 : ℝ) * 3) := by norm_num
        _ = √(6561 : ℝ) * √3 := by rw [Real.sqrt_mul (by norm_num)]
        _ = 81 * √3 := by norm_num
    rw [hsqrt19683]
    rw [show (4 / Real.pi) ^ 3 * (5 / 324 * (81 * √3)) =
      80 * √3 / Real.pi ^ 3 by ring]
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ (pow_pos Real.pi_pos 3)]
      have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hpi3 : Real.pi ^ 3 < (3.15 : ℝ) ^ 3 := by gcongr
      have hsqrt : (1.73 : ℝ) < √3 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      norm_num at hpi3 hsqrt ⊢
      nlinarith
    · norm_num
      rw [div_lt_iff₀ (pow_pos Real.pi_pos 3)]
      have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      have hpi3 : (3.14 : ℝ) ^ 3 < Real.pi ^ 3 := by gcongr
      have hsqrt : √(3 : ℝ) < 1.74 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      norm_num at hpi3 hsqrt ⊢
      nlinarith
  have horderTwo : orderOf (2 : ZMod 9) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  rw [CyclotomicClassNumber, NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  rw [hfloor]
  intro p hp hpprime P hP hpow
  have hp_le : p ≤ 4 := (Finset.mem_Icc.mp hp).2
  have hp_ge : 2 ≤ p := hpprime.two_le
  have hp_cases : p = 2 ∨ p = 3 := by
    by_cases hp_two : p = 2
    · exact Or.inl hp_two
    · right
      have hp_ne_four : p ≠ 4 := by
        intro hp_four
        subst p
        norm_num at hpprime
      omega
  rcases hp_cases with rfl | rfl
  · letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
    have hinertia : (Ideal.span {(2 : ℤ)}).inertiaDeg P =
        orderOf (2 : ZMod 9) :=
      @IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 9 2 inferInstance
        (CyclotomicField 9 ℚ) inferInstance inferInstance P inferInstance inferInstance
        inferInstance hcyclo (by norm_num)
    change 2 ^ (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P ≤ 4 at hpow
    rw [hinertia, horderTwo] at hpow
    norm_num at hpow
  · letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
    have hζ : IsPrimitiveRoot
        (IsCyclotomicExtension.zeta (3 ^ (1 + 1)) ℚ (CyclotomicField 9 ℚ))
        (3 ^ (1 + 1)) :=
      @IsCyclotomicExtension.zeta_spec (3 ^ (1 + 1)) inferInstance ℚ
        (CyclotomicField 9 ℚ) inferInstance inferInstance inferInstance hcycloPow
    rw [@IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver
      3 1 inferInstance (CyclotomicField 9 ℚ) inferInstance inferInstance hcycloPow
        _ hζ P inferInstance inferInstance]
    exact ⟨hζ.toInteger - 1, rfl⟩

open Polynomial Ideal NumberField RingOfIntegers NumberField.Ideal

abbrev K11 := CyclotomicField 11 ℚ

/-- The conductor `11` positive case of Theorem 72. -/
theorem cyclotomic_eleven_number :
    CyclotomicClassNumber 11 := by
  letI : NeZero (11 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (11 : ℚ) := ⟨by norm_num⟩
  letI : NeZero (23 : ℕ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  letI hcyclo : IsCyclotomicExtension {11} ℚ K11 :=
    CyclotomicField.isCyclotomicExtension 11 ℚ
  let hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 11 ℚ K11) 11 :=
    IsCyclotomicExtension.zeta_spec 11 ℚ K11
  let θ : 𝓞 K11 := hζ.toInteger
  let Q : ℤ[X] := X - C 13
  have hexponent : exponent θ = 1 := by
    apply exponent_eq_one_iff.mpr
    exact @IsCyclotomicExtension.Rat.adjoin_singleton_eq_top 11 K11 inferInstance
      inferInstance inferInstance hcyclo _ hζ
  have hnotdvd : ¬ 23 ∣ exponent θ := by
    rw [hexponent]
    norm_num
  have hminpoly : minpoly ℤ θ = cyclotomic 11 ℤ := by
    calc
      minpoly ℤ θ = minpoly ℤ (θ : K11) := (RingOfIntegers.minpoly_coe θ).symm
      _ = minpoly ℤ (IsCyclotomicExtension.zeta 11 ℚ K11) := by
        simp [θ]
      _ = cyclotomic 11 ℤ :=
        (cyclotomic_eq_minpoly hζ (by norm_num)).symm
  have hQ : Q.map (Int.castRingHom (ZMod 23)) ∈
      monicFactorsMod θ 23 := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
      (map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    constructor
    · simpa [Q] using irreducible_X_sub_C (13 : ZMod 23)
    · constructor
      · simpa [Q] using monic_X_sub_C (13 : ZMod 23)
      · have hroot : IsRoot
            (map (Int.castRingHom (ZMod 23)) (minpoly ℤ θ))
            (13 : ZMod 23) := by
          change eval (13 : ZMod 23)
            (map (Int.castRingHom (ZMod 23)) (minpoly ℤ θ)) = 0
          rw [hminpoly, map_cyclotomic_int]
          norm_num [eval_map, cyclotomic_prime]
          decide
        simpa [Q] using (dvd_iff_isRoot.mpr hroot)
  let A : ℤ[X] := 1 - X + X ^ 3
  let U : ℤ[X] := -11 * X ^ 2 - 5 * X + 15
  let V : ℤ[X] :=
    11 * X ^ 9 + 16 * X ^ 8 + 12 * X ^ 7 + 6 * X ^ 6 - 3 * X ^ 5 -
      5 * X ^ 4 - 8 * X ^ 3 - X ^ 2 - 2 * X + 8
  let Cpoly : ℤ[X] :=
    6 * X ^ 8 + 10 * X ^ 7 - 7 * X ^ 6 - 9 * X ^ 5 - 7 * X ^ 4 +
      8 * X ^ 3 - 11 * X ^ 2 + 2 * X - 9
  let D : ℤ[X] := X ^ 9 + X ^ 8 + X ^ 5 + X ^ 4 + X ^ 2
  let B : ℤ[X] := X ^ 2 + 13 * X + 168
  have hbezout : U * cyclotomic 11 ℤ + V * A = C 23 := by
    norm_num [U, V, A, cyclotomic_prime, Finset.sum_range_succ]
    ring
  have hlinear :
      Cpoly * A - Q = (6 * X + 4) * cyclotomic 11 ℤ - C 23 * D := by
    norm_num [Cpoly, A, Q, D, cyclotomic_prime, Finset.sum_range_succ]
    ring
  have halpha : A = Q * B + C (23 * 95) := by
    simp [A, Q, B]
    ring
  let α : 𝓞 K11 := 1 - θ + θ ^ 3
  have hphi_eval : aeval θ (cyclotomic 11 ℤ) = 0 := by
    rw [← hminpoly]
    exact minpoly.aeval ℤ θ
  have hA_eval : aeval θ A = α := by
    simp [A, α]
  have hQ_eval : aeval θ Q = θ - 13 := by
    simp only [Q, map_sub, aeval_X, aeval_C]
    rfl
  have hValpha : aeval θ V * α = 23 := by
    have h := congrArg (aeval θ) hbezout
    simp only [map_add, map_mul, hphi_eval, mul_zero, zero_add, hA_eval, aeval_C] at h
    norm_num at h ⊢
    exact h
  have h23_span : (23 : 𝓞 K11) ∈ span ({α} : Set (𝓞 K11)) := by
    rw [Ideal.mem_span_singleton']
    exact ⟨aeval θ V, hValpha⟩
  have hlinear_span : θ - 13 ∈ span ({α} : Set (𝓞 K11)) := by
    rw [Ideal.mem_span_singleton']
    refine ⟨aeval θ Cpoly + aeval θ D * aeval θ V, ?_⟩
    have h : aeval θ Cpoly * α - (θ - 13) = -(23 : 𝓞 K11) * aeval θ D := by
      have h' := congrArg (aeval θ) hlinear
      simp only [map_sub, map_mul, map_add, hphi_eval, mul_zero,
        hA_eval, hQ_eval, aeval_C] at h'
      norm_num at h' ⊢
      exact h'
    calc
      (aeval θ Cpoly + aeval θ D * aeval θ V) * α =
          aeval θ Cpoly * α + aeval θ D * (aeval θ V * α) := by ring
      _ = aeval θ Cpoly * α + aeval θ D * 23 := by rw [hValpha]
      _ = θ - 13 := by linear_combination h
  have halpha_pair : α ∈ span ({(23 : 𝓞 K11), θ - 13} : Set (𝓞 K11)) := by
    rw [Ideal.mem_span_pair]
    refine ⟨95, aeval θ B, ?_⟩
    have h : α = (θ - 13) * aeval θ B + (23 * 95 : 𝓞 K11) := by
      have h' := congrArg (aeval θ) halpha
      simp only [map_add, map_mul, hA_eval, hQ_eval, aeval_C] at h'
      norm_num at h' ⊢
      exact h'
    rw [h]
    ring
  let Psub := (primesOverSpanEquivMonicFactorsMod hnotdvd).symm
    ⟨Q.map (Int.castRingHom (ZMod 23)), hQ⟩
  let P : Ideal (𝓞 K11) := Psub
  have hPspan : P = span ({(23 : 𝓞 K11), θ - 13} : Set (𝓞 K11)) := by
      rw [show P = (Psub : Ideal (𝓞 K11)) by rfl]
      rw [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hnotdvd hQ]
      simp [hQ_eval]
  have hP_eq : P = span ({α} : Set (𝓞 K11)) := by
    rw [hPspan]
    apply le_antisymm
    · rw [span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact h23_span
      · exact hlinear_span
    · rw [span_singleton_le_iff_mem]
      exact halpha_pair
  have hPprincipal : Submodule.IsPrincipal P := by
    rw [hP_eq]
    exact ⟨α, rfl⟩
  have hdiscr : NumberField.discr K11 = -2357947691 := by
    simpa using
      (@IsCyclotomicExtension.Rat.discr_prime 11 K11 inferInstance inferInstance
        inferInstance hcyclo)
  have hfinrank : Module.finrank ℚ K11 = 10 := by
    rw [IsCyclotomicExtension.finrank (n := 11) K11
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    rw [Nat.totient_prime (by norm_num)]
  have hfinrank_numberField :
      @Module.finrank ℚ K11 inferInstance inferInstance
        (@Algebra.toModule ℚ K11 inferInstance inferInstance
          (@DivisionRing.toRatAlgebra K11 inferInstance inferInstance)) = 10 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ K11) =
          @DivisionRing.toRatAlgebra K11 inferInstance inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K11 = 5 := by
    simpa using
      (@IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 11 inferInstance
        K11 inferInstance inferInstance hcyclo)
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K11 *
        (Nat.factorial
            (@Module.finrank ℚ K11 inferInstance inferInstance
              (@Algebra.toModule ℚ K11 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K11 inferInstance inferInstance))) /
          (@Module.finrank ℚ K11 inferInstance inferInstance
              (@Algebra.toModule ℚ K11 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K11 inferInstance inferInstance))) ^
            (@Module.finrank ℚ K11 inferInstance inferInstance
              (@Algebra.toModule ℚ K11 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K11 inferInstance inferInstance))) *
          √|NumberField.discr K11|)⌋₊ = 58 := by
    rw [hcomplex, hfinrank_numberField, hdiscr]
    norm_num
    have hsqrtDiscr : √(2357947691 : ℝ) = 14641 * √11 := by
      calc
        √(2357947691 : ℝ) = √((214358881 : ℝ) * 11) := by norm_num
        _ = √(214358881 : ℝ) * √11 := by
          rw [Real.sqrt_mul (by norm_num)]
        _ = 14641 * √11 := by norm_num
    rw [hsqrtDiscr]
    rw [show (4 / Real.pi) ^ 5 * (567 / 1562500 * (14641 * √11)) =
      8500681728 * √11 / (1562500 * Real.pi ^ 5) by ring]
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ (by positivity)]
      have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
      have hpi5 : Real.pi ^ 5 < (3.1416 : ℝ) ^ 5 := by gcongr
      have hsqrt : (3.316 : ℝ) < √11 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      norm_num at hpi5 hsqrt ⊢
      nlinarith
    · rw [div_lt_iff₀ (by positivity)]
      have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
      have hpi5 : (3.1415 : ℝ) ^ 5 < Real.pi ^ 5 := by gcongr
      have hsqrt : √(11 : ℝ) < 3.317 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      norm_num at hpi5 hsqrt ⊢
      nlinarith
  have horderTwo : orderOf (2 : ZMod 11) = 10 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderThree : orderOf (3 : ZMod 11) = 5 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderFour : orderOf (4 : ZMod 11) = 5 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderFive : orderOf (5 : ZMod 11) = 5 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderSix : orderOf (6 : ZMod 11) = 10 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderSeven : orderOf (7 : ZMod 11) = 10 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderEight : orderOf (8 : ZMod 11) = 10 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderNine : orderOf (9 : ZMod 11) = 5 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderTen : orderOf (10 : ZMod 11) = 2 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have hlarge (p : ℕ) (hp_le : p ≤ 58) (hpprime : p.Prime)
      (hp_ne_eleven : p ≠ 11) (hp_ne_twentythree : p ≠ 23) :
      58 < p ^ orderOf (p : ZMod 11) := by
    rw [← ZMod.natCast_mod p 11]
    interval_cases p <;> norm_num [Nat.prime_def] at hpprime
    all_goals first | omega | norm_num [horderTwo, horderThree, horderFour,
      horderFive, horderSix, horderSeven, horderEight, horderNine, horderTen]
  rw [Towers.NumberTheory.CNOne.CyclotomicClassNumber,
    NumberField.classNumber_eq_one_iff]
  letI hGalois : IsGalois ℚ K11 :=
    IsCyclotomicExtension.isGalois {11} ℚ K11
  apply @isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    K11 inferInstance inferInstance hGalois
  rw [hfloor]
  intro p hp hpprime
  have hp_le : p ≤ 58 := (Finset.mem_Icc.mp hp).2
  by_cases hp_eleven : p = 11
  · subst p
    letI : (Ideal.span ({(11 : ℤ)} : Set ℤ)).IsPrime :=
      isPrime_of_prime
        (prime_span_singleton_iff.mpr
          (Nat.prime_iff_prime_int.mp (by norm_num)))
    obtain ⟨⟨P11, hP11prime, hP11over⟩⟩ :=
      (Ideal.span ({(11 : ℤ)} : Set ℤ)).nonempty_primesOver (S := 𝓞 K11)
    refine ⟨P11, ⟨hP11prime, hP11over⟩, Or.inr ?_⟩
    letI : P11.IsPrime := hP11prime
    letI : P11.LiesOver (Ideal.span ({(11 : ℤ)} : Set ℤ)) := hP11over
    rw [@IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' 11
      inferInstance K11 inferInstance inferInstance hcyclo _ hζ P11 inferInstance
        inferInstance]
    exact ⟨hζ.toInteger - 1, rfl⟩
  by_cases hp_twentythree : p = 23
  · subst p
    refine ⟨P, ?_, Or.inr hPprincipal⟩
    simp [P]
  · letI : Fact p.Prime := ⟨hpprime⟩
    letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
      isPrime_of_prime
        (prime_span_singleton_iff.mpr
          (Nat.prime_iff_prime_int.mp hpprime))
    obtain ⟨⟨P0, hP0prime, hP0over⟩⟩ :=
      (Ideal.span ({(p : ℤ)} : Set ℤ)).nonempty_primesOver (S := 𝓞 K11)
    refine ⟨P0, ⟨hP0prime, hP0over⟩, Or.inl ?_⟩
    letI : P0.IsPrime := hP0prime
    letI : P0.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hP0over
    rw [@IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 11 p inferInstance
      K11 inferInstance inferInstance P0 inferInstance inferInstance inferInstance hcyclo
        (by
          intro hdiv
          exact hp_eleven
            ((Nat.prime_dvd_prime_iff_eq hpprime (by norm_num)).mp hdiv))]
    exact hlarge p hp_le hpprime hp_eleven hp_twentythree

/-- The conductor `12` positive case of Theorem 72. -/
theorem cyclotomic_twelve_number :
    CyclotomicClassNumber 12 := by
  letI : NeZero (12 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (12 : ℚ) := ⟨by norm_num⟩
  let hcyclo : IsCyclotomicExtension {12} ℚ (CyclotomicField 12 ℚ) :=
    CyclotomicField.isCyclotomicExtension 12 ℚ
  letI : IsCyclotomicExtension {12} ℚ (CyclotomicField 12 ℚ) := hcyclo
  have hdiscr : NumberField.discr (CyclotomicField 12 ℚ) = 144 := by
    rw [@IsCyclotomicExtension.Rat.discr 12 (CyclotomicField 12 ℚ)
      inferInstance inferInstance inferInstance hcyclo]
    have hprimeFactors : (12 : ℕ).primeFactors = {2, 3} := by
      ext p
      simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hpdvd, -⟩
        have hpdvd' : p ∣ 3 * 4 := by simpa using hpdvd
        rcases hp.dvd_mul.mp hpdvd' with hp3 | hp4
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3)
        · have hp4' : p ∣ 2 * 2 := by simpa using hp4
          rcases hp.dvd_mul.mp hp4' with hp2 | hp2
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)
      · rintro (rfl | rfl)
        · exact ⟨Nat.prime_two, by norm_num, by norm_num⟩
        · exact ⟨Nat.prime_three, by norm_num, by norm_num⟩
    rw [hprimeFactors, show (12 : ℕ).totient = 4 by decide]
    norm_num
  have hfinrank : Module.finrank ℚ (CyclotomicField 12 ℚ) = 4 := by
    rw [IsCyclotomicExtension.finrank (n := 12) (CyclotomicField 12 ℚ)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  have hfinrank_numberField :
      @Module.finrank ℚ (CyclotomicField 12 ℚ) inferInstance inferInstance
        (@Algebra.toModule ℚ (CyclotomicField 12 ℚ) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (CyclotomicField 12 ℚ) inferInstance
            inferInstance)) = 4 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (CyclotomicField 12 ℚ)) =
          @DivisionRing.toRatAlgebra (CyclotomicField 12 ℚ) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces
      (CyclotomicField 12 ℚ) = 2 := by
    simpa using
      (@IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 12 inferInstance
        (CyclotomicField 12 ℚ) inferInstance inferInstance hcyclo)
  rw [CyclotomicClassNumber, NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [hdiscr, hfinrank_numberField, hcomplex]
  norm_num
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  nlinarith [sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 3.14) Real.pi_pos.le |>.2 hpi]


private theorem principal_prime_certificates
    {K : Type*} [Field K] [NumberField K]
    (q : ℕ) [NeZero q] [Fact q.Prime]
    (θ : 𝓞 K) (hexponent : exponent θ = 1)
    (Q A U V Cpoly F D B E : ℤ[X])
    (hQ : Q.map (Int.castRingHom (ZMod q)) ∈ monicFactorsMod θ q)
    (hbezout : U * minpoly ℤ θ + V * A = C (q : ℤ))
    (hlinear : Cpoly * A - Q = F * minpoly ℤ θ + C (q : ℤ) * D)
    (halpha : A = Q * B + C (q : ℤ) * E) :
    ∃ P ∈ primesOver (span ({(q : ℤ)} : Set ℤ)) (𝓞 K),
      Submodule.IsPrincipal P := by
  have hnotdvd : ¬q ∣ exponent θ := by
    rw [hexponent]
    exact (Fact.out : q.Prime).not_dvd_one
  let α : 𝓞 K := aeval θ A
  have hminpoly_eval : aeval θ (minpoly ℤ θ) = 0 := minpoly.aeval ℤ θ
  have hValpha : aeval θ V * α = q := by
    have h := congrArg (aeval θ) hbezout
    simp only [map_add, map_mul, hminpoly_eval, mul_zero, zero_add, aeval_C] at h
    simpa using h
  have hq_span : (q : 𝓞 K) ∈ span ({α} : Set (𝓞 K)) := by
    rw [Ideal.mem_span_singleton']
    exact ⟨aeval θ V, hValpha⟩
  have hQ_span : aeval θ Q ∈ span ({α} : Set (𝓞 K)) := by
    rw [Ideal.mem_span_singleton']
    refine ⟨aeval θ Cpoly - aeval θ D * aeval θ V, ?_⟩
    have h : aeval θ Cpoly * α - aeval θ Q = q * aeval θ D := by
      have h' := congrArg (aeval θ) hlinear
      simp only [map_sub, map_add, map_mul, hminpoly_eval, mul_zero, aeval_C,
        zero_add] at h'
      simpa [mul_comm] using h'
    calc
      (aeval θ Cpoly - aeval θ D * aeval θ V) * α =
          aeval θ Cpoly * α - aeval θ D * (aeval θ V * α) := by ring
      _ = aeval θ Cpoly * α - aeval θ D * q := by rw [hValpha]
      _ = aeval θ Q := by rw [mul_comm (aeval θ D) q]; linear_combination h
  have halpha_pair : α ∈
      span ({(q : 𝓞 K), aeval θ Q} : Set (𝓞 K)) := by
    rw [Ideal.mem_span_pair]
    refine ⟨aeval θ E, aeval θ B, ?_⟩
    have h : α = aeval θ Q * aeval θ B + q * aeval θ E := by
      have h' := congrArg (aeval θ) halpha
      simp only [map_add, map_mul, aeval_C] at h'
      have hcast : algebraMap ℤ (𝓞 K) (q : ℤ) = (q : 𝓞 K) := by norm_num
      simpa [α, hcast] using h'
    rw [h]
    ring
  let Psub := (primesOverSpanEquivMonicFactorsMod hnotdvd).symm
    ⟨Q.map (Int.castRingHom (ZMod q)), hQ⟩
  let P : Ideal (𝓞 K) := Psub
  have hPspan : P = span ({(q : 𝓞 K), aeval θ Q} : Set (𝓞 K)) := by
    rw [show P = (Psub : Ideal (𝓞 K)) by rfl]
    exact primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hnotdvd hQ
  have hP_eq : P = span ({α} : Set (𝓞 K)) := by
    rw [hPspan]
    apply le_antisymm
    · rw [span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hq_span
      · exact hQ_span
    · rw [span_singleton_le_iff_mem]
      exact halpha_pair
  refine ⟨P, Psub.prop, ?_⟩
  rw [hP_eq]
  exact ⟨α, rfl⟩

abbrev K13 := CyclotomicField 13 ℚ

set_option maxHeartbeats 800000 in
-- The explicit polynomial certificates and finite prime enumeration need extra elaboration.
/-- The conductor `13` positive case of Theorem 72. -/
theorem cyclotomic_thirteen_number :
    CyclotomicClassNumber 13 := by
  letI : NeZero (13 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (13 : ℚ) := ⟨by norm_num⟩
  letI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (53 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (79 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (131 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (157 : ℕ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 79) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 131) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  letI hcyclo : IsCyclotomicExtension {13} ℚ K13 :=
    CyclotomicField.isCyclotomicExtension 13 ℚ
  let hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 13 ℚ K13) 13 :=
    IsCyclotomicExtension.zeta_spec 13 ℚ K13
  let θ : 𝓞 K13 := hζ.toInteger
  have hexponent : exponent θ = 1 := by
    apply exponent_eq_one_iff.mpr
    exact @IsCyclotomicExtension.Rat.adjoin_singleton_eq_top 13 K13 inferInstance
      inferInstance inferInstance hcyclo _ hζ
  have hminpoly : minpoly ℤ θ = cyclotomic 13 ℤ := by
    calc
      minpoly ℤ θ = minpoly ℤ (θ : K13) := (RingOfIntegers.minpoly_coe θ).symm
      _ = minpoly ℤ (IsCyclotomicExtension.zeta 13 ℚ K13) := by simp [θ]
      _ = cyclotomic 13 ℤ :=
        (cyclotomic_eq_minpoly hζ (by norm_num)).symm
  let A : ℤ[X] := X ^ 4 + X ^ 3 - X ^ 2 - 2 * X - 1
  let Q : ℤ[X] := X ^ 3 - X - 1
  let U : ℤ[X] := 4 * X ^ 3 - 7 * X
  let V : ℤ[X] :=
    -4 * X ^ 11 - X ^ 9 - 4 * X ^ 8 + 2 * X ^ 7 - 5 * X ^ 6 + X ^ 5 -
      3 * X ^ 4 - X ^ 3 - 2 * X ^ 2 - X - 3
  let Cpoly : ℤ[X] := X ^ 8 - X ^ 6 + X ^ 5 - X ^ 2
  let F : ℤ[X] := 1
  let D : ℤ[X] := -X ^ 10 - X ^ 9 - X ^ 6 - X ^ 5
  let B : ℤ[X] := X + 1
  let E : ℤ[X] := 0
  have hQ : Q.map (Int.castRingHom (ZMod 3)) ∈ monicFactorsMod θ 3 := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
      (map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    constructor
    · norm_num [Q]
      apply irreducible_of_degree_le_three_of_not_isRoot
      · rw [Finset.mem_Icc]
        have hd : (X ^ 3 - X - 1 : (ZMod 3)[X]).natDegree = 3 := by
          compute_degree
          norm_num
        omega
      · intro x
        fin_cases x <;> norm_num [IsRoot, eval_sub, eval_add, eval_pow] <;> decide
    · constructor
      · norm_num [Q]
        rw [show (X ^ 3 - X - 1 : (ZMod 3)[X]) = X ^ 3 + (-X - 1) by ring]
        apply monic_X_pow_add
        compute_degree
        norm_num
      · let R : ℤ[X] := X ^ 9 + X ^ 8 - X ^ 7 + X ^ 5 - X ^ 3 - X ^ 2 - 1
        have hfactor : Q * R = cyclotomic 13 ℤ + C 3 * D := by
          norm_num [Q, R, D, cyclotomic_prime, Finset.sum_range_succ]
          ring
        refine ⟨R.map (Int.castRingHom (ZMod 3)), ?_⟩
        rw [hminpoly, map_cyclotomic_int]
        have h := congrArg (Polynomial.map (Int.castRingHom (ZMod 3))) hfactor
        simp only [Polynomial.map_mul, Polynomial.map_add, map_cyclotomic_int,
          map_C] at h
        have hthree : (Int.castRingHom (ZMod 3)) 3 = 0 := by
          change (3 : ZMod 3) = 0
          exact ZMod.natCast_self 3
        simp [hthree] at h
        exact h.symm
  have hbezout : U * minpoly ℤ θ + V * A = C 3 := by
    rw [hminpoly]
    norm_num [U, V, A, cyclotomic_prime, Finset.sum_range_succ]
    ring
  have hlinear : Cpoly * A - Q = F * minpoly ℤ θ + C 3 * D := by
    rw [hminpoly]
    norm_num [Cpoly, A, Q, F, D, cyclotomic_prime, Finset.sum_range_succ]
    ring
  have halpha : A = Q * B + C 3 * E := by
    simp [A, Q, B, E]
    ring
  obtain ⟨P3, hP3, hprincipal3⟩ :=
    principal_prime_certificates 3 θ hexponent
      Q A U V Cpoly F D B E hQ hbezout hlinear halpha
  let A53 : ℤ[X] := -X ^ 5 - X ^ 2 - X - 2
  let Q53 : ℤ[X] := X - C 13
  let U53 : ℤ[X] := 24 * X ^ 4 + 153 * X ^ 3 - 131 * X ^ 2 - 36 * X + 351
  let V53 : ℤ[X] :=
    24 * X ^ 11 + 177 * X ^ 10 + 46 * X ^ 9 - 14 * X ^ 8 + 160 * X ^ 7 +
      90 * X ^ 6 - 25 * X ^ 5 + 123 * X ^ 4 + 139 * X ^ 3 - 24 * X ^ 2 +
      83 * X + 149
  let C53 : ℤ[X] :=
    -X ^ 10 + 7 * X ^ 9 - 9 * X ^ 8 - 18 * X ^ 7 - 25 * X ^ 6 - 15 * X ^ 5 -
      6 * X ^ 4 - 11 * X ^ 3 + 4 * X ^ 2 - X - 25
  let F53 : ℤ[X] := X ^ 3 - 8 * X ^ 2 + 16 * X + 10
  let D53 : ℤ[X] := X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + 1
  let B53 : ℤ[X] :=
    -X ^ 4 - 13 * X ^ 3 - 169 * X ^ 2 - 2198 * X - 28575
  let E53 : ℤ[X] := -7009
  have hQ53 : Q53.map (Int.castRingHom (ZMod 53)) ∈ monicFactorsMod θ 53 := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
      (map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    constructor
    · simpa [Q53] using irreducible_X_sub_C (13 : ZMod 53)
    · constructor
      · simpa [Q53] using monic_X_sub_C (13 : ZMod 53)
      · have hroot : IsRoot
            (map (Int.castRingHom (ZMod 53)) (minpoly ℤ θ))
            (13 : ZMod 53) := by
          change eval (13 : ZMod 53)
            (map (Int.castRingHom (ZMod 53)) (minpoly ℤ θ)) = 0
          rw [hminpoly, map_cyclotomic_int]
          norm_num [eval_map, cyclotomic_prime]
          decide
        simpa [Q53] using (dvd_iff_isRoot.mpr hroot)
  have hbezout53 : U53 * minpoly ℤ θ + V53 * A53 = C 53 := by
    rw [hminpoly]
    norm_num [U53, V53, A53, cyclotomic_prime, Finset.sum_range_succ]
    ring
  have hlinear53 : C53 * A53 - Q53 = F53 * minpoly ℤ θ + C 53 * D53 := by
    rw [hminpoly]
    norm_num [C53, A53, Q53, F53, D53, cyclotomic_prime,
      Finset.sum_range_succ]
    ring
  have halpha53 : A53 = Q53 * B53 + C 53 * E53 := by
    simp [A53, Q53, B53, E53]
    ring
  obtain ⟨P53, hP53, hprincipal53⟩ :=
    principal_prime_certificates 53 θ hexponent
      Q53 A53 U53 V53 C53 F53 D53 B53 E53 hQ53 hbezout53 hlinear53 halpha53
  let A79 : ℤ[X] := X ^ 7 - X ^ 3 - X ^ 2 - 2 * X - 1
  let Q79 : ℤ[X] := X - C 22
  let U79 : ℤ[X] :=
    53 * X ^ 6 - 98 * X ^ 5 - 23 * X ^ 4 + 126 * X ^ 3 - 125 * X ^ 2 -
      38 * X + 164
  let V79 : ℤ[X] :=
    -53 * X ^ 11 + 45 * X ^ 10 + 68 * X ^ 9 - 58 * X ^ 8 + 14 * X ^ 7 +
      97 * X ^ 6 - 52 * X ^ 5 - 12 * X ^ 4 + 78 * X ^ 3 + 4 * X ^ 2 -
      44 * X + 85
  let C79 : ℤ[X] :=
    16 * X ^ 10 + 6 * X ^ 9 - 2 * X ^ 8 + 38 * X ^ 7 - 32 * X ^ 6 -
      32 * X ^ 5 - 18 * X ^ 4 + 10 * X ^ 3 + 33 * X ^ 2 + 35 * X + 28
  let F79 : ℤ[X] :=
    16 * X ^ 5 - 10 * X ^ 4 - 8 * X ^ 3 - 39 * X ^ 2 - 7 * X - 6
  let D79 : ℤ[X] :=
    X ^ 14 + X ^ 9 + X ^ 8 + 2 * X ^ 7 + 2 * X ^ 6 + X ^ 5 - X ^ 3 -
      X ^ 2 - X
  let B79 : ℤ[X] :=
    X ^ 6 + 22 * X ^ 5 + 484 * X ^ 4 + 10648 * X ^ 3 + 234255 * X ^ 2 +
      5153609 * X + 113379396
  let E79 : ℤ[X] := 31574009
  have hQ79 : Q79.map (Int.castRingHom (ZMod 79)) ∈ monicFactorsMod θ 79 := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
      (map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    constructor
    · simpa [Q79] using irreducible_X_sub_C (22 : ZMod 79)
    · constructor
      · simpa [Q79] using monic_X_sub_C (22 : ZMod 79)
      · have hroot : IsRoot
            (map (Int.castRingHom (ZMod 79)) (minpoly ℤ θ))
            (22 : ZMod 79) := by
          change eval (22 : ZMod 79)
            (map (Int.castRingHom (ZMod 79)) (minpoly ℤ θ)) = 0
          rw [hminpoly, map_cyclotomic_int]
          norm_num [eval_map, cyclotomic_prime]
          decide
        simpa [Q79] using (dvd_iff_isRoot.mpr hroot)
  have hbezout79 : U79 * minpoly ℤ θ + V79 * A79 = C 79 := by
    rw [hminpoly]
    norm_num [U79, V79, A79, cyclotomic_prime, Finset.sum_range_succ]
    ring
  have hlinear79 : C79 * A79 - Q79 = F79 * minpoly ℤ θ + C 79 * D79 := by
    rw [hminpoly]
    norm_num [C79, A79, Q79, F79, D79, cyclotomic_prime,
      Finset.sum_range_succ]
    ring
  have halpha79 : A79 = Q79 * B79 + C 79 * E79 := by
    simp [A79, Q79, B79, E79]
    ring
  obtain ⟨P79, hP79, hprincipal79⟩ :=
    principal_prime_certificates 79 θ hexponent
      Q79 A79 U79 V79 C79 F79 D79 B79 E79 hQ79 hbezout79 hlinear79 halpha79
  let A131 : ℤ[X] := X ^ 5 - 2 * X ^ 2 - X - 1
  let Q131 : ℤ[X] := X - C (-18)
  let U131 : ℤ[X] :=
    152 * X ^ 4 + 15 * X ^ 3 - 139 * X ^ 2 - 291 * X - 23
  let V131 : ℤ[X] :=
    -152 * X ^ 11 - 167 * X ^ 10 - 28 * X ^ 9 - 41 * X ^ 8 - 200 * X ^ 7 -
      89 * X ^ 6 + 9 * X ^ 5 - 183 * X ^ 4 - 133 * X ^ 3 + 15 * X ^ 2 -
      160 * X - 154
  let C131 : ℤ[X] :=
    14 * X ^ 10 + 25 * X ^ 9 + 35 * X ^ 8 + 42 * X ^ 7 - 53 * X ^ 6 -
      8 * X ^ 5 + 27 * X ^ 4 - 15 * X ^ 3 - 13 * X ^ 2 + 7 * X + 3
  let F131 : ℤ[X] := 14 * X ^ 3 + 11 * X ^ 2 + 10 * X - 21
  let D131 : ℤ[X] := -X ^ 11 - X ^ 10 - X ^ 9
  let B131 : ℤ[X] :=
    X ^ 4 - 18 * X ^ 3 + 324 * X ^ 2 - 5834 * X + 105011
  let E131 : ℤ[X] := -14429
  have hQ131 : Q131.map (Int.castRingHom (ZMod 131)) ∈ monicFactorsMod θ 131 := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
      (map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    constructor
    · simpa [Q131] using irreducible_X_sub_C (-18 : ZMod 131)
    · constructor
      · simpa [Q131] using monic_X_sub_C (-18 : ZMod 131)
      · have hroot : IsRoot
            (map (Int.castRingHom (ZMod 131)) (minpoly ℤ θ))
            (-18 : ZMod 131) := by
          change eval (-18 : ZMod 131)
            (map (Int.castRingHom (ZMod 131)) (minpoly ℤ θ)) = 0
          rw [hminpoly, map_cyclotomic_int]
          norm_num [eval_map, cyclotomic_prime]
          decide
        simpa [Q131] using (dvd_iff_isRoot.mpr hroot)
  have hbezout131 : U131 * minpoly ℤ θ + V131 * A131 = C 131 := by
    rw [hminpoly]
    norm_num [U131, V131, A131, cyclotomic_prime, Finset.sum_range_succ]
    ring
  have hlinear131 :
      C131 * A131 - Q131 = F131 * minpoly ℤ θ + C 131 * D131 := by
    rw [hminpoly]
    norm_num [C131, A131, Q131, F131, D131, cyclotomic_prime,
      Finset.sum_range_succ]
    ring
  have halpha131 : A131 = Q131 * B131 + C 131 * E131 := by
    simp [A131, Q131, B131, E131]
    ring
  obtain ⟨P131, hP131, hprincipal131⟩ :=
    principal_prime_certificates 131 θ hexponent
      Q131 A131 U131 V131 C131 F131 D131 B131 E131 hQ131 hbezout131
        hlinear131 halpha131
  let A157 : ℤ[X] := -X ^ 6 - X ^ 2 + X - 2
  let Q157 : ℤ[X] := X - C 14
  let U157 : ℤ[X] :=
    58 * X ^ 5 - 130 * X ^ 4 - 93 * X ^ 3 + 111 * X ^ 2 + 199 * X - 255
  let V157 : ℤ[X] :=
    58 * X ^ 11 - 72 * X ^ 10 - 165 * X ^ 9 - 54 * X ^ 8 + 87 * X ^ 7 +
      20 * X ^ 6 - 133 * X ^ 5 - 77 * X ^ 4 + 79 * X ^ 3 + 65 * X ^ 2 -
      131 * X - 206
  let C157 : ℤ[X] :=
    -62 * X ^ 10 + 24 * X ^ 9 - 6 * X ^ 8 + X ^ 7 - 28 * X ^ 6 -
      19 * X ^ 5 + 64 * X ^ 4 + 12 * X ^ 3 - 49 * X ^ 2 + 56 * X + 40
  let F157 : ℤ[X] :=
    62 * X ^ 4 + 71 * X ^ 3 + 30 * X ^ 2 - 7 * X - 66
  let D157 : ℤ[X] :=
    -X ^ 15 - X ^ 14 - X ^ 13 - X ^ 11 - X ^ 9 - X ^ 7 - X ^ 6 - X ^ 4 -
      X ^ 3 + X ^ 2
  let B157 : ℤ[X] :=
    -X ^ 5 - 14 * X ^ 4 - 196 * X ^ 3 - 2744 * X ^ 2 - 38417 * X - 537837
  let E157 : ℤ[X] := -47960
  have hQ157 : Q157.map (Int.castRingHom (ZMod 157)) ∈ monicFactorsMod θ 157 := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
      (map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    constructor
    · simpa [Q157] using irreducible_X_sub_C (14 : ZMod 157)
    · constructor
      · simpa [Q157] using monic_X_sub_C (14 : ZMod 157)
      · have hroot : IsRoot
            (map (Int.castRingHom (ZMod 157)) (minpoly ℤ θ))
            (14 : ZMod 157) := by
          change eval (14 : ZMod 157)
            (map (Int.castRingHom (ZMod 157)) (minpoly ℤ θ)) = 0
          rw [hminpoly, map_cyclotomic_int]
          norm_num [eval_map, cyclotomic_prime]
          decide
        simpa [Q157] using (dvd_iff_isRoot.mpr hroot)
  have hbezout157 : U157 * minpoly ℤ θ + V157 * A157 = C 157 := by
    rw [hminpoly]
    norm_num [U157, V157, A157, cyclotomic_prime, Finset.sum_range_succ]
    ring
  have hlinear157 :
      C157 * A157 - Q157 = F157 * minpoly ℤ θ + C 157 * D157 := by
    rw [hminpoly]
    norm_num [C157, A157, Q157, F157, D157, cyclotomic_prime,
      Finset.sum_range_succ]
    ring
  have halpha157 : A157 = Q157 * B157 + C 157 * E157 := by
    simp [A157, Q157, B157, E157]
    ring
  obtain ⟨P157, hP157, hprincipal157⟩ :=
    principal_prime_certificates 157 θ hexponent
      Q157 A157 U157 V157 C157 F157 D157 B157 E157 hQ157 hbezout157
        hlinear157 halpha157
  have hdiscr : NumberField.discr K13 = 1792160394037 := by
    simpa using
      (@IsCyclotomicExtension.Rat.discr_prime 13 K13 inferInstance inferInstance
        inferInstance hcyclo)
  have hfinrank : Module.finrank ℚ K13 = 12 := by
    rw [IsCyclotomicExtension.finrank (n := 13) K13
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    rw [Nat.totient_prime (by norm_num)]
  have hfinrank_numberField :
      @Module.finrank ℚ K13 inferInstance inferInstance
        (@Algebra.toModule ℚ K13 inferInstance inferInstance
          (@DivisionRing.toRatAlgebra K13 inferInstance inferInstance)) = 12 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ K13) =
          @DivisionRing.toRatAlgebra K13 inferInstance inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K13 = 6 := by
    simpa using
      (@IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 13 inferInstance
        K13 inferInstance inferInstance hcyclo)
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K13 *
        (Nat.factorial
            (@Module.finrank ℚ K13 inferInstance inferInstance
              (@Algebra.toModule ℚ K13 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K13 inferInstance inferInstance))) /
          (@Module.finrank ℚ K13 inferInstance inferInstance
              (@Algebra.toModule ℚ K13 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K13 inferInstance inferInstance))) ^
            (@Module.finrank ℚ K13 inferInstance inferInstance
              (@Algebra.toModule ℚ K13 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K13 inferInstance inferInstance))) *
          √|NumberField.discr K13|)⌋₊ = 306 := by
    rw [hcomplex, hfinrank_numberField, hdiscr]
    norm_num
    have hsqrtDiscr : √(1792160394037 : ℝ) = 371293 * √13 := by
      calc
        √(1792160394037 : ℝ) = √((137858491849 : ℝ) * 13) := by norm_num
        _ = √(137858491849 : ℝ) * √13 := by
          rw [Real.sqrt_mul (by norm_num)]
        _ = 371293 * √13 := by norm_num
    rw [hsqrtDiscr]
    rw [show (4 / Real.pi) ^ 6 * (1925 / 35831808 * (371293 * √13)) =
      714739025 * √13 / (8748 * Real.pi ^ 6) by ring]
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ (by positivity)]
      have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
      have hpi6 : Real.pi ^ 6 < (3.1416 : ℝ) ^ 6 := by gcongr
      have hsqrt : (3.6055 : ℝ) < √13 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      norm_num at hpi6 hsqrt ⊢
      nlinarith
    · rw [div_lt_iff₀ (by positivity)]
      have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
      have hpi6 : (3.1415 : ℝ) ^ 6 < Real.pi ^ 6 := by gcongr
      have hsqrt : √(13 : ℝ) < 3.6056 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      norm_num at hpi6 hsqrt ⊢
      nlinarith
  have horderTwo : orderOf (2 : ZMod 13) = 12 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderThree : orderOf (3 : ZMod 13) = 3 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderFour : orderOf (4 : ZMod 13) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderFive : orderOf (5 : ZMod 13) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderSix : orderOf (6 : ZMod 13) = 12 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderSeven : orderOf (7 : ZMod 13) = 12 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderEight : orderOf (8 : ZMod 13) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderNine : orderOf (9 : ZMod 13) = 3 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderTen : orderOf (10 : ZMod 13) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderEleven : orderOf (11 : ZMod 13) = 12 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderTwelve : orderOf (12 : ZMod 13) = 2 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have hlarge (p : ℕ) (hp_le : p ≤ 306) (hpprime : p.Prime)
      (hp_ne_three : p ≠ 3) (hp_ne_thirteen : p ≠ 13)
      (hp_ne_fiftythree : p ≠ 53) (hp_ne_seventynine : p ≠ 79)
      (hp_ne_onethirtyone : p ≠ 131) (hp_ne_onefiftyseven : p ≠ 157) :
      306 < p ^ orderOf (p : ZMod 13) := by
    rw [← ZMod.natCast_mod p 13]
    interval_cases p <;> norm_num [Nat.prime_def] at hpprime
    all_goals first | omega | norm_num [horderTwo, horderThree, horderFour,
      horderFive, horderSix, horderSeven, horderEight, horderNine, horderTen,
      horderEleven, horderTwelve]
  rw [CyclotomicClassNumber,
    NumberField.classNumber_eq_one_iff]
  letI hGalois : IsGalois ℚ K13 :=
    IsCyclotomicExtension.isGalois {13} ℚ K13
  apply @isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    K13 inferInstance inferInstance hGalois
  rw [hfloor]
  intro p hp hpprime
  have hp_le : p ≤ 306 := (Finset.mem_Icc.mp hp).2
  by_cases hp_three : p = 3
  · subst p
    exact ⟨P3, hP3, Or.inr hprincipal3⟩
  by_cases hp_thirteen : p = 13
  · subst p
    letI : (Ideal.span ({(13 : ℤ)} : Set ℤ)).IsPrime :=
      isPrime_of_prime
        (prime_span_singleton_iff.mpr
          (Nat.prime_iff_prime_int.mp (by norm_num)))
    obtain ⟨⟨P13, hP13prime, hP13over⟩⟩ :=
      (Ideal.span ({(13 : ℤ)} : Set ℤ)).nonempty_primesOver (S := 𝓞 K13)
    refine ⟨P13, ⟨hP13prime, hP13over⟩, Or.inr ?_⟩
    letI : P13.IsPrime := hP13prime
    letI : P13.LiesOver (Ideal.span ({(13 : ℤ)} : Set ℤ)) := hP13over
    rw [@IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' 13
      inferInstance K13 inferInstance inferInstance hcyclo _ hζ P13 inferInstance
        inferInstance]
    exact ⟨hζ.toInteger - 1, rfl⟩
  by_cases hp_fiftythree : p = 53
  · subst p
    exact ⟨P53, hP53, Or.inr hprincipal53⟩
  by_cases hp_seventynine : p = 79
  · subst p
    exact ⟨P79, hP79, Or.inr hprincipal79⟩
  by_cases hp_onethirtyone : p = 131
  · subst p
    exact ⟨P131, hP131, Or.inr hprincipal131⟩
  by_cases hp_onefiftyseven : p = 157
  · subst p
    exact ⟨P157, hP157, Or.inr hprincipal157⟩
  · letI : Fact p.Prime := ⟨hpprime⟩
    letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
      isPrime_of_prime
        (prime_span_singleton_iff.mpr
          (Nat.prime_iff_prime_int.mp hpprime))
    obtain ⟨⟨P0, hP0prime, hP0over⟩⟩ :=
      (Ideal.span ({(p : ℤ)} : Set ℤ)).nonempty_primesOver (S := 𝓞 K13)
    refine ⟨P0, ⟨hP0prime, hP0over⟩, Or.inl ?_⟩
    letI : P0.IsPrime := hP0prime
    letI : P0.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hP0over
    rw [@IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 13 p inferInstance
      K13 inferInstance inferInstance P0 inferInstance inferInstance inferInstance hcyclo
        (by
          intro hdiv
          exact hp_thirteen
            ((Nat.prime_dvd_prime_iff_eq hpprime (by norm_num)).mp hdiv))]
    exact hlarge p hp_le hpprime hp_three hp_thirteen hp_fiftythree hp_seventynine
      hp_onethirtyone hp_onefiftyseven

abbrev K15 := CyclotomicField 15 ℚ

set_option maxHeartbeats 400000 in
-- The exact Minkowski floor calculation uses explicit rational bounds for pi.
/-- The conductor `15` positive case of Theorem 72. -/
theorem cyclotomic_fifteen_number :
    CyclotomicClassNumber 15 := by
  letI : NeZero (15 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (15 : ℚ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let hcyclo : IsCyclotomicExtension {15} ℚ K15 :=
    CyclotomicField.isCyclotomicExtension 15 ℚ
  letI : IsCyclotomicExtension {15} ℚ K15 := hcyclo
  have hdiscr : NumberField.discr K15 = 1265625 := by
    rw [@IsCyclotomicExtension.Rat.discr 15 K15 inferInstance inferInstance
      inferInstance hcyclo]
    have hprimeFactors : (15 : ℕ).primeFactors = {3, 5} := by
      ext p
      simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hpdvd, -⟩
        have hpdvd' : p ∣ 3 * 5 := by simpa using hpdvd
        rcases hp.dvd_mul.mp hpdvd' with hp3 | hp5
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp5)
      · rintro (rfl | rfl)
        · exact ⟨Nat.prime_three, by norm_num, by norm_num⟩
        · exact ⟨by norm_num, by norm_num, by norm_num⟩
    rw [hprimeFactors, show (15 : ℕ).totient = 8 by decide]
    norm_num
  have hfinrank : Module.finrank ℚ K15 = 8 := by
    rw [IsCyclotomicExtension.finrank (n := 15) K15
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  have hfinrank_numberField :
      @Module.finrank ℚ K15 inferInstance inferInstance
        (@Algebra.toModule ℚ K15 inferInstance inferInstance
          (@DivisionRing.toRatAlgebra K15 inferInstance inferInstance)) = 8 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ K15) =
          @DivisionRing.toRatAlgebra K15 inferInstance inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K15 = 4 := by
    simpa using
      (@IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 15 inferInstance
        K15 inferInstance inferInstance hcyclo)
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K15 *
        (Nat.factorial
            (@Module.finrank ℚ K15 inferInstance inferInstance
              (@Algebra.toModule ℚ K15 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K15 inferInstance inferInstance))) /
          (@Module.finrank ℚ K15 inferInstance inferInstance
              (@Algebra.toModule ℚ K15 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K15 inferInstance inferInstance))) ^
            (@Module.finrank ℚ K15 inferInstance inferInstance
              (@Algebra.toModule ℚ K15 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K15 inferInstance inferInstance))) *
          √|NumberField.discr K15|)⌋₊ = 7 := by
    rw [hcomplex, hfinrank_numberField, hdiscr]
    norm_num
    rw [show (4 / Real.pi) ^ 4 * (354375 / 131072) =
      354375 / (512 * Real.pi ^ 4) by ring]
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ (by positivity)]
      have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
      have hpi4 : Real.pi ^ 4 < (3.1416 : ℝ) ^ 4 := by gcongr
      norm_num at hpi4 ⊢
      nlinarith
    · rw [div_lt_iff₀ (by positivity)]
      have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
      have hpi4 : (3.1415 : ℝ) ^ 4 < Real.pi ^ 4 := by gcongr
      norm_num at hpi4 ⊢
      nlinarith
  have horderTwo : orderOf (2 : ZMod 15) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderThree : orderOf (3 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderFive : orderOf (5 : ZMod 3) = 2 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderSeven : orderOf (7 : ZMod 15) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  rw [CyclotomicClassNumber,
    NumberField.classNumber_eq_one_iff]
  letI : IsGalois ℚ K15 := IsCyclotomicExtension.isGalois {15} ℚ K15
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  rw [hfloor]
  intro p hp hpprime P hP hpow
  have hp_le : p ≤ 7 := (Finset.mem_Icc.mp hp).2
  have hp_ge : 2 ≤ p := hpprime.two_le
  have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    by_cases hp_two : p = 2
    · exact Or.inl hp_two
    by_cases hp_three : p = 3
    · exact Or.inr (Or.inl hp_three)
    by_cases hp_five : p = 5
    · exact Or.inr (Or.inr (Or.inl hp_five))
    by_cases hp_seven : p = 7
    · exact Or.inr (Or.inr (Or.inr hp_seven))
    have hp_four_or_six : p = 4 ∨ p = 6 := by omega
    rcases hp_four_or_six with rfl | rfl <;> norm_num at hpprime
  rcases hp_cases with rfl | rfl | rfl | rfl
  · letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
    have hinertia : (Ideal.span {(2 : ℤ)}).inertiaDeg P =
        orderOf (2 : ZMod 15) :=
      @IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 15 2 inferInstance
        K15 inferInstance inferInstance P inferInstance inferInstance inferInstance hcyclo
          (by norm_num)
    change 2 ^ (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P ≤ 7 at hpow
    rw [hinertia, horderTwo] at hpow
    norm_num at hpow
  · letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
    have hinertia : (Ideal.span {(3 : ℤ)}).inertiaDeg P =
        orderOf (3 : ZMod 5) :=
      @IsCyclotomicExtension.Rat.inertiaDeg_eq 15 5 3 0 inferInstance K15
        inferInstance inferInstance P inferInstance inferInstance hcyclo
          (by norm_num) (by norm_num)
    change 3 ^ (Ideal.span ({(3 : ℤ)} : Set ℤ)).inertiaDeg P ≤ 7 at hpow
    rw [hinertia, horderThree] at hpow
    norm_num at hpow
  · letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span {(5 : ℤ)}) := hP.2
    have hinertia : (Ideal.span {(5 : ℤ)}).inertiaDeg P =
        orderOf (5 : ZMod 3) :=
      @IsCyclotomicExtension.Rat.inertiaDeg_eq 15 3 5 0 inferInstance K15
        inferInstance inferInstance P inferInstance inferInstance hcyclo
          (by norm_num) (by norm_num)
    change 5 ^ (Ideal.span ({(5 : ℤ)} : Set ℤ)).inertiaDeg P ≤ 7 at hpow
    rw [hinertia, horderFive] at hpow
    norm_num at hpow
  · letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span {(7 : ℤ)}) := hP.2
    have hinertia : (Ideal.span {(7 : ℤ)}).inertiaDeg P =
        orderOf (7 : ZMod 15) :=
      @IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 15 7 inferInstance
        K15 inferInstance inferInstance P inferInstance inferInstance inferInstance hcyclo
          (by norm_num)
    change 7 ^ (Ideal.span ({(7 : ℤ)} : Set ℤ)).inertiaDeg P ≤ 7 at hpow
    rw [hinertia, horderSeven] at hpow
    norm_num at hpow

abbrev K16 := CyclotomicField 16 ℚ

set_option maxHeartbeats 400000 in
-- Explicit Kummer-Dedekind certificates and the Minkowski calculation need extra elaboration.
/-- The conductor `16` positive case of Theorem 72. -/
theorem cyclotomic_sixteen_number :
    CyclotomicClassNumber 16 := by
  letI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (16 : ℚ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI : NeZero (17 : ℕ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  let hcyclo : IsCyclotomicExtension {16} ℚ K16 :=
    CyclotomicField.isCyclotomicExtension 16 ℚ
  letI : IsCyclotomicExtension {16} ℚ K16 := hcyclo
  have hcycloPow : IsCyclotomicExtension {2 ^ (3 + 1)} ℚ K16 := by
    norm_num
    exact hcyclo
  have hphi : cyclotomic 16 ℤ = X ^ 8 + 1 := by
    rw [show 16 = 2 ^ (3 + 1) by norm_num,
      cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    norm_num [Finset.sum_range_succ]
    ring
  let hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 16 ℚ K16) 16 :=
    IsCyclotomicExtension.zeta_spec 16 ℚ K16
  let θ : 𝓞 K16 := hζ.toInteger
  have hexponent : exponent θ = 1 := by
    apply exponent_eq_one_iff.mpr
    exact @IsCyclotomicExtension.Rat.adjoin_singleton_eq_top 16 K16 inferInstance
      inferInstance inferInstance hcyclo _ hζ
  have hminpoly : minpoly ℤ θ = cyclotomic 16 ℤ := by
    calc
      minpoly ℤ θ = minpoly ℤ (θ : K16) := (RingOfIntegers.minpoly_coe θ).symm
      _ = minpoly ℤ (IsCyclotomicExtension.zeta 16 ℚ K16) := by simp [θ]
      _ = cyclotomic 16 ℤ :=
        (cyclotomic_eq_minpoly hζ (by norm_num)).symm
  let A : ℤ[X] := -X ^ 3 - X - 1
  let Q : ℤ[X] := X - C 11
  let U : ℤ[X] := 9 * X ^ 2 - 3 * X + 10
  let V : ℤ[X] :=
    9 * X ^ 7 - 3 * X ^ 6 + X ^ 5 - 6 * X ^ 4 + 2 * X ^ 3 +
      5 * X ^ 2 + 4 * X - 7
  let Cpoly : ℤ[X] := -6 * X ^ 5 + 6 * X ^ 3 + 6 * X ^ 2 - 6 * X + 5
  let F : ℤ[X] := 6
  let D : ℤ[X] := -X ^ 3
  let B : ℤ[X] := -X ^ 2 - 11 * X - 122
  let E : ℤ[X] := -79
  have hQ : Q.map (Int.castRingHom (ZMod 17)) ∈ monicFactorsMod θ 17 := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
      (map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    constructor
    · simpa [Q] using irreducible_X_sub_C (11 : ZMod 17)
    · constructor
      · simpa [Q] using monic_X_sub_C (11 : ZMod 17)
      · have hroot : IsRoot
            (map (Int.castRingHom (ZMod 17)) (minpoly ℤ θ))
            (11 : ZMod 17) := by
          change eval (11 : ZMod 17)
            (map (Int.castRingHom (ZMod 17)) (minpoly ℤ θ)) = 0
          rw [hminpoly, hphi]
          norm_num [eval_map]
          decide
        simpa [Q] using (dvd_iff_isRoot.mpr hroot)
  have hbezout : U * minpoly ℤ θ + V * A = C 17 := by
    rw [hminpoly, hphi]
    norm_num [U, V, A]
    ring
  have hlinear : Cpoly * A - Q = F * minpoly ℤ θ + C 17 * D := by
    rw [hminpoly, hphi]
    norm_num [Cpoly, A, Q, F, D]
    ring
  have halpha : A = Q * B + C 17 * E := by
    norm_num [A, Q, B, E]
    ring
  obtain ⟨P17, hP17, hprincipal17⟩ :=
    principal_prime_certificates 17 θ hexponent
      Q A U V Cpoly F D B E hQ hbezout hlinear halpha
  have hdiscr : NumberField.discr K16 = 16777216 := by
    simpa using
      (@IsCyclotomicExtension.Rat.discr_prime_pow 2 4 K16 inferInstance
        inferInstance inferInstance hcyclo)
  have hfinrank : Module.finrank ℚ K16 = 8 := by
    rw [IsCyclotomicExtension.finrank (n := 16) K16
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  have hfinrank_numberField :
      @Module.finrank ℚ K16 inferInstance inferInstance
        (@Algebra.toModule ℚ K16 inferInstance inferInstance
          (@DivisionRing.toRatAlgebra K16 inferInstance inferInstance)) = 8 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ K16) =
          @DivisionRing.toRatAlgebra K16 inferInstance inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K16 = 4 := by
    simpa using
      (@IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 16 inferInstance
        K16 inferInstance inferInstance hcyclo)
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K16 *
        (Nat.factorial
            (@Module.finrank ℚ K16 inferInstance inferInstance
              (@Algebra.toModule ℚ K16 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K16 inferInstance inferInstance))) /
          (@Module.finrank ℚ K16 inferInstance inferInstance
              (@Algebra.toModule ℚ K16 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K16 inferInstance inferInstance))) ^
            (@Module.finrank ℚ K16 inferInstance inferInstance
              (@Algebra.toModule ℚ K16 inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K16 inferInstance inferInstance))) *
          √|NumberField.discr K16|)⌋₊ = 25 := by
    rw [hcomplex, hfinrank_numberField, hdiscr]
    norm_num
    rw [show (4 / Real.pi) ^ 4 * (315 / 32) = 2520 / Real.pi ^ 4 by ring]
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ (by positivity)]
      have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
      have hpi4 : Real.pi ^ 4 < (3.1416 : ℝ) ^ 4 := by gcongr
      norm_num at hpi4 ⊢
      nlinarith
    · rw [div_lt_iff₀ (by positivity)]
      have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
      have hpi4 : (3.1415 : ℝ) ^ 4 < Real.pi ^ 4 := by gcongr
      norm_num at hpi4 ⊢
      nlinarith
  have horderThree : orderOf (3 : ZMod 16) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderFive : orderOf (5 : ZMod 16) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderSeven : orderOf (7 : ZMod 16) = 2 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderEleven : orderOf (11 : ZMod 16) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have horderThirteen : orderOf (13 : ZMod 16) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  have hlarge (p : ℕ) (hp_le : p ≤ 25) (hpprime : p.Prime)
      (hp_ne_two : p ≠ 2) (hp_ne_seventeen : p ≠ 17) :
      25 < p ^ orderOf (p : ZMod 16) := by
    rw [← ZMod.natCast_mod p 16]
    interval_cases p <;> norm_num [Nat.prime_def] at hpprime
    all_goals first | omega | norm_num [horderThree, horderFive, horderSeven,
      horderEleven, horderThirteen]
  rw [CyclotomicClassNumber,
    NumberField.classNumber_eq_one_iff]
  letI hGalois : IsGalois ℚ K16 :=
    IsCyclotomicExtension.isGalois {16} ℚ K16
  apply @isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    K16 inferInstance inferInstance hGalois
  rw [hfloor]
  intro p hp hpprime
  have hp_le : p ≤ 25 := (Finset.mem_Icc.mp hp).2
  by_cases hp_two : p = 2
  · subst p
    letI : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
      isPrime_of_prime
        (prime_span_singleton_iff.mpr
          (Nat.prime_iff_prime_int.mp (by norm_num)))
    obtain ⟨⟨P2, hP2prime, hP2over⟩⟩ :=
      (Ideal.span ({(2 : ℤ)} : Set ℤ)).nonempty_primesOver (S := 𝓞 K16)
    refine ⟨P2, ⟨hP2prime, hP2over⟩, Or.inr ?_⟩
    letI : P2.IsPrime := hP2prime
    letI : P2.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hP2over
    have hζPow : IsPrimitiveRoot
        (IsCyclotomicExtension.zeta (2 ^ (3 + 1)) ℚ K16) (2 ^ (3 + 1)) :=
      @IsCyclotomicExtension.zeta_spec (2 ^ (3 + 1)) inferInstance ℚ K16
        inferInstance inferInstance inferInstance hcycloPow
    rw [@IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver
      2 3 inferInstance K16 inferInstance inferInstance hcycloPow _ hζPow P2
        inferInstance inferInstance]
    exact ⟨hζPow.toInteger - 1, rfl⟩
  by_cases hp_seventeen : p = 17
  · subst p
    exact ⟨P17, hP17, Or.inr hprincipal17⟩
  · letI : Fact p.Prime := ⟨hpprime⟩
    letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
      isPrime_of_prime
        (prime_span_singleton_iff.mpr
          (Nat.prime_iff_prime_int.mp hpprime))
    obtain ⟨⟨P0, hP0prime, hP0over⟩⟩ :=
      (Ideal.span ({(p : ℤ)} : Set ℤ)).nonempty_primesOver (S := 𝓞 K16)
    refine ⟨P0, ⟨hP0prime, hP0over⟩, Or.inl ?_⟩
    letI : P0.IsPrime := hP0prime
    letI : P0.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hP0over
    rw [@IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 16 p inferInstance
      K16 inferInstance inferInstance P0 inferInstance inferInstance inferInstance hcyclo
        (by
          intro hdiv
          have hp_dvd_two : p ∣ 2 := by
            exact hpprime.dvd_of_dvd_pow (n := 4) (by simpa using hdiv)
          exact hp_two
            ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp hp_dvd_two))]
    exact hlarge p hp_le hpprime hp_two hp_seventeen

end CNOne

end Towers.NumberTheory
