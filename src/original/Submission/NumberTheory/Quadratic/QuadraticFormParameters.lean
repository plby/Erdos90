import Submission.NumberTheory.Quadratic.PrimeFactorization
import Submission.NumberTheory.Quadratic.PositiveLeadingCoefficient

/-!
# Quadratic-order parameters for Theorem 4.29

For a squarefree radicand `d`, this file packages the two integral-basis cases used in the
ideal-form correspondence.  The order has relation `omega^2 = A + B * omega`, where `B` is
zero or one, and its discriminant is the fundamental discriminant attached to `d`.
-/

namespace Submission.NumberTheory.Milne

open Submission.NumberTheory
open scoped NumberField

/-- The field discriminant attached to a squarefree radicand. -/
def quadraticFundamentalDiscriminant (d : ℤ) : ℤ :=
  if d % 4 = 1 then d else 4 * d

/-- The constant coefficient in the relation for the standard quadratic order. -/
def quadraticOrderParameter (d : ℤ) : ℤ :=
  if d % 4 = 1 then (d - 1) / 4 else d

/-- The linear coefficient in the relation for the standard quadratic order. -/
def quadraticParameterB (d : ℤ) : ℤ :=
  if d % 4 = 1 then 1 else 0

/-- The standard quadratic order has the fundamental discriminant attached to `d`. -/
theorem fundam_discr_param (d : ℤ) :
    quadraticFundamentalDiscriminant d =
      quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d := by
  by_cases h : d % 4 = 1
  · have hdiv : 4 ∣ d - 1 := Int.dvd_iff_emod_eq_zero.mpr (by omega)
    have hmul : 4 * ((d - 1) / 4) = d - 1 := by
      simpa [mul_comm] using Int.ediv_mul_cancel hdiv
    simp only [quadraticFundamentalDiscriminant, quadraticOrderParameter,
      quadraticParameterB, if_pos h]
    omega
  · simp [quadraticFundamentalDiscriminant, quadraticOrderParameter,
      quadraticParameterB, h]

/-- A squarefree integer other than `1` is not a square. -/
theorem not_square_squarefree {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    ¬ IsSquare d := by
  rintro ⟨x, hx⟩
  have hxunit : IsUnit x := hd x ⟨1, by simpa [pow_two] using hx⟩
  rw [Int.isUnit_iff] at hxunit
  rcases hxunit with rfl | rfl <;> apply hd1 <;> simpa using hx

/-- The fundamental discriminant of a squarefree radicand other than `1` is nonsquare. -/
theorem fundamental_discriminant_square
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    ¬ IsSquare (quadraticFundamentalDiscriminant d) := by
  by_cases h : d % 4 = 1
  · simpa [quadraticFundamentalDiscriminant, h] using
      not_square_squarefree hd hd1
  · simp only [quadraticFundamentalDiscriminant, if_neg h]
    rintro ⟨x, hx⟩
    have htwo_sq : (2 : ℤ) ∣ x * x := by
      refine ⟨2 * d, ?_⟩
      nlinarith [hx]
    have htwo_prime : Prime (2 : ℤ) := by norm_num
    have htwo : (2 : ℤ) ∣ x := by
      rcases htwo_prime.dvd_mul.mp htwo_sq with hx | hx <;> exact hx
    obtain ⟨y, rfl⟩ := htwo
    have hy : d = y * y := by nlinarith [hx]
    exact not_square_squarefree hd hd1 ⟨y, hy⟩

/-- A form of the fundamental discriminant has the parity required by the standard quadratic
order: its middle coefficient is `B` modulo two. -/
theorem middle_parameter_b
    {d : ℤ} (Q : BQForm)
    (hdisc : Q.discriminant = quadraticFundamentalDiscriminant d) :
    ∃ r : ℤ, Q.b = quadraticParameterB d + 2 * r := by
  by_cases h : d % 4 = 1
  · have hb_odd : Odd Q.b := by
      rw [← Int.not_even_iff_odd]
      rintro ⟨k, hk⟩
      have hfour : (4 : ℤ) ∣ Q.discriminant := by
        refine ⟨k ^ 2 - Q.a * Q.c, ?_⟩
        simp only [BQForm.discriminant]
        rw [hk]
        ring
      have hmod0 : Q.discriminant % 4 = 0 := Int.dvd_iff_emod_eq_zero.mp hfour
      rw [hdisc] at hmod0
      simp [quadraticFundamentalDiscriminant, h] at hmod0
    obtain ⟨r, hr⟩ := hb_odd
    refine ⟨r, ?_⟩
    simp only [quadraticParameterB, if_pos h]
    omega
  · have htwo_sq : (2 : ℤ) ∣ Q.b * Q.b := by
      have heq : Q.b ^ 2 - 4 * Q.a * Q.c = 4 * d := by
        simpa [quadraticFundamentalDiscriminant, h,
          BQForm.discriminant] using hdisc
      refine ⟨2 * (Q.a * Q.c + d), ?_⟩
      nlinarith
    have htwo_prime : Prime (2 : ℤ) := by norm_num
    have hb_even : (2 : ℤ) ∣ Q.b := by
      rcases htwo_prime.dvd_mul.mp htwo_sq with hb | hb <;> exact hb
    obtain ⟨r, hr⟩ := hb_even
    refine ⟨r, ?_⟩
    simp only [quadraticParameterB, if_neg h, zero_add]
    exact hr

/-- The parity parameter also satisfies the quadratic relation needed to make
`(a, omega + r)` an ideal. -/
theorem middle_parameter_relation
    {d : ℤ} (Q : BQForm)
    (hdisc : Q.discriminant = quadraticFundamentalDiscriminant d) :
    ∃ r : ℤ,
      Q.b = quadraticParameterB d + 2 * r ∧
        r ^ 2 + quadraticParameterB d * r - quadraticOrderParameter d =
          Q.a * Q.c := by
  obtain ⟨r, hr⟩ := middle_parameter_b Q hdisc
  refine ⟨r, hr, ?_⟩
  have hparameters := fundam_discr_param d
  rw [BQForm.discriminant, hr] at hdisc
  nlinarith

/-- The coordinate embedding of the integral-basis order `Z[sqrt d]`. -/
def quadraticIntegralEmbedding (d : ℤ) :
    QOrd d 0 →+* QFModel d where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> norm_num
  map_one' := by
    apply QuadraticAlgebra.ext
    · change ((1 : ℤ) : ℚ) = 1
      norm_num
    · change ((0 : ℤ) : ℚ) = 0
      norm_num
  map_add' x y := by apply QuadraticAlgebra.ext <;> simp
  map_mul' x y := by
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

theorem quadratic_embedding_injective (d : ℤ) :
    Function.Injective (quadraticIntegralEmbedding d) := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.re hxy)
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.im hxy)

instance quadraticIntegralAlgebra (d : ℤ) :
    Algebra (QOrd d 0) (QFModel d) :=
  (quadraticIntegralEmbedding d).toAlgebra

instance quadraticScalarTower (d : ℤ) :
    IsScalarTower ℤ (QOrd d 0) (QFModel d) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Outside the `1 mod 4` case, the integral-coordinate quadratic order is the full ring of
integers. -/
theorem quadratic_integral_closure (d : ℤ)
    (hd : Squarefree d) (hmod : d % 4 ≠ 1) :
    IsIntegralClosure (QOrd d 0) ℤ (QFModel d) where
  algebraMap_injective := quadratic_embedding_injective d
  isIntegral_iff {x} := by
    rw [QFModel.integral_integer_coordinates d hd hmod]
    constructor
    · rintro ⟨a, b, ha, hb⟩
      refine ⟨(⟨a, b⟩ : QOrd d 0), ?_⟩
      apply QuadraticAlgebra.ext
      · exact ha.symm
      · exact hb.symm
    · rintro ⟨y, rfl⟩
      exact ⟨y.re, y.im, rfl, rfl⟩

end Submission.NumberTheory.Milne
