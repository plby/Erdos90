import Towers.NumberTheory.Quadratic.IntegralElements

/-!
# Milne, Algebraic Number Theory, two-hour examination 1(b)

The order `Z[sqrt 29]` is not integrally closed: the element `(1 + sqrt 29) / 2` is
integral but does not have integral coordinates in the basis `1, sqrt 29`.  This is the
standard obstruction showing that the order is not a principal ideal domain.
-/

namespace Towers.NumberTheory.Milne

open Towers.NumberTheory

/-- The quadratic order `Z[sqrt 29]`, in coordinates `a + b sqrt 29`. -/
abbrev SqrtTwentyNine := QuadraticAlgebra ℤ 29 0

/-- The coordinate embedding `Z[sqrt 29] -> Q[sqrt 29]`. -/
def twentyNineEmbedding :
    SqrtTwentyNine →+* QFModel 29 where
  toFun z := ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_zero' := by
    apply QuadraticAlgebra.ext <;> norm_num
  map_one' := by
    apply QuadraticAlgebra.ext <;>
      norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
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

theorem twenty_nine_injective :
    Function.Injective twentyNineEmbedding := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.re hxy)
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.im hxy)

local instance : Algebra SqrtTwentyNine (QFModel 29) :=
  twentyNineEmbedding.toAlgebra

local instance : IsScalarTower ℤ SqrtTwentyNine (QFModel 29) :=
  IsScalarTower.of_algebraMap_eq' rfl

private local instance :
    Fact (∀ r : ℚ, r ^ 2 ≠ ((29 : ℤ) : ℚ) + 0 * r) := by
  refine ⟨fun r hr => ?_⟩
  have hsquare : IsSquare (29 : ℚ) := ⟨r, by simpa [pow_two] using hr.symm⟩
  norm_num at hsquare

private local instance : IsDomain SqrtTwentyNine :=
  twenty_nine_injective.isDomain twentyNineEmbedding

private local instance :
    IsFractionRing SqrtTwentyNine (QFModel 29) where
  map_units y := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    apply mem_nonZeroDivisors_iff_ne_zero.mp y.2
    apply twenty_nine_injective
    simpa using hzero
  surj z := by
    let numerator : SqrtTwentyNine :=
      ⟨z.re.num * z.im.den, z.im.num * z.re.den⟩
    let denominator : SqrtTwentyNine :=
      ⟨z.re.den * z.im.den, 0⟩
    refine ⟨⟨numerator, ⟨denominator, ?_⟩⟩, ?_⟩
    · rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hzero
      have hre := congrArg QuadraticAlgebra.re hzero
      simp [denominator] at hre
    · change z * twentyNineEmbedding denominator =
        twentyNineEmbedding numerator
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_mul]
        dsimp [twentyNineEmbedding, numerator, denominator]
        simp only [mul_zero, add_zero, Int.cast_mul, Int.cast_natCast]
        calc
          z.re * ((z.re.den : ℚ) * (z.im.den : ℚ)) =
              (z.re * (z.re.den : ℚ)) * (z.im.den : ℚ) := by
                ring
          _ = (z.re.num : ℚ) * (z.im.den : ℚ) := by
                rw [Rat.mul_den_eq_num]
      · simp only [QuadraticAlgebra.im_mul]
        dsimp [twentyNineEmbedding, numerator, denominator]
        simp only [mul_zero, zero_mul, zero_add, add_zero, Int.cast_mul, Int.cast_natCast]
        calc
          z.im * ((z.re.den : ℚ) * (z.im.den : ℚ)) =
              (z.im * (z.im.den : ℚ)) * (z.re.den : ℚ) := by
                ring
          _ = (z.im.num : ℚ) * (z.re.den : ℚ) := by
                rw [Rat.mul_den_eq_num]
  exists_of_eq {x y} h := by
    refine ⟨1, ?_⟩
    simpa using twenty_nine_injective h

/-- The missing algebraic integer `(1 + sqrt 29) / 2`. -/
def examinationBElement : QFModel 29 := ⟨1 / 2, 1 / 2⟩

theorem examination_b_integer :
    IsIntegral ℤ examinationBElement := by
  rw [QFModel.integral_trace_norm]
  constructor
  · convert (isIntegral_algebraMap : IsIntegral ℤ (1 : ℚ)) using 1
    norm_num [examinationBElement]
  · convert (isIntegral_algebraMap : IsIntegral ℤ (-7 : ℚ)) using 1
    norm_num [examinationBElement]

theorem examination_b_order :
    IsIntegral SqrtTwentyNine examinationBElement :=
  examination_b_integer.tower_top

theorem examination_b_element :
    examinationBElement ∉
      Set.range (algebraMap SqrtTwentyNine (QFModel 29)) := by
  rintro ⟨z, hz⟩
  have him := congrArg QuadraticAlgebra.im hz
  change (z.im : ℚ) = 1 / 2 at him
  have hq : (2 : ℚ) * z.im = 1 := by rw [him]; norm_num
  have hz : (2 : ℤ) * z.im = 1 := by exact_mod_cast hq
  omega

/-- Examination 1(b), integral-closure obstruction: `Z[sqrt 29]` is not integrally
closed in its ambient quadratic field. -/
theorem twenty_nine_integrally :
    ¬IsIntegrallyClosedIn SqrtTwentyNine (QFModel 29) := by
  intro h
  obtain ⟨z, hz⟩ :=
    h.algebraMap_eq_of_integral examination_b_order
  exact examination_b_element ⟨z, hz⟩

/-- Examination 1(b): `Z[sqrt 29]` is not a principal ideal domain. -/
theorem sqrt_twenty_nine :
    ¬IsPrincipalIdealRing SqrtTwentyNine := by
  intro hpid
  letI : IsPrincipalIdealRing SqrtTwentyNine := hpid
  have hclosed :
      IsIntegrallyClosedIn SqrtTwentyNine (QFModel 29) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (QFModel 29)).mp inferInstance
  exact twenty_nine_integrally hclosed

end Towers.NumberTheory.Milne
