import Towers.NumberTheory.Quadratic.IntegralElements

/-!
# Milne, Algebraic Number Theory, after Proposition 2.9

The order `ℤ[√5]` is not integrally closed: `(1 + √5) / 2` is integral but does not belong
to the order.
-/

namespace Towers.NumberTheory.Milne

open Towers.NumberTheory

/-- The quadratic order `ℤ[√5]`, in coordinates `a + b√5`. -/
abbrev SqrtFiveOrder := QuadraticAlgebra ℤ 5 0

/-- The coordinate embedding `ℤ[√5] → ℚ[√5]`. -/
def fiveOrderEmbedding : SqrtFiveOrder →+* QFModel 5 where
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

theorem five_embedding_injective :
    Function.Injective fiveOrderEmbedding := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.re hxy)
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.im hxy)

local instance : Algebra SqrtFiveOrder (QFModel 5) :=
  fiveOrderEmbedding.toAlgebra

local instance : IsScalarTower ℤ SqrtFiveOrder (QFModel 5) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The element `(1 + √5) / 2` in the ambient quadratic algebra. -/
def goldenRatio : QFModel 5 := ⟨1 / 2, 1 / 2⟩

theorem golden_ratio_integer : IsIntegral ℤ goldenRatio := by
  rw [QFModel.integral_trace_norm]
  constructor
  · convert (isIntegral_algebraMap : IsIntegral ℤ (1 : ℚ)) using 1
    norm_num [goldenRatio]
  · convert (isIntegral_algebraMap : IsIntegral ℤ (-1 : ℚ)) using 1
    norm_num [goldenRatio]

theorem golden_ratio_five :
    IsIntegral SqrtFiveOrder goldenRatio :=
  golden_ratio_integer.tower_top

theorem golden_ratio_sqrt :
    goldenRatio ∉ Set.range (algebraMap SqrtFiveOrder (QFModel 5)) := by
  rintro ⟨z, hz⟩
  have him := congrArg QuadraticAlgebra.im hz
  change (z.im : ℚ) = 1 / 2 at him
  have : (2 : ℚ) * z.im = 1 := by rw [him]; norm_num
  have : (2 : ℤ) * z.im = 1 := by exact_mod_cast this
  omega

/-- The order `ℤ[√5]` is not integrally closed in `ℚ[√5]`.

The witness is `(1 + √5) / 2`, which satisfies `X² - X - 1` but has nonintegral
coordinates in the order basis `1, √5`.
-/
theorem sqrt_integrally_closed :
    ¬IsIntegrallyClosedIn SqrtFiveOrder (QFModel 5) := by
  intro h
  obtain ⟨z, hz⟩ := h.algebraMap_eq_of_integral golden_ratio_five
  exact golden_ratio_sqrt ⟨z, hz⟩

end Towers.NumberTheory.Milne
