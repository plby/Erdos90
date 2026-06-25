import Submission.NumberTheory.Quadratic.BiquadraticIntegerRings
import Submission.NumberTheory.Ramification.RamificationDiscriminant
import Submission.NumberTheory.Ramification.TowerFormulas
import Submission.NumberTheory.Quadratic.ClassGroups
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification


/-!
# Milne, Chapter 4, Exercise 7

We use nested quadratic algebras to model
`Q(sqrt(-1), sqrt(5))`.  The outer generator `gamma` satisfies
`gamma^2 = gamma + 1`, so it is `(1 + sqrt(5)) / 2`, while the inner generator is `i`.

The final identification as the Hilbert class field is not encoded here.  Milne deduces it from
Remark 4.11, which in turn invokes class field theory.  We prove all of the concrete input: the
ring of integers, ramification indices, everywhere-unramifiedness over `Q(sqrt(-5))`, and the
class-number computation.
-/

namespace Submission.NumberTheory.Milne

open Polynomial NumberField
open scoped Kronecker

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

/-- The Gaussian order `Z[i]`. -/
abbrev FiveBiquadraticGaussian := ExplicitQuadraticOrder (-1)

/-- The Gaussian quadratic field in coordinates. -/
abbrev SqrtBiquadraticGaussian := QFModel (-1)

/-- Milne's order `Z[i][gamma]`, where `gamma^2 = gamma + 1`. -/
abbrev SqrtBiquadraticOrder :=
  QuadraticAlgebra FiveBiquadraticGaussian (1 : FiveBiquadraticGaussian) 1

/-- The rational biquadratic algebra `Q(i, sqrt(5))`, written using `gamma`. -/
abbrev FieldModel :=
  QuadraticAlgebra SqrtBiquadraticGaussian (1 : SqrtBiquadraticGaussian) 1

/-- The quadratic subfield `Q(sqrt(-5))` in the tower used by Exercise 4-7. -/
abbrev SqrtFiveField := QFModel (-5)

private theorem rat_sq_five (q : ℚ) : q ^ 2 ≠ 5 := by
  intro h
  have hsquare : IsSquare (5 : ℚ) := ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hsquare

private local instance gaussian_irreducible :
    Fact (∀ r : ℚ, r ^ 2 ≠ ((-1 : ℤ) : ℚ) + 0 * r) :=
  ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩

/-- The polynomial `X^2 - X - 1` has no root in `Q(i)`.  In coordinates, its imaginary
part says `b * (2*a - 1) = 0`; the two cases respectively make `5` a rational square or
make `b^2` negative. -/
theorem golden_ratio_gaussian
    (r : SqrtBiquadraticGaussian) :
    r ^ 2 ≠ (1 : SqrtBiquadraticGaussian) + r := by
  intro hr
  have hre := congrArg QuadraticAlgebra.re hr
  have him := congrArg QuadraticAlgebra.im hr
  simp only [Int.reduceNeg, Rat.intCast_neg, Rat.intCast_ofNat, pow_two,
    QuadraticAlgebra.re_mul, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
    QuadraticAlgebra.re_add, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_mul, zero_mul,
    add_zero, QuadraticAlgebra.im_add, QuadraticAlgebra.im_one, zero_add] at hre him
  have hprod : r.im * (2 * r.re - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hy | hx
  · have hsquare : (2 * r.re - 1) ^ 2 = 5 := by
      rw [hy] at hre
      nlinarith
    exact rat_sq_five _ hsquare
  · have hre' : 2 * r.re = 1 := by nlinarith
    nlinarith [sq_nonneg r.im]

private local instance sqrtNegFiveBiquadraticbiquadratic_irreducible :
    Fact (∀ r : SqrtBiquadraticGaussian,
      r ^ 2 ≠ (1 : SqrtBiquadraticGaussian) + 1 * r) :=
  ⟨fun r => by simpa using golden_ratio_gaussian r⟩

private local instance gaussian_moduleFinite :
    Module.Finite ℚ SqrtBiquadraticGaussian :=
  Module.Finite.of_basis (QuadraticAlgebra.basis (-1) 0)

private local instance gaussian_numberField :
    NumberField SqrtBiquadraticGaussian :=
  @NumberField.of_module_finite ℚ SqrtBiquadraticGaussian _ _ _ _
    gaussian_moduleFinite

private local instance biquadratic_relative_moduleFinite :
    Module.Finite SqrtBiquadraticGaussian FieldModel :=
  Module.Finite.of_basis (QuadraticAlgebra.basis 1 1)

private local instance biquadratic_moduleFinite :
    Module.Finite ℚ FieldModel :=
  Module.Finite.trans SqrtBiquadraticGaussian FieldModel

private local instance biquadratic_numberField :
    NumberField FieldModel :=
  @NumberField.of_module_finite ℚ FieldModel _ _ _ _
    biquadratic_moduleFinite

/-- The coordinate inclusion `Z[sqrt(-5)] -> Q(sqrt(-5))`. -/
def sqrtFiveEmbedding :
    Submission.NumberTheory.SNFive →+* SqrtFiveField where
  toFun z := ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_zero' := by ext <;> norm_num
  map_one' := by
    ext <;> norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by
    apply QuadraticAlgebra.ext
    · simp only [Zsqrtd.re_add, QuadraticAlgebra.re_add]
      norm_cast
    · simp only [Zsqrtd.im_add, QuadraticAlgebra.im_add]
      norm_cast
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp only [Zsqrtd.re_mul, QuadraticAlgebra.re_mul]
      push_cast
      ring
    · simp only [Zsqrtd.im_mul, QuadraticAlgebra.im_mul]
      push_cast
      ring

theorem sqrt_embedding_injective :
    Function.Injective sqrtFiveEmbedding := by
  intro x y hxy
  ext
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.re hxy)
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.im hxy)

private local instance sqrtNegFive_field_irreducible :
    Fact (∀ r : ℚ, r ^ 2 ≠ ((-5 : ℤ) : ℚ) + 0 * r) :=
  ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩

private local instance sqrtNegFive_orderAlgebra :
    Algebra Submission.NumberTheory.SNFive SqrtFiveField :=
  sqrtFiveEmbedding.toAlgebra

private local instance sqrtNegFive_orderScalarTower :
    IsScalarTower ℤ Submission.NumberTheory.SNFive
      SqrtFiveField :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- `Z[sqrt(-5)]` is the full integral closure of `Z` in the displayed quadratic field. -/
@[reducible] def sqrt_five_closure :
    IsIntegralClosure Submission.NumberTheory.SNFive ℤ
      SqrtFiveField where
  algebraMap_injective := sqrt_embedding_injective
  isIntegral_iff {x} := by
    have hm : Squarefree (-5 : ℤ) := by
      rw [← Int.squarefree_natAbs]
      norm_num
      exact Nat.prime_five.squarefree
    rw [QFModel.integral_integer_coordinates (-5) hm (by norm_num)]
    constructor
    · rintro ⟨a, b, ha, hb⟩
      refine ⟨(⟨a, b⟩ : Submission.NumberTheory.SNFive), ?_⟩
      apply QuadraticAlgebra.ext
      · exact ha.symm
      · exact hb.symm
    · rintro ⟨y, rfl⟩
      exact ⟨y.re, y.im, rfl, rfl⟩

private local instance sqrtNegFive_integralClosure :
    IsIntegralClosure Submission.NumberTheory.SNFive ℤ
      SqrtFiveField :=
  sqrt_five_closure

private local instance sqrtNegFive_moduleFinite :
    Module.Finite ℚ SqrtFiveField :=
  Module.Finite.of_basis (QuadraticAlgebra.basis (-5) 0)

private local instance sqrtNegFive_ratScalarTower :
    IsScalarTower ℤ ℚ SqrtFiveField :=
  IsScalarTower.of_algebraMap_eq fun z => by
    apply QuadraticAlgebra.ext <;> simp

private local instance sqrtNegFive_numberField :
    NumberField SqrtFiveField :=
  @NumberField.of_module_finite ℚ SqrtFiveField _ _ _ _
    sqrtNegFive_moduleFinite

private local instance sqrtNegFive_isDedekindDomain :
    IsDedekindDomain Submission.NumberTheory.SNFive :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ SqrtFiveField _

private local instance sqrtNegFive_moduleFree :
    Module.Free ℤ Submission.NumberTheory.SNFive :=
  IsIntegralClosure.module_free ℤ ℚ SqrtFiveField _

private local instance sqrtNegFive_isNoetherian :
    IsNoetherian ℤ Submission.NumberTheory.SNFive :=
  IsIntegralClosure.isNoetherian ℤ ℚ SqrtFiveField _

private local instance sqrtNegFive_order_moduleFinite :
    Module.Finite ℤ Submission.NumberTheory.SNFive :=
  inferInstance

/-- The coordinatewise embedding `Z[i][gamma] -> Q(i, sqrt(5))`. -/
def sqrtBiquadraticEmbedding : SqrtBiquadraticOrder →+* FieldModel where
  toFun z :=
    ⟨QuadraticOrderEmbedding (-1) z.re,
      QuadraticOrderEmbedding (-1) z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by
    apply QuadraticAlgebra.ext
    · exact map_one (QuadraticOrderEmbedding (-1))
    · exact map_zero (QuadraticOrderEmbedding (-1))
  map_add' x y := by apply QuadraticAlgebra.ext <;> simp
  map_mul' x y := by
    apply QuadraticAlgebra.ext <;>
      apply QuadraticAlgebra.ext <;>
        simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
          QuadraticOrderEmbedding,
          ]

theorem sqrt_five_biquadratic :
    Function.Injective sqrtBiquadraticEmbedding := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · exact quadratic_order_injective (-1)
      (congrArg QuadraticAlgebra.re hxy)
  · exact quadratic_order_injective (-1)
      (congrArg QuadraticAlgebra.im hxy)

/-- The element `i` in the nested coordinate model. -/
def sqrt_biquadratic_i : FieldModel := ⟨⟨0, 1⟩, 0⟩

/-- The element `gamma = (1 + sqrt(5)) / 2`. -/
def sqrtFiveBiquadraticgamma : FieldModel := ⟨0, 1⟩

/-- The resulting square root of five. -/
def sqrtNegBiquadraticsqrt : FieldModel := 2 * sqrtFiveBiquadraticgamma - 1

theorem sqrt_biquadratici_sq : sqrt_biquadratic_i ^ 2 = -1 := by
  apply QuadraticAlgebra.ext <;>
    apply QuadraticAlgebra.ext <;>
      norm_num [sqrt_biquadratic_i, pow_two, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

theorem gamma_sq :
    sqrtFiveBiquadraticgamma ^ 2 = sqrtFiveBiquadraticgamma + 1 := by
  apply QuadraticAlgebra.ext <;>
    apply QuadraticAlgebra.ext <;>
      norm_num [sqrtFiveBiquadraticgamma, pow_two, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

theorem five_biquadraticsqrt_sq : sqrtNegBiquadraticsqrt ^ 2 = 5 := by
  rw [sqrtNegBiquadraticsqrt, pow_two]
  calc
    (2 * sqrtFiveBiquadraticgamma - 1) * (2 * sqrtFiveBiquadraticgamma - 1) =
        4 * sqrtFiveBiquadraticgamma ^ 2 - 4 * sqrtFiveBiquadraticgamma + 1 := by ring
    _ = 5 := by rw [gamma_sq]; ring

/-- The element `sqrt(-5) = i * sqrt(5)` in the biquadratic model. -/
def sqrtFiveBiquadraticsqrt : FieldModel :=
  sqrt_biquadratic_i * sqrtNegBiquadraticsqrt

theorem sqrt_biquadraticsqrt_sq : sqrtFiveBiquadraticsqrt ^ 2 = -5 := by
  rw [sqrtFiveBiquadraticsqrt, mul_pow, sqrt_biquadratici_sq,
    five_biquadraticsqrt_sq]
  ring

/-- The concrete field inclusion `Q(sqrt(-5)) -> Q(i, sqrt(5))`. -/
def sqrtNegEmbedding :
    SqrtFiveField →ₐ[ℚ] FieldModel :=
  QuadraticAlgebra.lift ⟨sqrtFiveBiquadraticsqrt, by
    calc
      sqrtFiveBiquadraticsqrt * sqrtFiveBiquadraticsqrt =
          sqrtFiveBiquadraticsqrt ^ 2 := (pow_two _).symm
      _ = -5 := sqrt_biquadraticsqrt_sq
      _ = (-5 : ℚ) • (1 : FieldModel) +
          (0 : ℚ) • sqrtFiveBiquadraticsqrt := by
        ext <;>
          norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
            QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]⟩

theorem sqrt_five_injective :
    Function.Injective sqrtNegEmbedding :=
  sqrtNegEmbedding.injective

instance sqrt_five_algebra :
    Algebra SqrtFiveField FieldModel :=
  sqrtNegEmbedding.toAlgebra

instance sqrt_scalar_tower :
    IsScalarTower ℚ SqrtFiveField FieldModel :=
  IsScalarTower.of_algebraMap_eq' (by
    ext q <;>
      norm_num [sqrtNegEmbedding,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])

private local instance sqrtNegFive_relative_moduleFinite :
    Module.Finite SqrtFiveField FieldModel :=
  Module.Finite.right ℚ SqrtFiveField FieldModel

/-- The same square root of `-5`, now as an element of Milne's full integer order.
Its coordinates are `-i + 2*i*gamma`. -/
def sqrtFiveOrder : SqrtBiquadraticOrder :=
  ⟨⟨0, -1⟩, ⟨0, 2⟩⟩

theorem sqrt_five_image :
    sqrtBiquadraticEmbedding sqrtFiveOrder =
      sqrtFiveBiquadraticsqrt := by
  apply QuadraticAlgebra.ext <;>
    apply QuadraticAlgebra.ext <;>
      norm_num [sqrtBiquadraticEmbedding, sqrtFiveOrder,
        sqrtFiveBiquadraticsqrt, sqrt_biquadratic_i, sqrtNegBiquadraticsqrt,
        sqrtFiveBiquadraticgamma, QuadraticOrderEmbedding,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

theorem sqrt_neg_sq :
    sqrtFiveOrder ^ 2 = -5 := by
  apply sqrt_five_biquadratic
  rw [map_pow, sqrt_five_image,
    sqrt_biquadraticsqrt_sq, map_neg, map_ofNat]

/-- The concrete inclusion `Z[sqrt(-5)] -> O_K` for
`K = Q(i, sqrt(5))`. -/
def sqrtOrderEmbedding :
    Submission.NumberTheory.SNFive →+* SqrtBiquadraticOrder :=
  Zsqrtd.lift ⟨sqrtFiveOrder, by
    simpa [pow_two] using sqrt_neg_sq⟩

theorem sqrt_five_embedding :
    Function.Injective sqrtOrderEmbedding := by
  apply Zsqrtd.lift_injective
  intro n hn
  nlinarith [sq_nonneg n]

@[simp] theorem sqrt_embedding_sqrtd :
    sqrtOrderEmbedding Zsqrtd.sqrtd =
      sqrtFiveOrder := by
  rfl

private local instance sqrtNegFive_topOrderAlgebra :
    Algebra Submission.NumberTheory.SNFive SqrtBiquadraticOrder :=
  sqrtOrderEmbedding.toAlgebra

private local instance sqrtNegFive_topOrderScalarTower :
    IsScalarTower ℤ Submission.NumberTheory.SNFive SqrtBiquadraticOrder :=
  IsScalarTower.of_algebraMap_eq' (by
    ext z <;>
      norm_num [sqrtOrderEmbedding,
        sqrtFiveOrder,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])

private local instance gaussianOrder_moduleFinite :
    Module.Finite ℤ FiveBiquadraticGaussian :=
  Module.Finite.of_basis (QuadraticAlgebra.basis (-1) 0)

private local instance topOrder_relativeGaussian_moduleFinite :
    Module.Finite FiveBiquadraticGaussian SqrtBiquadraticOrder :=
  Module.Finite.of_basis (QuadraticAlgebra.basis 1 1)

private local instance topOrder_moduleFinite :
    Module.Finite ℤ SqrtBiquadraticOrder :=
  Module.Finite.trans FiveBiquadraticGaussian SqrtBiquadraticOrder

private local instance sqrtNegFive_topOrder_moduleFinite :
    Module.Finite Submission.NumberTheory.SNFive SqrtBiquadraticOrder :=
  Module.Finite.right ℤ Submission.NumberTheory.SNFive SqrtBiquadraticOrder

/-- The two monic equations showing that Milne's generators are algebraic integers. -/
theorem sqrt_biqua_integ :
    IsIntegral ℤ sqrt_biquadratic_i ∧ IsIntegral ℤ sqrtFiveBiquadraticgamma := by
  constructor
  · refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity ; norm_num
    · simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one]
      rw [sqrt_biquadratici_sq]
      ring
  · refine ⟨X ^ 2 - X - 1, ?_, ?_⟩
    · monicity ; norm_num
    · simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
      rw [gamma_sq]
      ring

private theorem relative_trace_formula (x : SqrtBiquadraticOrder) :
    Algebra.trace FiveBiquadraticGaussian
      SqrtBiquadraticOrder x = 2 * x.re + x.im := by
  have hmat : Algebra.leftMulMatrix
      (QuadraticAlgebra.basis (1 : FiveBiquadraticGaussian) 1) x =
      !![x.re, x.im; x.im, x.re + x.im] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      apply QuadraticAlgebra.ext <;>
        simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis,
          QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd,
          QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  rw [Algebra.trace_eq_matrix_trace
      (QuadraticAlgebra.basis (1 : FiveBiquadraticGaussian) 1), hmat,
    Matrix.trace_fin_two_of]
  ring

/-- The relative discriminant of the displayed basis `(1, gamma)` over `Z[i]` is `5`. -/
theorem relative_discr :
    Algebra.discr FiveBiquadraticGaussian
      (QuadraticAlgebra.basis (1 : FiveBiquadraticGaussian) 1) = 5 := by
  rw [Algebra.discr_def]
  have hmat :
      Algebra.traceMatrix FiveBiquadraticGaussian
          (QuadraticAlgebra.basis (1 : FiveBiquadraticGaussian) 1) =
        !![2, 1; 1, 3] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    all_goals
      apply QuadraticAlgebra.ext <;>
        simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
          relative_trace_formula, QuadraticAlgebra.basis,
          QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd,
          QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
          QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  rw [hmat, Matrix.det_fin_two_of]
  norm_num

/-- The integral basis `(1, i, gamma, i*gamma)` of the displayed order. -/
noncomputable def orderBasis :
    Module.Basis (Fin 2 × Fin 2) ℤ SqrtBiquadraticOrder :=
  (QuadraticAlgebra.basis (-1) 0).smulTower
    (QuadraticAlgebra.basis (1 : FiveBiquadraticGaussian) 1)

private theorem gaussian_trace_formula
    (x : FiveBiquadraticGaussian) :
    Algebra.trace ℤ FiveBiquadraticGaussian x = 2 * x.re := by
  have hmat :
      Algebra.leftMulMatrix (QuadraticAlgebra.basis (-1) 0) x =
        !![x.re, -x.im; x.im, x.re] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis,
        QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (-1) 0), hmat,
    Matrix.trace_fin_two_of]
  ring

private theorem absolute_trace_formula (x : SqrtBiquadraticOrder) :
    Algebra.trace ℤ SqrtBiquadraticOrder x = 4 * x.re.re + 2 * x.im.re := by
  rw [← Algebra.trace_trace_of_basis
    (QuadraticAlgebra.basis (-1) 0)
    (QuadraticAlgebra.basis (1 : FiveBiquadraticGaussian) 1)]
  rw [relative_trace_formula, gaussian_trace_formula]
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  ring

/-- The discriminant of the integral basis `(1, i, gamma, i*gamma)` is `400`. -/
theorem order_discr :
    Algebra.discr ℤ orderBasis = 400 := by
  rw [Algebra.discr_def]
  have hmat :
      Algebra.traceMatrix ℤ orderBasis =
        !![(2 : ℤ), 0; 0, -2] ⊗ₖ !![(2 : ℤ), 1; 1, 3] := by
    apply Matrix.ext
    rintro ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        orderBasis, absolute_trace_formula,
        QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple,
        QuadraticAlgebra.equivProd, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat, Matrix.kronecker_apply]
  rw [hmat, Matrix.det_kronecker]
  norm_num [Matrix.det_fin_two_of]

/-- The relative discriminant is not a square in the Gaussian order, as used in Milne's
application of the quadratic integral-basis criterion. -/
theorem five_square_gaussian
    (z : FiveBiquadraticGaussian) : z ^ 2 ≠ 5 := by
  intro hz
  have hre := congrArg QuadraticAlgebra.re hz
  have him := congrArg QuadraticAlgebra.im hz
  simp only [Int.reduceNeg, pow_two, QuadraticAlgebra.re_mul, neg_mul,
    one_mul, QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_mul, zero_mul, add_zero, QuadraticAlgebra.im_ofNat] at hre him
  have hab : z.re = 0 ∨ z.im = 0 := by
    have : z.re * z.im = 0 := by nlinarith
    exact mul_eq_zero.mp this
  rcases hab with ha | hb
  · rw [ha] at hre
    nlinarith [sq_nonneg z.im]
  · rw [hb] at hre
    have hlo : (-3 : ℤ) ≤ z.re := by nlinarith [sq_nonneg (z.re + 3)]
    have hhi : z.re ≤ (3 : ℤ) := by nlinarith [sq_nonneg (z.re - 3)]
    interval_cases z.re <;> norm_num at hre

private theorem gaussian_embedding_integral
    (z : FiveBiquadraticGaussian) :
    IsIntegral ℤ
      (⟨QuadraticOrderEmbedding (-1) z, 0⟩ : FieldModel) := by
  have hi := sqrt_biqua_integ.1
  have hrepr :
      (⟨QuadraticOrderEmbedding (-1) z, 0⟩ : FieldModel) =
        algebraMap ℤ FieldModel z.re +
          algebraMap ℤ FieldModel z.im * sqrt_biquadratic_i := by
    apply QuadraticAlgebra.ext <;>
      apply QuadraticAlgebra.ext <;>
        norm_num [QuadraticOrderEmbedding, sqrt_biquadratic_i,
          QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
          QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [hrepr]
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hi)

/-- Every element of `Z[i][gamma]` maps to an algebraic integer.  This proves the inclusion of
Milne's displayed order in the full ring of integers. -/
theorem order_embedding_integral (z : SqrtBiquadraticOrder) :
    IsIntegral ℤ (sqrtBiquadraticEmbedding z) := by
  have hre := gaussian_embedding_integral z.re
  have him := gaussian_embedding_integral z.im
  have hgamma := sqrt_biqua_integ.2
  have hrepr :
      sqrtBiquadraticEmbedding z =
        (⟨QuadraticOrderEmbedding (-1) z.re, 0⟩ : FieldModel) +
          (⟨QuadraticOrderEmbedding (-1) z.im, 0⟩ : FieldModel) *
            sqrtFiveBiquadraticgamma := by
    apply QuadraticAlgebra.ext <;>
      apply QuadraticAlgebra.ext <;>
        norm_num [sqrtBiquadraticEmbedding, sqrtFiveBiquadraticgamma,
          QuadraticOrderEmbedding, QuadraticAlgebra.re_mul,
          QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [hrepr]
  exact hre.add (him.mul hgamma)

private theorem biquadraticrat_squarefree_sq
    (m : ℤ) (hm : Squarefree m) (q : ℚ)
    (h : IsIntegral ℤ ((m : ℚ) * q ^ 2)) : IsIntegral ℤ q := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  change (z : ℚ) = (m : ℚ) * q ^ 2 at hz
  have hqden : q * (q.den : ℚ) = q.num := by
    nth_rw 1 [← Rat.num_div_den q]
    field_simp
  have heqZ : m * q.num ^ 2 = z * (q.den : ℤ) ^ 2 := by
    apply Rat.intCast_injective
    calc
      ((m * q.num ^ 2 : ℤ) : ℚ) = (m : ℚ) * (q.num : ℚ) ^ 2 := by norm_cast
      _ = (m : ℚ) * q ^ 2 * (q.den : ℚ) ^ 2 := by
        rw [← hqden]
        ring
      _ = (z : ℚ) * (q.den : ℚ) ^ 2 := by rw [← hz]
      _ = ((z * (q.den : ℤ) ^ 2 : ℤ) : ℚ) := by norm_cast
  have heqN := congrArg Int.natAbs heqZ
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at heqN
  have hdvd : q.den * q.den ∣ m.natAbs * (q.num.natAbs * q.num.natAbs) := by
    refine ⟨z.natAbs, ?_⟩
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using heqN
  have hdvdNum : q.den ∣ q.num.natAbs * q.num.natAbs :=
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right
      (Int.squarefree_natAbs.mpr hm) hdvd
  have hcop : q.den.Coprime (q.num.natAbs ^ 2) := q.reduced.symm.pow_right 2
  have hdvdOne : q.den ∣ 1 := hcop.dvd_of_dvd_mul_right <| by
    simpa [pow_two] using hdvdNum
  have hden : q.den = 1 := Nat.dvd_one.mp hdvdOne
  exact IsIntegrallyClosed.isIntegral_iff.mpr
    ⟨q.num, (Rat.den_eq_one_iff q).mp hden⟩

private theorem gaussian_five_sq
    (q : SqrtBiquadraticGaussian)
    (h : IsIntegral ℤ ((5 : SqrtBiquadraticGaussian) * q ^ 2)) :
    IsIntegral ℤ q := by
  let y : SqrtBiquadraticGaussian := 5 * q ^ 2
  have hy : IsIntegral ℤ y := h
  obtain ⟨a, b, ha, hb⟩ :=
    QFModel.gaussian_integer_coordinates y |>.mp hy
  have hyre : IsIntegral ℤ y.re := by
    rw [ha]
    exact isIntegral_algebraMap
  have hyim : IsIntegral ℤ y.im := by
    rw [hb]
    exact isIntegral_algebraMap
  have hsq : IsIntegral ℤ ((5 * (q.re ^ 2 + q.im ^ 2)) ^ 2 : ℚ) := by
    have hsum := (hyre.pow 2).add (hyim.pow 2)
    convert hsum using 1
    dsimp [y]
    simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
    ring
  have hsum : IsIntegral ℤ (5 * (q.re ^ 2 + q.im ^ 2) : ℚ) := by
    apply biquadraticrat_squarefree_sq 1 (by norm_num)
    simpa using hsq
  have hqre10 : IsIntegral ℤ (10 * q.re ^ 2 : ℚ) := by
    have := hsum.add hyre
    convert this using 1
    dsimp [y]
    simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, mul_zero]
    ring
  have hqim10 : IsIntegral ℤ (10 * q.im ^ 2 : ℚ) := by
    have := hsum.sub hyre
    convert this using 1
    dsimp [y]
    simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, mul_zero]
    ring
  have hten : Squarefree (10 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    change Squarefree (10 : ℕ)
    rw [show (10 : ℕ) = 2 * 5 by norm_num, Nat.squarefree_mul (by norm_num)]
    exact ⟨Nat.prime_two.squarefree, (by norm_num : Nat.Prime 5).squarefree⟩
  have hqre := biquadraticrat_squarefree_sq 10 hten q.re hqre10
  have hqim := biquadraticrat_squarefree_sq 10 hten q.im hqim10
  rw [QFModel.gaussian_integer_coordinates]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqre
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqim
  exact ⟨c, d, hc.symm, hd.symm⟩

/-- Milne's displayed order is the full ring of integers of
`ℚ(i, √5)`: an element is integral exactly when all four coordinates
in the basis `(1, i, gamma, i*gamma)` are integers. -/
theorem ringOfIntegers (x : FieldModel) :
    IsIntegral ℤ x ↔
      ∃ z : SqrtBiquadraticOrder, sqrtBiquadraticEmbedding z = x := by
  constructor
  · intro hx
    let conj : FieldModel →ₐ[ℤ] FieldModel :=
      { starRingEnd FieldModel with
        commutes' := fun z => by simp }
    have hconj : IsIntegral ℤ (star x) := by
      simpa [conj] using hx.map conj
    let incl : SqrtBiquadraticGaussian →ₐ[ℤ] FieldModel :=
      IsScalarTower.toAlgHom ℤ SqrtBiquadraticGaussian FieldModel
    have hincl : Function.Injective incl := by
      intro a b hab
      have := congrArg QuadraticAlgebra.re hab
      simpa [incl] using this
    have hincl_apply (a : SqrtBiquadraticGaussian) :
        incl a = (⟨a, 0⟩ : FieldModel) := by
      rfl
    have htrace : IsIntegral ℤ (2 * x.re + x.im) := by
      rw [← isIntegral_algHom_iff incl hincl]
      have hsum := hx.add hconj
      convert hsum using 1
      rw [hincl_apply]
      apply QuadraticAlgebra.ext
      · simp [QuadraticAlgebra.re_star]
        ring
      · simp [QuadraticAlgebra.im_star]
    have hnorm : IsIntegral ℤ (QuadraticAlgebra.norm x) := by
      rw [← isIntegral_algHom_iff incl hincl]
      have hprod := hx.mul hconj
      convert hprod using 1
      rw [hincl_apply]
      exact QuadraticAlgebra.algebraMap_norm_eq_mul_star x
    have himDisc : IsIntegral ℤ ((5 : SqrtBiquadraticGaussian) * x.im ^ 2) := by
      have hfour : IsIntegral ℤ (4 : SqrtBiquadraticGaussian) := isIntegral_algebraMap
      have h := (htrace.pow 2).sub (hfour.mul hnorm)
      convert h using 1
      simp only [QuadraticAlgebra.norm_def]
      ring
    have him : IsIntegral ℤ x.im :=
      gaussian_five_sq x.im himDisc
    have hre : IsIntegral ℤ x.re := by
      rw [← isIntegral_algHom_iff incl hincl]
      have himOuter : IsIntegral ℤ (incl x.im) := him.map incl
      have hsub := hx.sub (himOuter.mul sqrt_biqua_integ.2)
      convert hsub using 1
      rw [hincl_apply, hincl_apply]
      apply QuadraticAlgebra.ext <;>
        simp [sqrtFiveBiquadraticgamma]
    obtain ⟨a, b, ha, hb⟩ :=
      QFModel.gaussian_integer_coordinates x.re |>.mp hre
    obtain ⟨c, d, hc, hd⟩ :=
      QFModel.gaussian_integer_coordinates x.im |>.mp him
    refine ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ?_⟩
    apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · change (a : ℚ) = x.re.re
        exact ha.symm
      · change (b : ℚ) = x.re.im
        exact hb.symm
    · apply QuadraticAlgebra.ext
      · change (c : ℚ) = x.im.re
        exact hc.symm
      · change (d : ℚ) = x.im.im
        exact hd.symm
  · rintro ⟨z, rfl⟩
    exact order_embedding_integral z

private local instance topOrder_fieldAlgebra :
    Algebra SqrtBiquadraticOrder FieldModel :=
  sqrtBiquadraticEmbedding.toAlgebra

private local instance topOrder_fieldScalarTower :
    IsScalarTower ℤ SqrtBiquadraticOrder FieldModel :=
  IsScalarTower.of_algebraMap_eq' (by
    ext z <;>
      norm_num [sqrtBiquadraticEmbedding,
        QuadraticOrderEmbedding,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])

/-- The displayed order `Z[i][gamma]` is the integral closure of `Z` in the concrete
biquadratic field model. -/
@[reducible] def sqrt_top_closure :
    IsIntegralClosure SqrtBiquadraticOrder ℤ FieldModel where
  algebraMap_injective := sqrt_five_biquadratic
  isIntegral_iff {x} := ringOfIntegers x

private local instance topOrder_integralClosure :
    IsIntegralClosure SqrtBiquadraticOrder ℤ FieldModel :=
  sqrt_top_closure

private local instance topOrder_isDomain : IsDomain SqrtBiquadraticOrder :=
  sqrt_five_biquadratic.isDomain sqrtBiquadraticEmbedding

private local instance topOrder_isDedekindDomain :
    IsDedekindDomain SqrtBiquadraticOrder :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ FieldModel _

private local instance topOrder_moduleFree :
    Module.Free ℤ SqrtBiquadraticOrder :=
  IsIntegralClosure.module_free ℤ ℚ FieldModel _

private local instance topOrder_isNoetherian :
    IsNoetherian ℤ SqrtBiquadraticOrder :=
  IsIntegralClosure.isNoetherian ℤ ℚ FieldModel _

/-- The absolute discriminant of `ℚ(i, √5)` is `400`. -/
theorem sqrt_biquadraticnumber_discr :
    NumberField.discr FieldModel = 400 := by
  let eRing : 𝓞 FieldModel ≃+* SqrtBiquadraticOrder :=
    @NumberField.RingOfIntegers.equiv FieldModel inferInstance
      SqrtBiquadraticOrder inferInstance sqrtBiquadraticEmbedding.toAlgebra
      sqrt_top_closure
  let eAlg : SqrtBiquadraticOrder ≃ₐ[ℤ] 𝓞 FieldModel :=
    AlgEquiv.ofRingEquiv (f := eRing.symm) (fun z => by simp)
  let b' : Module.Basis (Fin 2 × Fin 2) ℤ (𝓞 FieldModel) :=
    orderBasis.map eAlg.toLinearEquiv
  calc
    NumberField.discr FieldModel = Algebra.discr ℤ b' :=
      (NumberField.discr_eq_discr FieldModel b').symm
    _ = Algebra.discr ℤ orderBasis := by
      simpa [b'] using
        (Algebra.discr_eq_discr_of_algEquiv
          (orderBasis : Fin 2 × Fin 2 → SqrtBiquadraticOrder) eAlg).symm
    _ = 400 := order_discr

/-- The absolute degree of the Gaussian quadratic subfield. -/
theorem gaussianField_finrank :
    Module.finrank ℚ SqrtBiquadraticGaussian = 2 :=
  QuadraticAlgebra.finrank_eq_two (-1 : ℚ) 0

/-- The absolute degree of `ℚ(√-5)`. -/
theorem neg_five_finrank :
    Module.finrank ℚ SqrtFiveField = 2 :=
  QuadraticAlgebra.finrank_eq_two (-5 : ℚ) 0

/-- The biquadratic field has absolute degree four. -/
theorem fieldModel_finrank :
    Module.finrank ℚ FieldModel = 4 := by
  calc
    Module.finrank ℚ FieldModel =
        Module.finrank ℚ SqrtBiquadraticGaussian *
          Module.finrank SqrtBiquadraticGaussian FieldModel :=
      (Module.finrank_mul_finrank ℚ SqrtBiquadraticGaussian
        FieldModel).symm
    _ = 2 * 2 := by
      rw [gaussianField_finrank,
        QuadraticAlgebra.finrank_eq_two (1 : SqrtBiquadraticGaussian) 1]
    _ = 4 := by norm_num

/-- The extension `ℚ(i,√5) / ℚ(√-5)` is quadratic. -/
theorem relative_finrank :
    Module.finrank SqrtFiveField FieldModel = 2 := by
  have h := Module.finrank_mul_finrank ℚ SqrtFiveField
    FieldModel
  rw [neg_five_finrank,
    fieldModel_finrank] at h
  omega

/-- The relative different has absolute norm one.  Numerically, the discriminant tower
formula reads `400 = N(D) * 20^2`. -/
theorem different_abs_norm :
    Ideal.absNorm
      (differentIdeal (𝓞 SqrtFiveField)
        (𝓞 FieldModel)) = 1 := by
  have h :=
    NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
      SqrtFiveField (𝓞 SqrtFiveField)
      FieldModel (𝓞 FieldModel)
  rw [sqrt_biquadraticnumber_discr,
    sqrt_discr_twenty,
    relative_finrank] at h
  norm_num at h
  simp [h]

/-- The relative different is the unit ideal. -/
theorem relative_different_top :
    differentIdeal (𝓞 SqrtFiveField)
      (𝓞 FieldModel) = ⊤ :=
  Ideal.absNorm_eq_one_iff.mp different_abs_norm

/-- Every finite prime of `ℚ(i,√5)` is unramified over `ℚ(√-5)`. -/
theorem unramified_finite
    (P : Ideal (𝓞 FieldModel)) [P.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 SqrtFiveField) P := by
  rw [← not_dvd_differentIdeal_iff]
  rw [relative_different_top]
  intro h
  exact Ideal.IsPrime.ne_top (I := P) inferInstance
    (top_unique (Ideal.dvd_iff_le.mp h))

private theorem sqrt_five_complex
    (w : NumberField.InfinitePlace SqrtFiveField) :
    w.IsComplex := by
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  let phi := w.embedding_of_isReal hw
  have homega :
      (QuadraticAlgebra.omega :
        SqrtFiveField) ^ 2 = -5 := by
    apply QuadraticAlgebra.ext <;>
      norm_num [pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  have hsq :
      (phi (QuadraticAlgebra.omega :
        SqrtFiveField)) ^ 2 = (-5 : ℝ) := by
    have h := congrArg phi homega
    simpa only [map_pow, map_neg, map_ofNat] using h
  nlinarith [sq_nonneg
    (phi (QuadraticAlgebra.omega : SqrtFiveField))]

/-- There are no ramified infinite places, since the base field is imaginary quadratic. -/
theorem unramifiedInfinitePlaces :
    IsUnramifiedAtInfinitePlaces SqrtFiveField
      FieldModel :=
  ⟨fun w =>
    NumberField.InfinitePlace.isUnramified_iff.mpr
      (Or.inr (sqrt_five_complex
        (w.comap (algebraMap SqrtFiveField
          FieldModel))))⟩

/-- The order really contains the two displayed generators. -/
theorem generators_mem_order :
    sqrt_biquadratic_i ∈ Set.range sqrtBiquadraticEmbedding ∧
      sqrtFiveBiquadraticgamma ∈ Set.range sqrtBiquadraticEmbedding := by
  constructor
  · refine ⟨⟨⟨0, 1⟩, 0⟩, ?_⟩
    rfl
  · refine ⟨⟨0, 1⟩, ?_⟩
    rfl

/-- The `sqrt(5)` reconstructed from `gamma` belongs to the same order. -/
theorem sqrt_five_order :
    sqrtNegBiquadraticsqrt ∈ Set.range sqrtBiquadraticEmbedding := by
  refine ⟨⟨-1, 2⟩, ?_⟩
  apply QuadraticAlgebra.ext <;>
    apply QuadraticAlgebra.ext <;>
      norm_num [sqrtBiquadraticEmbedding, sqrtNegBiquadraticsqrt,
        sqrtFiveBiquadraticgamma, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticOrderEmbedding, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

/-- The class-number computation required in the last part of Exercise 4-7. -/
theorem sqrt_five_biquadraticsqrt :
    CNOne.negativeQuadraticNumber (-5) (by norm_num) = 2 :=
  negative_quadratic_five

/-- The class number of the concrete quadratic field model is two. -/
theorem sqrt_neg_five :
    NumberField.classNumber SqrtFiveField = 2 := by
  have h := negative_quadratic_five
  change NumberField.classNumber SqrtFiveField = 2 at h
  exact h

/-- A direct specialization of multiplicativity: an unramified step above an index-two step
still has ramification index two.  This is the tower argument Milne uses for both `2` and `5`. -/
theorem ramification_idx_tower
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P.IsMaximal] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hbase : p.ramificationIdx P = 2) (htop : P.ramificationIdx Q = 1) :
    p.ramificationIdx Q = 2 := by
  rw [← ramificationIdx_mul p P Q, hbase, htop]

/-- Conversely, if the base and total ramification indices are both two, multiplicativity forces
the upper step to be unramified.  This is the deduction for
`Q(i,sqrt(5)) / Q(sqrt(-5))`. -/
theorem sqrt_five_biquadratictop
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P.IsMaximal] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hbase : p.ramificationIdx P = 2) (htotal : p.ramificationIdx Q = 2) :
    P.ramificationIdx Q = 1 := by
  have hmul := ramificationIdx_mul p P Q
  rw [hbase, htotal] at hmul
  omega

/-- The same tower calculation in Mathlib's intrinsic unramified-at-prime language. -/
theorem top_unramified
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C]
    [Algebra.EssFiniteType B C] [Module.Finite ℤ B] [CharZero B]
    [Algebra.IsIntegral B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P.IsMaximal] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hQ : Q ≠ ⊥) (hbase : p.ramificationIdx P = 2)
    (htotal : p.ramificationIdx Q = 2) :
    Algebra.IsUnramifiedAt B Q := by
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hQ,
    ← Ideal.over_def Q P]
  exact sqrt_five_biquadratictop p P Q hbase htotal

/-- Every prime of `ℚ(√-5)` above `2` or `5` has ramification index two. -/
private theorem sqrt_five_ramification
    (p : ℕ) (hp : p = 2 ∨ p = 5)
    (P : Ideal (𝓞 SqrtFiveField)) [P.IsPrime]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) P = 2 := by
  have hpPrime : p.Prime := by
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · norm_num
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpIdeal : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hpPrime.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpPrime)
  letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime := hpIdeal
  have hp0 : Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊥ := by
    simp [hpPrime.ne_zero]
  obtain ⟨P₀, hP₀, hram₀⟩ :=
    (discr_ramification_idx
      ℤ (𝓞 SqrtFiveField)
      (NumberField.RingOfIntegers.basis SqrtFiveField) hp0).mp (by
        change NumberField.discr SqrtFiveField ∈
          Ideal.span ({(p : ℤ)} : Set ℤ)
        rw [sqrt_discr_twenty,
          Ideal.mem_span_singleton]
        rcases hp with rfl | rfl <;> norm_num)
  letI : Algebra.IsQuadraticExtension ℚ SqrtFiveField :=
    { finrank_eq_two' := neg_five_finrank }
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ
    SqrtFiveField (𝓞 SqrtFiveField)
  letI : Finite Gal(SqrtFiveField/ℚ) :=
    IsGaloisGroup.finite Gal(SqrtFiveField/ℚ) ℚ
      SqrtFiveField
  letI : IsGaloisGroup Gal(SqrtFiveField/ℚ) ℤ
      (𝓞 SqrtFiveField) :=
    IsGaloisGroup.of_isFractionRing Gal(SqrtFiveField/ℚ) ℤ
      (𝓞 SqrtFiveField) ℚ SqrtFiveField
  letI : P₀.IsPrime := hP₀.1
  letI : P₀.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hP₀.2
  have heq :
      Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) P₀ =
        Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) P :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup
      (Ideal.span ({(p : ℤ)} : Set ℤ)) P₀ P
        Gal(SqrtFiveField/ℚ)
  have hne :
      Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) P ≠ 1 := by
    rwa [heq] at hram₀
  have hle :
      Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) P ≤ 2 := by
    simpa [neg_five_finrank] using
      (Ideal.ramificationIdx_le_finrank
        (S := 𝓞 SqrtFiveField) (K := ℚ)
        (L := SqrtFiveField) P)
  have hne0 :
      Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
  omega

/-- Every prime of `ℚ(i,√5)` above `2` or `5` has ramification index two over `ℚ`. -/
theorem ramification_idx_two
    (p : ℕ) (hp : p = 2 ∨ p = 5)
    (Q : Ideal (𝓞 FieldModel)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) Q = 2 := by
  have hpPrime : p.Prime := by
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · norm_num
  have hp0 : Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊥ := by
    simp [hpPrime.ne_zero]
  let P : Ideal (𝓞 SqrtFiveField) :=
    Q.under (𝓞 SqrtFiveField)
  letI : P.IsPrime :=
    Ideal.IsPrime.under (𝓞 SqrtFiveField) Q
  letI : Q.LiesOver P :=
    Ideal.over_under (A := 𝓞 SqrtFiveField) (P := Q)
  letI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) :=
    Ideal.under_liesOver_of_liesOver (𝓞 SqrtFiveField)
      (𝔓 := Q) (p := Ideal.span ({(p : ℤ)} : Set ℤ))
  letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hpPrime.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpPrime)).isMaximal hp0
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  letI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP0
  have hbase := sqrt_five_ramification p hp P
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
  have htop : Ideal.ramificationIdx P Q = 1 := by
    change Ideal.ramificationIdx
      (Q.under (𝓞 SqrtFiveField)) Q = 1
    exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hQ0).mp
      (unramified_finite Q)
  exact ramification_idx_tower
    (Ideal.span ({(p : ℤ)} : Set ℤ)) P Q hbase htop

/-- Once the discriminant calculation shows that every ramified rational prime divides `10`,
primality leaves only `2` and `5`. -/
theorem only_five_ramify
    (Ramifies : ℕ → Prop)
    (hdisc : ∀ p, Nat.Prime p → Ramifies p → p ∣ 10) :
    ∀ p, Nat.Prime p → Ramifies p → p = 2 ∨ p = 5 := by
  intro p hp hram
  have hdvd := hdisc p hp hram
  have hten : (10 : ℕ) = 2 * 5 := by norm_num
  rw [hten] at hdvd
  rcases hp.dvd_mul.mp hdvd with htwo | hfive
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp htwo)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hfive)

/-- In the concrete biquadratic field, a ramified rational prime is `2` or `5`. -/
theorem ramified_or_five
    {p : ℕ} [Fact p.Prime]
    (P : Ideal (𝓞 FieldModel)) [P.IsPrime]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (hram :
      Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) P ≠ 1) :
    p = 2 ∨ p = 5 := by
  have hp0 : Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊥ := by
    simp [NeZero.ne p]
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have hramUnder : Ideal.ramificationIdx (P.under ℤ) P ≠ 1 := by
    rw [← Ideal.over_def P (Ideal.span ({(p : ℤ)} : Set ℤ))]
    exact hram
  have hdvd : P ∣ differentIdeal ℤ (𝓞 FieldModel) :=
    (ramifies_dvd_different ℤ
      (𝓞 FieldModel) P hP0).mp hramUnder
  have hdiscP :
      algebraMap ℤ (𝓞 FieldModel)
        (NumberField.discr FieldModel) ∈ P :=
    Ideal.dvd_iff_le.mp hdvd
      (NumberField.discr_mem_differentIdeal FieldModel _)
  have hdiscBase :
      NumberField.discr FieldModel ∈
        Ideal.span ({(p : ℤ)} : Set ℤ) :=
    (Ideal.mem_of_liesOver P (Ideal.span ({(p : ℤ)} : Set ℤ)) _).mpr hdiscP
  rw [sqrt_biquadraticnumber_discr, Ideal.mem_span_singleton] at hdiscBase
  have hp400 : p ∣ 400 := Int.natCast_dvd_natCast.mp hdiscBase
  have hp20 : p ∣ 20 := by
    have hpPow : p ∣ 20 ^ 2 := by
      norm_num
      exact hp400
    exact (show Nat.Prime p from Fact.out).dvd_of_dvd_pow hpPow
  have hpFactor : p ∣ 2 ^ 2 * 5 := by
    simpa using hp20
  rcases (show Nat.Prime p from Fact.out).dvd_mul.mp hpFactor with htwoSq | hfive
  · have htwo : p ∣ 2 :=
      (show Nat.Prime p from Fact.out).dvd_of_dvd_pow htwoSq
    exact Or.inl
      ((Nat.prime_dvd_prime_iff_eq (show Nat.Prime p from Fact.out)
        Nat.prime_two).mp htwo)
  · exact Or.inr
      ((Nat.prime_dvd_prime_iff_eq (show Nat.Prime p from Fact.out)
        (by norm_num)).mp hfive)

private theorem rational_prime_ramifies
    (p : ℕ) (hp : p = 2 ∨ p = 5) :
    ∃ P ∈ Ideal.primesOver (Ideal.span ({(p : ℤ)} : Set ℤ))
        (𝓞 FieldModel),
      Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) P ≠ 1 := by
  have hpPrime : p.Prime := by
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · norm_num
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpIdeal :
      (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hpPrime.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpPrime)
  letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime := hpIdeal
  apply (discr_ramification_idx
    ℤ (𝓞 FieldModel)
    (NumberField.RingOfIntegers.basis FieldModel)
    (by simp [hpPrime.ne_zero])).mp
  change NumberField.discr FieldModel ∈
    Ideal.span ({(p : ℤ)} : Set ℤ)
  rw [sqrt_biquadraticnumber_discr, Ideal.mem_span_singleton]
  rcases hp with rfl | rfl <;> norm_num

/-- The rational prime `2` ramifies in `ℚ(i,√5)`. -/
theorem two_ramifies :
    ∃ P ∈ Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
        (𝓞 FieldModel),
      Ideal.ramificationIdx (Ideal.span ({(2 : ℤ)} : Set ℤ)) P ≠ 1 :=
  rational_prime_ramifies 2 (Or.inl rfl)

/-- The rational prime `5` ramifies in `ℚ(i,√5)`. -/
theorem five_ramifies :
    ∃ P ∈ Ideal.primesOver (Ideal.span ({(5 : ℤ)} : Set ℤ))
        (𝓞 FieldModel),
      Ideal.ramificationIdx (Ideal.span ({(5 : ℤ)} : Set ℤ)) P ≠ 1 :=
  rational_prime_ramifies 5 (Or.inr rfl)

/-- The finite and infinite unramified conditions used in the defining characterization of a
Hilbert class field. -/
def EverywhereUnramified
    (k K : Type*) [Field k] [Field K] [NumberField k] [NumberField K]
    [Algebra k K] : Prop :=
  (∀ (P : Ideal (𝓞 K)) (_ : P.IsPrime), P ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 k) P) ∧
    IsUnramifiedAtInfinitePlaces k K

/-- The numerical and unramified properties used before invoking the class-field-theoretic
identification in Remark 4.11.  This is not a definition of a Hilbert class field. -/
def NumericalUnramifiedCriterion
    (k K : Type*) [Field k] [Field K] [NumberField k] [NumberField K]
    [Algebra k K] : Prop :=
  IsAbelianGalois k K ∧
    Module.finrank k K = NumberField.classNumber k ∧
    EverywhereUnramified k K

/-- The concrete extension is unramified at every finite and infinite prime. -/
theorem everywhereUnramified :
    EverywhereUnramified SqrtFiveField
      FieldModel := by
  constructor
  · intro P hP _
    letI : P.IsPrime := hP
    exact unramified_finite P
  · exact unramifiedInfinitePlaces

/-- The concrete quadratic extension is abelian Galois. -/
theorem sqrtBiquadraticisAbelian :
    IsAbelianGalois SqrtFiveField FieldModel := by
  letI : Algebra.IsQuadraticExtension SqrtFiveField
      FieldModel :=
    { finrank_eq_two' := relative_finrank }
  exact IsAbelianGalois.of_isCyclic
    SqrtFiveField FieldModel

/-- A degree-two, everywhere-unramified abelian extension of a class-number-two field satisfies
the numerical criterion.  Identifying it with the Hilbert class field still uses Remark 4.11. -/
theorem numerical_unramified_criterion
    {k K : Type*} [Field k] [Field K] [NumberField k] [NumberField K]
    [Algebra k K]
    (habelian : IsAbelianGalois k K)
    (hclass : NumberField.classNumber k = 2)
    (hdegree : Module.finrank k K = 2)
    (hunramified : EverywhereUnramified k K) :
    NumericalUnramifiedCriterion k K := by
  exact ⟨habelian, hdegree.trans hclass.symm, hunramified⟩

/-- Exercise 4-7, with the class-field-theoretic final identification kept
separate: `Q(i, sqrt(5)) / Q(sqrt(-5))` is an everywhere-unramified abelian
extension whose degree is the class number of the base field. -/
theorem numericalUnramifiedCriterion :
    NumericalUnramifiedCriterion
      SqrtFiveField FieldModel := by
  apply numerical_unramified_criterion
  · exact sqrtBiquadraticisAbelian
  · exact sqrt_neg_five
  · exact relative_finrank
  · exact everywhereUnramified

end

end Submission.NumberTheory.Milne
