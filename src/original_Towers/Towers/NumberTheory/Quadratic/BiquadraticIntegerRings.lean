import Towers.NumberTheory.Quadratic.QuadraticIntegerRings

/-!
# Milne, Chapter 3, Exercise 2

The coordinate model `QuadraticAlgebra ℚ m 0` represents `ℚ[√m]`, and
`QuadraticAlgebra ℤ m 0` represents its evident integral order.  For `m = 3, 7`, the
quadratic integrality criterion shows that this order contains every algebraic integer.

For the biquadratic compositum, we use a nested quadratic algebra.  The element
`(√3 + √7) / 2` has half-integral coordinates, so it does not lie in the evident order, but it
is integral because it satisfies `X⁴ - 5X² + 1`.
-/

namespace Towers.NumberTheory.Milne

open Polynomial
open Towers.NumberTheory

noncomputable section

/-- The evident order `ℤ[√m]` in the coordinate model of `ℚ[√m]`. -/
abbrev ExplicitQuadraticOrder (m : ℤ) := QuadraticAlgebra ℤ m 0

/-- The coordinatewise embedding `ℤ[√m] → ℚ[√m]`. -/
def QuadraticOrderEmbedding (m : ℤ) :
    ExplicitQuadraticOrder m →+* QFModel m where
  toFun z := ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> norm_num
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

theorem quadratic_order_injective (m : ℤ) :
    Function.Injective (QuadraticOrderEmbedding m) := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.re hxy)
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.im hxy)

private theorem integral_quadratic_order
    (m : ℤ) (hm : Squarefree m) (hm1 : m % 4 ≠ 1)
    (x : QFModel m) :
    IsIntegral ℤ x ↔
      ∃ z : ExplicitQuadraticOrder m,
        QuadraticOrderEmbedding m z = x := by
  rw [QFModel.integral_integer_coordinates m hm hm1]
  constructor
  · rintro ⟨a, b, ha, hb⟩
    refine ⟨⟨a, b⟩, ?_⟩
    apply QuadraticAlgebra.ext
    · exact ha.symm
    · exact hb.symm
  · rintro ⟨z, rfl⟩
    exact ⟨z.re, z.im, rfl, rfl⟩

/-- Every algebraic integer in `ℚ[√3]` lies in `ℤ[√3]`. -/
theorem sqrt_ring_integers (x : QFModel 3) :
    IsIntegral ℤ x ↔
      ∃ z : ExplicitQuadraticOrder 3,
        QuadraticOrderEmbedding 3 z = x := by
  exact integral_quadratic_order 3 (by norm_num) (by norm_num) x

/-- Every algebraic integer in `ℚ[√7]` lies in `ℤ[√7]`. -/
theorem sqrt_seven_integers (x : QFModel 7) :
    IsIntegral ℤ x ↔
      ∃ z : ExplicitQuadraticOrder 7,
        QuadraticOrderEmbedding 7 z = x := by
  exact integral_quadratic_order 7 (by norm_num) (by norm_num) x

/-- The evident order `ℤ[√3, √7]`, represented as a nested quadratic algebra. -/
abbrev BiquadraticOrder :=
  QuadraticAlgebra (ExplicitQuadraticOrder 3)
    (7 : ExplicitQuadraticOrder 3) 0

/-- The corresponding rational biquadratic algebra `ℚ[√3, √7]`. -/
abbrev BiquadraticAlgebra :=
  QuadraticAlgebra (QFModel 3) (7 : QFModel 3) 0

/-- The coordinatewise embedding of the evident biquadratic order. -/
def BiquadraticOrderEmbedding :
    BiquadraticOrder →+* BiquadraticAlgebra where
  toFun z :=
    ⟨QuadraticOrderEmbedding 3 z.re,
      QuadraticOrderEmbedding 3 z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by
    apply QuadraticAlgebra.ext
    · exact map_one (QuadraticOrderEmbedding 3)
    · exact map_zero (QuadraticOrderEmbedding 3)
  map_add' x y := by apply QuadraticAlgebra.ext <;> simp
  map_mul' x y := by
    apply QuadraticAlgebra.ext <;>
      apply QuadraticAlgebra.ext <;>
        simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
          QuadraticOrderEmbedding,
          QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

theorem biquadratic_embedding_injective :
    Function.Injective BiquadraticOrderEmbedding := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · exact quadratic_order_injective 3
      (congrArg QuadraticAlgebra.re hxy)
  · exact quadratic_order_injective 3
      (congrArg QuadraticAlgebra.im hxy)

/-- Milne's element `(√3 + √7) / 2` in nested quadratic coordinates. -/
def BiquadraticIntegralWitness : BiquadraticAlgebra :=
  ⟨⟨0, 1 / 2⟩, ⟨1 / 2, 0⟩⟩

/-- The monic polynomial `X⁴ - 5X² + 1` satisfied by the witness. -/
def BiquadraticWitnessPolynomial : ℤ[X] :=
  X ^ 4 - 5 * X ^ 2 + 1

theorem biquadratic_witness_monic :
    BiquadraticWitnessPolynomial.Monic := by
  rw [show BiquadraticWitnessPolynomial =
      X ^ 4 + (-5 * X ^ 2 + 1) by
      simp only [BiquadraticWitnessPolynomial]
      ring]
  apply monic_X_pow_add
  compute_degree
  norm_num

/-- The half-integral witness satisfies `X⁴ - 5X² + 1`. -/
theorem BiquadraticWitness_aeval :
    Polynomial.aeval BiquadraticIntegralWitness
      BiquadraticWitnessPolynomial = 0 := by
  simp only [BiquadraticWitnessPolynomial, map_add, map_sub, map_mul,
    map_pow, aeval_X, map_ofNat]
  apply QuadraticAlgebra.ext <;>
    norm_num [BiquadraticIntegralWitness, pow_succ,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    apply QuadraticAlgebra.ext <;>
      norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

theorem biquadratic_witness_integral :
    IsIntegral ℤ BiquadraticIntegralWitness :=
  ⟨BiquadraticWitnessPolynomial,
    biquadratic_witness_monic,
    BiquadraticWitness_aeval⟩

/-- The witness is not in `ℤ[√3, √7]`: its `√7` coefficient has real coordinate `1/2`. -/
theorem biquadratic_witness_order :
    BiquadraticIntegralWitness ∉
      Set.range BiquadraticOrderEmbedding := by
  rintro ⟨z, hz⟩
  have him := congrArg QuadraticAlgebra.im hz
  have hre := congrArg QuadraticAlgebra.re him
  change ((z.im.re : ℤ) : ℚ) = 1 / 2 at hre
  have htwo : (2 : ℚ) * (z.im.re : ℚ) = 1 := by
    rw [hre]
    norm_num
  have htwoZ : 2 * z.im.re = 1 := by
    exact_mod_cast htwo
  omega

/-- The evident order misses an algebraic integer, so it is not the full ring of integers. -/
theorem biquadratic_not_full :
    ∃ x : BiquadraticAlgebra,
      IsIntegral ℤ x ∧ x ∉ Set.range BiquadraticOrderEmbedding :=
  ⟨BiquadraticIntegralWitness,
    biquadratic_witness_integral,
    biquadratic_witness_order⟩

end


end Towers.NumberTheory.Milne
