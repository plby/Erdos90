import Towers.NumberTheory.Quadratic.QuadraticUnitExamples
import Towers.NumberTheory.Quadratic.FieldFormSetup

/-!
# Roots of unity in imaginary quadratic fields

This file assembles the final roots-of-unity classification in Milne's
Example 5.3.  We use the fixed coordinate field `QFModel d`, since
the informal phrase "except `Q(i)` and `Q(sqrt(-3))`" compares fields of
different Lean types.  The two exceptional coordinate models are stated
separately.
-/

namespace Towers.NumberTheory.Milne

open Towers.NumberTheory
open scoped NumberField

noncomputable section

/-- The zero-linear-term quadratic order is the usual `Z[sqrt d]` model. -/
def quadraticOrderZsqrtd (d : ℤ) :
    QOrd d 0 ≃+* ℤ√d where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

private theorem standard_or_neg
    {d : ℤ} (hdneg : d < 0) (hdNegOne : d ≠ -1)
    (hdNegThree : d ≠ -3)
    (z : QOrd (quadraticOrderParameter d)
      (quadraticParameterB d)) (hz : IsUnit z) :
    z = 1 ∨ z = -1 := by
  by_cases hmod : d % 4 = 1
  · have hdiv : 4 ∣ d - 1 := Int.dvd_iff_emod_eq_zero.mpr (by omega)
    have hmul : 4 * ((d - 1) / 4) = d - 1 := by
      simpa [mul_comm] using Int.ediv_mul_cancel hdiv
    have hAneg : (d - 1) / 4 < 0 := by omega
    have hAne : (d - 1) / 4 ≠ -1 := by
      intro h
      rw [h] at hmul
      exact hdNegThree (by omega)
    have hA : quadraticOrderParameter d ≤ -2 := by
      simp only [quadraticOrderParameter, if_pos hmod]
      omega
    have hz' : IsUnit
        (⟨z.re, z.im⟩ : QuadraticAlgebra ℤ (quadraticOrderParameter d) 1) := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit] at hz ⊢
      change IsUnit (z.re * z.re + quadraticParameterB d * z.re * z.im -
        quadraticOrderParameter d * z.im * z.im) at hz
      change IsUnit (z.re * z.re + 1 * z.re * z.im -
        quadraticOrderParameter d * z.im * z.im)
      simpa [quadraticParameterB, hmod] using hz
    rcases (half_quadratic_neg hA).mp hz' with
      ⟨hn, hm | hm⟩
    · left
      apply QuadraticAlgebra.ext <;>
        simp [hm, hn, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    · right
      apply QuadraticAlgebra.ext <;>
        simp [hm, hn, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · have hd : d ≤ -2 := by omega
    have hz' : IsUnit (⟨z.re, z.im⟩ : ℤ√d) := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit] at hz
      rw [Zsqrtd.isUnit_iff_norm_isUnit (⟨z.re, z.im⟩ : ℤ√d)]
      change IsUnit (z.re * z.re + quadraticParameterB d * z.re * z.im -
        quadraticOrderParameter d * z.im * z.im) at hz
      change IsUnit (z.re * z.re - d * z.im * z.im)
      simpa [quadraticOrderParameter, quadraticParameterB, hmod] using hz
    rcases (zsqrtd_neg_two hd).mp hz' with ⟨hn, hm | hm⟩
    · left
      apply QuadraticAlgebra.ext <;>
        simp [hm, hn, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    · right
      apply QuadraticAlgebra.ext <;>
        simp [hm, hn, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- **Milne, Example 5.3, assembled field-level form.** For a squarefree
negative radicand other than `-1` and `-3`, the roots of unity in the full
ring of integers of `Q(sqrt d)` are exactly `1` and `-1`. -/
theorem imaginary_roots_unity
    {d : ℤ} (hd : Squarefree d) (hdneg : d < 0)
    (hdNegOne : d ≠ -1) (hdNegThree : d ≠ -3) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd (by omega)
    letI : Module.Finite ℚ (QFModel d) :=
      quadraticModuleFinite hd (by omega)
    letI : NumberField (QFModel d) :=
      quadraticFieldNumber hd (by omega)
    {ζ : NumberField.RingOfIntegers (QFModel d) |
      IsOfFinOrder ζ} = {1, -1} := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd (by omega)
  letI : Module.Finite ℚ (QFModel d) :=
    quadraticModuleFinite hd (by omega)
  letI : NumberField (QFModel d) :=
    quadraticFieldNumber hd (by omega)
  let e := integersQuadraticOrder hd (by omega : d ≠ 1)
  ext ζ
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hζ
    have hefin : IsOfFinOrder (e ζ) :=
      (Function.Injective.isOfFinOrder_iff
        (f := e.toMonoidHom) e.injective).mpr hζ
    rcases standard_or_neg hdneg hdNegOne
        hdNegThree (e ζ) hefin.isUnit with h | h
    · left
      apply e.injective
      simpa using h
    · right
      apply e.injective
      simpa using h
  · rintro (rfl | rfl)
    · rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨1, by norm_num, by simp⟩
    · rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨2, by norm_num, by simp⟩

local instance sqrtNegOneNonsquareFact :
    Fact (∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + 0 * r) :=
  ⟨fun r h => by norm_num at h; nlinarith [sq_nonneg r]⟩

local instance sqrtNegOneField : Field (QFModel (-1)) :=
  @QuadraticAlgebra.instField ℚ inferInstance (-1) 0 sqrtNegOneNonsquareFact

local instance sqrtNegOneAlgebra : Algebra ℚ (QFModel (-1)) :=
  @QuadraticAlgebra.instAlgebra ℚ ℚ (-1) 0 inferInstance inferInstance inferInstance

local instance sqrtNegOneModuleFinite :
    Module.Finite ℚ (QFModel (-1)) :=
  Module.Finite.of_basis (QuadraticAlgebra.basis (-1) 0)

local instance sqrtNegOneNumberField : NumberField (QFModel (-1)) :=
  quadraticFieldNumber (d := (-1 : ℤ)) (by norm_num) (by norm_num)

/-- The maximal order of the coordinate model of `Q(i)`, identified with the
Gaussian order. -/
def sqrtRingIntegers :
    NumberField.RingOfIntegers (QFModel (-1)) ≃+* ℤ√(-1) :=
  (integersQuadraticOrder (d := (-1 : ℤ))
    (by norm_num) (by norm_num)).trans (quadraticOrderZsqrtd (-1))

/-- **Milne, Example 5.3, Gaussian exception.** The roots of unity in the
coordinate model of `Q(i)` are the four elements `±1, ±i`. -/
theorem sqrt_neg_model (ζ :
    NumberField.RingOfIntegers (QFModel (-1))) :
    IsOfFinOrder ζ ↔
      let z := sqrtRingIntegers ζ
      (z.re = 1 ∧ z.im = 0) ∨ (z.re = -1 ∧ z.im = 0) ∨
        (z.re = 0 ∧ z.im = 1) ∨ (z.re = 0 ∧ z.im = -1) := by
  let e := sqrtRingIntegers
  rw [← (Function.Injective.isOfFinOrder_iff
    (f := e.toMonoidHom) e.injective)]
  exact gaussian_quadratic_fin (e ζ).re (e ζ).im

private theorem squarefree_neg_three : Squarefree (-3 : ℤ) := by
  rw [← Int.squarefree_natAbs]
  norm_num
  exact Nat.prime_three.squarefree

local instance sqrtNegThreeNonsquareFact :
    Fact (∀ r : ℚ, r ^ 2 ≠ (-3 : ℚ) + 0 * r) :=
  ⟨fun r h => by norm_num at h; nlinarith [sq_nonneg r]⟩

local instance sqrtNegThreeField : Field (QFModel (-3)) :=
  @QuadraticAlgebra.instField ℚ inferInstance (-3) 0 sqrtNegThreeNonsquareFact

local instance sqrtNegThreeAlgebra : Algebra ℚ (QFModel (-3)) :=
  @QuadraticAlgebra.instAlgebra ℚ ℚ (-3) 0 inferInstance inferInstance inferInstance

local instance sqrtNegThreeModuleFinite :
    Module.Finite ℚ (QFModel (-3)) :=
  Module.Finite.of_basis (QuadraticAlgebra.basis (-3) 0)

local instance sqrtNegThreeNumberField : NumberField (QFModel (-3)) :=
  quadraticFieldNumber (d := (-3 : ℤ)) squarefree_neg_three (by norm_num)

/-- The maximal order of the coordinate model of `Q(sqrt(-3))`. -/
def sqrtNegIntegers :
    NumberField.RingOfIntegers (QFModel (-3)) ≃+*
      QOrd (-1) 1 := by
  simpa [quadraticOrderParameter, quadraticParameterB] using
    (integersQuadraticOrder (d := (-3 : ℤ))
      squarefree_neg_three (by norm_num))

/-- **Milne, Example 5.3, Eisenstein exception.** The roots of unity in the
coordinate model of `Q(sqrt(-3))` are its six standard units. -/
theorem sqrt_model_order (ζ :
    NumberField.RingOfIntegers (QFModel (-3))) :
    IsOfFinOrder ζ ↔
      let z := sqrtNegIntegers ζ
      (z.re = 1 ∧ z.im = 0) ∨ (z.re = -1 ∧ z.im = 0) ∨
        (z.re = 0 ∧ z.im = 1) ∨ (z.re = 0 ∧ z.im = -1) ∨
          (z.re = -1 ∧ z.im = 1) ∨ (z.re = 1 ∧ z.im = -1) := by
  let e := sqrtNegIntegers
  rw [← (Function.Injective.isOfFinOrder_iff
    (f := e.toMonoidHom) e.injective)]
  exact sqrt_neg_fin (e ζ).re (e ζ).im

end

end Towers.NumberTheory.Milne
