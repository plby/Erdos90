import Submission.NumberTheory.Quadratic.ProperPrimitiveClasses
import Submission.NumberTheory.ClassGroup.NarrowClassGroup
import Submission.NumberTheory.Quadratic.IntegralElements
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.PicardGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-!
# Theorem 4.29 for the Gaussian field

This file proves the corrected form-side classification for discriminant `-4`:
every positive primitive form of discriminant `-4` is properly equivalent to
`X² + Y²`.  Together with principality of the Gaussian integers, this gives the
Gaussian specialization of Theorem 4.29 as an equivalence of singleton types.
-/

namespace Submission.NumberTheory.Milne

open CommRing NumberField
open scoped MatrixGroups NumberField

namespace BQForm

private theorem exists_centered_shear (a b : ℤ) (ha : 0 < a) :
    ∃ q : ℤ, |b + 2 * a * q| ≤ a := by
  let m : ℤ := 2 * a
  let r : ℤ := b % m
  let d : ℤ := b / m
  have hm : 0 < m := by dsimp [m]; omega
  have hr0 : 0 ≤ r := Int.emod_nonneg b (ne_of_gt hm)
  have hrm : r < m := Int.emod_lt_of_pos b hm
  have hdecomp : r + m * d = b := by
    simpa [r, d, m, mul_comm] using Int.emod_add_ediv_mul b m
  by_cases hra : r ≤ a
  · refine ⟨-d, ?_⟩
    have heq : b + 2 * a * (-d) = r := by
      rw [← hdecomp]
      dsimp [m]
      ring
    rw [heq, abs_of_nonneg hr0]
    exact hra
  · refine ⟨-d - 1, ?_⟩
    have heq : b + 2 * a * (-d - 1) = r - m := by
      rw [← hdecomp]
      ring
    rw [heq, abs_of_nonpos (by omega : r - m ≤ 0)]
    dsimp [m] at hrm ⊢
    omega

/-- Every positive primitive form of discriminant `-4` is properly equivalent
to the Gaussian norm form `X² + Y²`. -/
theorem gaussian_proper_primitive
    (Q : BQForm)
    (hQ : ProperDiscriminant (-4) Q) :
    gaussianPositiveForm.Equivalent Q := by
  have hpositive : Q.IsPositiveDefinite := hQ.2.2 (by norm_num)
  obtain ⟨q, hq⟩ := exists_centered_shear Q.a Q.b hpositive.1
  let g : SL(2, ℤ) := ModularGroup.T ^ q
  let Q' : BQForm := Q.transform g
  have hQQ' : Q.Equivalent Q' := ⟨g, rfl⟩
  have ha' : Q'.a = Q.a := by
    simp [Q', g, transform, ModularGroup.coe_T_zpow]
  have hb' : Q'.b = Q.b + 2 * Q.a * q := by
    simp [Q', g, transform, ModularGroup.coe_T_zpow]
    ring
  have hdisc' : Q'.discriminant = -4 := by
    rw [discriminant_transform]
    exact hQ.1
  have hpositive' : Q'.IsPositiveDefinite :=
    definite_transform Q g hpositive
  have hc' : 0 < Q'.c := by
    have := pos_positive_definite hpositive'
      (x := 0) (y := 1) (Or.inr one_ne_zero)
    simpa [eval] using this
  have hb_le : |Q'.b| ≤ Q'.a := by
    rw [ha', hb']
    exact hq
  by_cases hca : Q'.c < Q'.a
  · let Q'' : BQForm := Q'.transform ModularGroup.S
    have hQ'Q'' : Q'.Equivalent Q'' := ⟨ModularGroup.S, rfl⟩
    have ha'' : Q''.a = Q'.c := by
      simp [Q'', transform, ModularGroup.S, Matrix.cons_val_zero,
        Matrix.cons_val_one]
    have hproper' : ProperDiscriminant (-4) Q' :=
      (proper_discr_equiv hQQ').mp hQ
    have hproper'' : ProperDiscriminant (-4) Q'' :=
      (proper_discr_equiv hQ'Q'').mp hproper'
    have hrec := gaussian_proper_primitive Q'' hproper''
    exact equivalent_trans hrec
      (equivalent_trans (equivalent_symm hQ'Q'') (equivalent_symm hQQ'))
  · have hac : Q'.a ≤ Q'.c := le_of_not_gt hca
    have ha_pos : 0 < Q'.a := hpositive'.1
    have hb_sq_le : Q'.b ^ 2 ≤ Q'.a ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg Q'.b) ha_pos.le).mpr hb_le
    have hdisc_eq : Q'.b ^ 2 - 4 * Q'.a * Q'.c = -4 := hdisc'
    have ha_one : Q'.a = 1 := by
      nlinarith [sq_nonneg (Q'.a - 1)]
    have hb_bounds : -1 ≤ Q'.b ∧ Q'.b ≤ 1 := by
      rw [ha_one] at hb_le
      exact abs_le.mp hb_le
    have hb_zero : Q'.b = 0 := by
      rcases hb_bounds with ⟨hl, hu⟩
      rw [ha_one] at hdisc_eq
      interval_cases Q'.b <;> omega
    have hc_one : Q'.c = 1 := by
      rw [ha_one, hb_zero] at hdisc_eq
      norm_num at hdisc_eq ⊢
      omega
    have hQ'eq : Q' = gaussianPositiveForm := by
      ext <;> simp [ha_one, hb_zero, hc_one, gaussianPositiveForm]
    rw [← hQ'eq]
    exact equivalent_symm hQQ'
termination_by Q.a.natAbs
decreasing_by
  rw [ha'']
  apply Int.natAbs_lt_natAbs_of_nonneg_of_lt hc'.le
  rw [← ha']
  exact hca

/-- The corrected proper form-class type of discriminant `-4` is a singleton. -/
noncomputable instance gaussianProperUnique :
    Unique (ProperPrimitDiscri (-4)) where
  default := Quotient.mk''
    (⟨gaussianPositiveForm,
      proper_primi_discr⟩ :
      ProperPrimitive (-4))
  uniq C := by
    refine Quotient.inductionOn C ?_
    intro Q
    apply Quotient.sound
    exact equivalent_symm
      (gaussian_proper_primitive Q.1 Q.2)

end BQForm

/-- The Gaussian specialization of the corrected Theorem 4.29.  Both the
Gaussian ideal class group and the positive proper form-class type of
discriminant `-4` have one element. -/
noncomputable def gaussian :
    ClassGroup GaussianInt ≃
      BQForm.ProperPrimitDiscri (-4) := by
  letI : Subsingleton (ClassGroup GaussianInt) :=
    Fintype.card_le_one_iff_subsingleton.mp
      (card_classGroup_eq_one (R := GaussianInt)).le
  letI : Unique (ClassGroup GaussianInt) := uniqueOfSubsingleton 1
  exact Equiv.ofUnique _ _

private theorem neg_rat_square :
    ∀ r : ℚ, r ^ 2 ≠ ((-1 : ℤ) : ℚ) + 0 * r := by
  intro r hr
  norm_num at hr
  nlinarith [sq_nonneg r]

private local instance : Fact
    (∀ r : ℚ, r ^ 2 ≠ ((-1 : ℤ) : ℚ) + 0 * r) :=
  ⟨neg_rat_square⟩

private local instance : Module.Finite ℚ (QFModel (-1)) :=
  Module.Finite.of_basis (QuadraticAlgebra.basis (-1 : ℚ) 0)

private local instance : NumberField (QFModel (-1)) := by
  exact NumberField.of_module_finite ℚ (QFModel (-1))

private abbrev GaussianOrder429 := QuadraticAlgebra ℤ (-1) 0

private def gaussianInt429 : GaussianInt ≃+* GaussianOrder429 where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_mul' x y := by ext <;> simp

private def gaussianEmbedding429 :
    GaussianOrder429 →+* QFModel (-1) where
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

private theorem gaussian_429_injective :
    Function.Injective gaussianEmbedding429 := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.re hxy)
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.im hxy)

private local instance : Algebra GaussianOrder429 (QFModel (-1)) :=
  gaussianEmbedding429.toAlgebra

private local instance : IsScalarTower ℤ GaussianOrder429 (QFModel (-1)) :=
  IsScalarTower.of_algebraMap_eq' rfl

@[reducible] private def gaussian429Closure :
    IsIntegralClosure GaussianOrder429 ℤ (QFModel (-1)) where
  algebraMap_injective := gaussian_429_injective
  isIntegral_iff {x} := by
    rw [QFModel.gaussian_integer_coordinates]
    constructor
    · rintro ⟨a, b, ha, hb⟩
      refine ⟨(⟨a, b⟩ : GaussianOrder429), ?_⟩
      change gaussianEmbedding429 (⟨a, b⟩ : GaussianOrder429) = x
      apply QuadraticAlgebra.ext
      · exact ha.symm
      · exact hb.symm
    · rintro ⟨y, rfl⟩
      exact ⟨y.re, y.im, rfl, rfl⟩

private local instance :
    IsIntegralClosure GaussianOrder429 ℤ (QFModel (-1)) :=
  gaussian429Closure

/-- The ring of integers in the coordinate model of `ℚ(i)` is the Gaussian integers. -/
private noncomputable def integersGaussian429 :
    NumberField.RingOfIntegers (QFModel (-1)) ≃+* GaussianInt :=
  (@NumberField.RingOfIntegers.equiv (QFModel (-1)) inferInstance
      GaussianOrder429 inferInstance gaussianEmbedding429.toAlgebra
      gaussian429Closure).trans
    gaussianInt429.symm

private theorem gaussian_no_embedding :
    IsEmpty (QFModel (-1) →+* ℝ) := by
  constructor
  intro φ
  let i : QFModel (-1) := ⟨0, 1⟩
  have hi : i * i = -1 := by
    apply QuadraticAlgebra.ext <;>
      norm_num [i, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hφ : φ i * φ i = -(1 : ℝ) := by
    calc
      φ i * φ i = φ (i * i) := (map_mul φ i i).symm
      _ = φ (-1) := congrArg φ hi
      _ = -(1 : ℝ) := by simp
  nlinarith [sq_nonneg (φ i)]

private local instance : IsEmpty (QFModel (-1) →+* ℝ) :=
  gaussian_no_embedding

private noncomputable def picardRing429
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) : Pic A ≃* Pic B where
  toFun := Pic.mapRingHom e.toRingHom
  invFun := Pic.mapRingHom e.symm.toRingHom
  left_inv x := by
    rw [Pic.mapRingHom_mapRingHom]
    convert Pic.mapRingHom_id_apply
    ext r
    simp
  right_inv x := by
    rw [Pic.mapRingHom_mapRingHom]
    convert Pic.mapRingHom_id_apply
    ext r
    simp
  map_mul' := map_mul (Pic.mapRingHom e.toRingHom)

private noncomputable def classRing429
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    (e : A ≃+* B) : ClassGroup A ≃* ClassGroup B :=
  (ClassGroup.equivPic A).trans
    ((picardRing429 e).trans (ClassGroup.equivPic B).symm)

/-- The corrected Gaussian case of Theorem 4.29 with the actual narrow class
group of `ℚ(i)` as its source. -/
noncomputable def gaussian_narrow :
    NCGroup (QFModel (-1)) ≃
      BQForm.ProperPrimitDiscri (-4) :=
  (narrowClassEquiv (QFModel (-1))).toEquiv.trans
    ((classRing429 integersGaussian429).toEquiv.trans
      gaussian)

end Submission.NumberTheory.Milne
