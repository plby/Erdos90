import Submission.NumberTheory.Quadratic.OrientedBasisExistence
import Submission.NumberTheory.Quadratic.PositiveLeadingCoefficient
import Submission.NumberTheory.Quadratic.IdealFormMap

/-!
# Positive-leading oriented bases of quadratic ideals

Every nonzero integral ideal in the squarefree quadratic model admits a positively oriented
basis.  Starting with such a basis, an `SL(2, Z)` change of variables can make the leading
coefficient of its normalized norm form positive.  Applying the same matrix to the basis
preserves its positive orientation and realizes exactly that transformed form.
-/

namespace Submission.NumberTheory.Milne

open Submission.NumberTheory
open Module
open scoped MatrixGroups NumberField

noncomputable section

namespace INForm

variable {K : Type*} [Field K]

/-- Apply an `SL(2, Z)` matrix to the columns of an ordered ideal basis. -/
def properTransformBasis {I : Ideal (𝓞 K)} (b : Basis (Fin 2) ℤ I)
    (g : SL(2, ℤ)) : Basis (Fin 2) ℤ I :=
  b.map (b.equivFun |>.trans ((Matrix.SpecialLinearGroup.toLin') g) |>.trans b.equivFun.symm)

@[simp]
theorem proper_transform_basis {I : Ideal (𝓞 K)} (b : Basis (Fin 2) ℤ I)
    (g : SL(2, ℤ)) (j : Fin 2) :
    properTransformBasis b g j = g 0 j • b 0 + g 1 j • b 1 := by
  rw [properTransformBasis, Basis.map_apply]
  change b.equivFun.symm (((Matrix.SpecialLinearGroup.toLin') g) (b.equivFun (b j))) = _
  apply b.equivFun.injective
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.toLin', Matrix.toLin'_apply,
      Fin.sum_univ_two]

@[simp]
theorem matrix_proper_transform {I : Ideal (𝓞 K)} (b : Basis (Fin 2) ℤ I)
    (g : SL(2, ℤ)) :
    b.toMatrix (properTransformBasis b g) = (g : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Basis.toMatrix_apply, proper_transform_basis]

variable [NumberField K]

omit [NumberField K] in
/-- A determinant-one change of ideal basis preserves positive orientation. -/
theorem transf_posit_orien
    (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)} (b : Basis (Fin 2) ℤ I)
    (g : SL(2, ℤ)) (hb : IsPositivelyOriented B b) :
    IsPositivelyOriented B (properTransformBasis b g) := by
  rw [IsPositivelyOriented, basis_matrix_change, Matrix.det_mul,
    matrix_proper_transform, g.det_coe, mul_one]
  exact hb

/-- Applying a proper matrix to a basis realizes the corresponding transform of its norm
form. -/
theorem form_proper_transform
    (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (b : Basis (Fin 2) ℤ I) (g : SL(2, ℤ)) :
    formOfBasis I (properTransformBasis b g) = (formOfBasis I b).transform g := by
  apply form_basis_change B hI b (properTransformBasis b g) g
  · have h := congrArg (fun z : I ↦ (z : 𝓞 K)) (proper_transform_basis b g 0)
    simpa only [Submodule.coe_add, Submodule.coe_smul_of_tower] using h
  · have h := congrArg (fun z : I ↦ (z : 𝓞 K)) (proper_transform_basis b g 1)
    simpa only [Submodule.coe_add, Submodule.coe_smul_of_tower] using h

private theorem squarefree_emod_cases {d : ℤ} (hd : Squarefree d) :
    d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
  have h0 : d % 4 ≠ 0 := by
    intro hd0
    have h4 : (4 : ℤ) ∣ d := Int.dvd_iff_emod_eq_zero.mpr hd0
    have h22 : (2 : ℤ) * 2 ∣ d := by simpa using h4
    have hunit := hd 2 h22
    rw [Int.isUnit_iff] at hunit
    omega
  have hlo : 0 ≤ d % 4 := Int.emod_nonneg d (by norm_num)
  have hhi : d % 4 < 4 := Int.emod_lt_of_pos d (by norm_num)
  omega

/-- Every nonzero integral ideal in the squarefree quadratic model has a positively oriented
basis whose normalized norm form has positive leading coefficient. -/
theorem pos_leading_oriented
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    [Fact (∀ x : ℚ, x ^ 2 ≠ (d : ℚ) + 0 * x)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (B : Basis (Fin 2) ℤ (𝓞 (QFModel d)))
    (I : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥) :
    ∃ b : PositivelyOrientedBasis B I, 0 < (formOfBasis I b.1).a := by
  let b : PositivelyOrientedBasis B I := positivelyOrientedBasis B I hI
  let Q := formOfBasis I b.1
  have hproper : BQForm.ProperDiscriminant
      (quadraticFundamentalDiscriminant d) Q :=
    form_proper_primitive hd hd1 (squarefree_emod_cases hd) B I hI b.1
  obtain ⟨g, hg⟩ :=
    BQForm.transform_proper_square
      (quadraticFundamentalDiscriminant d) Q hproper
        (fundamental_discriminant_square hd hd1)
  let b' : Basis (Fin 2) ℤ I := properTransformBasis b.1 g
  have hb' : IsPositivelyOriented B b' :=
    transf_posit_orien B b.1 g b.2
  refine ⟨⟨b', hb'⟩, ?_⟩
  rw [show formOfBasis I b' = Q.transform g by
    exact form_proper_transform B hI b.1 g]
  exact hg

end INForm

end

end Submission.NumberTheory.Milne
