import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Submission.ClassField.CrossedProducts.CrossedProductBrauer
import Submission.ClassField.LocalBrauer.RealNumbers

/-!
# Chapter IV, Section 4: the real crossed product

This file formalizes the factor set used by Milne for `Complex/Real`. Its
only nontrivial value is `-1` on complex conjugation paired with itself. The
associated crossed product has the two defining quaternion relations.

The final algebra equivalence is obtained directly from the two standard
crossed-product coordinates.  Multiplicativity is checked on basis terms,
and bijectivity follows from simplicity and the equality of real dimensions.
-/

namespace Submission.CField.LBrauer

noncomputable section

open scoped ComplexConjugate Quaternion
open CProduca

attribute [local instance] Units.mulDistribMulActionRight

private instance : Algebra.IsQuadraticExtension ℝ ℂ where
  finrank_eq_two' := Complex.finrank_real_complex

/-- Every real algebra automorphism of `Complex` is the identity or complex
conjugation. -/
theorem complex_gal_or (sigma : Gal(ℂ/ℝ)) :
    sigma = 1 ∨ sigma = Complex.conjAe := by
  rcases Complex.real_algHom_eq_id_or_conj sigma.toAlgHom with h | h
  · left
    ext z
    exact DFunLike.congr_fun h z
  · right
    ext z
    exact DFunLike.congr_fun h z

theorem conj_ne_one : (Complex.conjAe : Gal(ℂ/ℝ)) ≠ 1 := by
  intro h
  have hi := DFunLike.congr_fun h Complex.I
  have hi' : Complex.I = conj Complex.I := by
    change Complex.conjAe Complex.I = Complex.I at hi
    simpa only [Complex.conjAe_coe] using hi.symm
  have him := congrArg Complex.im hi'
  norm_num at him

@[simp]
theorem complexConj_sq :
    (Complex.conjAe : Gal(ℂ/ℝ)) * Complex.conjAe = 1 := by
  ext z
  simp [Complex.conjAe]

/-- The normalized factor set representing the nontrivial class for
`Complex/Real`. -/
def realFactorSet :
    NMCocycl₂ (G := Gal(ℂ/ℝ)) (M := ℂˣ) := by
  classical
  have hone_ne_conj : (1 : Gal(ℂ/ℝ)) ≠ Complex.conjAe := by
    intro h
    have hi := DFunLike.congr_fun h Complex.I
    have hi' : Complex.I = conj Complex.I := by
      change Complex.I = Complex.conjAe Complex.I at hi
      simpa only [Complex.conjAe_coe] using hi
    have him := congrArg Complex.im hi'
    norm_num at him
  have hconj_ne_one : (Complex.conjAe : Gal(ℂ/ℝ)) ≠ 1 :=
    Ne.symm hone_ne_conj
  have hconj_sq :
      (Complex.conjAe : Gal(ℂ/ℝ)) * Complex.conjAe = 1 := by
    ext z
    simp [Complex.conjAe]
  have hsmul_neg_one (sigma : Gal(ℂ/ℝ)) :
      sigma • (-1 : ℂˣ) = -1 := by
    ext
    simp
  exact
    { toFun := fun p ↦
        if p.1 = Complex.conjAe ∧ p.2 = Complex.conjAe then -1 else 1
      isMulCocycle₂ := by
        intro sigma tau rho
        rcases complex_gal_or sigma with rfl | rfl <;>
          rcases complex_gal_or tau with rfl | rfl <;>
            rcases complex_gal_or rho with rfl | rfl <;>
              simp only [mul_one, hone_ne_conj, and_self, ↓reduceIte,
                smul_one, and_true, one_mul, and_false, mul_neg,
                hsmul_neg_one, mul_eq_left, false_and, true_and, mul_ite,
                neg_neg]
        all_goals
          by_cases h : (Complex.conjAe : Gal(ℂ/ℝ)) = 1
          · exact (hconj_ne_one h).elim
          · have hleft :
                (if (Complex.conjAe : Gal(ℂ/ℝ)) = 1 then (-1 : ℂˣ) else 1) = 1 :=
              if_neg h
            have hright :
                (if (Complex.conjAe : Gal(ℂ/ℝ)) = 1 then (1 : ℂˣ) else -1) = -1 :=
              if_neg h
            calc
              -(if (Complex.conjAe : Gal(ℂ/ℝ)) = 1 then (-1 : ℂˣ) else 1) =
                  -(1 : ℂˣ) := congrArg Neg.neg hleft
              _ = -1 := rfl
              _ = if (Complex.conjAe : Gal(ℂ/ℝ)) = 1 then (1 : ℂˣ) else -1 :=
                hright.symm
      map_one_fst := by
        intro sigma
        simp [hone_ne_conj]
      map_one_snd := by
        intro sigma
        simp [hone_ne_conj] }

@[simp]
theorem real_set_conj :
    realFactorSet (Complex.conjAe, Complex.conjAe) = (-1 : ℂˣ) := by
  simp [realFactorSet]

@[simp]
theorem real_set_left (sigma : Gal(ℂ/ℝ)) :
    realFactorSet (1, sigma) = 1 :=
  realFactorSet.map_one_fst sigma

@[simp]
theorem real_set_right (sigma : Gal(ℂ/ℝ)) :
    realFactorSet (sigma, 1) = 1 :=
  realFactorSet.map_one_snd sigma

namespace RCProduc

abbrev A := CProduc realFactorSet

/-- The standard basis element corresponding to complex conjugation. -/
def j : A := CProduc.basis realFactorSet Complex.conjAe

/-- The coefficient-field embedding of `Complex` in the real crossed
product. -/
def coefficientEmbedding : ℂ →ₐ[ℝ] A :=
  CProduc.fieldEmbedding ℝ ℂ realFactorSet

@[simp]
theorem j_coefficient_embedding (z : ℂ) :
    j * coefficientEmbedding z = coefficientEmbedding (conj z) * j := by
  simp [j, coefficientEmbedding]

@[simp]
theorem j_sq : j * j = coefficientEmbedding (-1) := by
  have hconj_sq :
      (Complex.conjAe : Gal(ℂ/ℝ)) * Complex.conjAe = 1 := by
    ext z
    simp [Complex.conjAe]
  rw [j, CProduc.basis_mul_basis]
  simp only [real_set_conj, Units.val_neg, Units.val_one,
    CProduc.fieldEmbedding_apply, CProduc.basis_apply,
    CProduc.single_mul_single, one_mul, smul_one, mul_one,
    NMCocycl₂.apply_one_fst, coefficientEmbedding]
  exact congrArg (fun sigma ↦ CProduc.single realFactorSet sigma (-1)) hconj_sq

/-- The image in Hamilton's quaternions of a single crossed-product term. -/
noncomputable def singleToHamilton (sigma : Gal(ℂ/ℝ)) (z : ℂ) : ℍ[ℝ] :=
  by
    classical
    exact if sigma = 1 then Quaternion.ofComplex z
      else Quaternion.ofComplex z * quatJ

@[simp]
theorem single_hamilton_one (z : ℂ) :
    singleToHamilton 1 z = Quaternion.ofComplex z := by
  simp [singleToHamilton]

@[simp]
theorem single_hamilton_conj (z : ℂ) :
    singleToHamilton Complex.conjAe z = Quaternion.ofComplex z * quatJ := by
  unfold singleToHamilton
  exact if_neg conj_ne_one

@[simp]
theorem single_hamilton_zero (sigma : Gal(ℂ/ℝ)) :
    singleToHamilton sigma 0 = 0 := by
  simp [singleToHamilton]

theorem single_hamilton_add (sigma : Gal(ℂ/ℝ)) (z w : ℂ) :
    singleToHamilton sigma (z + w) =
      singleToHamilton sigma z + singleToHamilton sigma w := by
  by_cases h : sigma = 1 <;> simp [singleToHamilton, h, add_mul]

/-- The quaternion images of basis terms satisfy the crossed-product
multiplication law. -/
theorem single_hamilton_mul
    (sigma tau : Gal(ℂ/ℝ)) (z w : ℂ) :
    singleToHamilton sigma z * singleToHamilton tau w =
      singleToHamilton (sigma * tau)
        (z * sigma w * (realFactorSet (sigma, tau) : ℂ)) := by
  rcases complex_gal_or sigma with rfl | rfl <;>
    rcases complex_gal_or tau with rfl | rfl
  · simp
  · simp [mul_assoc]
  · simp only [mul_one, real_set_right, Units.val_one]
    rw [single_hamilton_conj, single_hamilton_one,
      single_hamilton_conj, mul_assoc, quat_j_complex,
      ← mul_assoc, ← map_mul]
    rfl
  · simp only [real_set_conj, Units.val_neg, Units.val_one]
    rw [single_hamilton_conj, single_hamilton_conj]
    calc
      (Quaternion.ofComplex z * quatJ) *
            (Quaternion.ofComplex w * quatJ) =
          Quaternion.ofComplex z *
            ((quatJ * Quaternion.ofComplex w) * quatJ) := by
              simp only [mul_assoc]
      _ = Quaternion.ofComplex z *
            ((Quaternion.ofComplex (conj w) * quatJ) * quatJ) := by
              rw [quat_j_complex]
      _ = Quaternion.ofComplex z *
            (Quaternion.ofComplex (conj w) * (quatJ * quatJ)) := by
              rw [mul_assoc]
      _ = Quaternion.ofComplex z *
            (Quaternion.ofComplex (conj w) * (-1)) := by rw [quatJ_sq]
      _ = Quaternion.ofComplex (z * conj w * (-1)) := by
            simp only [map_mul, map_neg, map_one]
            rw [mul_assoc]
      _ = singleToHamilton 1 (z * conj w * (-1)) :=
            (single_hamilton_one _).symm
      _ = singleToHamilton
            ((Complex.conjAe : Gal(ℂ/ℝ)) * Complex.conjAe)
            (z * Complex.conjAe w * (-1)) := by
              exact congrArg₂ singleToHamilton complexConj_sq.symm rfl

/-- The additive crossed-product expansion evaluated in Hamilton's
quaternions. -/
noncomputable def toHamilton (x : A) : ℍ[ℝ] :=
  CProduc.sum realFactorSet x singleToHamilton

@[simp]
theorem toHamilton_single (sigma : Gal(ℂ/ℝ)) (z : ℂ) :
    toHamilton (CProduc.single realFactorSet sigma z) =
      singleToHamilton sigma z := by
  rw [toHamilton, CProduc.sum_single_index]
  exact single_hamilton_zero sigma

theorem toHamilton_add (x y : A) :
    toHamilton (x + y) = toHamilton x + toHamilton y := by
  exact CProduc.sum_add_index' realFactorSet
    single_hamilton_zero single_hamilton_add

/-- The explicit real-algebra map from Milne's crossed product to Hamilton's
quaternion algebra. -/
noncomputable def hamiltonAlgHom : A →ₐ[ℝ] ℍ[ℝ] where
  toFun := toHamilton
  map_zero' := CProduc.sum_zero_index realFactorSet
  map_one' := by simp [CProduc.one_def]
  map_add' := toHamilton_add
  map_mul' x y := by
    induction x using CProduc.induction_on realFactorSet with
    | zero => simp [toHamilton]
    | hadd x₁ x₂ hx₁ hx₂ =>
        rw [add_mul, toHamilton_add, toHamilton_add, hx₁, hx₂, add_mul]
    | hsingle sigma z =>
        induction y using CProduc.induction_on realFactorSet with
        | zero => simp [toHamilton]
        | hadd y₁ y₂ hy₁ hy₂ =>
            rw [mul_add, toHamilton_add, toHamilton_add, hy₁, hy₂, mul_add]
        | hsingle tau w =>
            rw [CProduc.single_mul_single, toHamilton_single,
              toHamilton_single, toHamilton_single, single_hamilton_mul]
            rfl
  commutes' r := by
    change toHamilton (CProduc.single realFactorSet 1 (algebraMap ℝ ℂ r)) = _
    simp

@[simp]
theorem hamilton_alg_coefficient (z : ℂ) :
    hamiltonAlgHom (coefficientEmbedding z) = Quaternion.ofComplex z := by
  change toHamilton (CProduc.single realFactorSet 1 z) = _
  rw [toHamilton_single, single_hamilton_one]

@[simp]
theorem hamilton_alg_j : hamiltonAlgHom j = quatJ := by
  change toHamilton (CProduc.single realFactorSet Complex.conjAe 1) = _
  rw [toHamilton_single, single_hamilton_conj]
  simp

theorem hamilton_alg_bijective : Function.Bijective hamiltonAlgHom := by
  have hinj : Function.Injective hamiltonAlgHom :=
    hamiltonAlgHom.toRingHom.injective
  have hsurj : Function.Surjective hamiltonAlgHom := by
    intro q
    obtain ⟨⟨z, w⟩, hq, _⟩ := unique_quat_j q
    refine ⟨coefficientEmbedding z + coefficientEmbedding w * j, ?_⟩
    rw [map_add, map_mul, hamilton_alg_coefficient,
      hamilton_alg_coefficient, hamilton_alg_j]
    exact hq.symm
  exact ⟨hinj, hsurj⟩

/-- Milne's explicit identification of the nontrivial real crossed product
with Hamilton's quaternion algebra. -/
noncomputable def algEquivHamilton : A ≃ₐ[ℝ] ℍ[ℝ] :=
  AlgEquiv.ofBijective hamiltonAlgHom hamilton_alg_bijective

@[simp]
theorem alg_hamilton_coefficient (z : ℂ) :
    algEquivHamilton (coefficientEmbedding z) = Quaternion.ofComplex z := by
  exact hamilton_alg_coefficient z

@[simp]
theorem alg_hamilton_j : algEquivHamilton j = quatJ := by
  exact hamilton_alg_j

end RCProduc

end

end Submission.CField.LBrauer
