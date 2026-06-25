import Submission.NumberTheory.Quadratic.FormIdealEquivalence
import Submission.NumberTheory.Quadratic.FormClassNarrow
import Submission.NumberTheory.Quadratic.IdealFormInverse
import Submission.NumberTheory.Quadratic.ImaginaryNarrowClass
import Submission.NumberTheory.Quadratic.NarrowIntegralRepresentative
import Submission.NumberTheory.Quadratic.OrientedBasisExistence
import Submission.NumberTheory.Quadratic.PositiveLeadingBasis
import Submission.NumberTheory.Quadratic.IdealFormMap


/-!
# Milne, Algebraic Number Theory, Theorem 4.29

This file assembles the ideal--form correspondence for squarefree quadratic fields.  The
codomain is the corrected one: proper primitive classes of fundamental discriminant, restricted
to the positive-definite component when the discriminant is negative.  For positive
discriminant the forms are indefinite and no sign component is removed.  The negative case
needs the restriction because, for example, the positive and negative Gaussian forms both have
discriminant `-4` but are not properly equivalent.

The constructions below are the genuine ones from the proof.  A form is sent to the ideal
`Z a + Z (omega + r)`, and an ideal is sent to its normalized norm form on a positively oriented
basis.  The auxiliary files prove the two explicit principal-scaling identities needed for
descent through the respective quotients.
-/

namespace Submission.NumberTheory.Milne

open Submission.NumberTheory
open scoped MatrixGroups NumberField QuadraticAlgebra nonZeroDivisors
open Module

noncomputable section

namespace NGEquiv

/-- A squarefree integer is congruent to `1`, `2`, or `3` modulo four.  The excluded residue
zero would make `2^2` divide it. -/
theorem squarefree_emod_cases {d : ℤ} (hd : Squarefree d) :
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

theorem quadra_funda_discr {d : ℤ} (hdneg : d < 0) :
    quadraticFundamentalDiscriminant d < 0 := by
  by_cases h : d % 4 = 1
  · simpa [quadraticFundamentalDiscriminant, h] using hdneg
  · simp only [quadraticFundamentalDiscriminant, if_neg h]
    nlinarith

variable {d : ℤ}
variable (hd : Squarefree d) (hd1 : d ≠ 1) (hdneg : d < 0)
variable [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
variable [Module.Finite ℚ (QFModel d)]
variable [NumberField (QFModel d)]

/-- The standard quadratic order, identified with the full ring of integers. -/
noncomputable def orderEquiv :
    QOrd (quadraticOrderParameter d) (quadraticParameterB d) ≃+*
      𝓞 (QFModel d) :=
  (integersQuadraticOrder hd hd1).symm

/-- The positively oriented standard basis `1, omega` of the ring of integers. -/
noncomputable def ringBasis : Basis (Fin 2) ℤ (𝓞 (QFModel d)) :=
  quadraticIntegersBasis hd hd1

section FormToIdeal

open BQForm

/-- The integer `r` determined by `b = B + 2r` for a form of fundamental discriminant. -/
noncomputable def middleRoot
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) : ℤ :=
  Classical.choose
    (middle_parameter_relation Q.1 Q.2.1)

omit [Fact (∀ (r : ℚ), r ^ 2 ≠ ↑d + 0 * r)] [Module.Finite ℚ (QFModel d)]
  [NumberField (QFModel d)] in
theorem middleRoot_spec
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    Q.1.b = quadraticParameterB d + 2 * middleRoot Q ∧
      middleRoot Q ^ 2 + quadraticParameterB d * middleRoot Q -
          quadraticOrderParameter d = Q.1.a * Q.1.c :=
  Classical.choose_spec
    (middle_parameter_relation Q.1 Q.2.1)

/-- The integral ideal `Z a + Z (omega + r)` attached to a positive primitive form. -/
noncomputable def formIdeal
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    Ideal (𝓞 (QFModel d)) :=
  Q.1.mappedFormIdeal (orderEquiv hd hd1)
    (middleRoot Q) (middleRoot_spec Q).1
    (Q.2.1.trans (fundam_discr_param d))

omit [Module.Finite ℚ (QFModel d)] in
theorem form_ne_bot
    (hdneg : d < 0)
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    formIdeal hd hd1 Q ≠ ⊥ := by
  rw [formIdeal, BQForm.mappedFormIdeal]
  intro hbot
  have ha : Q.1.a ≠ 0 :=
    (Q.2.2.2 (quadra_funda_discr hdneg)).1.ne'
  apply Q.1.ideal_ne (middleRoot Q) (middleRoot_spec Q).1
    (Q.2.1.trans (fundam_discr_param d)) ha
  exact (Ideal.map_eq_bot_iff_of_injective (orderEquiv hd hd1).injective).mp hbot

omit [Module.Finite ℚ (QFModel d)] in
/-- The evident ordered basis `(a, omega + r)` of the form ideal has positive orientation.
Its coordinate matrix in the standard ring basis is upper triangular with diagonal `(a, 1)`. -/
theorem basis_positively_oriented
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    INForm.IsPositivelyOriented (ringBasis hd hd1)
      (Q.1.mappedIdealBasis (orderEquiv hd hd1) (middleRoot Q)
        (middleRoot_spec Q).1
        (Q.2.1.trans (fundam_discr_param d))
        ((Q.2.2.2 (quadra_funda_discr hdneg)).1.ne')) := by
  let r := middleRoot Q
  let hdisc := Q.2.1.trans (fundam_discr_param d)
  let ha : 0 < Q.1.a :=
    (Q.2.2.2 (quadra_funda_discr hdneg)).1
  change INForm.IsPositivelyOriented (ringBasis hd hd1)
    (Q.1.mappedIdealBasis (orderEquiv hd hd1) r
      (middleRoot_spec Q).1 hdisc ha.ne')
  rw [INForm.IsPositivelyOriented, INForm.basisCoordinateMatrix,
    Matrix.det_fin_two]
  simp only [BQForm.mapped_form_ideal]
  have h0 :
      (((Q.1.toIdealBasis r (middleRoot_spec Q).1 hdisc ha.ne' 0 :
          Q.1.toIdeal r (middleRoot_spec Q).1 hdisc) :
        QOrd (quadraticOrderParameter d) (quadraticParameterB d))) = Q.1.a :=
    BQForm.lattice_basis_coe _ _ Q.1.a r Q.1.c
      (Q.1.lattice_relation r (middleRoot_spec Q).1 hdisc) ha.ne'
  have h1 :
      (((Q.1.toIdealBasis r (middleRoot_spec Q).1 hdisc ha.ne' 1 :
          Q.1.toIdeal r (middleRoot_spec Q).1 hdisc) :
        QOrd (quadraticOrderParameter d) (quadraticParameterB d))) =
          QuadraticAlgebra.omega + (r : QOrd
            (quadraticOrderParameter d) (quadraticParameterB d)) :=
    BQForm.lattice_one_coe _ _ Q.1.a r Q.1.c
      (Q.1.lattice_relation r (middleRoot_spec Q).1 hdisc) ha.ne'
  simp only [ringBasis, quadraticIntegersBasis, orderEquiv,
    Basis.toMatrix_apply,
    Fin.isValue, Int.sub_pos, gt_iff_lt]
  rw [h0, h1]
  simp
  simpa using ha

/-- The ordinary ideal class attached to a corrected form representative. -/
noncomputable def formIdealClass
    (hdneg : d < 0)
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    ClassGroup (𝓞 (QFModel d)) :=
  ClassGroup.mk0
    ⟨formIdeal hd hd1 Q,
      mem_nonZeroDivisors_iff_ne_zero.mpr (form_ne_bot hd hd1 hdneg Q)⟩

omit [Module.Finite ℚ (QFModel d)] in
/-- Properly equivalent corrected forms define the same ordinary ideal class. -/
theorem form_ideal_equivalent
    (hdneg : d < 0)
    (Q Q' : ProperPrimitive (quadraticFundamentalDiscriminant d))
    (hQQ' : Q.1.Equivalent Q'.1) :
    formIdealClass hd hd1 hdneg Q = formIdealClass hd hd1 hdneg Q' := by
  obtain ⟨g, hg⟩ := hQQ'
  let r := middleRoot Q
  let r' := middleRoot Q'
  have hb : Q.1.b = quadraticParameterB d + 2 * r := (middleRoot_spec Q).1
  have hb' : (Q.1.transform g).b = quadraticParameterB d + 2 * r' := by
    rw [← hg]
    exact (middleRoot_spec Q').1
  have hdisc : Q.1.discriminant =
      quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d :=
    Q.2.1.trans (fundam_discr_param d)
  have ha : Q.1.a ≠ 0 :=
    (Q.2.2.2 (quadra_funda_discr hdneg)).1.ne'
  have ha' : (Q.1.transform g).a ≠ 0 := by
    rw [← hg]
    exact (Q'.2.2.2 (quadra_funda_discr hdneg)).1.ne'
  have hclass := Q.1.mapped_form_transform
    (orderEquiv hd hd1) r r' g hb hb' hdisc ha ha'
  simpa [formIdealClass, formIdeal, r, r', hg] using hclass

/-- Descent of the explicit form ideal through proper equivalence. -/
noncomputable def formClassGroup (hdneg : d < 0) :
    ProperPrimitDiscri (quadraticFundamentalDiscriminant d) →
      ClassGroup (𝓞 (QFModel d)) :=
  Quotient.lift (formIdealClass hd hd1 hdneg)
    (fun Q Q' h ↦ form_ideal_equivalent hd hd1 hdneg Q Q' h)

/-- In the imaginary case, the explicit form ideal gives a genuine narrow ideal class. -/
noncomputable def formNarrowGroup (hdneg : d < 0) :
    ProperPrimitDiscri (quadraticFundamentalDiscriminant d) →
      NCGroup (QFModel d) :=
  (imaginaryQuadraticNarrow hd hd1 hdneg).symm ∘
    formClassGroup hd hd1 hdneg

end FormToIdeal

section IdealToForm

open INForm BQForm

/-- A chosen nonzero integral representative of an ordinary ideal class. -/
noncomputable def integralRepresentative
    (C : ClassGroup (𝓞 (QFModel d))) : (
      Ideal (𝓞 (QFModel d)))⁰ :=
  Classical.choose (ClassGroup.mk0_surjective C)

omit [Module.Finite ℚ (QFModel d)] in
@[simp] theorem integralr_class
    (C : ClassGroup (𝓞 (QFModel d))) :
    ClassGroup.mk0 (integralRepresentative C) = C :=
  Classical.choose_spec (ClassGroup.mk0_surjective C)

/-- A chosen positive ordered basis of the chosen integral ideal representative. -/
noncomputable def integ_repre_basis
    (C : ClassGroup (𝓞 (QFModel d))) :
    PositivelyOrientedBasis (ringBasis hd hd1) (integralRepresentative C : Ideal _) :=
  positivelyOrientedBasis (ringBasis hd hd1) (integralRepresentative C)
    (mem_nonZeroDivisors_iff_ne_zero.mp (integralRepresentative C).2)

/-- The normalized norm-form class attached to an ordinary ideal class. -/
noncomputable def classForm
    (C : ClassGroup (𝓞 (QFModel d))) :
    ProperPrimitDiscri (quadraticFundamentalDiscriminant d) :=
  POData.proper_primi_class hd hd1
    (squarefree_emod_cases hd) (ringBasis hd hd1)
    ⟨integralRepresentative C,
      mem_nonZeroDivisors_iff_ne_zero.mp (integralRepresentative C).2,
      integ_repre_basis hd hd1 C⟩

omit [Module.Finite ℚ (QFModel d)] in
private theorem form_basis_equivalent
    {I J : Ideal (𝓞 (QFModel d))} (hI : I ≠ ⊥) (hIJ : I = J)
    (bI : PositivelyOrientedBasis (ringBasis hd hd1) I)
    (bJ : PositivelyOrientedBasis (ringBasis hd hd1) J) :
    (formOfBasis I bI.1).Equivalent (formOfBasis J bJ.1) := by
  subst J
  exact positi_orien_equiv (ringBasis hd hd1) hI bI bJ

/-- The normalized norm-form class depends only on the ordinary ideal class, not on the chosen
nonzero integral ideal or its positively oriented basis.  In an imaginary quadratic field every
nonzero algebraic integer has positive norm, so the two principal scalings in the classical
criterion `ClassGroup.mk0_eq_mk0_iff` preserve both the normalized form and its orientation. -/
theorem form_mk_0
    (hdneg : d < 0)
    (I J : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (bI : PositivelyOrientedBasis (ringBasis hd hd1) I)
    (bJ : PositivelyOrientedBasis (ringBasis hd hd1) J)
    (hclass :
      ClassGroup.mk0
          (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ :
            (Ideal (𝓞 (QFModel d)))⁰) =
        ClassGroup.mk0
          (⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩ :
            (Ideal (𝓞 (QFModel d)))⁰)) :
    POData.proper_primi_class hd hd1
        (squarefree_emod_cases hd) (ringBasis hd hd1) ⟨I, hI, bI⟩ =
      POData.proper_primi_class hd hd1
        (squarefree_emod_cases hd) (ringBasis hd hd1) ⟨J, hJ, bJ⟩ := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hclass
  have hxnorm : 0 < Algebra.norm ℤ x :=
    QIMap.int_pos_neg hdneg x hx
  have hynorm : 0 < Algebra.norm ℤ y :=
    QIMap.int_pos_neg hdneg y hy
  let Ix := principalScaleIdeal x I
  let Jy := principalScaleIdeal y J
  change Ix = Jy at hxy
  have hIx : Ix ≠ ⊥ := by
    dsimp [Ix, principalScaleIdeal]
    rw [Ideal.mul_eq_bot, not_or]
    exact ⟨by simpa [Ideal.span_singleton_eq_bot] using hx, hI⟩
  have hJy : Jy ≠ ⊥ := by
    dsimp [Jy, principalScaleIdeal]
    rw [Ideal.mul_eq_bot, not_or]
    exact ⟨by simpa [Ideal.span_singleton_eq_bot] using hy, hJ⟩
  let bx : Basis (Fin 2) ℤ Ix := principalScaleBasis x hx I bI.1
  let byBasis : Basis (Fin 2) ℤ Jy := principalScaleBasis y hy J bJ.1
  have hbx : IsPositivelyOriented (ringBasis hd hd1) bx :=
    scale_positively_oriented (ringBasis hd hd1) x hxnorm I bI.1 bI.2
  have hby : IsPositivelyOriented (ringBasis hd hd1) byBasis :=
    scale_positively_oriented (ringBasis hd hd1) y hynorm J bJ.1 bJ.2
  apply Quotient.sound
  change (formOfBasis I bI.1).Equivalent (formOfBasis J bJ.1)
  have hxform : formOfBasis Ix bx = formOfBasis I bI.1 :=
    form_scale_pos (ringBasis hd hd1) x hxnorm I bI.1
  have hyform : formOfBasis Jy byBasis = formOfBasis J bJ.1 :=
    form_scale_pos (ringBasis hd hd1) y hynorm J bJ.1
  rw [← hxform, ← hyform]
  exact form_basis_equivalent hd hd1 hIx hxy
    ⟨bx, hbx⟩ ⟨byBasis, hby⟩

/-- Starting from a corrected form, taking its explicit ideal and then the normalized norm form
recovers its proper-equivalence class. -/
theorem class_form_ideal
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    classForm hd hd1 (formIdealClass hd hd1 hdneg Q) = Quotient.mk _ Q := by
  let C := formIdealClass hd hd1 hdneg Q
  let I := (integralRepresentative C : Ideal (𝓞 (QFModel d)))
  have hI : I ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp (integralRepresentative C).2
  let bI := integ_repre_basis hd hd1 C
  let r := middleRoot Q
  let hdisc := Q.2.1.trans (fundam_discr_param d)
  let ha : 0 < Q.1.a :=
    (Q.2.2.2 (quadra_funda_discr hdneg)).1
  let J := formIdeal hd hd1 Q
  have hJ : J ≠ ⊥ := form_ne_bot hd hd1 hdneg Q
  let bJ : Basis (Fin 2) ℤ J :=
    Q.1.mappedIdealBasis (orderEquiv hd hd1) r (middleRoot_spec Q).1 hdisc ha.ne'
  have hbJ : IsPositivelyOriented (ringBasis hd hd1) bJ := by
    simpa [bJ, J, r, hdisc, ha] using
      basis_positively_oriented hd hd1 hdneg Q
  have hclasses :
      ClassGroup.mk0
          (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ :
            (Ideal (𝓞 (QFModel d)))⁰) =
        ClassGroup.mk0
          (⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩ :
            (Ideal (𝓞 (QFModel d)))⁰) := by
    rw [show ClassGroup.mk0
        (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ :
          (Ideal (𝓞 (QFModel d)))⁰) = C by
      exact integralr_class C]
    rfl
  have hchoice := form_mk_0 hd hd1 hdneg I J hI hJ bI
    (⟨bJ, hbJ⟩ : PositivelyOrientedBasis (ringBasis hd hd1) J) hclasses
  let R := QOrd (quadraticOrderParameter d) (quadraticParameterB d)
  letI : IsDomain R :=
    (orderEquiv hd hd1).toMulEquiv.isDomain (𝓞 (QFModel d))
  letI : IsNoetherianRing R :=
    isNoetherianRing_of_ringEquiv (𝓞 (QFModel d)) (orderEquiv hd hd1).symm
  letI : IsIntegrallyClosed R :=
    IsIntegrallyClosed.of_equiv (orderEquiv hd hd1).symm
  letI : Ring.DimensionLEOne R :=
    Ring.DimensionLEOne.of_ringEquiv (orderEquiv hd hd1)
  letI : IsDedekindDomain R :=
    (isDedekindDomain_iff (A := R) (FractionRing R)).2
      ⟨inferInstance, inferInstance, inferInstance,
        (isIntegrallyClosed_iff (R := R) (FractionRing R)).mp inferInstance⟩
  have hinverse : formOfBasis J bJ = Q.1 := by
    simpa [J, bJ, r, hdisc, ha] using
      Q.1.form_basis_mapped (orderEquiv hd hd1) (ringBasis hd hd1)
        r (middleRoot_spec Q).1 hdisc ha
  have hJclass :
      POData.proper_primi_class hd hd1
          (squarefree_emod_cases hd) (ringBasis hd hd1) ⟨J, hJ, ⟨bJ, hbJ⟩⟩ =
        Quotient.mk _ Q := by
    apply Quotient.sound
    change (formOfBasis J bJ).Equivalent Q.1
    rw [hinverse]
    exact equivalent_refl Q.1
  exact hchoice.trans hJclass

/-- Starting from an ordinary ideal class, taking its normalized norm form and reconstructing
the explicit form ideal returns the original ideal class. -/
theorem form_class_group
    (C : ClassGroup (𝓞 (QFModel d))) :
    formClassGroup hd hd1 hdneg (classForm hd hd1 C) = C := by
  let I := (integralRepresentative C : Ideal (𝓞 (QFModel d)))
  have hI : I ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp (integralRepresentative C).2
  let b := integ_repre_basis hd hd1 C
  let X : POData (ringBasis hd hd1) := ⟨I, hI, b⟩
  let Q : ProperPrimitive (quadraticFundamentalDiscriminant d) :=
    X.proper_primi_form hd hd1 (squarefree_emod_cases hd) (ringBasis hd hd1)
  let r := middleRoot Q
  have hb : (formOfBasis I b.1).b = quadraticParameterB d + 2 * r := by
    exact (middleRoot_spec Q).1
  have hdisc : (formOfBasis I b.1).discriminant =
      quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d := by
    exact Q.2.1.trans (fundam_discr_param d)
  have hinverse := mapped_form_basis hd hd1 I hI b r hb hdisc
  change formIdealClass hd hd1 hdneg Q = C
  simpa [formIdealClass, formIdeal, Q, X, r] using
    hinverse.trans (integralr_class C)

/-- The form-to-ideal-to-form inverse law on the proper-equivalence quotient. -/
theorem class_group_form
    (F : ProperPrimitDiscri (quadraticFundamentalDiscriminant d)) :
    classForm hd hd1 (formClassGroup hd hd1 hdneg F) = F := by
  refine Quotient.inductionOn F ?_
  intro Q
  exact class_form_ideal hd hd1 hdneg Q

/-- The corrected ideal--form correspondence for the ordinary class group of an imaginary
quadratic field. -/
noncomputable def classGroupForm :
    ClassGroup (𝓞 (QFModel d)) ≃
      ProperPrimitDiscri (quadraticFundamentalDiscriminant d) where
  toFun := classForm hd hd1
  invFun := formClassGroup hd hd1 hdneg
  left_inv := form_class_group hd hd1 hdneg
  right_inv := class_group_form hd hd1 hdneg

/-- The ideal-to-form map on the genuine narrow class group in the imaginary case. -/
noncomputable def narrowGroupForm (hdneg : d < 0) :
    NCGroup (QFModel d) →
      ProperPrimitDiscri (quadraticFundamentalDiscriminant d) :=
  classForm hd hd1 ∘
    imaginaryQuadraticNarrow hd hd1 hdneg

/-- **Theorem 4.29, corrected imaginary-quadratic statement.**  The genuine narrow ideal class
group of `Q(sqrt d)` is in bijection with proper classes of positive primitive integral binary
quadratic forms of fundamental discriminant. -/
noncomputable def imaginaryNarrowForm :
    NCGroup (QFModel d) ≃
      ProperPrimitDiscri (quadraticFundamentalDiscriminant d) :=
  (imaginaryQuadraticNarrow hd hd1 hdneg).toEquiv.trans
    (classGroupForm hd hd1 hdneg)

end IdealToForm

namespace General

open INForm BQForm

/-- A positive-leading, positively oriented basis of the chosen integral representative of a
narrow ideal class. -/
noncomputable def integ_repre_basis
    (C : NCGroup (QFModel d)) :
    PositivelyOrientedBasis (ringBasis hd hd1)
      (NCGroup.integralRepresentative C) :=
  Classical.choose
    (pos_leading_oriented hd hd1 (ringBasis hd hd1)
      (NCGroup.integralRepresentative C)
      (NCGroup.integr_repre_bot C))

theorem integ_repre_pos
    (C : NCGroup (QFModel d)) :
    0 < (formOfBasis (NCGroup.integralRepresentative C)
      (integ_repre_basis hd hd1 C).1).a :=
  Classical.choose_spec
    (pos_leading_oriented hd hd1 (ringBasis hd hd1)
      (NCGroup.integralRepresentative C)
      (NCGroup.integr_repre_bot C))

/-- Positive integral principal scalings preserve the proper class of an oriented ideal norm
form. -/
theorem form_princ_scali
    (I J : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (bI : PositivelyOrientedBasis (ringBasis hd hd1) I)
    (bJ : PositivelyOrientedBasis (ringBasis hd hd1) J)
    (x y : 𝓞 (QFModel d)) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxnorm : 0 < Algebra.norm ℤ x) (hynorm : 0 < Algebra.norm ℤ y)
    (hscale : principalScaleIdeal x I = principalScaleIdeal y J) :
    POData.proper_primi_class hd hd1
        (squarefree_emod_cases hd) (ringBasis hd hd1) ⟨I, hI, bI⟩ =
      POData.proper_primi_class hd hd1
        (squarefree_emod_cases hd) (ringBasis hd hd1) ⟨J, hJ, bJ⟩ := by
  let Ix := principalScaleIdeal x I
  let Jy := principalScaleIdeal y J
  have hIx : Ix ≠ ⊥ := by
    dsimp [Ix, principalScaleIdeal]
    rw [Ideal.mul_eq_bot, not_or]
    exact ⟨by simpa [Ideal.span_singleton_eq_bot] using hx, hI⟩
  have hJy : Jy ≠ ⊥ := by
    dsimp [Jy, principalScaleIdeal]
    rw [Ideal.mul_eq_bot, not_or]
    exact ⟨by simpa [Ideal.span_singleton_eq_bot] using hy, hJ⟩
  let bx : Basis (Fin 2) ℤ Ix := principalScaleBasis x hx I bI.1
  let byBasis : Basis (Fin 2) ℤ Jy := principalScaleBasis y hy J bJ.1
  have hbx : IsPositivelyOriented (ringBasis hd hd1) bx :=
    scale_positively_oriented (ringBasis hd hd1) x hxnorm I bI.1 bI.2
  have hby : IsPositivelyOriented (ringBasis hd hd1) byBasis :=
    scale_positively_oriented (ringBasis hd hd1) y hynorm J bJ.1 bJ.2
  apply Quotient.sound
  change (formOfBasis I bI.1).Equivalent (formOfBasis J bJ.1)
  have hxform : formOfBasis Ix bx = formOfBasis I bI.1 :=
    form_scale_pos (ringBasis hd hd1) x hxnorm I bI.1
  have hyform : formOfBasis Jy byBasis = formOfBasis J bJ.1 :=
    form_scale_pos (ringBasis hd hd1) y hynorm J bJ.1
  rw [← hxform, ← hyform]
  exact form_basis_equivalent hd hd1 hIx
    (by simpa [Ix, Jy] using hscale) ⟨bx, hbx⟩ ⟨byBasis, hby⟩

/-- Positively oriented norm forms of two integral ideals in the same narrow class define the
same corrected proper form class. -/
theorem form_class_narrow
    (I J : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (bI : PositivelyOrientedBasis (ringBasis hd hd1) I)
    (bJ : PositivelyOrientedBasis (ringBasis hd hd1) J)
    (hclass :
      NCGroup.mk (QFModel d)
          (FractionalIdeal.mk0 (QFModel d)
            ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩) =
        NCGroup.mk (QFModel d)
          (FractionalIdeal.mk0 (QFModel d)
            ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩)) :
    POData.proper_primi_class hd hd1
        (squarefree_emod_cases hd) (ringBasis hd hd1) ⟨I, hI, bI⟩ =
      POData.proper_primi_class hd hd1
        (squarefree_emod_cases hd) (ringBasis hd hd1) ⟨J, hJ, bJ⟩ := by
  obtain ⟨P, hP, hmul⟩ := (QuotientGroup.mk'_eq_mk'
    (NarrowPrincipalIdeals (QFModel d))).mp hclass
  obtain ⟨t, ht, htP⟩ :=
    (narrow_principal (QFModel d) P).mp hP
  have hfrac :
      (I : FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d)) *
          FractionalIdeal.spanSingleton (𝓞 (QFModel d))⁰ (t : QFModel d) =
        (J : FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d)) := by
    have hmul' := congrArg Units.val hmul
    rw [← htP] at hmul'
    simpa only [Units.val_mul, FractionalIdeal.coe_mk0, coe_toPrincipalIdeal] using hmul'
  obtain ⟨⟨a, s⟩, hts⟩ := IsLocalization.surj
    (𝓞 (QFModel d))⁰ (t : QFModel d)
  let b : 𝓞 (QFModel d) := s.1
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.2
  have ht_mk : (t : QFModel d) =
      IsLocalization.mk' (QFModel d) a s :=
    IsLocalization.eq_mk'_iff_mul_eq.mpr hts
  have hintegral : Ideal.span ({a} : Set (𝓞 (QFModel d))) * I =
      Ideal.span ({b} : Set (𝓞 (QFModel d))) * J := by
    apply (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal
      (QFModel d) s.2).mp
    rw [← ht_mk]
    simpa only [mul_comm] using hfrac
  let x : 𝓞 (QFModel d) := a * b
  let y : 𝓞 (QFModel d) := b * b
  have hscale : principalScaleIdeal x I = principalScaleIdeal y J := by
    dsimp only [principalScaleIdeal, x, y]
    calc
      Ideal.span ({a * b} : Set (𝓞 (QFModel d))) * I =
          Ideal.span ({b} : Set (𝓞 (QFModel d))) *
            (Ideal.span ({a} : Set (𝓞 (QFModel d))) * I) := by
        rw [← Ideal.span_singleton_mul_span_singleton]
        ac_rfl
      _ = Ideal.span ({b} : Set (𝓞 (QFModel d))) *
          (Ideal.span ({b} : Set (𝓞 (QFModel d))) * J) := by rw [hintegral]
      _ = Ideal.span ({b * b} : Set (𝓞 (QFModel d))) * J := by
        rw [← Ideal.span_singleton_mul_span_singleton]
        ac_rfl
  have hbK : algebraMap (𝓞 (QFModel d)) (QFModel d) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hyK : ((y : 𝓞 (QFModel d)) : QFModel d) ≠ 0 := by
    simpa [y] using pow_ne_zero 2 hbK
  have hyTotal : ITPos (QFModel d)
      ((y : 𝓞 (QFModel d)) : QFModel d) := by
    intro phi
    have hphi : phi (algebraMap (𝓞 (QFModel d))
        (QFModel d) b) ≠ 0 := by
      intro h
      exact hbK (phi.injective (by simpa using h))
    simpa only [y, map_mul, pow_two] using mul_self_pos.mpr hphi
  have hxfield : ((x : 𝓞 (QFModel d)) : QFModel d) =
      (t : QFModel d) *
        ((y : 𝓞 (QFModel d)) : QFModel d) := by
    change algebraMap (𝓞 (QFModel d)) (QFModel d) (a * b) = _
    simp only [map_mul, y]
    rw [← hts]
    ring
  have hxK : ((x : 𝓞 (QFModel d)) : QFModel d) ≠ 0 := by
    rw [hxfield]
    exact mul_ne_zero t.ne_zero hyK
  have hxTotal : ITPos (QFModel d)
      ((x : 𝓞 (QFModel d)) : QFModel d) := by
    rw [hxfield]
    exact ITPos.mul (QFModel d) ht hyTotal
  have hxnormQ := QTPositi.pos_totally_positive
    ((x : 𝓞 (QFModel d)) : QFModel d) hxK hxTotal
  have hynormQ := QTPositi.pos_totally_positive
    ((y : 𝓞 (QFModel d)) : QFModel d) hyK hyTotal
  have hxnorm : 0 < Algebra.norm ℤ x := by
    have hcast : ((Algebra.norm ℤ x : ℤ) : ℚ) =
        Algebra.norm ℚ ((x : 𝓞 (QFModel d)) : QFModel d) :=
      Algebra.coe_norm_int x
    exact_mod_cast hcast.symm ▸ hxnormQ
  have hynorm : 0 < Algebra.norm ℤ y := by
    have hcast : ((Algebra.norm ℤ y : ℤ) : ℚ) =
        Algebra.norm ℚ ((y : 𝓞 (QFModel d)) : QFModel d) :=
      Algebra.coe_norm_int y
    exact_mod_cast hcast.symm ▸ hynormQ
  have hx : x ≠ 0 := by
    intro h
    apply hxK
    exact congrArg Subtype.val h
  have hy : y ≠ 0 := by
    intro h
    apply hyK
    exact congrArg Subtype.val h
  exact form_princ_scali hd hd1 I J hI hJ bI bJ
    x y hx hy hxnorm hynorm hscale

omit [Module.Finite ℚ (QFModel d)] in
/-- The evident basis `(a, omega + r)` of a positive-leading mapped form ideal has positive
orientation, independently of the sign of the quadratic discriminant. -/
theorem mappe_posit_orien
    (Q : BQForm) (r : ℤ)
    (hb : Q.b = quadraticParameterB d + 2 * r)
    (hdisc : Q.discriminant =
      quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d)
    (ha : 0 < Q.a) :
    IsPositivelyOriented (ringBasis hd hd1)
      (Q.mappedIdealBasis (orderEquiv hd hd1) r hb hdisc ha.ne') := by
  rw [IsPositivelyOriented, basisCoordinateMatrix, Matrix.det_fin_two]
  simp only [BQForm.mapped_form_ideal]
  have h0 :
      (((Q.toIdealBasis r hb hdisc ha.ne' 0 : Q.toIdeal r hb hdisc) :
        QOrd (quadraticOrderParameter d) (quadraticParameterB d))) = Q.a :=
    BQForm.lattice_basis_coe _ _ Q.a r Q.c
      (Q.lattice_relation r hb hdisc) ha.ne'
  have h1 :
      (((Q.toIdealBasis r hb hdisc ha.ne' 1 : Q.toIdeal r hb hdisc) :
        QOrd (quadraticOrderParameter d) (quadraticParameterB d))) =
          QuadraticAlgebra.omega +
            (r : QOrd (quadraticOrderParameter d)
              (quadraticParameterB d)) :=
    BQForm.lattice_one_coe _ _ Q.a r Q.c
      (Q.lattice_relation r hb hdisc) ha.ne'
  simp only [ringBasis, quadraticIntegersBasis, orderEquiv,
    Basis.toMatrix_apply,
    Fin.isValue, Int.sub_pos, gt_iff_lt]
  rw [h0, h1]
  simp
  simpa using ha

/-- The norm-form class attached to a genuine narrow ideal class, for an arbitrary squarefree
quadratic radicand. -/
noncomputable def narrowGroupForm
    (C : NCGroup (QFModel d)) :
    ProperPrimitDiscri (quadraticFundamentalDiscriminant d) :=
  POData.proper_primi_class hd hd1
    (squarefree_emod_cases hd) (ringBasis hd hd1)
    ⟨NCGroup.integralRepresentative C,
      NCGroup.integr_repre_bot C,
      integ_repre_basis hd hd1 C⟩

/-- Reconstructing the narrow ideal class of its chosen positive-leading norm form returns the
original narrow class. -/
theorem form_narrow_group
    (C : NCGroup (QFModel d)) :
    FNarrow.narrowGroup hd hd1
        (narrowGroupForm hd hd1 C) = C := by
  let I := NCGroup.integralRepresentative C
  let b := integ_repre_basis hd hd1 C
  let X : POData (ringBasis hd hd1) :=
    ⟨I, NCGroup.integr_repre_bot C, b⟩
  let Q : ProperPrimitive (quadraticFundamentalDiscriminant d) :=
    X.proper_primi_form hd hd1 (squarefree_emod_cases hd) (ringBasis hd hd1)
  have ha : 0 < Q.1.a := by
    change 0 < (formOfBasis I b.1).a
    simpa [I, b] using integ_repre_pos hd hd1 C
  let r := FNarrow.middleRoot Q
  have hb : (formOfBasis I b.1).b = quadraticParameterB d + 2 * r := by
    exact (FNarrow.middleRoot_spec Q).1
  have hdisc : (formOfBasis I b.1).discriminant =
      quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d :=
    Q.2.1.trans (fundam_discr_param d)
  have hinverse := narrow_mapped_form hd hd1 I
    (NCGroup.integr_repre_bot C) b ha r hb hdisc
  change FNarrow.narrowGroup hd hd1 (Quotient.mk _ Q) = C
  rw [FNarrow.narrow_mk_pos hd hd1 Q ha]
  simpa [FNarrow.ofPositiveRepresentative,
    mappedFormBasis, Q, X, I, b, r] using
    hinverse.trans (NCGroup.mk_integralRepresentative C)

/-- Taking the explicit narrow ideal class of a corrected form and then its chosen norm form
returns the original proper-equivalence class. -/
theorem narrow_class_form
    (F : ProperPrimitDiscri (quadraticFundamentalDiscriminant d)) :
    narrowGroupForm hd hd1
        (FNarrow.narrowGroup hd hd1 F) = F := by
  refine Quotient.inductionOn F ?_
  intro Q
  let Qpos := FNarrow.positiveRepresentative hd hd1 Q
  have ha : 0 < Qpos.1.a := FNarrow.representative_pos hd hd1 Q
  let r := FNarrow.middleRoot Qpos
  let hdisc := Qpos.2.1.trans (fundam_discr_param d)
  let J : Ideal (𝓞 (QFModel d)) :=
    Qpos.1.mappedFormIdeal (orderEquiv hd hd1) r
      (FNarrow.middleRoot_spec Qpos).1 hdisc
  have hJ : J ≠ ⊥ := by
    change Qpos.1.mappedFormIdeal (orderEquiv hd hd1) r
      (FNarrow.middleRoot_spec Qpos).1 hdisc ≠ ⊥
    rw [BQForm.mappedFormIdeal]
    intro hbot
    apply Qpos.1.ideal_ne r (FNarrow.middleRoot_spec Qpos).1
      hdisc ha.ne'
    exact (Ideal.map_eq_bot_iff_of_injective (orderEquiv hd hd1).injective).mp hbot
  let bJ : Basis (Fin 2) ℤ J :=
    Qpos.1.mappedIdealBasis (orderEquiv hd hd1) r
      (FNarrow.middleRoot_spec Qpos).1 hdisc ha.ne'
  have hbJ : IsPositivelyOriented (ringBasis hd hd1) bJ := by
    simpa [bJ, J, r, hdisc] using
      mappe_posit_orien hd hd1 Qpos.1 r
        (FNarrow.middleRoot_spec Qpos).1 hdisc ha
  let C := FNarrow.ofPositiveRepresentative hd hd1 Qpos ha
  let I := NCGroup.integralRepresentative C
  have hI : I ≠ ⊥ := NCGroup.integr_repre_bot C
  let bI := integ_repre_basis hd hd1 C
  have hclasses :
      NCGroup.mk (QFModel d)
          (FractionalIdeal.mk0 (QFModel d)
            ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩) =
        NCGroup.mk (QFModel d)
          (FractionalIdeal.mk0 (QFModel d)
            ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩) := by
    rw [show NCGroup.mk (QFModel d)
        (FractionalIdeal.mk0 (QFModel d)
          ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩) = C by
      exact NCGroup.mk_integralRepresentative C]
    rfl
  have hchoice := form_class_narrow hd hd1 I J hI hJ bI
    (⟨bJ, hbJ⟩ : PositivelyOrientedBasis (ringBasis hd hd1) J) hclasses
  let R := QOrd (quadraticOrderParameter d) (quadraticParameterB d)
  letI : IsDomain R :=
    (orderEquiv hd hd1).toMulEquiv.isDomain (𝓞 (QFModel d))
  letI : IsNoetherianRing R :=
    isNoetherianRing_of_ringEquiv (𝓞 (QFModel d)) (orderEquiv hd hd1).symm
  letI : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv (orderEquiv hd hd1).symm
  letI : Ring.DimensionLEOne R := Ring.DimensionLEOne.of_ringEquiv (orderEquiv hd hd1)
  letI : IsDedekindDomain R :=
    (isDedekindDomain_iff (A := R) (FractionRing R)).2
      ⟨inferInstance, inferInstance, inferInstance,
        (isIntegrallyClosed_iff (R := R) (FractionRing R)).mp inferInstance⟩
  have hinverse : formOfBasis J bJ = Qpos.1 := by
    simpa [J, bJ, r, hdisc] using
      Qpos.1.form_basis_mapped (orderEquiv hd hd1) (ringBasis hd hd1)
        r (FNarrow.middleRoot_spec Qpos).1 hdisc ha
  have hJclass :
      POData.proper_primi_class hd hd1
          (squarefree_emod_cases hd) (ringBasis hd hd1) ⟨J, hJ, ⟨bJ, hbJ⟩⟩ =
        Quotient.mk _ Q := by
    apply Quotient.sound
    change (formOfBasis J bJ).Equivalent Q.1
    rw [hinverse]
    exact equivalent_trans
      (equivalent_symm (FNarrow.positiver_equivale hd hd1 Q))
      (equivalent_refl Q.1)
  change narrowGroupForm hd hd1 C = Quotient.mk _ Q
  exact hchoice.trans hJclass

/-- **Theorem 4.29, corrected general statement.**  Narrow ideal classes of a squarefree
quadratic field correspond to proper classes of primitive forms of its fundamental
discriminant, with the positive-definite component selected when the discriminant is negative. -/
noncomputable def narrowClassForm :
    NCGroup (QFModel d) ≃
      ProperPrimitDiscri (quadraticFundamentalDiscriminant d) where
  toFun := narrowGroupForm hd hd1
  invFun := FNarrow.narrowGroup hd hd1
  left_inv := form_narrow_group hd hd1
  right_inv := narrow_class_form hd hd1

end General

end NGEquiv

/-- **Milne, Theorem 4.29 (imaginary quadratic fields).**  For a negative squarefree integer
`d`, narrow ideal classes of `Q(sqrt d)` correspond bijectively to proper equivalence classes of
positive primitive forms of the field discriminant.  The positivity restriction corrects the
over-broad printed target, which would otherwise also contain the negative-definite component. -/
noncomputable def narrowClassEquivimaginary {d : ℤ} (hd : Squarefree d) (hdneg : d < 0) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd (by omega)
    letI : Module.Finite ℚ (QFModel d) :=
      quadraticModuleFinite hd (by omega)
    letI : NumberField (QFModel d) :=
      quadraticFieldNumber hd (by omega)
    NCGroup (QFModel d) ≃
      BQForm.ProperPrimitDiscri
        (quadraticFundamentalDiscriminant d) := by
  let hd1 : d ≠ 1 := by omega
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) :=
    quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) :=
    quadraticFieldNumber hd hd1
  exact NGEquiv.imaginaryNarrowForm hd hd1 hdneg

/-- **Milne, Theorem 4.29 (corrected general statement).**  For every squarefree `d ≠ 1`,
the narrow ideal classes of `Q(sqrt d)` correspond to proper equivalence classes of primitive
integral binary quadratic forms of the field discriminant.  When the discriminant is negative,
the form target selects its positive-definite component; when it is positive, all primitive
indefinite forms remain, and positive leading coefficient is used only for representatives in the
construction. -/
noncomputable def narrowClass29 {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) :=
      quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) :=
      quadraticFieldNumber hd hd1
    NCGroup (QFModel d) ≃
      BQForm.ProperPrimitDiscri
        (quadraticFundamentalDiscriminant d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) :=
    quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) :=
    quadraticFieldNumber hd hd1
  exact NGEquiv.General.narrowClassForm hd hd1

end

end Submission.NumberTheory.Milne
