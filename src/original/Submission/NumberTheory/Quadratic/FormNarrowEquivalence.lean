import Submission.NumberTheory.Quadratic.FormIdealEquivalence
import Submission.NumberTheory.Quadratic.QuadraticTotalPositivity

/-!
# Milne, Algebraic Number Theory, Theorem 4.29: descent to narrow ideal classes

The integral scaling identity for properly equivalent forms says

`(a) I(Q.transform g) = (conj alpha) I(Q)`.

For positive leading coefficients, `conj alpha / a` has positive norm.  In a quadratic field,
either it or its negative is totally positive, and changing this sign does not change its
principal fractional ideal.  This file uses that observation to descend the explicit
form-to-ideal construction to the genuine narrow class group.
-/

namespace Submission.NumberTheory.Milne

open Submission.NumberTheory
open scoped MatrixGroups NumberField QuadraticAlgebra nonZeroDivisors

noncomputable section

namespace BQForm

variable {A B : ℤ}

/-- The norm of the conjugate first transformed basis vector is the product of the old and
new leading coefficients. -/
theorem conjugate_first_vector
    (Q : BQForm) (r : ℤ) (g : SL(2, ℤ))
    (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) :
    QuadraticAlgebra.norm
        (conjugateBasisVector (A := A) (B := B) Q r g) =
      Q.a * (Q.transform g).a := by
  have hrel := Q.lattice_relation r hb hdisc
  have hA : A = r ^ 2 + B * r - Q.a * Q.c := by linarith
  simp only [QuadraticAlgebra.norm_def, conjugateBasisVector,
    QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul,
    QuadraticAlgebra.im_smul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
    QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.omega_re,
    QuadraticAlgebra.omega_im, BQForm.transform]
  norm_num
  rw [hb, hA]
  ring

/-- Regard a nonzero mapped form ideal as an invertible fractional ideal. -/
def mappedFormUnit
    {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K)
    (Q : BQForm) (r : ℤ)
    (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A)
    (ha : Q.a ≠ 0) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K
    ⟨mappedFormIdeal e Q r hb hdisc,
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        rw [mappedFormIdeal]
        intro h
        apply Q.ideal_ne r hb hdisc ha
        exact (Ideal.map_eq_bot_iff_of_injective e.injective).mp h)⟩

@[simp]
theorem coe_mapped_form
    {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K)
    (Q : BQForm) (r : ℤ)
    (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A)
    (ha : Q.a ≠ 0) :
    (mappedFormUnit e Q r hb hdisc ha :
        FractionalIdeal (𝓞 K)⁰ K) = mappedFormIdeal e Q r hb hdisc :=
  rfl

/-- **Theorem 4.29 (narrow-class descent).**  If two positive-leading forms of the
fundamental discriminant of `Q(sqrt d)` differ by an `SL(2, Z)` change of variables, their
explicit form ideals determine the same genuine narrow ideal class. -/
theorem narrow_mapped_transform
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    [Fact (∀ x : ℚ, x ^ 2 ≠ (d : ℚ) + 0 * x)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (Q : BQForm) (r r' : ℤ) (g : SL(2, ℤ))
    (hb : Q.b = quadraticParameterB d + 2 * r)
    (hb' : (Q.transform g).b = quadraticParameterB d + 2 * r')
    (hdisc : Q.discriminant =
      quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d)
    (ha : 0 < Q.a) (ha' : 0 < (Q.transform g).a) :
    NCGroup.mk (QFModel d)
        (mappedFormUnit
          (integersQuadraticOrder hd hd1).symm Q r hb hdisc ha.ne') =
      NCGroup.mk (QFModel d)
        (mappedFormUnit
          (integersQuadraticOrder hd hd1).symm (Q.transform g) r' hb'
            ((Q.discriminant_transform g).trans hdisc) ha'.ne') := by
  let e : QOrd (quadraticOrderParameter d) (quadraticParameterB d) ≃+*
      𝓞 (QFModel d) :=
    (integersQuadraticOrder hd hd1).symm
  let alphaBarOrder :
      QOrd (quadraticOrderParameter d) (quadraticParameterB d) :=
    conjugateBasisVector Q r g
  let alphaBarInt : 𝓞 (QFModel d) := e alphaBarOrder
  let aInt : 𝓞 (QFModel d) := e Q.a
  let x : QFModel d :=
    (alphaBarInt : QFModel d) / (aInt : QFModel d)
  have hnormOrder : QuadraticAlgebra.norm alphaBarOrder = Q.a * (Q.transform g).a := by
    exact Q.conjugate_first_vector r g hb hdisc
  have hnormInt : Algebra.norm ℤ alphaBarInt = Q.a * (Q.transform g).a := by
    change Algebra.norm ℤ (e alphaBarOrder) = _
    rw [algebra_quadratic_order]
    exact hnormOrder
  have hnormAlphaBar : Algebra.norm ℚ (alphaBarInt : QFModel d) =
      ((Q.a * (Q.transform g).a : ℤ) : ℚ) := by
    calc
      Algebra.norm ℚ (alphaBarInt : QFModel d) =
          ((Algebra.norm ℤ alphaBarInt : ℤ) : ℚ) :=
        (Algebra.coe_norm_int alphaBarInt).symm
      _ = ((Q.a * (Q.transform g).a : ℤ) : ℚ) := by rw [hnormInt]
  have hnormAInt : Algebra.norm ℤ aInt = Q.a ^ 2 := by
    change Algebra.norm ℤ (e (Q.a : QOrd
      (quadraticOrderParameter d) (quadraticParameterB d))) = _
    rw [algebra_quadratic_order, QuadraticAlgebra.norm_intCast]
    norm_cast
  have hnormA : Algebra.norm ℚ (aInt : QFModel d) = (Q.a : ℚ) ^ 2 := by
    calc
      Algebra.norm ℚ (aInt : QFModel d) =
          ((Algebra.norm ℤ aInt : ℤ) : ℚ) := (Algebra.coe_norm_int aInt).symm
      _ = (Q.a : ℚ) ^ 2 := by rw [hnormAInt]; norm_cast
  have halphaBarInt : alphaBarInt ≠ 0 := by
    intro h
    have hzero : Algebra.norm ℤ alphaBarInt = 0 := by simp [h]
    rw [hnormInt] at hzero
    exact (mul_ne_zero ha.ne' ha'.ne') hzero
  have haInt : aInt ≠ 0 := by
    have haOrder : (Q.a : QOrd
        (quadraticOrderParameter d) (quadraticParameterB d)) ≠ 0 := by
      intro h
      apply ha.ne'
      have hre := congrArg QuadraticAlgebra.re h
      simpa using hre
    simpa [aInt] using e.injective.ne haOrder
  have hx : x ≠ 0 := div_ne_zero (by
      intro h
      apply halphaBarInt
      exact Subtype.ext h) (by
      intro h
      apply haInt
      exact Subtype.ext h)
  have hnormX : 0 < Algebra.norm ℚ x := by
    have hnum : (0 : ℚ) < ((Q.a * (Q.transform g).a : ℤ) : ℚ) := by
      exact_mod_cast mul_pos ha ha'
    have hden : (0 : ℚ) < (Q.a : ℚ) ^ 2 := sq_pos_of_pos (by exact_mod_cast ha)
    change 0 < Algebra.norm ℚ
      ((alphaBarInt : QFModel d) / (aInt : QFModel d))
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, hnormAlphaBar, hnormA]
    exact mul_pos hnum (inv_pos.mpr hden)
  obtain ⟨epsilon, hepsilon, htotal⟩ :=
    QTPositi.sign_totally_positive x hx hnormX
  let numerator : 𝓞 (QFModel d) :=
    (epsilon : 𝓞 (QFModel d)) * alphaBarInt
  let t : QFModel d := (epsilon : QFModel d) * x
  have ht : ITPos (QFModel d) t := htotal
  have ht_ne : t ≠ 0 := by
    rcases hepsilon with rfl | rfl
    · simpa [t] using hx
    · simpa [t] using hx
  let tUnit : (QFModel d)ˣ := Units.mk0 t ht_ne
  have hnumeratorSpan :
      Ideal.span ({numerator} : Set (𝓞 (QFModel d))) =
        Ideal.span ({alphaBarInt} : Set (𝓞 (QFModel d))) := by
    rcases hepsilon with rfl | rfl
    · simp [numerator]
    · simpa only [numerator, Int.cast_neg, Int.cast_one, neg_mul, one_mul] using
        Ideal.span_singleton_neg alphaBarInt
  have haInt_mem : aInt ∈ (𝓞 (QFModel d))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr haInt
  have ht_fraction :
      t = IsLocalization.mk' (QFModel d) numerator ⟨aInt, haInt_mem⟩ := by
    rw [IsFractionRing.mk'_eq_div]
    simp only [t, x, numerator, map_mul, map_intCast,
      NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [mul_div_assoc]
  have hIntegralScale :
      Ideal.span ({numerator} : Set (𝓞 (QFModel d))) *
          mappedFormIdeal e Q r hb hdisc =
        Ideal.span ({aInt} : Set (𝓞 (QFModel d))) *
          mappedFormIdeal e (Q.transform g) r' hb'
            ((Q.discriminant_transform g).trans hdisc) := by
    rw [hnumeratorSpan]
    exact (leading_mapped_transform e Q r r' g hb hb' hdisc).symm
  have hFractionalScale :
      FractionalIdeal.spanSingleton (𝓞 (QFModel d))⁰ t *
          (mappedFormIdeal e Q r hb hdisc :
            FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d)) =
        (mappedFormIdeal e (Q.transform g) r' hb'
          ((Q.discriminant_transform g).trans hdisc) :
            FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d)) := by
    rw [ht_fraction]
    exact (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal
      (QFModel d) haInt_mem).mpr hIntegralScale
  apply (QuotientGroup.mk'_eq_mk'
    (NarrowPrincipalIdeals (QFModel d))).mpr
  refine ⟨toPrincipalIdeal (𝓞 (QFModel d)) (QFModel d) tUnit, ?_, ?_⟩
  · exact ⟨⟨tUnit, by simpa [tUnit] using ht⟩, rfl⟩
  · apply Units.ext
    simp only [Units.val_mul, coe_mapped_form, coe_toPrincipalIdeal]
    change
      (mappedFormIdeal e Q r hb hdisc :
          FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d)) *
          FractionalIdeal.spanSingleton (𝓞 (QFModel d))⁰ t =
        (mappedFormIdeal e (Q.transform g) r' hb'
          ((Q.discriminant_transform g).trans hdisc) :
            FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d))
    simpa only [mul_comm] using hFractionalScale

end BQForm

end

end Submission.NumberTheory.Milne
