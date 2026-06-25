import Submission.NumberTheory.Quadratic.NarrowNormClass
import Submission.NumberTheory.Quadratic.FieldFormSetup

/-!
# Milne, Algebraic Number Theory, Theorem 4.29: quadratic ideal norm forms

For the explicit model `QFModel d = Q(sqrt d)`, this file proves that the normalized
norm form of a nonzero integral ideal belongs to the corrected form-side target of Theorem 4.29.
The discriminant is the fundamental discriminant, primitivity follows from squarefreeness, and in
the imaginary case positivity follows from the coordinate formula `re^2 - d im^2` for the norm.

We then package the resulting forward map on nonzero integral ideals equipped with a positively
oriented basis and prove independence of that basis.
-/

namespace Submission.NumberTheory.Milne

open Submission.NumberTheory
open scoped NumberField QuadraticAlgebra
open Module

noncomputable section

namespace QIMap

private theorem quadratic_algebra_formula (A B : ℤ)
    (x : QuadraticAlgebra ℤ A B) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ A B) x = 2 * x.re + B * x.im := by
  have hmat : Algebra.leftMulMatrix (QuadraticAlgebra.basis A B) x =
      !![x.re, A * x.im; x.im, x.re + B * x.im] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis,
        QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis A B), hmat,
    Matrix.trace_fin_two_of]
  ring

/-- The discriminant of the standard basis of `Z[omega]`, where `omega^2 = A + B omega`. -/
theorem quadratic_discr_basis (A B : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis A B) = B ^ 2 + 4 * A := by
  rw [Algebra.discr_def]
  have hmat : Algebra.traceMatrix ℤ (QuadraticAlgebra.basis A B) =
      !![2, B; B, 2 * A + B ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        quadratic_algebra_formula, QuadraticAlgebra.basis,
        QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd]
    ring
  rw [hmat, Matrix.det_fin_two_of]
  ring

/-- A ring equivalence from the ring of integers to an explicit order transports the standard
order basis into a basis computing the number-field discriminant. -/
theorem number_discr_order
    {K R : Type*} [Field K] [NumberField K] [CommRing R]
    (e : 𝓞 K ≃+* R) (b : Basis (Fin 2) ℤ R) :
    NumberField.discr K = Algebra.discr ℤ b := by
  let eAlg : R ≃ₐ[ℤ] 𝓞 K :=
    AlgEquiv.ofRingEquiv (f := e.symm) (fun z ↦ by simp)
  let b' : Basis (Fin 2) ℤ (𝓞 K) := b.map eAlg.toLinearEquiv
  calc
    NumberField.discr K = Algebra.discr ℤ b' :=
      (NumberField.discr_eq_discr K b').symm
    _ = Algebra.discr ℤ b := by
      simpa [b'] using
        (Algebra.discr_eq_discr_of_algEquiv (b : Fin 2 → R) eAlg).symm

/-- The explicit quadratic-field model has Milne's fundamental discriminant. -/
theorem discr_quadratic_model
    (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)] :
    NumberField.discr (QFModel d) = quadraticFundamentalDiscriminant d :=
  quadraticField_discr hd hd1

/-- Coordinate formula for the norm in the explicit quadratic-field model. -/
theorem norm_quadratic_model (d : ℤ) (x : QFModel d) :
    Algebra.norm ℚ x = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
  have hmat : Algebra.leftMulMatrix (QuadraticAlgebra.basis (d : ℚ) 0) x =
      !![x.re, (d : ℚ) * x.im; x.im, x.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis,
        QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis (d : ℚ) 0), hmat,
    Matrix.det_fin_two_of]
  ring

/-- In an imaginary quadratic field, every nonzero element has positive rational norm. -/
theorem quadratic_model_pos {d : ℤ} (hdneg : d < 0)
    (x : QFModel d) (hx : x ≠ 0) :
    0 < Algebra.norm ℚ x := by
  rw [norm_quadratic_model]
  have hcoords : x.re ≠ 0 ∨ x.im ≠ 0 := by
    contrapose! hx
    apply QuadraticAlgebra.ext <;> simp [hx.1, hx.2]
  rcases hcoords with hre | him
  · have hre2 : 0 < x.re ^ 2 := sq_pos_of_ne_zero hre
    have him2 : 0 ≤ x.im ^ 2 := sq_nonneg _
    have hdnegQ : (d : ℚ) < 0 := by exact_mod_cast hdneg
    have hterm : 0 ≤ -(d : ℚ) * x.im ^ 2 :=
      mul_nonneg (le_of_lt (neg_pos.mpr hdnegQ)) him2
    nlinarith
  · have hre2 : 0 ≤ x.re ^ 2 := sq_nonneg _
    have him2 : 0 < x.im ^ 2 := sq_pos_of_ne_zero him
    have hdnegQ : (d : ℚ) < 0 := by exact_mod_cast hdneg
    have hterm : 0 < -(d : ℚ) * x.im ^ 2 :=
      mul_pos (neg_pos.mpr hdnegQ) him2
    nlinarith

/-- The integral norm of a nonzero algebraic integer in an imaginary quadratic model is
positive. -/
theorem int_pos_neg {d : ℤ} (hdneg : d < 0)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (x : 𝓞 (QFModel d)) (hx : x ≠ 0) :
    0 < Algebra.norm ℤ x := by
  have hpos := quadratic_model_pos hdneg (x : QFModel d) (by
    intro h
    apply hx
    exact Subtype.ext h)
  let canonical : Algebra ℚ (QFModel d) :=
    @DivisionRing.toRatAlgebra (QFModel d) inferInstance inferInstance
  have hRing :
      (QuadraticAlgebra.instField : Field (QFModel d)).toDivisionRing.toRing =
        (QuadraticAlgebra.instCommRing : CommRing (QFModel d)).toRing := by
    rfl
  have hposCanonical :
      0 < @Algebra.norm ℚ (QFModel d) inferInstance inferInstance canonical
        (x : QFModel d) := by
    cases hRing
    have hAlgebra : canonical = QuadraticAlgebra.instAlgebra := Subsingleton.elim _ _
    rw [hAlgebra]
    exact hpos
  have hcoe : ((Algebra.norm ℤ x : ℤ) : ℚ) =
      @Algebra.norm ℚ (QFModel d) inferInstance inferInstance canonical
        (x : QFModel d) := Algebra.coe_norm_int x
  have hcast : (0 : ℚ) < ((Algebra.norm ℤ x : ℤ) : ℚ) := by
    rw [hcoe]
    exact hposCanonical
  exact_mod_cast hcast

end QIMap

namespace INForm

open QIMap

/-- In an imaginary quadratic model, an ideal norm form has positive leading coefficient. -/
theorem form_pos_neg
    {d : ℤ} (hdneg : d < 0)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (I : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥)
    (b : Basis (Fin 2) ℤ I) :
    0 < (formOfBasis I b).a := by
  have hb0 : (b 0 : 𝓞 (QFModel d)) ≠ 0 := by
    intro h
    apply Basis.ne_zero b (0 : Fin 2)
    apply Subtype.ext
    exact h
  have hnorm : 0 < Algebra.norm ℤ (b 0 : 𝓞 (QFModel d)) :=
    int_pos_neg hdneg (b 0 : 𝓞 (QFModel d)) hb0
  have hmul := abs_norm_coeff I (b 0)
  have hnormI : 0 < (Ideal.absNorm I : ℤ) := by
    exact_mod_cast absNorm_pos hI
  change (Ideal.absNorm I : ℤ) * (formOfBasis I b).a =
    Algebra.norm ℤ (b 0 : 𝓞 (QFModel d)) at hmul
  nlinarith

/-- In the imaginary case the normalized ideal norm form is positive definite. -/
theorem form_definite_neg
    {d : ℤ} (hd : Squarefree d) (hdneg : d < 0)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (B : Basis (Fin 2) ℤ (𝓞 (QFModel d)))
    (I : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥)
    (b : Basis (Fin 2) ℤ I) :
    (formOfBasis I b).IsPositiveDefinite := by
  refine ⟨form_pos_neg hdneg I hI b, ?_⟩
  rw [form_basis_discriminant B hI b,
    QIMap.discr_quadratic_model d hd (by omega)]
  by_cases hmod : d % 4 = 1
  · simp [quadraticFundamentalDiscriminant, hmod, hdneg]
  · simp [quadraticFundamentalDiscriminant, hmod]
    nlinarith

/-- The normalized norm form of a nonzero ideal in the explicit quadratic model belongs to the
corrected target of Theorem 4.29. -/
theorem form_proper_primitive
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    (hmod : d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (B : Basis (Fin 2) ℤ (𝓞 (QFModel d)))
    (I : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥)
    (b : Basis (Fin 2) ℤ I) :
    BQForm.ProperDiscriminant
      (quadraticFundamentalDiscriminant d) (formOfBasis I b) := by
  have hdisc : (formOfBasis I b).discriminant = quadraticFundamentalDiscriminant d := by
    rw [form_basis_discriminant B hI b,
      QIMap.discr_quadratic_model d hd hd1]
  refine ⟨hdisc,
    BQForm.primit_funda_discr
      (formOfBasis I b) hd hmod hdisc, ?_⟩
  intro hDneg
  have hdneg : d < 0 := by
    by_cases hd1 : d % 4 = 1
    · simpa [quadraticFundamentalDiscriminant, hd1] using hDneg
    · simp only [quadraticFundamentalDiscriminant, if_neg hd1] at hDneg
      nlinarith
  exact form_definite_neg hd hdneg B I hI b

/-- A nonzero integral ideal together with a positively oriented ordered basis. -/
structure POData
    {d : ℤ} [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (B : Basis (Fin 2) ℤ (𝓞 (QFModel d))) where
  ideal : Ideal (𝓞 (QFModel d))
  ne_bot : ideal ≠ ⊥
  basis : PositivelyOrientedBasis B ideal

/-- The corrected-target representative attached to oriented integral ideal data. -/
def POData.proper_primi_form
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    (hmod : d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (B : Basis (Fin 2) ℤ (𝓞 (QFModel d)))
    (X : POData B) :
    BQForm.ProperPrimitive
      (quadraticFundamentalDiscriminant d) :=
  ⟨formOfBasis X.ideal X.basis.1,
    form_proper_primitive hd hd1 hmod B X.ideal X.ne_bot X.basis.1⟩

/-- The forward map from oriented integral ideal data to the corrected proper form class. -/
def POData.proper_primi_class
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    (hmod : d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (B : Basis (Fin 2) ℤ (𝓞 (QFModel d)))
    (X : POData B) :
    BQForm.ProperPrimitDiscri
      (quadraticFundamentalDiscriminant d) :=
  Quotient.mk _ (X.proper_primi_form hd hd1 hmod B)

/-- The forward map is independent of the positively oriented basis chosen for a fixed ideal. -/
theorem proper_primitive_same
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    (hmod : d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (B : Basis (Fin 2) ℤ (𝓞 (QFModel d)))
    (I : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥)
    (b b' : PositivelyOrientedBasis B I) :
    (POData.proper_primi_class hd hd1 hmod B ⟨I, hI, b⟩) =
      POData.proper_primi_class hd hd1 hmod B ⟨I, hI, b'⟩ := by
  apply Quotient.sound
  exact positi_orien_equiv B hI b b'

end INForm

end

end Submission.NumberTheory.Milne
