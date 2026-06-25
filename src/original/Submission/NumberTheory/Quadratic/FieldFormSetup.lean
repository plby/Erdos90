import Submission.NumberTheory.Quadratic.QuadraticFormParameters

attribute [-instance] DivisionRing.toRatAlgebra

/-!
# The quadratic number field used in Theorem 4.29

This file installs the coordinate model `Q(sqrt d)` for a squarefree integer `d != 1`, identifies
its ring of integers with the appropriate quadratic order, transports the standard order basis to
the ring of integers, and computes the field discriminant.
-/

namespace Submission.NumberTheory.Milne

open Submission.NumberTheory
open Module
open scoped NumberField

noncomputable section

/-- A squarefree integer other than one is not a square in `Q`. -/
theorem radicand_nonsquare_rat {d : ℤ}
    (hd : Squarefree d) (hd1 : d ≠ 1) :
    ∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r := by
  intro r hr
  apply not_square_squarefree hd hd1
  rw [← Rat.isSquare_intCast_iff]
  refine ⟨r, ?_⟩
  simpa [pow_two] using hr.symm

/-- The irreducibility fact that gives the coordinate quadratic algebra its field structure. -/
@[reducible] def quadraticNonsquareFact {d : ℤ}
    (hd : Squarefree d) (hd1 : d ≠ 1) :
    Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
  ⟨radicand_nonsquare_rat hd hd1⟩

/-- The coordinate basis makes `Q(sqrt d)` finite-dimensional over `Q`. -/
@[reducible] def quadraticModuleFinite {d : ℤ}
    (hd : Squarefree d) (hd1 : d ≠ 1) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    Module.Finite ℚ (QFModel d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  exact Module.Finite.of_basis (QuadraticAlgebra.basis (d : ℚ) 0)

/-- The canonical number-field structure on the coordinate model `Q(sqrt d)`. -/
@[reducible] def quadraticFieldNumber {d : ℤ}
    (hd : Squarefree d) (hd1 : d ≠ 1) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    NumberField (QFModel d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  exact NumberField.of_module_finite ℚ (QFModel d)

private theorem quadratic_discr_basis (A B : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis A B) = B ^ 2 + 4 * A := by
  have htrace (x : QuadraticAlgebra ℤ A B) :
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
  rw [Algebra.discr_def]
  have hmat : Algebra.traceMatrix ℤ (QuadraticAlgebra.basis A B) =
      !![2, B; B, 2 * A + B ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, htrace,
        QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple,
        QuadraticAlgebra.equivProd]
    ring
  rw [hmat, Matrix.det_fin_two_of]
  ring

private def quadraticHalfEmbedding (d A : ℤ)
    (hA : 4 * A + 1 = d) :
    QOrd A 1 →+* QFModel d where
  toFun z := ⟨(z.re : ℚ) + (z.im : ℚ) / 2, (z.im : ℚ) / 2⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> norm_num
  map_one' := by
    apply QuadraticAlgebra.ext <;>
      norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;>
      push_cast <;> ring
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
      push_cast
      rw [← hA]
      push_cast
      ring
    · simp only [QuadraticAlgebra.im_mul]
      push_cast
      ring

private theorem quadratic_half_injective (d A : ℤ)
    (hA : 4 * A + 1 = d) :
    Function.Injective (quadraticHalfEmbedding d A hA) := by
  intro x y hxy
  have him := congrArg QuadraticAlgebra.im hxy
  change (x.im : ℚ) / 2 = (y.im : ℚ) / 2 at him
  have him' : (x.im : ℚ) = (y.im : ℚ) := by linarith
  have hre := congrArg QuadraticAlgebra.re hxy
  change (x.re : ℚ) + (x.im : ℚ) / 2 =
    (y.re : ℚ) + (y.im : ℚ) / 2 at hre
  have hre' : (x.re : ℚ) = (y.re : ℚ) := by linarith
  apply QuadraticAlgebra.ext
  · exact Rat.intCast_injective hre'
  · exact Rat.intCast_injective him'

@[reducible] private def quadraticHalfClosure (d A : ℤ)
    (hd : Squarefree d) (hmod : d % 4 = 1) (hA : 4 * A + 1 = d) :
    letI : Algebra (QOrd A 1) (QFModel d) :=
      (quadraticHalfEmbedding d A hA).toAlgebra
    IsIntegralClosure (QOrd A 1) ℤ (QFModel d) := by
  letI : Algebra (QOrd A 1) (QFModel d) :=
    (quadraticHalfEmbedding d A hA).toAlgebra
  exact
    { algebraMap_injective := quadratic_half_injective d A hA
      isIntegral_iff := by
        intro x
        rw [QFModel.integral_half_coordinates d hd hmod]
        constructor
        · rintro ⟨a, b, ha, hb⟩
          refine ⟨(⟨a, b⟩ : QOrd A 1), ?_⟩
          apply QuadraticAlgebra.ext
          · exact ha.symm
          · exact hb.symm
        · rintro ⟨y, rfl⟩
          exact ⟨y.re, y.im, rfl, rfl⟩ }

/-- The full ring of integers of `Q(sqrt d)` is the standard quadratic order with parameters
`A(d), B(d)`. -/
noncomputable def integersQuadraticOrder
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    NumberField.RingOfIntegers (QFModel d) ≃+*
      QOrd (quadraticOrderParameter d) (quadraticParameterB d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  by_cases hmod : d % 4 = 1
  · have hdiv : 4 ∣ d - 1 := Int.dvd_iff_emod_eq_zero.mpr (by omega)
    let A : ℤ := (d - 1) / 4
    have hA : 4 * A + 1 = d := by
      dsimp [A]
      have := Int.ediv_mul_cancel hdiv
      omega
    let eHom := quadraticHalfEmbedding d A hA
    letI : Algebra (QOrd A 1) (QFModel d) := eHom.toAlgebra
    let hclosure : IsIntegralClosure (QOrd A 1) ℤ (QFModel d) :=
      quadraticHalfClosure d A hd hmod hA
    let e : NumberField.RingOfIntegers (QFModel d) ≃+* QOrd A 1 :=
      @NumberField.RingOfIntegers.equiv (QFModel d) inferInstance
        (QOrd A 1) inferInstance eHom.toAlgebra hclosure
    have hparamA : quadraticOrderParameter d = A := by
      simp [quadraticOrderParameter, hmod, A]
    have hparamB : quadraticParameterB d = 1 := by
      simp [quadraticParameterB, hmod]
    rw [hparamA, hparamB]
    exact e
  · letI : Algebra (QOrd d 0) (QFModel d) :=
      quadraticIntegralAlgebra d
    let hclosure := quadratic_integral_closure d hd hmod
    let e : NumberField.RingOfIntegers (QFModel d) ≃+* QOrd d 0 :=
      @NumberField.RingOfIntegers.equiv (QFModel d) inferInstance
        (QOrd d 0) inferInstance inferInstance hclosure
    have hparamA : quadraticOrderParameter d = d := by
      simp [quadraticOrderParameter, hmod]
    have hparamB : quadraticParameterB d = 0 := by
      simp [quadraticParameterB, hmod]
    rw [hparamA, hparamB]
    exact e

/-- The basis of the ring of integers corresponding to `1, omega` in the standard quadratic
order. -/
noncomputable def quadraticIntegersBasis
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    Basis (Fin 2) ℤ (NumberField.RingOfIntegers (QFModel d)) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  let e := integersQuadraticOrder hd hd1
  let eAlg : QOrd (quadraticOrderParameter d) (quadraticParameterB d) ≃ₐ[ℤ]
      NumberField.RingOfIntegers (QFModel d) :=
    AlgEquiv.ofRingEquiv (f := e.symm) (fun z ↦ by simp)
  exact (QuadraticAlgebra.basis (quadraticOrderParameter d)
    (quadraticParameterB d)).map eAlg.toLinearEquiv

@[simp] theorem ring_integers_basis
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) (i : Fin 2) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    integersQuadraticOrder hd hd1 (quadraticIntegersBasis hd hd1 i) =
      QuadraticAlgebra.basis (quadraticOrderParameter d)
        (quadraticParameterB d) i := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  simp [quadraticIntegersBasis]

/-- The discriminant of the coordinate quadratic number field is its fundamental discriminant. -/
theorem quadraticField_discr {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    NumberField.discr (QFModel d) = quadraticFundamentalDiscriminant d := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  let e := integersQuadraticOrder hd hd1
  let eAlg : QOrd (quadraticOrderParameter d) (quadraticParameterB d) ≃ₐ[ℤ]
      NumberField.RingOfIntegers (QFModel d) :=
    AlgEquiv.ofRingEquiv (f := e.symm) (fun z ↦ by simp)
  let b := quadraticIntegersBasis hd hd1
  calc
    NumberField.discr (QFModel d) = Algebra.discr ℤ b :=
      (NumberField.discr_eq_discr (QFModel d) b).symm
    _ = Algebra.discr ℤ
          (QuadraticAlgebra.basis (quadraticOrderParameter d)
            (quadraticParameterB d)) := by
      simpa [b, quadraticIntegersBasis, e, eAlg] using
        (Algebra.discr_eq_discr_of_algEquiv
          (QuadraticAlgebra.basis (quadraticOrderParameter d)
            (quadraticParameterB d) :
              Fin 2 → QOrd (quadraticOrderParameter d)
                (quadraticParameterB d)) eAlg).symm
    _ = quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d :=
      quadratic_discr_basis _ _
    _ = quadraticFundamentalDiscriminant d :=
      (fundam_discr_param d).symm

end

end Submission.NumberTheory.Milne
