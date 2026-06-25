import Towers.NumberTheory.Cyclotomic.ClassNumberOne
import Towers.NumberTheory.Quadratic.PrimeDecomposition
import Mathlib.Analysis.Real.Pi.Bounds

attribute [-instance] DivisionRing.toRatAlgebra
attribute [-instance] QuadraticAlgebra.instAddMonoid
attribute [-instance] QuadraticAlgebra.instAddCommMonoid
attribute [-instance] QuadraticAlgebra.instAddGroup
attribute [-instance] QuadraticAlgebra.instAddCommGroup
attribute [-instance] QuadraticAlgebra.instAddCommMonoidWithOne
attribute [-instance] QuadraticAlgebra.instAddCommGroupWithOne
attribute [-instance] QuadraticAlgebra.instNonUnitalNonAssocSemiring
attribute [-instance] QuadraticAlgebra.instNonAssocSemiring
attribute [-instance] QuadraticAlgebra.instCommSemiring
attribute [-instance] QuadraticAlgebra.instModule
attribute [-instance] LieAlgebra.ofAssociativeAlgebra
open scoped NumberField

namespace Towers.NumberTheory.CNOne

private lemma quadratic_algebra_formula (A B : ℤ)
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

private theorem quadratic_discr_basis (A B : ℤ) :
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

end Towers.NumberTheory.CNOne

namespace Towers.NumberTheory.CNOne

private abbrev IntegralQuadraticOrder (m : ℤ) := QuadraticAlgebra ℤ m 0

private def integralOrderEmbedding (m : ℤ) :
    IntegralQuadraticOrder m →+* QFModel m where
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

private theorem integral_embedding_injective (m : ℤ) :
    Function.Injective (integralOrderEmbedding m) := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.re hxy)
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.im hxy)

private local instance integralOrderAlgebra (m : ℤ) :
    Algebra (IntegralQuadraticOrder m) (QFModel m) :=
  (integralOrderEmbedding m).toAlgebra

private local instance integralOrderScalarTower (m : ℤ) :
    IsScalarTower ℤ (IntegralQuadraticOrder m) (QFModel m) :=
  IsScalarTower.of_algebraMap_eq' rfl

@[reducible] private def integralOrderClosure (m : ℤ) (hm : Squarefree m)
    (hm1 : m % 4 ≠ 1) :
    IsIntegralClosure (IntegralQuadraticOrder m) ℤ (QFModel m) where
  algebraMap_injective := integral_embedding_injective m
  isIntegral_iff {x} := by
    rw [QFModel.integral_integer_coordinates m hm hm1]
    constructor
    · rintro ⟨a, b, ha, hb⟩
      refine ⟨(⟨a, b⟩ : IntegralQuadraticOrder m), ?_⟩
      apply QuadraticAlgebra.ext
      · exact ha.symm
      · exact hb.symm
    · rintro ⟨y, rfl⟩
      exact ⟨y.re, y.im, rfl, rfl⟩

private abbrev HalfQuadraticOrder (A : ℤ) := QuadraticAlgebra ℤ A 1

private def halfOrderEmbedding (A : ℤ) :
    HalfQuadraticOrder A →+* QFModel (4 * A + 1) where
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
      ring
    · simp only [QuadraticAlgebra.im_mul]
      push_cast
      ring

private theorem half_embedding_injective (A : ℤ) :
    Function.Injective (halfOrderEmbedding A) := by
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

private local instance halfOrderAlgebra (A : ℤ) :
    Algebra (HalfQuadraticOrder A) (QFModel (4 * A + 1)) :=
  (halfOrderEmbedding A).toAlgebra

private local instance halfOrderScalarTower (A : ℤ) :
    IsScalarTower ℤ (HalfQuadraticOrder A) (QFModel (4 * A + 1)) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext z <;> norm_num [halfOrderEmbedding])

@[reducible] private def halfIntegralClosure (A : ℤ)
    (hm : Squarefree (4 * A + 1)) (hm1 : (4 * A + 1) % 4 = 1) :
    IsIntegralClosure (HalfQuadraticOrder A) ℤ
      (QFModel (4 * A + 1)) where
  algebraMap_injective := half_embedding_injective A
  isIntegral_iff {x} := by
    rw [QFModel.integral_half_coordinates
      (4 * A + 1) hm hm1]
    constructor
    · rintro ⟨a, b, ha, hb⟩
      refine ⟨(⟨a, b⟩ : HalfQuadraticOrder A), ?_⟩
      apply QuadraticAlgebra.ext
      · exact ha.symm
      · exact hb.symm
    · rintro ⟨y, rfl⟩
      exact ⟨y.re, y.im, rfl, rfl⟩

private theorem number_field_discr
    (K R : Type*) [Field K] [NumberField K] [CommRing R]
    [Algebra R K] [IsIntegralClosure R ℤ K]
    (b : Module.Basis (Fin 2) ℤ R) :
    NumberField.discr K = Algebra.discr ℤ b := by
  let eRing : 𝓞 K ≃+* R :=
    @NumberField.RingOfIntegers.equiv K inferInstance R inferInstance
      inferInstance inferInstance
  let eAlg : R ≃ₐ[ℤ] 𝓞 K :=
    AlgEquiv.ofRingEquiv (f := eRing.symm) (fun z => by simp)
  let b' : Module.Basis (Fin 2) ℤ (𝓞 K) := b.map eAlg.toLinearEquiv
  calc
    NumberField.discr K = Algebra.discr ℤ b' :=
      (NumberField.discr_eq_discr K b').symm
    _ = Algebra.discr ℤ b := by
      simpa [b'] using
        (Algebra.discr_eq_discr_of_algEquiv (b : Fin 2 → R) eAlg).symm

private theorem discr_pi_sq
    (K : Type*) [Field K] [NumberField K] (d : ℤ) (hd : d < 0)
    (hdiscr : NumberField.discr K = d)
    (hfinrank :
      @Module.finrank ℚ K inferInstance inferInstance
        (@Algebra.toModule ℚ K inferInstance inferInstance
          (@DivisionRing.toRatAlgebra K inferInstance inferInstance)) = 2)
    (hbound : ((|d| : ℤ) : ℝ) < Real.pi ^ 2) :
    NumberField.classNumber K = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    have hcard2 : NumberField.InfinitePlace.nrRealPlaces K +
        2 * NumberField.InfinitePlace.nrComplexPlaces K = 2 :=
      hcard.trans hfinrank
    have hsle : NumberField.InfinitePlace.nrComplexPlaces K ≤ 1 := by omega
    have hsign := NumberField.sign_discr (K := K)
    rw [hdiscr] at hsign
    interval_cases hC : NumberField.InfinitePlace.nrComplexPlaces K
    · have hsignD : d.sign = -1 := Int.sign_eq_neg_one_of_neg hd
      rw [hsignD] at hsign
      norm_num at hsign
    · rfl
  rw [hdiscr, hcomplex, hfinrank]
  norm_num
  rw [show (2 * (Real.pi / 4) * 2) ^ 2 = Real.pi ^ 2 by ring]
  simpa using hbound

/-- The `m = -2` positive case in the Baker--Heegner--Stark list. -/
theorem negative_number_neg :
    negativeQuadraticNumber (-2) (by norm_num) = 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ ((-2 : ℤ) : ℚ) + 0 * r) :=
    ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩
  let coordinateEquiv : QFModel (-2) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
    { toFun := fun x => ![x.re, x.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := fun _ => rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; ext i; fin_cases i <;> rfl
      map_smul' := by
        intro c x
        have hc_re : ((c : QFModel (-2)).re) = c := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-2)) c]
          rfl
        have hc_im : ((c : QFModel (-2)).im) = 0 := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-2)) c]
          rfl
        ext i
        fin_cases i <;>
          simp [Algebra.smul_def, QuadraticAlgebra.re_mul,
            QuadraticAlgebra.im_mul, hc_re, hc_im] }
  let coordinateBasis : Module.Basis (Fin 2) ℚ (QFModel (-2)) :=
    Module.Basis.ofEquivFun coordinateEquiv
  letI : Module.Finite ℚ (QFModel (-2)) :=
    Module.Finite.of_basis coordinateBasis
  letI : NumberField (QFModel (-2)) :=
    NumberField.of_module_finite ℚ (QFModel (-2))
  have hm : Squarefree (-2 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact Nat.squarefree_two
  let hclosure : IsIntegralClosure (IntegralQuadraticOrder (-2)) ℤ
      (QFModel (-2)) :=
    integralOrderClosure (-2) hm (by norm_num)
  letI : IsIntegralClosure (IntegralQuadraticOrder (-2)) ℤ
      (QFModel (-2)) := hclosure
  change NumberField.classNumber (QFModel (-2)) = 1
  have hdiscr : NumberField.discr (QFModel (-2)) = -8 := by
    calc
      NumberField.discr (QFModel (-2)) =
          Algebra.discr ℤ (QuadraticAlgebra.basis (-2) 0) :=
        @number_field_discr (QFModel (-2))
          (IntegralQuadraticOrder (-2)) inferInstance inferInstance inferInstance
          (integralOrderEmbedding (-2)).toAlgebra hclosure
          (QuadraticAlgebra.basis (-2) 0)
      _ = -8 := by simpa using quadratic_discr_basis (-2) 0
  have hfinrank : Module.finrank ℚ (QFModel (-2)) = 2 := by
    rw [Module.finrank_eq_card_basis coordinateBasis]
    simp
  have hfinrank_numberField :
      @Module.finrank ℚ (QFModel (-2)) inferInstance inferInstance
        (@Algebra.toModule ℚ (QFModel (-2)) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (QFModel (-2)) inferInstance
            inferInstance)) = 2 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (QFModel (-2))) =
          @DivisionRing.toRatAlgebra (QFModel (-2)) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  refine discr_pi_sq
    (QFModel (-2)) (-8) (by norm_num) hdiscr hfinrank_numberField ?_
  norm_num
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  nlinarith

/-- The `m = -3` positive case in the Baker--Heegner--Stark list. -/
theorem negative_quadratic_neg :
    negativeQuadraticNumber (-3) (by norm_num) = 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ ((-3 : ℤ) : ℚ) + 0 * r) :=
    ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩
  let coordinateEquiv : QFModel (-3) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
    { toFun := fun x => ![x.re, x.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := fun _ => rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; ext i; fin_cases i <;> rfl
      map_smul' := by
        intro c x
        have hc_re : ((c : QFModel (-3)).re) = c := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-3)) c]
          rfl
        have hc_im : ((c : QFModel (-3)).im) = 0 := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-3)) c]
          rfl
        ext i
        fin_cases i <;>
          simp [Algebra.smul_def, QuadraticAlgebra.re_mul,
            QuadraticAlgebra.im_mul, hc_re, hc_im] }
  let coordinateBasis : Module.Basis (Fin 2) ℚ (QFModel (-3)) :=
    Module.Basis.ofEquivFun coordinateEquiv
  letI : Module.Finite ℚ (QFModel (-3)) :=
    Module.Finite.of_basis coordinateBasis
  letI : NumberField (QFModel (-3)) :=
    NumberField.of_module_finite ℚ (QFModel (-3))
  have hm : Squarefree (-3 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact Nat.prime_three.squarefree
  letI : Algebra (HalfQuadraticOrder (-1)) (QFModel (-3)) := by
    simpa using (halfOrderEmbedding (-1)).toAlgebra
  letI : IsScalarTower ℤ (HalfQuadraticOrder (-1))
      (QFModel (-3)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z <;> norm_num [halfOrderEmbedding])
  have hm' : Squarefree (4 * (-1 : ℤ) + 1) := by simpa using hm
  let hclosure : IsIntegralClosure (HalfQuadraticOrder (-1)) ℤ
      (QFModel (-3)) := by
    simpa using halfIntegralClosure (-1) hm' (by norm_num)
  letI : IsIntegralClosure (HalfQuadraticOrder (-1)) ℤ
      (QFModel (-3)) := hclosure
  change NumberField.classNumber (QFModel (-3)) = 1
  have hdiscr : NumberField.discr (QFModel (-3)) = -3 := by
    calc
      NumberField.discr (QFModel (-3)) =
          Algebra.discr ℤ (QuadraticAlgebra.basis (-1) 1) :=
        @number_field_discr (QFModel (-3))
          (HalfQuadraticOrder (-1)) inferInstance inferInstance inferInstance
          inferInstance hclosure
          (QuadraticAlgebra.basis (-1) 1)
      _ = -3 := by simpa using quadratic_discr_basis (-1) 1
  have hfinrank : Module.finrank ℚ (QFModel (-3)) = 2 := by
    rw [Module.finrank_eq_card_basis coordinateBasis]
    simp
  have hfinrank_numberField :
      @Module.finrank ℚ (QFModel (-3)) inferInstance inferInstance
        (@Algebra.toModule ℚ (QFModel (-3)) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (QFModel (-3)) inferInstance
            inferInstance)) = 2 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (QFModel (-3))) =
          @DivisionRing.toRatAlgebra (QFModel (-3)) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  refine discr_pi_sq
    (QFModel (-3)) (-3) (by norm_num) hdiscr hfinrank_numberField ?_
  norm_num
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  nlinarith

/-- The `m = -7` positive case in the Baker--Heegner--Stark list. -/
theorem negative_quadratic_seven :
    negativeQuadraticNumber (-7) (by norm_num) = 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ ((-7 : ℤ) : ℚ) + 0 * r) :=
    ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩
  let coordinateEquiv : QFModel (-7) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
    { toFun := fun x => ![x.re, x.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := fun _ => rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; ext i; fin_cases i <;> rfl
      map_smul' := by
        intro c x
        have hc_re : ((c : QFModel (-7)).re) = c := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-7)) c]
          rfl
        have hc_im : ((c : QFModel (-7)).im) = 0 := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-7)) c]
          rfl
        ext i
        fin_cases i <;>
          simp [Algebra.smul_def, QuadraticAlgebra.re_mul,
            QuadraticAlgebra.im_mul, hc_re, hc_im] }
  let coordinateBasis : Module.Basis (Fin 2) ℚ (QFModel (-7)) :=
    Module.Basis.ofEquivFun coordinateEquiv
  letI : Module.Finite ℚ (QFModel (-7)) :=
    Module.Finite.of_basis coordinateBasis
  letI : NumberField (QFModel (-7)) :=
    NumberField.of_module_finite ℚ (QFModel (-7))
  have hm : Squarefree (-7 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 7).squarefree
  letI : Algebra (HalfQuadraticOrder (-2)) (QFModel (-7)) := by
    simpa using (halfOrderEmbedding (-2)).toAlgebra
  letI : IsScalarTower ℤ (HalfQuadraticOrder (-2))
      (QFModel (-7)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z <;> norm_num [halfOrderEmbedding])
  have hm' : Squarefree (4 * (-2 : ℤ) + 1) := by simpa using hm
  let hclosure : IsIntegralClosure (HalfQuadraticOrder (-2)) ℤ
      (QFModel (-7)) := by
    simpa using halfIntegralClosure (-2) hm' (by norm_num)
  letI : IsIntegralClosure (HalfQuadraticOrder (-2)) ℤ
      (QFModel (-7)) := hclosure
  change NumberField.classNumber (QFModel (-7)) = 1
  have hdiscr : NumberField.discr (QFModel (-7)) = -7 := by
    calc
      NumberField.discr (QFModel (-7)) =
          Algebra.discr ℤ (QuadraticAlgebra.basis (-2) 1) :=
        @number_field_discr (QFModel (-7))
          (HalfQuadraticOrder (-2)) inferInstance inferInstance inferInstance
          inferInstance hclosure
          (QuadraticAlgebra.basis (-2) 1)
      _ = -7 := by simpa using quadratic_discr_basis (-2) 1
  have hfinrank : Module.finrank ℚ (QFModel (-7)) = 2 := by
    rw [Module.finrank_eq_card_basis coordinateBasis]
    simp
  have hfinrank_numberField :
      @Module.finrank ℚ (QFModel (-7)) inferInstance inferInstance
        (@Algebra.toModule ℚ (QFModel (-7)) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (QFModel (-7)) inferInstance
            inferInstance)) = 2 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (QFModel (-7))) =
          @DivisionRing.toRatAlgebra (QFModel (-7)) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  refine discr_pi_sq
    (QFModel (-7)) (-7) (by norm_num) hdiscr hfinrank_numberField ?_
  norm_num
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  nlinarith

private theorem minkowski_floor_inert
    (K : Type*) [Field K] [NumberField K] [CharZero K] (bound : ℕ)
    (hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (Nat.factorial
            (@Module.finrank ℚ K inferInstance inferInstance
              (@Algebra.toModule ℚ K inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K inferInstance inferInstance))) /
          (@Module.finrank ℚ K inferInstance inferInstance
              (@Algebra.toModule ℚ K inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K inferInstance inferInstance))) ^
            (@Module.finrank ℚ K inferInstance inferInstance
              (@Algebra.toModule ℚ K inferInstance inferInstance
                (@DivisionRing.toRatAlgebra K inferInstance inferInstance))) *
          √|NumberField.discr K|)⌋₊ = bound)
    (hinert : ∀ p ∈ Finset.Icc 1 bound, p.Prime →
      (Ideal.span {(p : 𝓞 K)}).IsPrime) :
    NumberField.classNumber K = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  rw [hfloor]
  intro p hp hpprime P hP _
  have hp_span : (Ideal.span {(p : 𝓞 K)}).IsPrime := hinert p hp hpprime
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hspan_le : Ideal.span {(p : 𝓞 K)} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    simpa using
      ((Ideal.mem_of_liesOver (P := P) (p := Ideal.span {(p : ℤ)}) p).mp
        (Ideal.subset_span (Set.mem_singleton (p : ℤ))))
  have hspan_ne : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := by
    intro h
    have hmem : (p : 𝓞 K) ∈ (⊥ : Ideal (𝓞 K)) := by
      rw [← h]
      exact Ideal.subset_span (Set.mem_singleton (p : 𝓞 K))
    simp [hpprime.ne_zero] at hmem
  have hmax : (Ideal.span {(p : 𝓞 K)}).IsMaximal := hp_span.isMaximal hspan_ne
  have heq : Ideal.span {(p : 𝓞 K)} = P :=
    hmax.eq_of_le (Ideal.IsPrime.ne_top hP.1) hspan_le
  rw [← heq]
  exact ⟨p, rfl⟩

/-- The `m = -11` positive case in the Baker--Heegner--Stark list. -/
theorem negative_quadratic_eleven :
    negativeQuadraticNumber (-11) (by norm_num) = 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ ((-11 : ℤ) : ℚ) + 0 * r) :=
    ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩
  let coordinateEquiv : QFModel (-11) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
    { toFun := fun x => ![x.re, x.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := fun _ => rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; ext i; fin_cases i <;> rfl
      map_smul' := by
        intro c x
        have hc_re : ((c : QFModel (-11)).re) = c := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-11)) c]
          rfl
        have hc_im : ((c : QFModel (-11)).im) = 0 := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-11)) c]
          rfl
        ext i
        fin_cases i <;>
          simp [Algebra.smul_def, QuadraticAlgebra.re_mul,
            QuadraticAlgebra.im_mul, hc_re, hc_im] }
  let coordinateBasis : Module.Basis (Fin 2) ℚ (QFModel (-11)) :=
    Module.Basis.ofEquivFun coordinateEquiv
  letI : Module.Finite ℚ (QFModel (-11)) :=
    Module.Finite.of_basis coordinateBasis
  letI : NumberField (QFModel (-11)) :=
    NumberField.of_module_finite ℚ (QFModel (-11))
  have hm : Squarefree (-11 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 11).squarefree
  letI : Algebra (HalfQuadraticOrder (-3)) (QFModel (-11)) := by
    simpa using (halfOrderEmbedding (-3)).toAlgebra
  letI : IsScalarTower ℤ (HalfQuadraticOrder (-3))
      (QFModel (-11)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z <;> norm_num [halfOrderEmbedding])
  have hm' : Squarefree (4 * (-3 : ℤ) + 1) := by simpa using hm
  let hclosure : IsIntegralClosure (HalfQuadraticOrder (-3)) ℤ
      (QFModel (-11)) := by
    simpa using halfIntegralClosure (-3) hm' (by norm_num)
  letI : IsIntegralClosure (HalfQuadraticOrder (-3)) ℤ
      (QFModel (-11)) := hclosure
  change NumberField.classNumber (QFModel (-11)) = 1
  have hdiscr : NumberField.discr (QFModel (-11)) = -11 := by
    calc
      NumberField.discr (QFModel (-11)) =
          Algebra.discr ℤ (QuadraticAlgebra.basis (-3) 1) :=
        @number_field_discr (QFModel (-11))
          (HalfQuadraticOrder (-3)) inferInstance inferInstance inferInstance
          inferInstance hclosure
          (QuadraticAlgebra.basis (-3) 1)
      _ = -11 := by simpa using quadratic_discr_basis (-3) 1
  have hfinrank : Module.finrank ℚ (QFModel (-11)) = 2 := by
    rw [Module.finrank_eq_card_basis coordinateBasis]
    simp
  have hfinrank_numberField :
      @Module.finrank ℚ (QFModel (-11)) inferInstance inferInstance
        (@Algebra.toModule ℚ (QFModel (-11)) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (QFModel (-11)) inferInstance
            inferInstance)) = 2 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (QFModel (-11))) =
          @DivisionRing.toRatAlgebra (QFModel (-11)) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces
      (QFModel (-11)) = 1 := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
      (QFModel (-11))
    have hcard2 : NumberField.InfinitePlace.nrRealPlaces
          (QFModel (-11)) +
          2 * NumberField.InfinitePlace.nrComplexPlaces
            (QFModel (-11)) = 2 :=
      hcard.trans hfinrank_numberField
    have hsle : NumberField.InfinitePlace.nrComplexPlaces
        (QFModel (-11)) ≤ 1 := by omega
    have hsign := NumberField.sign_discr (K := QFModel (-11))
    rw [hdiscr] at hsign
    interval_cases hC : NumberField.InfinitePlace.nrComplexPlaces
        (QFModel (-11))
    · have : ((-11 : ℤ).sign) = -1 := Int.sign_eq_neg_one_of_neg (by norm_num)
      rw [this] at hsign
      norm_num at hsign
    · rfl
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (QFModel (-11)) *
        (Nat.factorial
            (@Module.finrank ℚ (QFModel (-11)) inferInstance inferInstance
              (@Algebra.toModule ℚ (QFModel (-11)) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (QFModel (-11)) inferInstance
                  inferInstance))) /
          (@Module.finrank ℚ (QFModel (-11)) inferInstance inferInstance
              (@Algebra.toModule ℚ (QFModel (-11)) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (QFModel (-11)) inferInstance
                  inferInstance))) ^
            (@Module.finrank ℚ (QFModel (-11)) inferInstance inferInstance
              (@Algebra.toModule ℚ (QFModel (-11)) inferInstance inferInstance
                (@DivisionRing.toRatAlgebra (QFModel (-11)) inferInstance
                  inferInstance))) *
          √|NumberField.discr (QFModel (-11))|)⌋₊ = 2 := by
    rw [hcomplex, hfinrank_numberField, hdiscr]
    norm_num
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hsqrt : (3.15 : ℝ) < √11 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      rw [show 4 / Real.pi * (1 / 2 * √11) = 2 * √11 / Real.pi by ring]
      rw [le_div_iff₀ Real.pi_pos]
      exact mul_le_mul_of_nonneg_left (le_of_lt (hpi.trans hsqrt)) (by norm_num)
    · have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hsqrt_sq : (√(11 : ℝ)) ^ 2 = 11 := Real.sq_sqrt (by norm_num)
      rw [show 4 / Real.pi * (1 / 2 * √11) = 2 * √11 / Real.pi by ring]
      norm_num
      rw [div_lt_iff₀ Real.pi_pos]
      nlinarith [Real.sqrt_nonneg (11 : ℝ)]
  let eRing : 𝓞 (QFModel (-11)) ≃+* HalfQuadraticOrder (-3) :=
    @NumberField.RingOfIntegers.equiv (QFModel (-11)) inferInstance
      (HalfQuadraticOrder (-3)) inferInstance inferInstance hclosure
  have htwoOrder :
      (Ideal.span {(2 : HalfQuadraticOrder (-3))}).IsPrime := by
    apply QOrd.inert_no_root (-3) 1 2
    intro r
    fin_cases r <;> decide
  letI : (Ideal.span {(2 : HalfQuadraticOrder (-3))}).IsPrime := htwoOrder
  have htwoMap :
      (Ideal.map eRing.symm
        (Ideal.span {(2 : HalfQuadraticOrder (-3))})).IsPrime :=
    Ideal.map_isPrime_of_equiv eRing.symm
  have hmap_eq : Ideal.map eRing.symm
      (Ideal.span {(2 : HalfQuadraticOrder (-3))}) =
      Ideal.span {(2 : 𝓞 (QFModel (-11)))} := by
    rw [Ideal.map_span]
    have htwo_map : eRing.symm (2 : HalfQuadraticOrder (-3)) =
        (2 : 𝓞 (QFModel (-11))) := by
      exact map_ofNat eRing.symm 2
    rw [Set.image_singleton, htwo_map]
  have htwo :
      (Ideal.span {(2 : 𝓞 (QFModel (-11)))}).IsPrime := by
    rw [← hmap_eq]
    exact htwoMap
  apply minkowski_floor_inert
    (QFModel (-11)) 2 hfloor
  intro p hp hpprime
  have hp_two : p = 2 := by
    have hp_le : p ≤ 2 := (Finset.mem_Icc.mp hp).2
    have hp_prime_two_le : 2 ≤ p := hpprime.two_le
    omega
  subst p
  exact htwo

private theorem floor_quadratic_minkowski
    (d bound : ℕ)
    (hlower : (bound : ℝ) * Real.pi ≤ 2 * √(d : ℝ))
    (hupper : 2 * √(d : ℝ) < ((bound + 1 : ℕ) : ℝ) * Real.pi) :
    ⌊4 / Real.pi * (1 / 2 * √(d : ℝ))⌋₊ = bound := by
  rw [show 4 / Real.pi * (1 / 2 * √(d : ℝ)) =
    2 * √(d : ℝ) / Real.pi by ring]
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ Real.pi_pos]
    exact hlower
  · rw [div_lt_iff₀ Real.pi_pos]
    simpa using hupper

private theorem negative_quadratic_half
    (A : ℤ) (hneg : 4 * A + 1 < 0) (hm : Squarefree (4 * A + 1))
    (bound : ℕ)
    (hfloorReal :
      ⌊4 / Real.pi * (1 / 2 * √|(((4 * A + 1 : ℤ) : ℝ))|)⌋₊ = bound)
    (hinertOrder : ∀ p ∈ Finset.Icc 1 bound, p.Prime →
      (Ideal.span {(p : HalfQuadraticOrder A)}).IsPrime) :
    negativeQuadraticNumber (4 * A + 1) hneg = 1 := by
  letI : Fact (∀ r : ℚ,
      r ^ 2 ≠ (((4 * A + 1 : ℤ) : ℚ)) + 0 * r) :=
    ⟨fun r hr => by
      simp only [zero_mul, add_zero] at hr
      have hmQ : (((4 * A + 1 : ℤ) : ℚ)) < 0 := by exact_mod_cast hneg
      nlinarith [sq_nonneg r]⟩
  let coordinateEquiv : QFModel (4 * A + 1) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
    { toFun := fun x => ![x.re, x.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := fun _ => rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; ext i; fin_cases i <;> rfl
      map_smul' := by
        intro c x
        have hc_re : ((c : QFModel (4 * A + 1)).re) = c := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (4 * A + 1)) c]
          rfl
        have hc_im : ((c : QFModel (4 * A + 1)).im) = 0 := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (4 * A + 1)) c]
          rfl
        ext i
        fin_cases i <;>
          simp [Algebra.smul_def, QuadraticAlgebra.re_mul,
            QuadraticAlgebra.im_mul, hc_re, hc_im] }
  let coordinateBasis : Module.Basis (Fin 2) ℚ
      (QFModel (4 * A + 1)) :=
    Module.Basis.ofEquivFun coordinateEquiv
  letI : Module.Finite ℚ (QFModel (4 * A + 1)) :=
    Module.Finite.of_basis coordinateBasis
  letI : NumberField (QFModel (4 * A + 1)) :=
    NumberField.of_module_finite ℚ (QFModel (4 * A + 1))
  let hclosure : IsIntegralClosure (HalfQuadraticOrder A) ℤ
      (QFModel (4 * A + 1)) :=
    halfIntegralClosure A hm (by omega)
  letI : IsIntegralClosure (HalfQuadraticOrder A) ℤ
      (QFModel (4 * A + 1)) := hclosure
  change NumberField.classNumber (QFModel (4 * A + 1)) = 1
  have hdiscr : NumberField.discr (QFModel (4 * A + 1)) =
      4 * A + 1 := by
    calc
      NumberField.discr (QFModel (4 * A + 1)) =
          Algebra.discr ℤ (QuadraticAlgebra.basis A 1) :=
        @number_field_discr (QFModel (4 * A + 1))
          (HalfQuadraticOrder A) inferInstance inferInstance inferInstance
          inferInstance hclosure (QuadraticAlgebra.basis A 1)
      _ = 4 * A + 1 := by
        rw [quadratic_discr_basis]
        ring
  have hfinrank : Module.finrank ℚ (QFModel (4 * A + 1)) = 2 := by
    rw [Module.finrank_eq_card_basis coordinateBasis]
    simp
  have hfinrank_numberField :
      @Module.finrank ℚ (QFModel (4 * A + 1)) inferInstance inferInstance
        (@Algebra.toModule ℚ (QFModel (4 * A + 1)) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (QFModel (4 * A + 1)) inferInstance
            inferInstance)) = 2 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (QFModel (4 * A + 1))) =
          @DivisionRing.toRatAlgebra (QFModel (4 * A + 1)) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces
      (QFModel (4 * A + 1)) = 1 := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
      (QFModel (4 * A + 1))
    have hcard2 : NumberField.InfinitePlace.nrRealPlaces
          (QFModel (4 * A + 1)) +
          2 * NumberField.InfinitePlace.nrComplexPlaces
            (QFModel (4 * A + 1)) = 2 :=
      hcard.trans hfinrank_numberField
    have hsle : NumberField.InfinitePlace.nrComplexPlaces
        (QFModel (4 * A + 1)) ≤ 1 := by omega
    have hsign := NumberField.sign_discr (K := QFModel (4 * A + 1))
    rw [hdiscr] at hsign
    interval_cases hC : NumberField.InfinitePlace.nrComplexPlaces
        (QFModel (4 * A + 1))
    · have hsignD : (4 * A + 1).sign = -1 :=
        Int.sign_eq_neg_one_of_neg hneg
      rw [hsignD] at hsign
      norm_num at hsign
    · rfl
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (QFModel (4 * A + 1)) *
        (Nat.factorial
            (@Module.finrank ℚ (QFModel (4 * A + 1)) inferInstance
              inferInstance
              (@Algebra.toModule ℚ (QFModel (4 * A + 1)) inferInstance
                inferInstance
                (@DivisionRing.toRatAlgebra (QFModel (4 * A + 1))
                  inferInstance inferInstance))) /
          (@Module.finrank ℚ (QFModel (4 * A + 1)) inferInstance
              inferInstance
              (@Algebra.toModule ℚ (QFModel (4 * A + 1)) inferInstance
                inferInstance
                (@DivisionRing.toRatAlgebra (QFModel (4 * A + 1))
                  inferInstance inferInstance))) ^
            (@Module.finrank ℚ (QFModel (4 * A + 1)) inferInstance
              inferInstance
              (@Algebra.toModule ℚ (QFModel (4 * A + 1)) inferInstance
                inferInstance
                (@DivisionRing.toRatAlgebra (QFModel (4 * A + 1))
                  inferInstance inferInstance))) *
          √|NumberField.discr (QFModel (4 * A + 1))|)⌋₊ = bound := by
    rw [hcomplex, hfinrank_numberField, hdiscr]
    norm_num
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hfloorReal
  let eRing : 𝓞 (QFModel (4 * A + 1)) ≃+* HalfQuadraticOrder A :=
    @NumberField.RingOfIntegers.equiv (QFModel (4 * A + 1)) inferInstance
      (HalfQuadraticOrder A) inferInstance inferInstance hclosure
  have hinert : ∀ p ∈ Finset.Icc 1 bound, p.Prime →
      (Ideal.span {(p : 𝓞 (QFModel (4 * A + 1)))}).IsPrime := by
    intro p hp hpprime
    have hpOrder := hinertOrder p hp hpprime
    letI : (Ideal.span {(p : HalfQuadraticOrder A)}).IsPrime := hpOrder
    have hpMap :
        (Ideal.map eRing.symm
          (Ideal.span {(p : HalfQuadraticOrder A)})).IsPrime :=
      Ideal.map_isPrime_of_equiv eRing.symm
    have hmap_eq : Ideal.map eRing.symm
        (Ideal.span {(p : HalfQuadraticOrder A)}) =
        Ideal.span {(p : 𝓞 (QFModel (4 * A + 1)))} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [← hmap_eq]
    exact hpMap
  exact minkowski_floor_inert
    (QFModel (4 * A + 1)) bound hfloor hinert

/-- The `m = -19` positive case in the Baker--Heegner--Stark list. -/
theorem negative_quadratic_nineteen :
    negativeQuadraticNumber (-19) (by norm_num) = 1 := by
  have hm : Squarefree (4 * (-5 : ℤ) + 1) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 19).squarefree
  have hfloor :
      ⌊4 / Real.pi *
        (1 / 2 * √|(((4 * (-5 : ℤ) + 1 : ℤ) : ℝ))|)⌋₊ = 2 := by
    norm_num
    apply floor_quadratic_minkowski 19 2
    · have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hsqrt : (4 : ℝ) < √19 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      calc
        (2 : ℝ) * Real.pi ≤ 2 * 3.15 :=
          mul_le_mul_of_nonneg_left (le_of_lt hpi) (by norm_num)
        _ ≤ 2 * √19 :=
          mul_le_mul_of_nonneg_left (by nlinarith [hsqrt]) (by norm_num)
    · have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hsqrt_sq : (√(19 : ℝ)) ^ 2 = 19 := Real.sq_sqrt (by norm_num)
      have hsqrt : √(19 : ℝ) < 4.5 := by
        nlinarith [Real.sqrt_nonneg (19 : ℝ)]
      norm_num
      calc
        2 * √(19 : ℝ) < 2 * 4.5 :=
          mul_lt_mul_of_pos_left hsqrt (by norm_num)
        _ < 3 * Real.pi := by nlinarith
  have hinert : ∀ p : ℕ, p ∈ Finset.Icc 1 2 → p.Prime →
      (Ideal.span {(p : HalfQuadraticOrder (-5))}).IsPrime := by
    intro p hp hpprime
    have hp_le : p ≤ 2 := (Finset.mem_Icc.mp hp).2
    have hp_ge : 2 ≤ p := hpprime.two_le
    have hp_two : p = 2 := by omega
    subst p
    apply QOrd.inert_no_root (-5) 1 2
    intro r
    fin_cases r <;> decide
  simpa using negative_quadratic_half
    (-5) (by norm_num) hm 2 hfloor hinert

/-- The `m = -43` positive case in the Baker--Heegner--Stark list. -/
theorem negative_quadratic_forty :
    negativeQuadraticNumber (-43) (by norm_num) = 1 := by
  have hm : Squarefree (4 * (-11 : ℤ) + 1) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 43).squarefree
  have hfloor :
      ⌊4 / Real.pi *
        (1 / 2 * √|(((4 * (-11 : ℤ) + 1 : ℤ) : ℝ))|)⌋₊ = 4 := by
    norm_num
    apply floor_quadratic_minkowski 43 4
    · have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hsqrt : (6.5 : ℝ) < √43 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      calc
        (4 : ℝ) * Real.pi ≤ 4 * 3.15 :=
          mul_le_mul_of_nonneg_left (le_of_lt hpi) (by norm_num)
        _ ≤ 2 * √43 := by nlinarith [hsqrt]
    · have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hsqrt_sq : (√(43 : ℝ)) ^ 2 = 43 := Real.sq_sqrt (by norm_num)
      have hsqrt : √(43 : ℝ) < 7 := by
        nlinarith [Real.sqrt_nonneg (43 : ℝ)]
      norm_num
      calc
        2 * √(43 : ℝ) < 2 * 7 :=
          mul_lt_mul_of_pos_left hsqrt (by norm_num)
        _ < 5 * Real.pi := by nlinarith
  have hinert : ∀ p : ℕ, p ∈ Finset.Icc 1 4 → p.Prime →
      (Ideal.span {(p : HalfQuadraticOrder (-11))}).IsPrime := by
    intro p hp hpprime
    have hp_le : p ≤ 4 := (Finset.mem_Icc.mp hp).2
    have hp_ge : 2 ≤ p := hpprime.two_le
    interval_cases p <;> norm_num at hpprime
    all_goals
      apply QOrd.inert_no_root (-11) 1 _
      intro r
      fin_cases r <;> decide
  simpa using negative_quadratic_half
    (-11) (by norm_num) hm 4 hfloor hinert

/-- The `m = -67` positive case in the Baker--Heegner--Stark list. -/
theorem negative_sixty_seven :
    negativeQuadraticNumber (-67) (by norm_num) = 1 := by
  have hm : Squarefree (4 * (-17 : ℤ) + 1) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 67).squarefree
  have hfloor :
      ⌊4 / Real.pi *
        (1 / 2 * √|(((4 * (-17 : ℤ) + 1 : ℤ) : ℝ))|)⌋₊ = 5 := by
    norm_num
    apply floor_quadratic_minkowski 67 5
    · have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hsqrt : (8 : ℝ) < √67 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      calc
        (5 : ℝ) * Real.pi ≤ 5 * 3.15 :=
          mul_le_mul_of_nonneg_left (le_of_lt hpi) (by norm_num)
        _ ≤ 2 * √67 := by nlinarith [hsqrt]
    · have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hsqrt_sq : (√(67 : ℝ)) ^ 2 = 67 := Real.sq_sqrt (by norm_num)
      have hsqrt : √(67 : ℝ) < 9 := by
        nlinarith [Real.sqrt_nonneg (67 : ℝ)]
      norm_num
      calc
        2 * √(67 : ℝ) < 2 * 9 :=
          mul_lt_mul_of_pos_left hsqrt (by norm_num)
        _ < 6 * Real.pi := by nlinarith
  have hinert : ∀ p : ℕ, p ∈ Finset.Icc 1 5 → p.Prime →
      (Ideal.span {(p : HalfQuadraticOrder (-17))}).IsPrime := by
    intro p hp hpprime
    have hp_le : p ≤ 5 := (Finset.mem_Icc.mp hp).2
    have hp_ge : 2 ≤ p := hpprime.two_le
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    interval_cases p <;> norm_num at hpprime
    all_goals
      apply QOrd.inert_no_root (-17) 1 _
      intro r
      fin_cases r <;> decide
  simpa using negative_quadratic_half
    (-17) (by norm_num) hm 5 hfloor hinert

/-- The `m = -163` positive case in the Baker--Heegner--Stark list. -/
theorem negative_quadratic_sixty :
    negativeQuadraticNumber (-163) (by norm_num) = 1 := by
  have hm : Squarefree (4 * (-41 : ℤ) + 1) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 163).squarefree
  have hfloor :
      ⌊4 / Real.pi *
        (1 / 2 * √|(((4 * (-41 : ℤ) + 1 : ℤ) : ℝ))|)⌋₊ = 8 := by
    norm_num
    apply floor_quadratic_minkowski 163 8
    · have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hsqrt : (12.7 : ℝ) < √163 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      calc
        (8 : ℝ) * Real.pi ≤ 8 * 3.15 :=
          mul_le_mul_of_nonneg_left (le_of_lt hpi) (by norm_num)
        _ ≤ 2 * √163 := by nlinarith [hsqrt]
    · have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hsqrt_sq : (√(163 : ℝ)) ^ 2 = 163 := Real.sq_sqrt (by norm_num)
      have hsqrt : √(163 : ℝ) < 13 := by
        nlinarith [Real.sqrt_nonneg (163 : ℝ)]
      norm_num
      calc
        2 * √(163 : ℝ) < 2 * 13 :=
          mul_lt_mul_of_pos_left hsqrt (by norm_num)
        _ < 9 * Real.pi := by nlinarith
  have hinert : ∀ p : ℕ, p ∈ Finset.Icc 1 8 → p.Prime →
      (Ideal.span {(p : HalfQuadraticOrder (-41))}).IsPrime := by
    intro p hp hpprime
    have hp_le : p ≤ 8 := (Finset.mem_Icc.mp hp).2
    have hp_ge : 2 ≤ p := hpprime.two_le
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    interval_cases p <;> norm_num at hpprime
    all_goals
      apply QOrd.inert_no_root (-41) 1 _
      intro r
      fin_cases r <;> decide
  simpa using negative_quadratic_half
    (-41) (by norm_num) hm 8 hfloor hinert

/-- The unconditional right-to-left direction of Wright's Theorem 74. -/
theorem negative_heegner_radicands
    {m : ℤ} (hm : m < 0) (hmem : m ∈ heegnerRadicands) :
    negativeQuadraticNumber m hm = 1 := by
  simp only [heegnerRadicands, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using negative_quadratic_number
  · simpa using negative_number_neg
  · simpa using negative_quadratic_neg
  · simpa using negative_quadratic_seven
  · simpa using negative_quadratic_eleven
  · simpa using negative_quadratic_nineteen
  · simpa using negative_quadratic_forty
  · simpa using negative_sixty_seven
  · simpa using negative_quadratic_sixty

end Towers.NumberTheory.CNOne
