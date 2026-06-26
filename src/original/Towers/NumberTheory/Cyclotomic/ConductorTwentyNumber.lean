import Towers.NumberTheory.Ideals.IdealNormCompatibility
import Towers.NumberTheory.Quadratic.NegativeClassNumbers
import Towers.NumberTheory.Quadratic.FieldFormSetup
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# The conductor-23 class-number obstruction

This file isolates the ideal-norm argument in Milne's unnumbered example
after Remark 6.6.  The class number of `Q(sqrt(-23))` is three, so it cannot
become principal in an extension of degree eleven.
-/

namespace Towers.NumberTheory.Milne

open Module NumberField
open scoped NumberField

noncomputable section

private local instance : Fact (∀ r : ℚ,
    r ^ 2 ≠ ((-23 : ℤ) : ℚ) + 0 * r) :=
  ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩

private local instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

section QuadraticGaussSum

variable (K : Type*) [Field K] [Algebra ℚ K]
  [IsCyclotomicExtension {23} ℚ K]

/-- The quadratic character modulo `23`, with values in a cyclotomic field. -/
noncomputable def conductorTwentyCharacter :
    MulChar (ZMod 23) K :=
  (quadraticChar (ZMod 23)).ringHomComp (algebraMap ℤ K)

/-- The additive character modulo `23` defined by the distinguished cyclotomic root. -/
noncomputable def conductorTwentyAdditive :
    AddChar (ZMod 23) K :=
  AddChar.zmodChar 23
    (IsCyclotomicExtension.zeta_spec 23 ℚ K).pow_eq_one

/-- The quadratic Gauss sum inside a field containing the `23`rd roots of unity. -/
noncomputable def conductorTwentyGauss : K :=
  gaussSum (conductorTwentyCharacter K)
    (conductorTwentyAdditive K)

/-- The classical quadratic Gauss-sum identity at `23`: the distinguished
Gauss sum is a square root of `-23`. -/
theorem conductor_twenty_gauss :
    conductorTwentyGauss K ^ 2 = -23 := by
  letI : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let χ := conductorTwentyCharacter K
  let ψ := conductorTwentyAdditive K
  have hχ : χ ≠ 1 := by
    simpa only [χ, conductorTwentyCharacter] using
      ((MulChar.ringHomComp_ne_one_iff
        (algebraMap ℤ K).injective_int).2
        (quadraticChar_ne_one (F := ZMod 23)
          ((ZMod.ringChar_zmod_n 23).substr (by norm_num))))
  have hquad : χ.IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod 23)).comp (algebraMap ℤ K)
  have hψ : ψ.IsPrimitive := by
    exact AddChar.zmodChar_primitive_of_primitive_root 23
      (IsCyclotomicExtension.zeta_spec 23 ℚ K)
  have hneg : χ (-1) = (-1 : K) := by
    change algebraMap ℤ K (quadraticChar (ZMod 23) (-1)) = -1
    rw [quadraticChar_neg_one
      ((ZMod.ringChar_zmod_n 23).substr (by norm_num))]
    norm_num [ZMod.χ₄]
  change gaussSum χ ψ ^ 2 = -23
  rw [gaussSum_sq hχ hquad hψ, hneg]
  norm_num [ZMod.card]

/-- The quadratic Gauss sum realizes `Q(sqrt(-23))` as a subfield of every
field containing the `23`rd roots of unity. -/
noncomputable def sqrtTwentyEmbedding :
    QFModel (-23) →ₐ[ℚ] K where
  toRingHom :=
    (QuadraticAlgebra.lift (R := ℚ) (A := K)
      ⟨conductorTwentyGauss K, by
        simpa [pow_two, Algebra.smul_def] using
          conductor_twenty_gauss K⟩).toRingHom
  commutes' q := by
    simp [QuadraticAlgebra.lift]

theorem sqrt_twenty_injective :
    Function.Injective (sqrtTwentyEmbedding K) :=
  (sqrtTwentyEmbedding K).injective

end QuadraticGaussSum

/-- The norm argument in Milne's conductor-`23` example: every degree-`11`
extension of `Q(sqrt(-23))` has nontrivial class group. -/
theorem twenty_eleven_extension
    (L : Type*) [Field L] [NumberField L]
    [Algebra (QFModel (-23)) L]
    [FiniteDimensional (QFModel (-23)) L]
    (hdegree : finrank (QFModel (-23)) L = 11) :
    NumberField.classNumber L ≠ 1 := by
  letI : Module ℚ (QFModel (-23)) :=
    (inferInstance : Algebra ℚ (QFModel (-23))).toModule
  letI : Module.Finite ℚ (QFModel (-23)) := by
    have hmodule :
        (inferInstance : Module ℚ (QFModel (-23))) =
          QuadraticAlgebra.instModule :=
      Subsingleton.elim _ _
    let nativeFinite := quadraticModuleFinite (d := -23) (by
        rw [← Int.squarefree_natAbs]
        norm_num
        exact (by norm_num : Nat.Prime 23).squarefree) (by norm_num)
    exact Eq.mp (congrArg (fun M : Module ℚ (QFModel (-23)) =>
      @Module.Finite ℚ (QFModel (-23)) _ _ M) hmodule).symm
        nativeFinite
  letI : NumberField (QFModel (-23)) :=
    NumberField.of_module_finite ℚ (QFModel (-23))
  have hclass : NumberField.classNumber (QFModel (-23)) = 3 := by
    change CNOne.negativeQuadraticNumber (-23) (by norm_num) = 3
    exact neg_twenty_three
  apply number_coprime_finrank
    (QFModel (-23)) L
  · omega
  · rw [hdegree, hclass]
    decide

/-- Milne's conductor-`23` example in its final cyclotomic form: the class
number of `Q(zeta_23)` is not one.  The quadratic Gauss sum constructs the
embedded copy of `Q(sqrt(-23))`, and the tower degree is `22 / 2 = 11`. -/
theorem conductor_twenty_ne :
    NumberField.classNumber (CyclotomicField 23 ℚ) ≠ 1 := by
  let K := CyclotomicField 23 ℚ
  letI : IsCyclotomicExtension {23} ℚ K :=
    CyclotomicField.isCyclotomicExtension 23 ℚ
  letI : Module.Finite ℚ (QFModel (-23)) :=
    Module.Finite.of_basis (QuadraticAlgebra.basis (-23) 0)
  let e := sqrtTwentyEmbedding K
  letI : Algebra (QFModel (-23)) K := e.toAlgebra
  letI : IsScalarTower ℚ (QFModel (-23)) K := {
    smul_assoc := fun q x y => by
      simp only [Algebra.smul_def]
      have hx : algebraMap (QFModel (-23)) K (q • x) =
          algebraMap ℚ K q *
            algebraMap (QFModel (-23)) K x := by
        change e (q • x) = algebraMap ℚ K q * e x
        have hsmul : q • x =
            algebraMap ℚ (QFModel (-23)) q * x := by
          have hAlgebra :
              (QuadraticAlgebra.instAlgebra :
                Algebra ℚ (QFModel (-23))) =
                @DivisionRing.toRatAlgebra (QFModel (-23))
                  inferInstance inferInstance :=
            Subsingleton.elim _ _
          have hmap :
              algebraMap ℚ (QFModel (-23)) q =
                QuadraticAlgebra.C q := by
            rw [← hAlgebra]
            exact (congrFun QuadraticAlgebra.C_eq_algebraMap q).symm
          rw [hmap, QuadraticAlgebra.C_mul_eq_smul]
        rw [hsmul, map_mul, e.commutes]
      have hqx :
          algebraMap (QFModel (-23)) K
              (algebraMap ℚ (QFModel (-23)) q * x) =
            algebraMap ℚ K q * algebraMap (QFModel (-23)) K x := by
        rw [map_mul]
        change e (algebraMap ℚ (QFModel (-23)) q) * e x =
          algebraMap ℚ K q * e x
        rw [e.commutes]
      rw [hqx, mul_assoc] }
  letI : FiniteDimensional (QFModel (-23)) K :=
    FiniteDimensional.right ℚ (QFModel (-23)) K
  have hbase : finrank ℚ (QFModel (-23)) = 2 :=
    QuadraticAlgebra.finrank_eq_two (-23 : ℚ) 0
  have htotal : finrank ℚ K = 22 := by
    simpa [K] using IsCyclotomicExtension.Rat.finrank 23 K
  have htower := Module.finrank_mul_finrank ℚ
    (QFModel (-23)) K
  have hrelative : finrank (QFModel (-23)) K = 11 := by
    rw [hbase, htotal] at htower
    omega
  exact twenty_eleven_extension
    K hrelative

end

end Towers.NumberTheory.Milne
