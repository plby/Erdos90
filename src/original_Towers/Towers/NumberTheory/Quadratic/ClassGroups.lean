import Towers.NumberTheory.Quadratic.HeegnerNumberOne
import Towers.NumberTheory.Quadratic.SqrtNonfreeIdeal
import Towers.NumberTheory.ClassGroup.MinkowskiClassBound
import Mathlib.RingTheory.PicardGroup

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

/-!
# Milne, Algebraic Number Theory, Examples 4.5 and 4.6

The Gaussian example is recorded through its class number and principal-ideal property.  For
`Z[sqrt(-5)]`, we record the explicit nonprincipal ideal used by Milne together with the fact that
its square is principal.
-/

namespace Towers.NumberTheory.Milne

open Ideal
open CommRing
open scoped NumberField nonZeroDivisors

private instance sqrt_no_divisors :
    NoZeroDivisors Towers.NumberTheory.SNFive where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    have hnorm : a.norm * b.norm = 0 := by
      rw [← Zsqrtd.norm_mul, hab, Zsqrtd.norm_zero]
    rcases mul_eq_zero.mp hnorm with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (by norm_num) a).mp ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (by norm_num) b).mp hb)

private instance sqrt_five_domain :
    IsDomain Towers.NumberTheory.SNFive :=
  NoZeroDivisors.to_isDomain _

private def negFiveEmbedding :
    Towers.NumberTheory.SNFive →+* QFModel (-5) where
  toFun z := ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_zero' := by ext <;> norm_num
  map_one' := by
    ext <;> norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by
    apply QuadraticAlgebra.ext
    · simp only [Zsqrtd.re_add, QuadraticAlgebra.re_add]
      norm_cast
    · simp only [Zsqrtd.im_add, QuadraticAlgebra.im_add]
      norm_cast
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp only [Zsqrtd.re_mul, QuadraticAlgebra.re_mul]
      push_cast
      ring
    · simp only [Zsqrtd.im_mul, QuadraticAlgebra.im_mul]
      push_cast
      ring

private theorem sqrt_neg_injective :
    Function.Injective negFiveEmbedding := by
  intro x y hxy
  ext
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.re hxy)
  · exact Rat.intCast_injective (congrArg QuadraticAlgebra.im hxy)

private local instance :
    Algebra Towers.NumberTheory.SNFive (QFModel (-5)) :=
  negFiveEmbedding.toAlgebra

private local instance :
    IsScalarTower ℤ Towers.NumberTheory.SNFive (QFModel (-5)) :=
  IsScalarTower.of_algebraMap_eq' rfl

@[reducible] private def sqrt_neg_closure :
    IsIntegralClosure Towers.NumberTheory.SNFive ℤ
      (QFModel (-5)) where
  algebraMap_injective := sqrt_neg_injective
  isIntegral_iff {x} := by
    have hm : Squarefree (-5 : ℤ) := by
      rw [← Int.squarefree_natAbs]
      norm_num
      exact Nat.prime_five.squarefree
    rw [QFModel.integral_integer_coordinates (-5) hm (by norm_num)]
    constructor
    · rintro ⟨a, b, ha, hb⟩
      refine ⟨(⟨a, b⟩ : Towers.NumberTheory.SNFive), ?_⟩
      apply QuadraticAlgebra.ext
      · exact ha.symm
      · exact hb.symm
    · rintro ⟨y, rfl⟩
      exact ⟨y.re, y.im, rfl, rfl⟩

private local instance :
    IsIntegralClosure Towers.NumberTheory.SNFive ℤ
      (QFModel (-5)) :=
  sqrt_neg_closure

private local instance : Fact (∀ r : ℚ, r ^ 2 ≠ ((-5 : ℤ) : ℚ) + 0 * r) :=
  ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩

private local instance : Module.Finite ℚ (QFModel (-5)) :=
  Module.Finite.of_basis (QuadraticAlgebra.basis (-5) 0)

private local instance : IsScalarTower ℤ ℚ (QFModel (-5)) :=
  IsScalarTower.of_algebraMap_eq fun z => by
    apply QuadraticAlgebra.ext <;> simp

private local instance : NumberField (QFModel (-5)) := by
  exact NumberField.of_module_finite ℚ (QFModel (-5))

private local instance :
    IsDedekindDomain Towers.NumberTheory.SNFive :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ (QFModel (-5)) _

private local instance :
    Module.Free ℤ Towers.NumberTheory.SNFive :=
  IsIntegralClosure.module_free ℤ ℚ (QFModel (-5)) _

private local instance :
    IsNoetherian ℤ Towers.NumberTheory.SNFive :=
  IsIntegralClosure.isNoetherian ℤ ℚ (QFModel (-5)) _

private local instance :
    Module.Finite ℤ Towers.NumberTheory.SNFive :=
  inferInstance

private local instance :
    Ring.HasFiniteQuotients Towers.NumberTheory.SNFive :=
  Ring.HasFiniteQuotients.of_module_finite ℤ _

private theorem abs_ring_equiv
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Free ℤ A] [Module.Free ℤ B]
    (e : A ≃+* B) (I : Ideal A) :
    Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv.symm

private theorem sqrt_five_bot :
    SNFive.primeIdealTwo ≠ ⊥ := by
  intro hbot
  have hmem : (2 : Towers.NumberTheory.SNFive) ∈
      SNFive.primeIdealTwo := by
    rw [SNFive.prime_span_pair]
    exact Ideal.subset_span (by simp)
  rw [hbot] at hmem
  simp at hmem

private theorem sqrt_or_abs
    (I : Ideal Towers.NumberTheory.SNFive)
    (hI0 : I ≠ ⊥) (hI : Ideal.absNorm I ≤ 2) :
    I = ⊤ ∨ I = SNFive.primeIdealTwo := by
  have hnorm0 : Ideal.absNorm I ≠ 0 := by
    rw [Ideal.absNorm_ne_zero_iff]
    exact Ring.HasFiniteQuotients.finiteQuotient hI0
  interval_cases hnorm : Ideal.absNorm I
  · exact False.elim (hnorm0 rfl)
  · exact Or.inl (Ideal.absNorm_eq_one_iff.mp hnorm)
  · right
    have hprime : I.IsPrime := by
      apply Ideal.isPrime_of_irreducible_absNorm
      rw [hnorm]
      exact (Nat.irreducible_iff_nat_prime 2).mpr Nat.prime_two
    have hItop : I ≠ ⊤ := hprime.ne_top
    letI : Nontrivial
        (Towers.NumberTheory.SNFive ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr hItop
    have hcard : Nat.card
        (Towers.NumberTheory.SNFive ⧸ I) = 2 := by
      simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hnorm
    have htwo : (2 : Towers.NumberTheory.SNFive) ∈ I := by
      simpa [hnorm] using Ideal.absNorm_mem I
    let q : Towers.NumberTheory.SNFive ⧸ I :=
      Ideal.Quotient.mk I (⟨0, 1⟩ : Towers.NumberTheory.SNFive)
    have hq_sq : q ^ 2 = 1 := by
      have hminusfive :
          Ideal.Quotient.mk I (-5 : Towers.NumberTheory.SNFive) = 1 := by
        apply Ideal.Quotient.eq.mpr
        convert I.mul_mem_left
          (-3 : Towers.NumberTheory.SNFive) htwo using 1
      calc
        q ^ 2 = Ideal.Quotient.mk I
            ((⟨0, 1⟩ : Towers.NumberTheory.SNFive) ^ 2) := by
              rfl
        _ = Ideal.Quotient.mk I
            (-5 : Towers.NumberTheory.SNFive) := by
              congr 1
        _ = 1 := hminusfive
    have hq0 : q ≠ 0 := by
      intro hq
      rw [hq, zero_pow (by norm_num : 2 ≠ 0)] at hq_sq
      exact zero_ne_one hq_sq
    have hq1 : q = 1 := by
      obtain ⟨y, hy0, hyuniq⟩ := (Nat.card_eq_two_iff' (0 :
        Towers.NumberTheory.SNFive ⧸ I)).mp hcard
      exact (hyuniq q hq0).trans (hyuniq 1 one_ne_zero).symm
    have honeAdd :
        (⟨1, 1⟩ : Towers.NumberTheory.SNFive) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      calc
        Ideal.Quotient.mk I
            (⟨1, 1⟩ : Towers.NumberTheory.SNFive) = 1 + q := by
              rfl
        _ = 1 + 1 := by rw [hq1]
        _ = Ideal.Quotient.mk I
            (2 : Towers.NumberTheory.SNFive) := by rfl
        _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr htwo
    have hle : SNFive.primeIdealTwo ≤ I := by
      rw [SNFive.prime_span_pair, Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact htwo
      · exact honeAdd
    exact ((SNFive.prime_ideal_two.isMaximal
      sqrt_five_bot).eq_of_le hItop hle).symm

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

private def quadraticSqrtFive :
    QOrd (-5) 0 ≃ₐ[ℤ] Towers.NumberTheory.SNFive :=
  AlgEquiv.ofRingEquiv (f := SNFive.quadraticOrderEquiv) (fun z => by
    ext <;> simp [SNFive.quadraticOrderEquiv])

private noncomputable def sqrtFiveBasis :
    Module.Basis (Fin 2) ℤ Towers.NumberTheory.SNFive :=
  (QuadraticAlgebra.basis (-5) 0).map
    quadraticSqrtFive.toLinearEquiv

private noncomputable def integersSqrtFive :
    𝓞 (QFModel (-5)) ≃+*
      Towers.NumberTheory.SNFive :=
  @NumberField.RingOfIntegers.equiv (QFModel (-5)) inferInstance
    Towers.NumberTheory.SNFive inferInstance
    negFiveEmbedding.toAlgebra sqrt_neg_closure

private theorem sqrt_neg_finrank :
    Module.finrank ℚ (QFModel (-5)) = 2 :=
  QuadraticAlgebra.finrank_eq_two (-5 : ℚ) 0

private theorem sqrt_five_finrank :
    @Module.finrank ℚ (QFModel (-5)) inferInstance inferInstance
      (@Algebra.toModule ℚ (QFModel (-5)) inferInstance inferInstance
        (@DivisionRing.toRatAlgebra (QFModel (-5)) inferInstance
          inferInstance)) = 2 := by
  have hAlgebra :
      (inferInstance : Algebra ℚ (QFModel (-5))) =
        @DivisionRing.toRatAlgebra (QFModel (-5)) inferInstance
          inferInstance :=
    Subsingleton.elim _ _
  rw [← hAlgebra]
  exact sqrt_neg_finrank

private theorem sqrt_five_discr :
    NumberField.discr (QFModel (-5)) = -20 := by
  let eAlg : Towers.NumberTheory.SNFive ≃ₐ[ℤ]
      𝓞 (QFModel (-5)) :=
    AlgEquiv.ofRingEquiv (f := integersSqrtFive.symm) (fun z => by simp)
  let b' : Module.Basis (Fin 2) ℤ (𝓞 (QFModel (-5))) :=
    sqrtFiveBasis.map eAlg.toLinearEquiv
  calc
    NumberField.discr (QFModel (-5)) = Algebra.discr ℤ b' :=
      (NumberField.discr_eq_discr (QFModel (-5)) b').symm
    _ = Algebra.discr ℤ sqrtFiveBasis := by
      simpa [b'] using
        (Algebra.discr_eq_discr_of_algEquiv
          (sqrtFiveBasis : Fin 2 →
            Towers.NumberTheory.SNFive) eAlg).symm
    _ = Algebra.discr ℤ (QuadraticAlgebra.basis (-5) 0) := by
      simpa [sqrtFiveBasis] using
        (Algebra.discr_eq_discr_of_algEquiv
          (QuadraticAlgebra.basis (-5) 0 : Fin 2 → QOrd (-5) 0)
          quadraticSqrtFive).symm
    _ = -20 := by norm_num [quadratic_discr_basis]

/-- The field discriminant of `ℚ(√-5)` is `-20`. -/
theorem sqrt_discr_twenty :
    NumberField.discr (QFModel (-5)) = -20 :=
  sqrt_five_discr

private theorem sqrt_nr_places :
    NumberField.InfinitePlace.nrComplexPlaces (QFModel (-5)) = 1 := by
  have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
    (QFModel (-5))
  have hcard2 :
      NumberField.InfinitePlace.nrRealPlaces (QFModel (-5)) +
          2 * NumberField.InfinitePlace.nrComplexPlaces (QFModel (-5)) = 2 :=
    hcard.trans sqrt_five_finrank
  have hsle :
      NumberField.InfinitePlace.nrComplexPlaces (QFModel (-5)) ≤ 1 := by
    omega
  have hsign := NumberField.sign_discr (K := QFModel (-5))
  rw [sqrt_five_discr] at hsign
  interval_cases hC :
      NumberField.InfinitePlace.nrComplexPlaces (QFModel (-5))
  · have hsignD : ((-20 : ℤ).sign) = -1 := Int.sign_eq_neg_one_of_neg (by norm_num)
    rw [hsignD] at hsign
    norm_num at hsign
  · rfl

private theorem sqrt_five_minkowski :
    (4 / Real.pi) ^
          NumberField.InfinitePlace.nrComplexPlaces (QFModel (-5)) *
        ((Nat.factorial (Module.finrank ℚ (QFModel (-5))) : ℝ) /
          (Module.finrank ℚ (QFModel (-5)) : ℝ) ^
            Module.finrank ℚ (QFModel (-5)) *
          Real.sqrt |NumberField.discr (QFModel (-5))|) < 3 := by
  rw [sqrt_nr_places, sqrt_neg_finrank,
    sqrt_five_discr]
  norm_num
  have hsqrt : Real.sqrt (20 : ℝ) < 9 / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 9 / 2)]
    norm_num
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi0 : 0 < Real.pi := Real.pi_pos
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpi0]
  nlinarith

/-- Example 4.5: the Gaussian quadratic field has class number one. -/
theorem gaussian_class_number :
    CNOne.negativeQuadraticNumber (-1) (by norm_num) = 1 :=
  CNOne.negative_quadratic_number

/-- Example 4.5: the Gaussian integers form a principal ideal ring. -/
theorem gaussian_int_ring : IsPrincipalIdealRing GaussianInt := inferInstance

/-- The explicit ideal in Example 4.6 is not principal. -/
theorem sqrt_five_principal :
    ¬ SNFive.primeIdealTwo.IsPrincipal :=
  SNFive.prime_not_principal

/-- The square of Milne's nonprincipal ideal is the principal ideal generated by `2`. -/
theorem sqrt_sq_principal :
    SNFive.primeIdealTwo ^ 2 =
      span {(2 : Towers.NumberTheory.SNFive)} :=
  SNFive.prime_ideal_sq

/-- The nonzero ideal `(2, 1 + sqrt(-5))`, viewed as an input to the class-group map. -/
noncomputable def sqrtFiveNonzero :
    (Ideal (Towers.NumberTheory.SNFive))⁰ :=
  ⟨SNFive.primeIdealTwo,
    mem_nonZeroDivisors_iff_ne_zero.mpr sqrt_five_bot⟩

/-- The class represented by `(2, 1 + sqrt(-5))`. -/
noncomputable def sqrtFiveNontrivial :
    ClassGroup Towers.NumberTheory.SNFive :=
  ClassGroup.mk0 sqrtFiveNonzero

/-- Milne's explicit ideal represents a nontrivial ideal class. -/
theorem sqrt_neg_nontrivial :
    sqrtFiveNontrivial ≠ 1 := by
  intro h
  apply SNFive.prime_not_principal
  exact (ClassGroup.mk0_eq_one_iff sqrtFiveNonzero.prop).mp h

set_option maxHeartbeats 800000 in
-- Expanding the square through the class-group quotient needs extra elaboration time.
/-- The class represented by `(2, 1 + sqrt(-5))` has square one. -/
theorem sqrt_nontrivial_sq :
    sqrtFiveNontrivial ^ 2 = 1 := by
  rw [sqrtFiveNontrivial, ← map_pow]
  rw [ClassGroup.mk0_eq_one_iff]
  rw [show ((sqrtFiveNonzero ^ 2 :
      (Ideal (Towers.NumberTheory.SNFive))⁰) :
      Ideal (Towers.NumberTheory.SNFive)) =
      SNFive.primeIdealTwo ^ 2 by rfl]
  rw [SNFive.prime_ideal_sq]
  exact ⟨2, rfl⟩

/-- The explicit nontrivial class in Example 4.6 has order exactly two. -/
theorem sqrt_five_nontrivial :
    orderOf sqrtFiveNontrivial = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime sqrt_nontrivial_sq
    sqrt_neg_nontrivial

/-- Example 4.6: the quadratic field `ℚ(√-5)` has class number exactly two. -/
theorem negative_quadratic_five :
    CNOne.negativeQuadraticNumber (-5) (by norm_num) = 2 := by
  change NumberField.classNumber (QFModel (-5)) = 2
  let e := integersSqrtFive
  let P : Ideal (𝓞 (QFModel (-5))) :=
    SNFive.primeIdealTwo.comap e
  have hmapP : P.map e = SNFive.primeIdealTwo := by
    exact Ideal.map_comap_of_surjective e e.surjective _
  have hPne : P ≠ ⊥ := by
    intro hP
    apply sqrt_five_bot
    rw [← hmapP, hP, Ideal.map_bot]
  let P0 : (Ideal (𝓞 (QFModel (-5))))⁰ :=
    ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hPne⟩
  let c : ClassGroup (𝓞 (QFModel (-5))) := ClassGroup.mk0 P0
  have hc : c ≠ 1 := by
    intro hc1
    have hprincipal : P.IsPrincipal := by
      exact (ClassGroup.mk0_eq_one_iff P0.prop).mp hc1
    have hmapPrincipal : (P.map e).IsPrincipal :=
      hprincipal.map_ringHom e
    rw [hmapP] at hmapPrincipal
    exact SNFive.prime_not_principal hmapPrincipal
  have hall : ∀ C : ClassGroup (𝓞 (QFModel (-5))), C = 1 ∨ C = c := by
    intro C
    obtain ⟨I, hIC, hnorm⟩ := NumberField.exists_ideal_in_class_of_norm_le C
    have hAlgebra :
        (QuadraticAlgebra.instAlgebra : Algebra ℚ (QFModel (-5))) =
          @DivisionRing.toRatAlgebra (QFModel (-5)) inferInstance
            inferInstance :=
      Subsingleton.elim _ _
    have hbound := sqrt_five_minkowski
    rw [hAlgebra] at hbound
    have hnormReal :
        (Ideal.absNorm (I : Ideal (𝓞 (QFModel (-5)))) : ℝ) < 3 :=
      lt_of_le_of_lt hnorm hbound
    have hnormNat :
        Ideal.absNorm (I : Ideal (𝓞 (QFModel (-5)))) ≤ 2 := by
      have : Ideal.absNorm (I : Ideal (𝓞 (QFModel (-5)))) < 3 := by
        exact_mod_cast hnormReal
      omega
    let J : Ideal Towers.NumberTheory.SNFive := (I : Ideal _).map e
    have hJne : J ≠ ⊥ := by
      change (I : Ideal (𝓞 (QFModel (-5)))).map e ≠ ⊥
      intro hJ
      exact (mem_nonZeroDivisors_iff_ne_zero.mp I.prop)
        ((Ideal.map_eq_bot_iff_of_injective e.injective).mp hJ)
    have hJnorm : Ideal.absNorm J ≤ 2 := by
      change Ideal.absNorm ((I : Ideal (𝓞 (QFModel (-5)))).map e) ≤ 2
      rw [abs_ring_equiv]
      exact hnormNat
    rcases sqrt_or_abs
        J hJne hJnorm with hJtop | hJP
    · left
      have hItop : (I : Ideal (𝓞 (QFModel (-5)))) = ⊤ := by
        apply (Ideal.map_eq_top_of_bijective e e.bijective).mp
        simpa [J] using hJtop
      have hIone : I = 1 := Subtype.ext (by simpa using hItop)
      rw [← hIC, hIone, map_one]
    · right
      have hIP : (I : Ideal (𝓞 (QFModel (-5)))) = P := by
        apply e.idealComapOrderIso.symm.injective
        exact (show (I : Ideal (𝓞 (QFModel (-5)))).map e = P.map e by
          rw [show (I : Ideal (𝓞 (QFModel (-5)))).map e = J by rfl,
            hJP, hmapP])
      have hIP0 : I = P0 := Subtype.ext hIP
      change C = ClassGroup.mk0 P0
      rw [← hIC, hIP0]
  change Fintype.card (ClassGroup (𝓞 (QFModel (-5)))) = 2
  let f : Fin 2 → ClassGroup (𝓞 (QFModel (-5))) := ![1, c]
  have hf_injective : Function.Injective f := by
    intro i j
    have hc' : (1 : ClassGroup (𝓞 (QFModel (-5)))) ≠ c := Ne.symm hc
    fin_cases i <;> fin_cases j <;> simp [f, hc, hc']
  have hf_surjective : Function.Surjective f := by
    intro C
    rcases hall C with rfl | rfl
    · exact ⟨0, by simp [f]⟩
    · exact ⟨1, by simp [f]⟩
  calc
    Fintype.card (ClassGroup (𝓞 (QFModel (-5)))) = Fintype.card (Fin 2) :=
      Fintype.card_congr (Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩).symm
    _ = 2 := Fintype.card_fin 2

private noncomputable def picardEquivRing
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

private noncomputable def classGroupRing
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    (e : A ≃+* B) : ClassGroup A ≃* ClassGroup B :=
  (ClassGroup.equivPic A).trans
    ((picardEquivRing e).trans (ClassGroup.equivPic B).symm)

/-- The concrete ideal class group of `ℤ[√-5]` has exactly two elements. -/
theorem sqrt_five_two :
    Nat.card (ClassGroup Towers.NumberTheory.SNFive) = 2 := by
  let E := classGroupRing integersSqrtFive
  calc
    Nat.card (ClassGroup Towers.NumberTheory.SNFive) =
        Nat.card (ClassGroup (𝓞 (QFModel (-5)))) :=
      Nat.card_congr E.symm.toEquiv
    _ = Fintype.card (ClassGroup (𝓞 (QFModel (-5)))) :=
      Nat.card_eq_fintype_card
    _ = NumberField.classNumber (QFModel (-5)) := rfl
    _ = 2 := by
      have h := negative_quadratic_five
      change NumberField.classNumber (QFModel (-5)) = 2 at h
      exact h

/-- In a Dedekind domain whose class group has two elements, the product of any two
nonprincipal nonzero ideals is principal. -/
theorem ideal_principal_two
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (hcard : Nat.card (ClassGroup R) = 2)
    {I J : Ideal R} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥)
    (hI : ¬ I.IsPrincipal) (hJ : ¬ J.IsPrincipal) :
    (I * J).IsPrincipal := by
  let I0 : (Ideal R)⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩
  let J0 : (Ideal R)⁰ :=
    ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ0⟩
  have hIc : ClassGroup.mk0 I0 ≠ 1 := by
    intro hc
    exact hI ((ClassGroup.mk0_eq_one_iff I0.prop).mp hc)
  have hJc : ClassGroup.mk0 J0 ≠ 1 := by
    intro hc
    exact hJ ((ClassGroup.mk0_eq_one_iff J0.prop).mp hc)
  obtain ⟨c, hc, hc_unique⟩ :=
    (Nat.card_eq_two_iff' (1 : ClassGroup R)).mp hcard
  have hclasses : ClassGroup.mk0 I0 = ClassGroup.mk0 J0 :=
    (hc_unique _ hIc).trans (hc_unique _ hJc).symm
  have hinv_ne : (ClassGroup.mk0 I0)⁻¹ ≠ 1 := by
    simpa using hIc
  have hinv_eq : (ClassGroup.mk0 I0)⁻¹ = ClassGroup.mk0 I0 :=
    (hc_unique _ hinv_ne).trans (hc_unique _ hIc).symm
  have hclassProduct : ClassGroup.mk0 I0 * ClassGroup.mk0 J0 = 1 := by
    calc
      ClassGroup.mk0 I0 * ClassGroup.mk0 J0 =
          ClassGroup.mk0 I0 * ClassGroup.mk0 I0 :=
        congrArg (fun x ↦ ClassGroup.mk0 I0 * x) hclasses.symm
      _ = (ClassGroup.mk0 I0)⁻¹ * ClassGroup.mk0 I0 :=
        congrArg (fun x ↦ x * ClassGroup.mk0 I0) hinv_eq.symm
      _ = 1 := inv_mul_cancel _
  let IJ0 : (Ideal R)⁰ := I0 * J0
  apply (ClassGroup.mk0_eq_one_iff IJ0.prop).mp
  have hIJ0 : IJ0 = I0 * J0 := by
    apply Subtype.ext
    rfl
  rw [hIJ0, map_mul]
  exact hclassProduct

/-- The class-number-two consequence used in Milne's introductory `ℤ[√-5]` example. -/
theorem sqrt_five_not
    {I J : Ideal Towers.NumberTheory.SNFive}
    (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥)
    (hI : ¬ I.IsPrincipal) (hJ : ¬ J.IsPrincipal) :
    (I * J).IsPrincipal :=
  ideal_principal_two
    sqrt_five_two hI0 hJ0 hI hJ

end Towers.NumberTheory.Milne
