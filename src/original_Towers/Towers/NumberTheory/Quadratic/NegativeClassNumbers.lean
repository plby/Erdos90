import Towers.NumberTheory.Quadratic.HeegnerNumberOne
import Towers.NumberTheory.ClassGroup.MinkowskiClassBound

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
# Milne, Chapter 4, Exercise 4

The imaginary quadratic fields of discriminants `-23` and `-47` have class numbers three and
five. We use the rings of integers with bases `1, omega`, where respectively
`omega^2 = omega - 6` and `omega^2 = omega - 12`.
-/

namespace Towers.NumberTheory.Milne

open Ideal
open scoped NumberField nonZeroDivisors QuadraticAlgebra

noncomputable section

private abbrev Numbers2347 (A : ℤ) := QOrd A 1

private theorem ideal_span_submodule {A : ℤ}
    (I : Ideal (Numbers2347 A)) (x : Numbers2347 A)
    (hx : (I : Submodule (Numbers2347 A) (Numbers2347 A)) =
      Submodule.span (Numbers2347 A) {x}) :
    I = span {x} := by
  apply Ideal.ext
  intro y
  change y ∈ (I : Submodule (Numbers2347 A) (Numbers2347 A)) ↔
    y ∈ Submodule.span (Numbers2347 A) {x}
  rw [hx]

private theorem int_algebra_norm (A : ℤ) (x : Numbers2347 A) :
    @Algebra.norm ℤ (Numbers2347 A) Int.instCommRing inferInstance
        (@Ring.toIntAlgebra (Numbers2347 A) inferInstance) x =
      Algebra.norm ℤ x := by
  have hAlgebra : (@Ring.toIntAlgebra (Numbers2347 A) inferInstance) =
      (QuadraticAlgebra.instAlgebra : Algebra ℤ (Numbers2347 A)) :=
    Subsingleton.elim _ _
  rw [hAlgebra]

private def numbers2347 (A : ℤ) :
    Numbers2347 A →+* QFModel (4 * A + 1) where
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

private theorem numbers_47_injective (A : ℤ) :
    Function.Injective (numbers2347 A) := by
  intro x y hxy
  have him := congrArg QuadraticAlgebra.im hxy
  have him' : (x.im : ℚ) = (y.im : ℚ) := by
    simpa [numbers2347] using congrArg (fun q : ℚ => 2 * q) him
  have himZ : x.im = y.im := Rat.intCast_injective him'
  have hre := congrArg QuadraticAlgebra.re hxy
  have hre' : (x.re : ℚ) = (y.re : ℚ) := by
    change (x.re : ℚ) + (x.im : ℚ) / 2 =
      (y.re : ℚ) + (y.im : ℚ) / 2 at hre
    linarith
  apply QuadraticAlgebra.ext
  · exact Rat.intCast_injective hre'
  · exact himZ

private local instance orderAlgebra (A : ℤ) :
    Algebra (Numbers2347 A) (QFModel (4 * A + 1)) :=
  (numbers2347 A).toAlgebra

private local instance orderScalarTower (A : ℤ) :
    IsScalarTower ℤ (Numbers2347 A) (QFModel (4 * A + 1)) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext z <;> norm_num [numbers2347])

@[reducible] private def negative_numbers_closure (A : ℤ)
    (hm : Squarefree (4 * A + 1)) (hm1 : (4 * A + 1) % 4 = 1) :
    IsIntegralClosure (Numbers2347 A) ℤ
      (QFModel (4 * A + 1)) where
  algebraMap_injective := numbers_47_injective A
  isIntegral_iff {x} := by
    rw [QFModel.integral_half_coordinates
      (4 * A + 1) hm hm1]
    constructor
    · rintro ⟨a, b, ha, hb⟩
      refine ⟨(⟨a, b⟩ : Numbers2347 A), ?_⟩
      apply QuadraticAlgebra.ext
      · exact ha.symm
      · exact hb.symm
    · rintro ⟨y, rfl⟩
      exact ⟨y.re, y.im, rfl, rfl⟩

private theorem numbers_47_formula (A B : ℤ)
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

private theorem numbers_47_discr (A B : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis A B) = B ^ 2 + 4 * A := by
  rw [Algebra.discr_def]
  have hmat : Algebra.traceMatrix ℤ (QuadraticAlgebra.basis A B) =
      !![2, B; B, 2 * A + B ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        numbers_47_formula, QuadraticAlgebra.basis,
        QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd]
    ring
  rw [hmat, Matrix.det_fin_two_of]
  ring

private local instance quadraticFieldModule (A : ℤ) :
    Module ℚ (QFModel (4 * A + 1)) :=
  QuadraticAlgebra.instModule

private theorem number_discr (A : ℤ)
    [Fact (∀ r : ℚ, r ^ 2 ≠ ((4 * A + 1 : ℤ) : ℚ) + 0 * r)]
    [Algebra ℚ (QFModel (4 * A + 1))]
    [Module.Finite ℚ (QFModel (4 * A + 1))]
    [NumberField (QFModel (4 * A + 1))]
    (hm : Squarefree (4 * A + 1)) (hm1 : (4 * A + 1) % 4 = 1) :
    NumberField.discr (QFModel (4 * A + 1)) = 4 * A + 1 := by
  let hclosure := negative_numbers_closure A hm hm1
  letI : IsIntegralClosure (Numbers2347 A) ℤ
      (QFModel (4 * A + 1)) := hclosure
  let eRing : 𝓞 (QFModel (4 * A + 1)) ≃+* Numbers2347 A :=
    @NumberField.RingOfIntegers.equiv (QFModel (4 * A + 1)) inferInstance
      (Numbers2347 A) inferInstance
      (numbers2347 A).toAlgebra hclosure
  let eAlg : Numbers2347 A ≃ₐ[ℤ]
      𝓞 (QFModel (4 * A + 1)) :=
    AlgEquiv.ofRingEquiv (f := eRing.symm) (fun z => by simp)
  let b' : Module.Basis (Fin 2) ℤ (𝓞 (QFModel (4 * A + 1))) :=
    (QuadraticAlgebra.basis A 1).map eAlg.toLinearEquiv
  calc
    NumberField.discr (QFModel (4 * A + 1)) = Algebra.discr ℤ b' :=
      (NumberField.discr_eq_discr (QFModel (4 * A + 1)) b').symm
    _ = Algebra.discr ℤ (QuadraticAlgebra.basis A 1) := by
      simpa [b'] using
        (Algebra.discr_eq_discr_of_algEquiv
          (QuadraticAlgebra.basis A 1 : Fin 2 → Numbers2347 A) eAlg).symm
    _ = 4 * A + 1 := by
      rw [numbers_47_discr]
      ring

private theorem order_norm_formula (A : ℤ)
    (x : Numbers2347 A) :
    Algebra.norm ℤ x = x.re ^ 2 + x.re * x.im - A * x.im ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis A 1)]
  have hmat : Algebra.leftMulMatrix (QuadraticAlgebra.basis A 1) x =
      !![x.re, A * x.im; x.im, x.re + x.im] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis,
        QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  rw [hmat, Matrix.det_fin_two_of]
  ring

private theorem numbers_23_47
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Module.Free ℤ R] [Module.Free ℤ S]
    (e : R ≃+* S) (I : Ideal R) :
    Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv.symm

private theorem classify_norm_ideal
    (A : ℤ) (p : ℕ) [Fact p.Prime]
    [NoZeroDivisors (Numbers2347 A)]
    [IsDedekindDomain (Numbers2347 A)]
    [Module.Free ℤ (Numbers2347 A)]
    [Module.Finite ℤ (Numbers2347 A)]
    (hpA : (p : ℤ) ∣ A) (I : Ideal (Numbers2347 A))
    (hnorm : Ideal.absNorm I = p) :
    I = QOrd.rootIdeal A 1 p 0 ∨
      I = QOrd.rootIdeal A 1 p 1 := by
  have hpA' := hpA
  have hIprime : I.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hnorm]
    exact (Nat.irreducible_iff_nat_prime p).mpr Fact.out
  have hpMem : (p : Numbers2347 A) ∈ I := by
    simpa [hnorm] using Ideal.absNorm_mem I
  obtain ⟨q, hA⟩ := hpA
  have hAMem : (A : Numbers2347 A) ∈ I := by
    convert I.mul_mem_left (q : Numbers2347 A) hpMem using 1
    apply QuadraticAlgebra.ext <;> simp
    simpa [mul_comm] using hA
  have hprod : QuadraticAlgebra.omega *
      (QuadraticAlgebra.omega - 1 : Numbers2347 A) ∈ I := by
    convert hAMem using 1
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  rcases hIprime.mem_or_mem hprod with hw | hw1
  · left
    symm
    apply (QOrd.root_ideal_maximal A 1 p 0 (by
      obtain ⟨q, rfl⟩ := hpA'
      simp)).eq_of_le hIprime.ne_top
    rw [QOrd.rootIdeal, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hpMem
    · simpa using hw
  · right
    symm
    apply (QOrd.root_ideal_maximal A 1 p 1 (by
      obtain ⟨q, rfl⟩ := hpA'
      simp)).eq_of_le hIprime.ne_top
    rw [QOrd.rootIdeal, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hpMem
    · simpa using hw1

private abbrev numbers_23_474 (A : ℤ) : Ideal (Numbers2347 A) :=
  QOrd.rootIdeal A 1 2 0

private abbrev numbers_474_q (A : ℤ) : Ideal (Numbers2347 A) :=
  QOrd.rootIdeal A 1 2 1

private abbrev numbers_474_u (A : ℤ) : Ideal (Numbers2347 A) :=
  QOrd.rootIdeal A 1 3 0

private abbrev numbers_474_v (A : ℤ) : Ideal (Numbers2347 A) :=
  QOrd.rootIdeal A 1 3 1

private theorem six_split_two :
    (numbers_23_474 (-6)).IsPrime ∧ (numbers_474_q (-6)).IsPrime ∧
      numbers_23_474 (-6) ≠ numbers_474_q (-6) ∧
      numbers_23_474 (-6) * numbers_474_q (-6) =
        span {(2 : Numbers2347 (-6))} := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa using QOrd.splits_at_root (-6) 1 2 0
    ⟨3, by norm_num⟩ ⟨0, -1, by norm_num⟩

private theorem neg_six_split :
    (numbers_474_u (-6)).IsPrime ∧ (numbers_474_v (-6)).IsPrime ∧
      numbers_474_u (-6) ≠ numbers_474_v (-6) ∧
      numbers_474_u (-6) * numbers_474_v (-6) =
        span {(3 : Numbers2347 (-6))} := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simpa using QOrd.splits_at_root (-6) 1 3 0
    ⟨2, by norm_num⟩ ⟨0, -1, by norm_num⟩

private theorem twelve_split_two :
    (numbers_23_474 (-12)).IsPrime ∧ (numbers_474_q (-12)).IsPrime ∧
      numbers_23_474 (-12) ≠ numbers_474_q (-12) ∧
      numbers_23_474 (-12) * numbers_474_q (-12) =
        span {(2 : Numbers2347 (-12))} := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa using QOrd.splits_at_root (-12) 1 2 0
    ⟨6, by norm_num⟩ ⟨0, -1, by norm_num⟩

private theorem neg_twelve_split :
    (numbers_474_u (-12)).IsPrime ∧ (numbers_474_v (-12)).IsPrime ∧
      numbers_474_u (-12) ≠ numbers_474_v (-12) ∧
      numbers_474_u (-12) * numbers_474_v (-12) =
        span {(3 : Numbers2347 (-12))} := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simpa using QOrd.splits_at_root (-12) 1 3 0
    ⟨4, by norm_num⟩ ⟨0, -1, by norm_num⟩

private theorem neg_six_u :
    numbers_23_474 (-6) * numbers_474_u (-6) =
      span {(QuadraticAlgebra.omega : Numbers2347 (-6))} := by
  change span {(2 : Numbers2347 (-6)), QuadraticAlgebra.omega} *
      span {(3 : Numbers2347 (-6)), QuadraticAlgebra.omega} = _
  rw [Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · apply Ideal.mem_span_singleton'.2
      exact ⟨(1 - QuadraticAlgebra.omega : Numbers2347 (-6)), by
        apply QuadraticAlgebra.ext <;>
          simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]⟩
    · exact Ideal.mem_span_singleton'.2 ⟨2, by ring⟩
    · exact Ideal.mem_span_singleton'.2 ⟨3, by ring⟩
    · exact Ideal.mem_span_singleton'.2
        ⟨QuadraticAlgebra.omega, by ring⟩
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    have hthree : (3 : Numbers2347 (-6)) * QuadraticAlgebra.omega ∈
        span ({(2 : Numbers2347 (-6)) * 3,
          (2 : Numbers2347 (-6)) * QuadraticAlgebra.omega,
          QuadraticAlgebra.omega * 3,
          QuadraticAlgebra.omega * QuadraticAlgebra.omega} :
            Set (Numbers2347 (-6))) :=
      Ideal.subset_span (by simp [mul_comm])
    have htwo : (2 : Numbers2347 (-6)) * QuadraticAlgebra.omega ∈
        span ({(2 : Numbers2347 (-6)) * 3,
          (2 : Numbers2347 (-6)) * QuadraticAlgebra.omega,
          QuadraticAlgebra.omega * 3,
          QuadraticAlgebra.omega * QuadraticAlgebra.omega} :
            Set (Numbers2347 (-6))) := Ideal.subset_span (by simp)
    convert (span _).sub_mem hthree htwo using 1

private theorem twelve_sq_u :
    numbers_23_474 (-12) ^ 2 * numbers_474_u (-12) =
      span {(QuadraticAlgebra.omega : Numbers2347 (-12))} := by
  change (span {(2 : Numbers2347 (-12)), QuadraticAlgebra.omega}) ^ 2 *
      span {(3 : Numbers2347 (-12)), QuadraticAlgebra.omega} = _
  rw [pow_two, Ideal.span_pair_mul_span_pair, Ideal.span_mul_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z ⟨x, hx, y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl
    all_goals
      apply Ideal.mem_span_singleton'.2
    · exact ⟨(1 - QuadraticAlgebra.omega : Numbers2347 (-12)), by
        apply QuadraticAlgebra.ext <;>
          simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]⟩
    · exact ⟨4, by ring⟩
    · exact ⟨6, by ring⟩
    · exact ⟨2 * QuadraticAlgebra.omega, by ring⟩
    · exact ⟨6, by ring⟩
    · exact ⟨2 * QuadraticAlgebra.omega, by ring⟩
    · exact ⟨3 * QuadraticAlgebra.omega, by ring⟩
    · exact ⟨QuadraticAlgebra.omega ^ 2, by ring⟩
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    let J : Ideal (Numbers2347 (-12)) :=
      span ({(2 : Numbers2347 (-12)) * 2,
        (2 : Numbers2347 (-12)) * QuadraticAlgebra.omega,
        QuadraticAlgebra.omega * 2,
        QuadraticAlgebra.omega * QuadraticAlgebra.omega} :
          Set (Numbers2347 (-12))) *
        span {(3 : Numbers2347 (-12)), QuadraticAlgebra.omega}
    have hfour : (4 : Numbers2347 (-12)) ∈
        span ({(2 : Numbers2347 (-12)) * 2,
          (2 : Numbers2347 (-12)) * QuadraticAlgebra.omega,
          QuadraticAlgebra.omega * 2,
          QuadraticAlgebra.omega * QuadraticAlgebra.omega} :
            Set (Numbers2347 (-12))) :=
      Ideal.subset_span (by norm_num)
    have homega : (QuadraticAlgebra.omega : Numbers2347 (-12)) ∈
        span {(3 : Numbers2347 (-12)), QuadraticAlgebra.omega} :=
      Ideal.subset_span (by simp)
    have hfourOmega : (4 : Numbers2347 (-12)) * QuadraticAlgebra.omega ∈ J :=
      Ideal.mul_mem_mul hfour homega
    have homegaSq : (QuadraticAlgebra.omega : Numbers2347 (-12)) ^ 2 ∈
        span ({(2 : Numbers2347 (-12)) * 2,
          (2 : Numbers2347 (-12)) * QuadraticAlgebra.omega,
          QuadraticAlgebra.omega * 2,
          QuadraticAlgebra.omega * QuadraticAlgebra.omega} :
            Set (Numbers2347 (-12))) := by
      apply Ideal.subset_span
      simp [pow_two]
    have hthree : (3 : Numbers2347 (-12)) ∈
        span {(3 : Numbers2347 (-12)), QuadraticAlgebra.omega} :=
      Ideal.subset_span (by simp)
    have hthreeOmegaSq : 3 * QuadraticAlgebra.omega ^ 2 ∈ J := by
      convert Ideal.mul_mem_mul homegaSq hthree using 1
    have htwelve : (12 : Numbers2347 (-12)) ∈ J := by
      convert Ideal.mul_mem_mul hfour hthree using 1
    have h := J.sub_mem (J.sub_mem hfourOmega hthreeOmegaSq)
      (J.mul_mem_left (3 : Numbers2347 (-12)) htwelve)
    have homegaJ : (QuadraticAlgebra.omega : Numbers2347 (-12)) ∈ J := by
      exact h
    simpa [J, Ideal.span_mul_span] using homegaJ

private theorem numbers_47_nonnegative (A : ℤ) (hA : A < 0)
    (x : Numbers2347 A) : 0 ≤ Algebra.norm ℤ x := by
  rw [order_norm_formula]
  nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg x.im]

private theorem neg_six_ne (x : Numbers2347 (-6)) :
    (Algebra.norm ℤ x).natAbs ≠ 2 := by
  intro h
  have hn : Algebra.norm ℤ x = 2 := by
    rw [← Int.natAbs_of_nonneg (numbers_47_nonnegative (-6) (by norm_num) x)]
    exact_mod_cast h
  rw [order_norm_formula] at hn
  have hbLower : -1 < x.im := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im + 1)]
  have hbUpper : x.im < 1 := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im - 1)]
  have hb : x.im = 0 := by omega
  rw [hb] at hn
  have hsquare : IsSquare (2 : ℤ) := ⟨x.re, by simpa [pow_two] using hn.symm⟩
  norm_num at hsquare

private theorem neg_six_four (x : Numbers2347 (-6))
    (h : (Algebra.norm ℤ x).natAbs = 4) :
    x = 2 ∨ x = -2 := by
  have hn : Algebra.norm ℤ x = 4 := by
    rw [← Int.natAbs_of_nonneg (numbers_47_nonnegative (-6) (by norm_num) x)]
    exact_mod_cast h
  rw [order_norm_formula] at hn
  have hbLower : -1 < x.im := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im + 1)]
  have hbUpper : x.im < 1 := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im - 1)]
  have hb : x.im = 0 := by omega
  rw [hb] at hn
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp
      (show x.re ^ 2 = (2 : ℤ) ^ 2 by
        norm_num at hn ⊢
        exact hn) with ha | ha
  · left; apply QuadraticAlgebra.ext <;> simp [hb, ha]
  · right; apply QuadraticAlgebra.ext <;> simp [hb, ha]

private theorem neg_twelve_ne (x : Numbers2347 (-12)) :
    (Algebra.norm ℤ x).natAbs ≠ 2 := by
  intro h
  have hn : Algebra.norm ℤ x = 2 := by
    rw [← Int.natAbs_of_nonneg (numbers_47_nonnegative (-12) (by norm_num) x)]
    exact_mod_cast h
  rw [order_norm_formula] at hn
  have hbLower : -1 < x.im := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im + 1)]
  have hbUpper : x.im < 1 := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im - 1)]
  have hb : x.im = 0 := by omega
  rw [hb] at hn
  have hsquare : IsSquare (2 : ℤ) := ⟨x.re, by simpa [pow_two] using hn.symm⟩
  norm_num at hsquare

private theorem neg_twelve_four (x : Numbers2347 (-12))
    (h : (Algebra.norm ℤ x).natAbs = 4) : x = 2 ∨ x = -2 := by
  have hn : Algebra.norm ℤ x = 4 := by
    rw [← Int.natAbs_of_nonneg (numbers_47_nonnegative (-12) (by norm_num) x)]
    exact_mod_cast h
  rw [order_norm_formula] at hn
  have hbLower : -1 < x.im := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im + 1)]
  have hbUpper : x.im < 1 := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im - 1)]
  have hb : x.im = 0 := by omega
  rw [hb] at hn
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp
      (show x.re ^ 2 = (2 : ℤ) ^ 2 by
        norm_num at hn ⊢
        exact hn) with ha | ha
  · left; apply QuadraticAlgebra.ext <;> simp [hb, ha]
  · right; apply QuadraticAlgebra.ext <;> simp [hb, ha]

private theorem neg_twelve_eight (x : Numbers2347 (-12)) :
    (Algebra.norm ℤ x).natAbs ≠ 8 := by
  intro h
  have hn : Algebra.norm ℤ x = 8 := by
    rw [← Int.natAbs_of_nonneg (numbers_47_nonnegative (-12) (by norm_num) x)]
    exact_mod_cast h
  rw [order_norm_formula] at hn
  have hbLower : -1 < x.im := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im + 1)]
  have hbUpper : x.im < 1 := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im - 1)]
  have hb : x.im = 0 := by omega
  rw [hb] at hn
  have hsquare : IsSquare (8 : ℤ) := ⟨x.re, by simpa [pow_two] using hn.symm⟩
  norm_num at hsquare

private theorem neg_twelve_sixteen (x : Numbers2347 (-12))
    (h : (Algebra.norm ℤ x).natAbs = 16) : x = 4 ∨ x = -4 := by
  have hn : Algebra.norm ℤ x = 16 := by
    rw [← Int.natAbs_of_nonneg (numbers_47_nonnegative (-12) (by norm_num) x)]
    exact_mod_cast h
  rw [order_norm_formula] at hn
  have hbLower : -2 < x.im := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im + 2)]
  have hbUpper : x.im < 2 := by
    nlinarith [sq_nonneg (2 * x.re + x.im), sq_nonneg (x.im - 2)]
  have him : x.im = -1 ∨ x.im = 0 ∨ x.im = 1 := by omega
  rcases him with him | him | him
  · rw [him] at hn
    have hsquare : (2 * x.re - 1) ^ 2 = (17 : ℤ) := by nlinarith
    have htLower : -5 < 2 * x.re - 1 := by
      nlinarith [sq_nonneg (2 * x.re - 1 + 5)]
    have htUpper : 2 * x.re - 1 < 5 := by
      nlinarith [sq_nonneg (2 * x.re - 1 - 5)]
    have haLower : -2 < x.re := by omega
    have haUpper : x.re < 3 := by omega
    interval_cases x.re <;> norm_num at hsquare
  · rw [him] at hn
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp
        (show x.re ^ 2 = (4 : ℤ) ^ 2 by norm_num at hn ⊢; exact hn)) with ha | ha
    · left
      apply QuadraticAlgebra.ext <;> simp [him, ha]
    · right
      apply QuadraticAlgebra.ext <;> simp [him, ha]
  · rw [him] at hn
    have hsquare : (2 * x.re + 1) ^ 2 = (17 : ℤ) := by nlinarith
    have htLower : -5 < 2 * x.re + 1 := by
      nlinarith [sq_nonneg (2 * x.re + 1 + 5)]
    have htUpper : 2 * x.re + 1 < 5 := by
      nlinarith [sq_nonneg (2 * x.re + 1 - 5)]
    have haLower : -3 < x.re := by omega
    have haUpper : x.re < 2 := by omega
    interval_cases x.re <;> norm_num at hsquare

set_option maxHeartbeats 800000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- Milne, Exercise 4-4: `Q(sqrt(-23))` has class number three. -/
theorem neg_twenty_three :
    CNOne.negativeQuadraticNumber (-23) (by norm_num) = 3 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ ((-23 : ℤ) : ℚ) + 0 * r) :=
    ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩
  letI : Module ℚ (QFModel (-23)) :=
    (inferInstance : Algebra ℚ (QFModel (-23))).toModule
  let coordinateEquiv : QFModel (-23) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
    { toFun := fun x => ![x.re, x.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := fun _ => rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; ext i; fin_cases i <;> rfl
      map_smul' := by
        intro c x
        have hc_re : ((c : QFModel (-23)).re) = c := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-23)) c]
          rfl
        have hc_im : ((c : QFModel (-23)).im) = 0 := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-23)) c]
          rfl
        ext i
        fin_cases i <;>
          simp [Algebra.smul_def, QuadraticAlgebra.re_mul,
            QuadraticAlgebra.im_mul, hc_re, hc_im] }
  let coordinateBasis : Module.Basis (Fin 2) ℚ (QFModel (-23)) :=
    Module.Basis.ofEquivFun coordinateEquiv
  letI : Module.Finite ℚ (QFModel (-23)) :=
    Module.Finite.of_basis coordinateBasis
  letI : NumberField (QFModel (-23)) :=
    NumberField.of_module_finite ℚ (QFModel (-23))
  have hm : Squarefree (-23 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 23).squarefree
  letI : Algebra (Numbers2347 (-6)) (QFModel (-23)) :=
    (numbers2347 (-6)).toAlgebra
  letI : IsScalarTower ℤ (Numbers2347 (-6)) (QFModel (-23)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z <;> norm_num [numbers2347])
  let hclosure : IsIntegralClosure (Numbers2347 (-6)) ℤ
      (QFModel (-23)) :=
    negative_numbers_closure (-6) hm (by norm_num)
  letI : IsIntegralClosure (Numbers2347 (-6)) ℤ
      (QFModel (-23)) := hclosure
  let emb : Numbers2347 (-6) →+* QFModel (-23) := by
    convert numbers2347 (-6) using 1
  have hemb : Function.Injective emb := by
    intro x y hxy
    apply numbers_47_injective (-6)
    simpa [emb] using hxy
  letI : NoZeroDivisors (Numbers2347 (-6)) :=
    hemb.noZeroDivisors emb (map_zero emb) (map_mul emb)
  letI : IsDomain (Numbers2347 (-6)) := NoZeroDivisors.to_isDomain _
  letI : IsDedekindDomain (Numbers2347 (-6)) :=
    IsIntegralClosure.isDedekindDomain ℤ ℚ (QFModel (-23)) _
  letI : Module.Free ℤ (Numbers2347 (-6)) :=
    IsIntegralClosure.module_free ℤ ℚ (QFModel (-23)) _
  letI : IsNoetherian ℤ (Numbers2347 (-6)) :=
    IsIntegralClosure.isNoetherian ℤ ℚ (QFModel (-23)) _
  letI : Module.Finite ℤ (Numbers2347 (-6)) := inferInstance
  letI : Ring.HasFiniteQuotients (Numbers2347 (-6)) :=
    Ring.HasFiniteQuotients.of_module_finite ℤ _
  change NumberField.classNumber (QFModel (-23)) = 3
  let e : 𝓞 (QFModel (-23)) ≃+* Numbers2347 (-6) :=
    @NumberField.RingOfIntegers.equiv (QFModel (-23)) inferInstance
      (Numbers2347 (-6)) inferInstance
      (numbers2347 (-6)).toAlgebra hclosure
  have hdiscr : NumberField.discr (QFModel (-23)) = -23 := by
    let eAlg : Numbers2347 (-6) ≃ₐ[ℤ]
        𝓞 (QFModel (-23)) :=
      AlgEquiv.ofRingEquiv (f := e.symm) (fun z => by simp)
    let b' : Module.Basis (Fin 2) ℤ (𝓞 (QFModel (-23))) :=
      (QuadraticAlgebra.basis (-6) 1).map eAlg.toLinearEquiv
    calc
      NumberField.discr (QFModel (-23)) = Algebra.discr ℤ b' :=
        (NumberField.discr_eq_discr (QFModel (-23)) b').symm
      _ = Algebra.discr ℤ (QuadraticAlgebra.basis (-6) 1) := by
        simpa [b'] using
          (Algebra.discr_eq_discr_of_algEquiv
            (QuadraticAlgebra.basis (-6) 1 : Fin 2 → Numbers2347 (-6)) eAlg).symm
      _ = -23 := by
        rw [numbers_47_discr]
        norm_num
  have hfinrank : Module.finrank ℚ (QFModel (-23)) = 2 :=
    QuadraticAlgebra.finrank_eq_two (-23 : ℚ) 0
  have hfinrankNF :
      @Module.finrank ℚ (QFModel (-23)) inferInstance inferInstance
        (@Algebra.toModule ℚ (QFModel (-23)) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (QFModel (-23)) inferInstance
            inferInstance)) = 2 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (QFModel (-23))) =
          @DivisionRing.toRatAlgebra (QFModel (-23)) inferInstance
            inferInstance := Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces
      (QFModel (-23)) = 1 := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
      (QFModel (-23))
    have hcard2 : NumberField.InfinitePlace.nrRealPlaces (QFModel (-23)) +
        2 * NumberField.InfinitePlace.nrComplexPlaces (QFModel (-23)) = 2 :=
      hcard.trans hfinrankNF
    have hsle : NumberField.InfinitePlace.nrComplexPlaces
        (QFModel (-23)) ≤ 1 := by omega
    have hsign := NumberField.sign_discr (K := QFModel (-23))
    rw [hdiscr] at hsign
    interval_cases hC : NumberField.InfinitePlace.nrComplexPlaces
        (QFModel (-23))
    · have hsignD : ((-23 : ℤ).sign) = -1 :=
        Int.sign_eq_neg_one_of_neg (by norm_num)
      rw [hsignD] at hsign
      norm_num at hsign
    · rfl
  have hbound :
      (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (QFModel (-23)) *
        ((Nat.factorial (Module.finrank ℚ (QFModel (-23))) : ℝ) /
          (Module.finrank ℚ (QFModel (-23)) : ℝ) ^
            Module.finrank ℚ (QFModel (-23)) *
          Real.sqrt |NumberField.discr (QFModel (-23))|) < 4 := by
    rw [hcomplex, hfinrank, hdiscr]
    norm_num
    have hsqrt : Real.sqrt (23 : ℝ) < 5 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5)]
      norm_num
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hpi0 : 0 < Real.pi := Real.pi_pos
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpi0]
    nlinarith
  let P : Ideal (𝓞 (QFModel (-23))) :=
    (numbers_23_474 (-6)).comap e
  let Q : Ideal (𝓞 (QFModel (-23))) :=
    (numbers_474_q (-6)).comap e
  let U : Ideal (𝓞 (QFModel (-23))) :=
    (numbers_474_u (-6)).comap e
  let V : Ideal (𝓞 (QFModel (-23))) :=
    (numbers_474_v (-6)).comap e
  have hmapP : P.map e = numbers_23_474 (-6) :=
    Ideal.map_comap_of_surjective e e.surjective _
  have hmapQ : Q.map e = numbers_474_q (-6) :=
    Ideal.map_comap_of_surjective e e.surjective _
  have hmapU : U.map e = numbers_474_u (-6) :=
    Ideal.map_comap_of_surjective e e.surjective _
  have hmapV : V.map e = numbers_474_v (-6) :=
    Ideal.map_comap_of_surjective e e.surjective _
  have hPordNe : numbers_23_474 (-6) ≠ ⊥ := by
    intro h
    have : (2 : Numbers2347 (-6)) ∈ numbers_23_474 (-6) :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at this
    norm_num at this
  have hQordNe : numbers_474_q (-6) ≠ ⊥ := by
    intro h
    have : (2 : Numbers2347 (-6)) ∈ numbers_474_q (-6) :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at this
    norm_num at this
  have hUordNe : numbers_474_u (-6) ≠ ⊥ := by
    intro h
    have : (3 : Numbers2347 (-6)) ∈ numbers_474_u (-6) :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at this
    norm_num at this
  have hVordNe : numbers_474_v (-6) ≠ ⊥ := by
    intro h
    have : (3 : Numbers2347 (-6)) ∈ numbers_474_v (-6) :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at this
    norm_num at this
  have hPnorm : Ideal.absNorm (numbers_23_474 (-6)) = 2 := by
    have hmul := congrArg Ideal.absNorm six_split_two.2.2.2
    simp only [map_mul] at hmul
    rw [Ideal.absNorm_span_singleton] at hmul
    rw [int_algebra_norm (-6) (2 : Numbers2347 (-6)),
      order_norm_formula] at hmul
    norm_num at hmul
    have hP0 : Ideal.absNorm (numbers_23_474 (-6)) ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hPordNe
    have hQ0 : Ideal.absNorm (numbers_474_q (-6)) ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hQordNe
    have hP1 : Ideal.absNorm (numbers_23_474 (-6)) ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr six_split_two.1.ne_top
    have hQ1 : Ideal.absNorm (numbers_474_q (-6)) ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr six_split_two.2.1.ne_top
    have hPge : 2 ≤ Ideal.absNorm (numbers_23_474 (-6)) := by omega
    have hQge : 2 ≤ Ideal.absNorm (numbers_474_q (-6)) := by omega
    nlinarith
  have hQnorm : Ideal.absNorm (numbers_474_q (-6)) = 2 := by
    have hmul := congrArg Ideal.absNorm six_split_two.2.2.2
    simp only [map_mul] at hmul
    rw [Ideal.absNorm_span_singleton, hPnorm] at hmul
    rw [int_algebra_norm (-6) (2 : Numbers2347 (-6)),
      order_norm_formula] at hmul
    norm_num at hmul
    omega
  have hUnorm : Ideal.absNorm (numbers_474_u (-6)) = 3 := by
    have hmul := congrArg Ideal.absNorm neg_six_split.2.2.2
    simp only [map_mul] at hmul
    rw [Ideal.absNorm_span_singleton] at hmul
    rw [int_algebra_norm (-6) (3 : Numbers2347 (-6)),
      order_norm_formula] at hmul
    norm_num at hmul
    have hU0 : Ideal.absNorm (numbers_474_u (-6)) ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hUordNe
    have hV0 : Ideal.absNorm (numbers_474_v (-6)) ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hVordNe
    have hU1 : Ideal.absNorm (numbers_474_u (-6)) ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr neg_six_split.1.ne_top
    have hV1 : Ideal.absNorm (numbers_474_v (-6)) ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr neg_six_split.2.1.ne_top
    have hUge : 2 ≤ Ideal.absNorm (numbers_474_u (-6)) := by omega
    have hVge : 2 ≤ Ideal.absNorm (numbers_474_v (-6)) := by omega
    have hUle : Ideal.absNorm (numbers_474_u (-6)) ≤ 4 := by nlinarith
    interval_cases hU : Ideal.absNorm (numbers_474_u (-6)) <;> omega
  have hVnorm : Ideal.absNorm (numbers_474_v (-6)) = 3 := by
    have hmul := congrArg Ideal.absNorm neg_six_split.2.2.2
    simp only [map_mul] at hmul
    rw [Ideal.absNorm_span_singleton, hUnorm] at hmul
    rw [int_algebra_norm (-6) (3 : Numbers2347 (-6)),
      order_norm_formula] at hmul
    norm_num at hmul
    omega
  have hPne : P ≠ ⊥ := by
    intro h; apply hPordNe; rw [← hmapP, h, Ideal.map_bot]
  have hQne : Q ≠ ⊥ := by
    intro h; apply hQordNe; rw [← hmapQ, h, Ideal.map_bot]
  have hUne : U ≠ ⊥ := by
    intro h; apply hUordNe; rw [← hmapU, h, Ideal.map_bot]
  have hVne : V ≠ ⊥ := by
    intro h; apply hVordNe; rw [← hmapV, h, Ideal.map_bot]
  let P0 : (Ideal (𝓞 (QFModel (-23))))⁰ :=
    ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hPne⟩
  let Q0 : (Ideal (𝓞 (QFModel (-23))))⁰ :=
    ⟨Q, mem_nonZeroDivisors_iff_ne_zero.mpr hQne⟩
  let U0 : (Ideal (𝓞 (QFModel (-23))))⁰ :=
    ⟨U, mem_nonZeroDivisors_iff_ne_zero.mpr hUne⟩
  let V0 : (Ideal (𝓞 (QFModel (-23))))⁰ :=
    ⟨V, mem_nonZeroDivisors_iff_ne_zero.mpr hVne⟩
  let c : ClassGroup (𝓞 (QFModel (-23))) := ClassGroup.mk0 P0
  have hPQprincipal : (P * Q).IsPrincipal := by
    refine ⟨e.symm 2, ?_⟩
    apply e.idealComapOrderIso.symm.injective
    change (P * Q).map e = (span {e.symm 2}).map e
    rw [Ideal.map_mul, hmapP, hmapQ, six_split_two.2.2.2,
      Ideal.map_span]
    simp
  have hPUprincipal : (P * U).IsPrincipal := by
    refine ⟨e.symm QuadraticAlgebra.omega, ?_⟩
    apply e.idealComapOrderIso.symm.injective
    change (P * U).map e = (span {e.symm QuadraticAlgebra.omega}).map e
    rw [Ideal.map_mul, hmapP, hmapU, neg_six_u,
      Ideal.map_span]
    simp
  have hcQ : ClassGroup.mk0 Q0 = c⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    change ClassGroup.mk0 P0 * ClassGroup.mk0 Q0 = 1
    rw [← (ClassGroup.mk0 :
      (Ideal (𝓞 (QFModel (-23))))⁰ →*
        ClassGroup (𝓞 (QFModel (-23)))).map_mul,
      ClassGroup.mk0_eq_one_iff]
    simpa only [show ((P0 * Q0 : (Ideal _)⁰) : Ideal _) = P * Q by rfl] using hPQprincipal
  have hcU : ClassGroup.mk0 U0 = c⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    change ClassGroup.mk0 P0 * ClassGroup.mk0 U0 = 1
    rw [← (ClassGroup.mk0 :
      (Ideal (𝓞 (QFModel (-23))))⁰ →*
        ClassGroup (𝓞 (QFModel (-23)))).map_mul,
      ClassGroup.mk0_eq_one_iff]
    simpa only [show ((P0 * U0 : (Ideal _)⁰) : Ideal _) = P * U by rfl] using hPUprincipal
  have hcV : ClassGroup.mk0 V0 = c := by
    have hUVprincipal : (U * V).IsPrincipal := by
      refine ⟨e.symm 3, ?_⟩
      apply e.idealComapOrderIso.symm.injective
      change (U * V).map e = (span {e.symm 3}).map e
      rw [Ideal.map_mul, hmapU, hmapV, neg_six_split.2.2.2,
        Ideal.map_span]
      simp
    have huv : ClassGroup.mk0 U0 * ClassGroup.mk0 V0 = 1 := by
      rw [← (ClassGroup.mk0 :
        (Ideal (𝓞 (QFModel (-23))))⁰ →*
          ClassGroup (𝓞 (QFModel (-23)))).map_mul,
        ClassGroup.mk0_eq_one_iff]
      simpa only [show ((U0 * V0 : (Ideal _)⁰) : Ideal _) = U * V by rfl] using hUVprincipal
    have := eq_inv_of_mul_eq_one_right huv
    rw [hcU, inv_inv] at this
    exact this
  have hc : c ≠ 1 := by
    intro hc1
    have hp : P.IsPrincipal := (ClassGroup.mk0_eq_one_iff P0.prop).mp hc1
    have hpMap : (numbers_23_474 (-6)).IsPrincipal := by
      rw [← hmapP]
      exact hp.map_ringHom e
    obtain ⟨x, hx⟩ := hpMap.principal
    have hxIdeal : numbers_23_474 (-6) = span {x} :=
      ideal_span_submodule _ _ hx
    have hxnorm : (Algebra.norm ℤ x).natAbs = 2 := by
      calc
        (Algebra.norm ℤ x).natAbs = Ideal.absNorm (span {x}) :=
          (Ideal.absNorm_span_singleton x).symm
        _ = Ideal.absNorm (numbers_23_474 (-6)) := by rw [hxIdeal]
        _ = 2 := hPnorm
    exact neg_six_ne x hxnorm
  have hc2 : c ^ 2 ≠ 1 := by
    intro hcSq
    have hPpow : (P ^ 2).IsPrincipal := by
      have hpowNe := mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero 2 hPne)
      apply (ClassGroup.mk0_eq_one_iff hpowNe).mp
      rw [show (⟨P ^ 2, hpowNe⟩ : (Ideal _)⁰) = P0 ^ 2 by
        apply Subtype.ext
        rfl]
      simpa only [map_pow, c] using hcSq
    have hPpowMap : (numbers_23_474 (-6) ^ 2).IsPrincipal := by
      simpa only [Ideal.map_pow, hmapP] using hPpow.map_ringHom e
    obtain ⟨x, hx⟩ := hPpowMap.principal
    have hxIdeal : numbers_23_474 (-6) ^ 2 = span {x} :=
      ideal_span_submodule _ _ hx
    have hxnorm : (Algebra.norm ℤ x).natAbs = 4 := by
      calc
        (Algebra.norm ℤ x).natAbs = Ideal.absNorm (span {x}) :=
          (Ideal.absNorm_span_singleton x).symm
        _ = Ideal.absNorm (numbers_23_474 (-6) ^ 2) := by rw [hxIdeal]
        _ = Ideal.absNorm (numbers_23_474 (-6)) ^ 2 := map_pow _ _ 2
        _ = 4 := by rw [hPnorm]; norm_num
    rcases neg_six_four x hxnorm with rfl | rfl
    all_goals
      have hPP : numbers_23_474 (-6) ^ 2 =
          span {(2 : Numbers2347 (-6))} := by
        simpa only [Ideal.span_singleton_neg] using hxIdeal
      have heq : numbers_23_474 (-6) = numbers_474_q (-6) := by
        apply mul_left_cancel₀ (show numbers_23_474 (-6) ≠ 0 by
          simpa only [Ideal.zero_eq_bot] using hPordNe)
        rw [← pow_two, hPP, six_split_two.2.2.2]
      exact six_split_two.2.2.1 heq
  have hall : ∀ C : ClassGroup (𝓞 (QFModel (-23))),
      C = 1 ∨ C = c ∨ C = c⁻¹ := by
    intro C
    obtain ⟨I, hIC, hnorm⟩ := NumberField.exists_ideal_in_class_of_norm_le C
    have hnormReal :
        (Ideal.absNorm (I : Ideal (𝓞 (QFModel (-23)))) : ℝ) < 4 :=
      lt_of_le_of_lt hnorm (by
        rw [hcomplex, hfinrankNF, hdiscr]
        norm_num
        have hsqrt : Real.sqrt (23 : ℝ) < 5 := by
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5)]
          norm_num
        have hpi : 3 < Real.pi := Real.pi_gt_three
        have hpi0 : 0 < Real.pi := Real.pi_pos
        rw [div_mul_eq_mul_div, div_lt_iff₀ hpi0]
        nlinarith)
    have hnormNat : Ideal.absNorm (I : Ideal (𝓞 (QFModel (-23)))) ≤ 3 := by
      have : Ideal.absNorm (I : Ideal (𝓞 (QFModel (-23)))) < 4 := by
        exact_mod_cast hnormReal
      omega
    let J : Ideal (Numbers2347 (-6)) := (I : Ideal _).map e
    have hJne : J ≠ ⊥ := by
      intro hJ
      exact (mem_nonZeroDivisors_iff_ne_zero.mp I.prop)
        ((Ideal.map_eq_bot_iff_of_injective e.injective).mp hJ)
    have hJnorm : Ideal.absNorm J ≤ 3 := by
      change Ideal.absNorm ((I : Ideal _).map e) ≤ 3
      rw [numbers_23_47]
      exact hnormNat
    have hnormPos : 0 < Ideal.absNorm J :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJne)
    interval_cases hNJ : Ideal.absNorm J
    · left
      have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hNJ
      have hItop : (I : Ideal (𝓞 (QFModel (-23)))) = ⊤ := by
        apply (Ideal.map_eq_top_of_bijective e e.bijective).mp
        simpa [J] using hJtop
      have hIone : I = 1 := Subtype.ext (by simpa using hItop)
      rw [← hIC, hIone, map_one]
    · rcases classify_norm_ideal (-6) 2 (by norm_num)
          J hNJ with hJP | hJQ
      · right; left
        have hIP : (I : Ideal _) = P := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = P.map e
          rw [show (I : Ideal _).map e = J by rfl, hJP, hmapP]
        change C = ClassGroup.mk0 P0
        rw [← hIC]
        congr 1
        exact Subtype.ext hIP
      · right; right
        have hIQ : (I : Ideal _) = Q := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = Q.map e
          rw [show (I : Ideal _).map e = J by rfl, hJQ, hmapQ]
        rw [← hIC, ← hcQ]
        congr 1
        exact Subtype.ext hIQ
    · rcases classify_norm_ideal (-6) 3 (by norm_num)
          J hNJ with hJU | hJV
      · right; right
        have hIU : (I : Ideal _) = U := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = U.map e
          rw [show (I : Ideal _).map e = J by rfl, hJU, hmapU]
        rw [← hIC, ← hcU]
        congr 1
        exact Subtype.ext hIU
      · right; left
        have hIV : (I : Ideal _) = V := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = V.map e
          rw [show (I : Ideal _).map e = J by rfl, hJV, hmapV]
        rw [← hIC, ← hcV]
        congr 1
        exact Subtype.ext hIV
  let f : Fin 3 → ClassGroup (𝓞 (QFModel (-23))) := ![1, c, c⁻¹]
  have hcinv : c⁻¹ ≠ 1 := by simpa using hc
  have hcneinv : c ≠ c⁻¹ := by
    intro h
    apply hc2
    calc
      c ^ 2 = c * c := by simp [pow_two]
      _ = c * c⁻¹ := congrArg (fun z => c * z) h
      _ = 1 := mul_inv_cancel c
  have hfInjective : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, hc, hcinv, hcneinv, hc.symm, hcinv.symm, hcneinv.symm]
  have hfSurjective : Function.Surjective f := by
    intro C
    rcases hall C with rfl | rfl | rfl
    · exact ⟨0, by simp [f]⟩
    · exact ⟨1, by simp [f]⟩
    · exact ⟨2, by simp [f]⟩
  change Fintype.card (ClassGroup (𝓞 (QFModel (-23)))) = 3
  have hle := Fintype.card_le_of_surjective f hfSurjective
  have hge := Fintype.card_le_of_injective f hfInjective
  simpa using le_antisymm hle hge

set_option maxHeartbeats 800000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- Milne, Exercise 4-4: `Q(sqrt(-47))` has class number five. -/
theorem neg_forty_seven :
    CNOne.negativeQuadraticNumber (-47) (by norm_num) = 5 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ ((-47 : ℤ) : ℚ) + 0 * r) :=
    ⟨fun r hr => by norm_num at hr; nlinarith [sq_nonneg r]⟩
  letI : Module ℚ (QFModel (-47)) :=
    (inferInstance : Algebra ℚ (QFModel (-47))).toModule
  let coordinateEquiv : QFModel (-47) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
    { toFun := fun x => ![x.re, x.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := fun _ => rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; ext i; fin_cases i <;> rfl
      map_smul' := by
        intro c x
        have hc_re : ((c : QFModel (-47)).re) = c := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-47)) c]
          rfl
        have hc_im : ((c : QFModel (-47)).im) = 0 := by
          rw [← algebraMap.coe_ratCast ℚ (QFModel (-47)) c]
          rfl
        ext i
        fin_cases i <;>
          simp [Algebra.smul_def, QuadraticAlgebra.re_mul,
            QuadraticAlgebra.im_mul, hc_re, hc_im] }
  let coordinateBasis : Module.Basis (Fin 2) ℚ (QFModel (-47)) :=
    Module.Basis.ofEquivFun coordinateEquiv
  letI : Module.Finite ℚ (QFModel (-47)) :=
    Module.Finite.of_basis coordinateBasis
  letI : NumberField (QFModel (-47)) :=
    NumberField.of_module_finite ℚ (QFModel (-47))
  have hm : Squarefree (-47 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 47).squarefree
  letI : Algebra (Numbers2347 (-12)) (QFModel (-47)) :=
    (numbers2347 (-12)).toAlgebra
  letI : IsScalarTower ℤ (Numbers2347 (-12)) (QFModel (-47)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z <;> norm_num [numbers2347])
  let hclosure : IsIntegralClosure (Numbers2347 (-12)) ℤ
      (QFModel (-47)) :=
    negative_numbers_closure (-12) hm (by norm_num)
  letI : IsIntegralClosure (Numbers2347 (-12)) ℤ
      (QFModel (-47)) := hclosure
  let emb : Numbers2347 (-12) →+* QFModel (-47) := by
    convert numbers2347 (-12) using 1
  have hemb : Function.Injective emb := by
    intro x y hxy
    apply numbers_47_injective (-12)
    simpa [emb] using hxy
  letI : NoZeroDivisors (Numbers2347 (-12)) :=
    hemb.noZeroDivisors emb (map_zero emb) (map_mul emb)
  letI : IsDomain (Numbers2347 (-12)) := NoZeroDivisors.to_isDomain _
  letI : IsDedekindDomain (Numbers2347 (-12)) :=
    IsIntegralClosure.isDedekindDomain ℤ ℚ (QFModel (-47)) _
  letI : Module.Free ℤ (Numbers2347 (-12)) :=
    IsIntegralClosure.module_free ℤ ℚ (QFModel (-47)) _
  letI : IsNoetherian ℤ (Numbers2347 (-12)) :=
    IsIntegralClosure.isNoetherian ℤ ℚ (QFModel (-47)) _
  letI : Module.Finite ℤ (Numbers2347 (-12)) := inferInstance
  letI : Ring.HasFiniteQuotients (Numbers2347 (-12)) :=
    Ring.HasFiniteQuotients.of_module_finite ℤ _
  change NumberField.classNumber (QFModel (-47)) = 5
  let e : 𝓞 (QFModel (-47)) ≃+* Numbers2347 (-12) :=
    @NumberField.RingOfIntegers.equiv (QFModel (-47)) inferInstance
      (Numbers2347 (-12)) inferInstance
      (numbers2347 (-12)).toAlgebra hclosure
  have hdiscr : NumberField.discr (QFModel (-47)) = -47 := by
    let eAlg : Numbers2347 (-12) ≃ₐ[ℤ]
        𝓞 (QFModel (-47)) :=
      AlgEquiv.ofRingEquiv (f := e.symm) (fun z => by simp)
    let b' : Module.Basis (Fin 2) ℤ (𝓞 (QFModel (-47))) :=
      (QuadraticAlgebra.basis (-12) 1).map eAlg.toLinearEquiv
    calc
      NumberField.discr (QFModel (-47)) = Algebra.discr ℤ b' :=
        (NumberField.discr_eq_discr (QFModel (-47)) b').symm
      _ = Algebra.discr ℤ (QuadraticAlgebra.basis (-12) 1) := by
        simpa [b'] using
          (Algebra.discr_eq_discr_of_algEquiv
            (QuadraticAlgebra.basis (-12) 1 : Fin 2 → Numbers2347 (-12)) eAlg).symm
      _ = -47 := by
        rw [numbers_47_discr]
        norm_num
  have hfinrank : Module.finrank ℚ (QFModel (-47)) = 2 :=
    QuadraticAlgebra.finrank_eq_two (-47 : ℚ) 0
  have hfinrankNF :
      @Module.finrank ℚ (QFModel (-47)) inferInstance inferInstance
        (@Algebra.toModule ℚ (QFModel (-47)) inferInstance inferInstance
          (@DivisionRing.toRatAlgebra (QFModel (-47)) inferInstance
            inferInstance)) = 2 := by
    have hAlgebra :
        (inferInstance : Algebra ℚ (QFModel (-47))) =
          @DivisionRing.toRatAlgebra (QFModel (-47)) inferInstance
            inferInstance := Subsingleton.elim _ _
    rw [← hAlgebra]
    exact hfinrank
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces
      (QFModel (-47)) = 1 := by
    have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
      (QFModel (-47))
    have hcard2 : NumberField.InfinitePlace.nrRealPlaces (QFModel (-47)) +
        2 * NumberField.InfinitePlace.nrComplexPlaces (QFModel (-47)) = 2 :=
      hcard.trans hfinrankNF
    have hsle : NumberField.InfinitePlace.nrComplexPlaces
        (QFModel (-47)) ≤ 1 := by omega
    have hsign := NumberField.sign_discr (K := QFModel (-47))
    rw [hdiscr] at hsign
    interval_cases hC : NumberField.InfinitePlace.nrComplexPlaces
        (QFModel (-47))
    · have hsignD : ((-47 : ℤ).sign) = -1 :=
        Int.sign_eq_neg_one_of_neg (by norm_num)
      rw [hsignD] at hsign
      norm_num at hsign
    · rfl
  have hbound :
      (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (QFModel (-47)) *
        ((Nat.factorial (Module.finrank ℚ (QFModel (-47))) : ℝ) /
          (Module.finrank ℚ (QFModel (-47)) : ℝ) ^
            Module.finrank ℚ (QFModel (-47)) *
          Real.sqrt |NumberField.discr (QFModel (-47))|) < 5 := by
    rw [hcomplex, hfinrank, hdiscr]
    norm_num
    have hsqrt : Real.sqrt (47 : ℝ) < 7 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 7)]
      norm_num
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hpi0 : 0 < Real.pi := Real.pi_pos
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpi0]
    nlinarith
  let P : Ideal (𝓞 (QFModel (-47))) :=
    (numbers_23_474 (-12)).comap e
  let Q : Ideal (𝓞 (QFModel (-47))) :=
    (numbers_474_q (-12)).comap e
  let U : Ideal (𝓞 (QFModel (-47))) :=
    (numbers_474_u (-12)).comap e
  let V : Ideal (𝓞 (QFModel (-47))) :=
    (numbers_474_v (-12)).comap e
  have hmapP : P.map e = numbers_23_474 (-12) :=
    Ideal.map_comap_of_surjective e e.surjective _
  have hmapQ : Q.map e = numbers_474_q (-12) :=
    Ideal.map_comap_of_surjective e e.surjective _
  have hmapU : U.map e = numbers_474_u (-12) :=
    Ideal.map_comap_of_surjective e e.surjective _
  have hmapV : V.map e = numbers_474_v (-12) :=
    Ideal.map_comap_of_surjective e e.surjective _
  have hPordNe : numbers_23_474 (-12) ≠ ⊥ := by
    intro h
    have : (2 : Numbers2347 (-12)) ∈ numbers_23_474 (-12) :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at this
    norm_num at this
  have hQordNe : numbers_474_q (-12) ≠ ⊥ := by
    intro h
    have : (2 : Numbers2347 (-12)) ∈ numbers_474_q (-12) :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at this
    norm_num at this
  have hUordNe : numbers_474_u (-12) ≠ ⊥ := by
    intro h
    have : (3 : Numbers2347 (-12)) ∈ numbers_474_u (-12) :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at this
    norm_num at this
  have hVordNe : numbers_474_v (-12) ≠ ⊥ := by
    intro h
    have : (3 : Numbers2347 (-12)) ∈ numbers_474_v (-12) :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at this
    norm_num at this
  have hPnorm : Ideal.absNorm (numbers_23_474 (-12)) = 2 := by
    have hmul := congrArg Ideal.absNorm twelve_split_two.2.2.2
    simp only [map_mul] at hmul
    rw [Ideal.absNorm_span_singleton] at hmul
    rw [int_algebra_norm (-12) (2 : Numbers2347 (-12)),
      order_norm_formula] at hmul
    norm_num at hmul
    have hP0 : Ideal.absNorm (numbers_23_474 (-12)) ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hPordNe
    have hQ0 : Ideal.absNorm (numbers_474_q (-12)) ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hQordNe
    have hP1 : Ideal.absNorm (numbers_23_474 (-12)) ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr twelve_split_two.1.ne_top
    have hQ1 : Ideal.absNorm (numbers_474_q (-12)) ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr twelve_split_two.2.1.ne_top
    have hPge : 2 ≤ Ideal.absNorm (numbers_23_474 (-12)) := by omega
    have hQge : 2 ≤ Ideal.absNorm (numbers_474_q (-12)) := by omega
    nlinarith
  have hQnorm : Ideal.absNorm (numbers_474_q (-12)) = 2 := by
    have hmul := congrArg Ideal.absNorm twelve_split_two.2.2.2
    simp only [map_mul] at hmul
    rw [Ideal.absNorm_span_singleton, hPnorm] at hmul
    rw [int_algebra_norm (-12) (2 : Numbers2347 (-12)),
      order_norm_formula] at hmul
    norm_num at hmul
    omega
  have hUnorm : Ideal.absNorm (numbers_474_u (-12)) = 3 := by
    have hmul := congrArg Ideal.absNorm neg_twelve_split.2.2.2
    simp only [map_mul] at hmul
    rw [Ideal.absNorm_span_singleton] at hmul
    rw [int_algebra_norm (-12) (3 : Numbers2347 (-12)),
      order_norm_formula] at hmul
    norm_num at hmul
    have hU0 : Ideal.absNorm (numbers_474_u (-12)) ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hUordNe
    have hV0 : Ideal.absNorm (numbers_474_v (-12)) ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hVordNe
    have hU1 : Ideal.absNorm (numbers_474_u (-12)) ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr neg_twelve_split.1.ne_top
    have hV1 : Ideal.absNorm (numbers_474_v (-12)) ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr neg_twelve_split.2.1.ne_top
    have hUge : 2 ≤ Ideal.absNorm (numbers_474_u (-12)) := by omega
    have hVge : 2 ≤ Ideal.absNorm (numbers_474_v (-12)) := by omega
    have hUle : Ideal.absNorm (numbers_474_u (-12)) ≤ 4 := by nlinarith
    interval_cases hU : Ideal.absNorm (numbers_474_u (-12)) <;> omega
  have hVnorm : Ideal.absNorm (numbers_474_v (-12)) = 3 := by
    have hmul := congrArg Ideal.absNorm neg_twelve_split.2.2.2
    simp only [map_mul] at hmul
    rw [Ideal.absNorm_span_singleton, hUnorm] at hmul
    rw [int_algebra_norm (-12) (3 : Numbers2347 (-12)),
      order_norm_formula] at hmul
    norm_num at hmul
    omega
  have hPne : P ≠ ⊥ := by
    intro h; apply hPordNe; rw [← hmapP, h, Ideal.map_bot]
  have hQne : Q ≠ ⊥ := by
    intro h; apply hQordNe; rw [← hmapQ, h, Ideal.map_bot]
  have hUne : U ≠ ⊥ := by
    intro h; apply hUordNe; rw [← hmapU, h, Ideal.map_bot]
  have hVne : V ≠ ⊥ := by
    intro h; apply hVordNe; rw [← hmapV, h, Ideal.map_bot]
  let P0 : (Ideal (𝓞 (QFModel (-47))))⁰ :=
    ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hPne⟩
  let Q0 : (Ideal (𝓞 (QFModel (-47))))⁰ :=
    ⟨Q, mem_nonZeroDivisors_iff_ne_zero.mpr hQne⟩
  let U0 : (Ideal (𝓞 (QFModel (-47))))⁰ :=
    ⟨U, mem_nonZeroDivisors_iff_ne_zero.mpr hUne⟩
  let V0 : (Ideal (𝓞 (QFModel (-47))))⁰ :=
    ⟨V, mem_nonZeroDivisors_iff_ne_zero.mpr hVne⟩
  let c : ClassGroup (𝓞 (QFModel (-47))) := ClassGroup.mk0 P0
  have hPQprincipal : (P * Q).IsPrincipal := by
    refine ⟨e.symm 2, ?_⟩
    apply e.idealComapOrderIso.symm.injective
    change (P * Q).map e = (span {e.symm 2}).map e
    rw [Ideal.map_mul, hmapP, hmapQ, twelve_split_two.2.2.2,
      Ideal.map_span]
    simp
  have hP2Uprincipal : (P ^ 2 * U).IsPrincipal := by
    refine ⟨e.symm QuadraticAlgebra.omega, ?_⟩
    apply e.idealComapOrderIso.symm.injective
    change (P ^ 2 * U).map e =
      (span {e.symm QuadraticAlgebra.omega}).map e
    rw [Ideal.map_mul, Ideal.map_pow, hmapP, hmapU,
      twelve_sq_u, Ideal.map_span]
    simp
  have hcQ : ClassGroup.mk0 Q0 = c⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    change ClassGroup.mk0 P0 * ClassGroup.mk0 Q0 = 1
    rw [← (ClassGroup.mk0 :
      (Ideal (𝓞 (QFModel (-47))))⁰ →*
        ClassGroup (𝓞 (QFModel (-47)))).map_mul,
      ClassGroup.mk0_eq_one_iff]
    simpa only [show ((P0 * Q0 : (Ideal _)⁰) : Ideal _) = P * Q by rfl] using hPQprincipal
  have hcU : ClassGroup.mk0 U0 = (c ^ 2)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    change (ClassGroup.mk0 P0) ^ 2 * ClassGroup.mk0 U0 = 1
    rw [← (ClassGroup.mk0 :
      (Ideal (𝓞 (QFModel (-47))))⁰ →*
        ClassGroup (𝓞 (QFModel (-47)))).map_pow,
      ← (ClassGroup.mk0 :
      (Ideal (𝓞 (QFModel (-47))))⁰ →*
        ClassGroup (𝓞 (QFModel (-47)))).map_mul,
      ClassGroup.mk0_eq_one_iff]
    simpa only [show ((P0 ^ 2 * U0 : (Ideal _)⁰) : Ideal _) = P ^ 2 * U by rfl]
      using hP2Uprincipal
  have hcV : ClassGroup.mk0 V0 = c ^ 2 := by
    have hUVprincipal : (U * V).IsPrincipal := by
      refine ⟨e.symm 3, ?_⟩
      apply e.idealComapOrderIso.symm.injective
      change (U * V).map e = (span {e.symm 3}).map e
      rw [Ideal.map_mul, hmapU, hmapV, neg_twelve_split.2.2.2,
        Ideal.map_span]
      simp
    have huv : ClassGroup.mk0 U0 * ClassGroup.mk0 V0 = 1 := by
      rw [← (ClassGroup.mk0 :
        (Ideal (𝓞 (QFModel (-47))))⁰ →*
          ClassGroup (𝓞 (QFModel (-47)))).map_mul,
        ClassGroup.mk0_eq_one_iff]
      simpa only [show ((U0 * V0 : (Ideal _)⁰) : Ideal _) = U * V by rfl] using hUVprincipal
    have := eq_inv_of_mul_eq_one_right huv
    rw [hcU, inv_inv] at this
    exact this
  have hc1 : c ≠ 1 := by
    intro hc
    have hp : P.IsPrincipal := (ClassGroup.mk0_eq_one_iff P0.prop).mp hc
    have hpMap : (numbers_23_474 (-12)).IsPrincipal := by
      rw [← hmapP]
      exact hp.map_ringHom e
    obtain ⟨x, hx⟩ := hpMap.principal
    have hxIdeal : numbers_23_474 (-12) = span {x} :=
      ideal_span_submodule _ _ hx
    have hxnorm : (Algebra.norm ℤ x).natAbs = 2 := by
      calc
        (Algebra.norm ℤ x).natAbs = Ideal.absNorm (span {x}) :=
          (Ideal.absNorm_span_singleton x).symm
        _ = Ideal.absNorm (numbers_23_474 (-12)) := by rw [hxIdeal]
        _ = 2 := hPnorm
    exact neg_twelve_ne x hxnorm
  have hc2 : c ^ 2 ≠ 1 := by
    intro hc
    have hPpow : (P ^ 2).IsPrincipal := by
      have hpowNe := mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero 2 hPne)
      apply (ClassGroup.mk0_eq_one_iff hpowNe).mp
      rw [show (⟨P ^ 2, hpowNe⟩ : (Ideal _)⁰) = P0 ^ 2 by
        apply Subtype.ext
        rfl]
      simpa only [map_pow, c] using hc
    have hPpowMap : (numbers_23_474 (-12) ^ 2).IsPrincipal := by
      simpa only [Ideal.map_pow, hmapP] using hPpow.map_ringHom e
    obtain ⟨x, hx⟩ := hPpowMap.principal
    have hxIdeal : numbers_23_474 (-12) ^ 2 = span {x} :=
      ideal_span_submodule _ _ hx
    have hxnorm : (Algebra.norm ℤ x).natAbs = 4 := by
      calc
        (Algebra.norm ℤ x).natAbs = Ideal.absNorm (span {x}) :=
          (Ideal.absNorm_span_singleton x).symm
        _ = Ideal.absNorm (numbers_23_474 (-12) ^ 2) := by rw [hxIdeal]
        _ = Ideal.absNorm (numbers_23_474 (-12)) ^ 2 := map_pow _ _ 2
        _ = 4 := by rw [hPnorm]; norm_num
    rcases neg_twelve_four x hxnorm with rfl | rfl
    all_goals
      have hPP : numbers_23_474 (-12) ^ 2 =
          span {(2 : Numbers2347 (-12))} := by
        simpa only [Ideal.span_singleton_neg] using hxIdeal
      have heq : numbers_23_474 (-12) = numbers_474_q (-12) := by
        apply mul_left_cancel₀ (show numbers_23_474 (-12) ≠ 0 by
          simpa only [Ideal.zero_eq_bot] using hPordNe)
        rw [← pow_two, hPP, twelve_split_two.2.2.2]
      exact twelve_split_two.2.2.1 heq
  have hc3 : c ^ 3 ≠ 1 := by
    intro hc
    have hPpow : (P ^ 3).IsPrincipal := by
      have hpowNe := mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero 3 hPne)
      apply (ClassGroup.mk0_eq_one_iff hpowNe).mp
      rw [show (⟨P ^ 3, hpowNe⟩ : (Ideal _)⁰) = P0 ^ 3 by
        apply Subtype.ext
        rfl]
      simpa only [map_pow, c] using hc
    have hPpowMap : (numbers_23_474 (-12) ^ 3).IsPrincipal := by
      simpa only [Ideal.map_pow, hmapP] using hPpow.map_ringHom e
    obtain ⟨x, hx⟩ := hPpowMap.principal
    have hxIdeal : numbers_23_474 (-12) ^ 3 = span {x} :=
      ideal_span_submodule _ _ hx
    have hxnorm : (Algebra.norm ℤ x).natAbs = 8 := by
      calc
        (Algebra.norm ℤ x).natAbs = Ideal.absNorm (span {x}) :=
          (Ideal.absNorm_span_singleton x).symm
        _ = Ideal.absNorm (numbers_23_474 (-12) ^ 3) := by rw [hxIdeal]
        _ = Ideal.absNorm (numbers_23_474 (-12)) ^ 3 := map_pow _ _ 3
        _ = 8 := by rw [hPnorm]; norm_num
    exact neg_twelve_eight x hxnorm
  have hc4 : c ^ 4 ≠ 1 := by
    intro hc
    have hPpow : (P ^ 4).IsPrincipal := by
      have hpowNe := mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero 4 hPne)
      apply (ClassGroup.mk0_eq_one_iff hpowNe).mp
      rw [show (⟨P ^ 4, hpowNe⟩ : (Ideal _)⁰) = P0 ^ 4 by
        apply Subtype.ext
        rfl]
      simpa only [map_pow, c] using hc
    have hPpowMap : (numbers_23_474 (-12) ^ 4).IsPrincipal := by
      simpa only [Ideal.map_pow, hmapP] using hPpow.map_ringHom e
    obtain ⟨x, hx⟩ := hPpowMap.principal
    have hxIdeal : numbers_23_474 (-12) ^ 4 = span {x} :=
      ideal_span_submodule _ _ hx
    have hxnorm : (Algebra.norm ℤ x).natAbs = 16 := by
      calc
        (Algebra.norm ℤ x).natAbs = Ideal.absNorm (span {x}) :=
          (Ideal.absNorm_span_singleton x).symm
        _ = Ideal.absNorm (numbers_23_474 (-12) ^ 4) := by rw [hxIdeal]
        _ = Ideal.absNorm (numbers_23_474 (-12)) ^ 4 := map_pow _ _ 4
        _ = 16 := by rw [hPnorm]; norm_num
    rcases neg_twelve_sixteen x hxnorm with rfl | rfl
    all_goals
      have hP4 : numbers_23_474 (-12) ^ 4 =
          span {(4 : Numbers2347 (-12))} := by
        simpa only [Ideal.span_singleton_neg] using hxIdeal
      have hPQ2 : (numbers_23_474 (-12) * numbers_474_q (-12)) ^ 2 =
          span {(4 : Numbers2347 (-12))} := by
        rw [twelve_split_two.2.2.2,
          Ideal.span_singleton_pow]
        norm_num
      have hP2Q2 : numbers_23_474 (-12) ^ 2 = numbers_474_q (-12) ^ 2 := by
        apply mul_left_cancel₀ (show numbers_23_474 (-12) ^ 2 ≠ 0 by
          exact pow_ne_zero 2 (by simpa only [Ideal.zero_eq_bot] using hPordNe))
        rw [← pow_add, show 2 + 2 = 4 by norm_num, hP4, ← hPQ2]
        ring
      have hPdvdQ2 : numbers_23_474 (-12) ∣ numbers_474_q (-12) ^ 2 := by
        rw [Ideal.dvd_iff_le, ← hP2Q2]
        exact Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0)
      have hPprime : Prime (numbers_23_474 (-12)) :=
        Ideal.prime_of_isPrime hPordNe twelve_split_two.1
      have hPdvdQ : numbers_23_474 (-12) ∣ numbers_474_q (-12) :=
        hPprime.dvd_of_dvd_pow hPdvdQ2
      have heq : numbers_23_474 (-12) = numbers_474_q (-12) := by
        exact ((twelve_split_two.2.1.isMaximal hQordNe).eq_of_le
          twelve_split_two.1.ne_top
          (Ideal.dvd_iff_le.mp hPdvdQ)).symm
      exact twelve_split_two.2.2.1 heq
  have hall : ∀ C : ClassGroup (𝓞 (QFModel (-47))),
      C = 1 ∨ C = c ∨ C = c⁻¹ ∨ C = c ^ 2 ∨ C = (c ^ 2)⁻¹ := by
    intro C
    obtain ⟨I, hIC, hnorm⟩ := NumberField.exists_ideal_in_class_of_norm_le C
    have hnormReal :
        (Ideal.absNorm (I : Ideal (𝓞 (QFModel (-47)))) : ℝ) < 5 :=
      lt_of_le_of_lt hnorm (by
        rw [hcomplex, hfinrankNF, hdiscr]
        norm_num
        have hsqrt : Real.sqrt (47 : ℝ) < 7 := by
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 7)]
          norm_num
        have hpi : 3 < Real.pi := Real.pi_gt_three
        have hpi0 : 0 < Real.pi := Real.pi_pos
        rw [div_mul_eq_mul_div, div_lt_iff₀ hpi0]
        nlinarith)
    have hnormNat : Ideal.absNorm (I : Ideal (𝓞 (QFModel (-47)))) ≤ 4 := by
      have : Ideal.absNorm (I : Ideal (𝓞 (QFModel (-47)))) < 5 := by
        exact_mod_cast hnormReal
      omega
    let J : Ideal (Numbers2347 (-12)) := (I : Ideal _).map e
    have hJne : J ≠ ⊥ := by
      intro hJ
      exact (mem_nonZeroDivisors_iff_ne_zero.mp I.prop)
        ((Ideal.map_eq_bot_iff_of_injective e.injective).mp hJ)
    have hJnorm : Ideal.absNorm J ≤ 4 := by
      change Ideal.absNorm ((I : Ideal _).map e) ≤ 4
      rw [numbers_23_47]
      exact hnormNat
    have hnormPos : 0 < Ideal.absNorm J :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJne)
    interval_cases hNJ : Ideal.absNorm J
    · left
      have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hNJ
      have hItop : (I : Ideal (𝓞 (QFModel (-47)))) = ⊤ := by
        apply (Ideal.map_eq_top_of_bijective e e.bijective).mp
        simpa [J] using hJtop
      have hIone : I = 1 := Subtype.ext (by simpa using hItop)
      rw [← hIC, hIone, map_one]
    · rcases classify_norm_ideal (-12) 2 (by norm_num)
          J hNJ with hJP | hJQ
      · right; left
        have hIP : (I : Ideal _) = P := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = P.map e
          rw [show (I : Ideal _).map e = J by rfl, hJP, hmapP]
        change C = ClassGroup.mk0 P0
        rw [← hIC]
        congr 1
        exact Subtype.ext hIP
      · right; right; left
        have hIQ : (I : Ideal _) = Q := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = Q.map e
          rw [show (I : Ideal _).map e = J by rfl, hJQ, hmapQ]
        rw [← hIC, ← hcQ]
        congr 1
        exact Subtype.ext hIQ
    · rcases classify_norm_ideal (-12) 3 (by norm_num)
          J hNJ with hJU | hJV
      · right; right; right; right
        have hIU : (I : Ideal _) = U := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = U.map e
          rw [show (I : Ideal _).map e = J by rfl, hJU, hmapU]
        rw [← hIC, ← hcU]
        congr 1
        exact Subtype.ext hIU
      · right; right; right; left
        have hIV : (I : Ideal _) = V := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = V.map e
          rw [show (I : Ideal _).map e = J by rfl, hJV, hmapV]
        rw [← hIC, ← hcV]
        congr 1
        exact Subtype.ext hIV
    · have hJnotPrime : ¬J.IsPrime := by
        intro hprime
        have hfour : (4 : Numbers2347 (-12)) ∈ J := by
          simpa [hNJ] using Ideal.absNorm_mem J
        have htwo : (2 : Numbers2347 (-12)) ∈ J := by
          exact hprime.mem_or_mem (by simpa [pow_two] using hfour) |>.elim id id
        have htwelve : (12 : Numbers2347 (-12)) ∈ J :=
          J.mul_mem_left 6 htwo
        have hprod : QuadraticAlgebra.omega *
            (QuadraticAlgebra.omega - 1 : Numbers2347 (-12)) ∈ J := by
          have homega : QuadraticAlgebra.omega *
              (QuadraticAlgebra.omega - 1 : Numbers2347 (-12)) = -12 := by
            apply QuadraticAlgebra.ext <;>
              norm_num [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
          rw [homega]
          exact J.neg_mem htwelve
        rcases hprime.mem_or_mem hprod with hw | hw1
        · have hle : numbers_23_474 (-12) ≤ J := by
            rw [numbers_23_474, QOrd.rootIdeal, Ideal.span_le]
            intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl
            · exact htwo
            · simpa using hw
          have hEq := (twelve_split_two.1.isMaximal hPordNe).eq_of_le
            hprime.ne_top hle
          rw [← hEq, hPnorm] at hNJ
          omega
        · have hle : numbers_474_q (-12) ≤ J := by
            rw [numbers_474_q, QOrd.rootIdeal, Ideal.span_le]
            intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl
            · exact htwo
            · simpa using hw1
          have hEq := (twelve_split_two.2.1.isMaximal hQordNe).eq_of_le
            hprime.ne_top hle
          rw [← hEq, hQnorm] at hNJ
          omega
      have hJnotUnit : ¬IsUnit J := by
        rw [Ideal.isUnit_iff, ← Ideal.absNorm_eq_one_iff]
        omega
      rcases (irreducible_or_factor hJnotUnit).resolve_left
          (fun hirr => hJnotPrime (Ideal.isPrime_of_prime
            (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr))) with
        ⟨A, B, hAnotUnit, hBnotUnit, hAB⟩
      have hAne : A ≠ ⊥ := by
        intro hA
        apply hJne
        simp [hAB, hA]
      have hBne : B ≠ ⊥ := by
        intro hB
        apply hJne
        simp [hAB, hB]
      have hAnorm0 : Ideal.absNorm A ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hAne
      have hBnorm0 : Ideal.absNorm B ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hBne
      have hAnorm1 : Ideal.absNorm A ≠ 1 := by
        intro hA
        exact hAnotUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hA))
      have hBnorm1 : Ideal.absNorm B ≠ 1 := by
        intro hB
        exact hBnotUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hB))
      have hnormAB : Ideal.absNorm A * Ideal.absNorm B = 4 := by
        rw [← map_mul, ← hAB, hNJ]
      have hAle : Ideal.absNorm A ≤ 4 :=
        Nat.le_of_dvd (by norm_num) ⟨Ideal.absNorm B, hnormAB.symm⟩
      have hAnorm : Ideal.absNorm A = 2 := by
        interval_cases hA : Ideal.absNorm A <;> omega
      have hBnorm : Ideal.absNorm B = 2 := by
        rw [hAnorm] at hnormAB
        omega
      rcases classify_norm_ideal (-12) 2 (by norm_num) A hAnorm with
        hAP | hAQ <;>
      rcases classify_norm_ideal (-12) 2 (by norm_num) B hBnorm with
        hBP | hBQ
      · right; right; right; left
        have hIP2 : (I : Ideal _) = P ^ 2 := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = (P ^ 2).map e
          rw [show (I : Ideal _).map e = J by rfl, hAB, hAP, hBP,
            ← pow_two, Ideal.map_pow, hmapP]
        rw [← hIC]
        change ClassGroup.mk0 I = (ClassGroup.mk0 P0) ^ 2
        rw [show I = P0 ^ 2 by exact Subtype.ext hIP2, map_pow]
      · left
        have hIPQ : (I : Ideal _) = P * Q := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = (P * Q).map e
          rw [show (I : Ideal _).map e = J by rfl, hAB, hAP, hBQ,
            Ideal.map_mul, hmapP, hmapQ]
        rw [← hIC]
        apply (ClassGroup.mk0_eq_one_iff I.prop).mpr
        simpa [hIPQ] using hPQprincipal
      · left
        have hIQP : (I : Ideal _) = Q * P := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = (Q * P).map e
          rw [show (I : Ideal _).map e = J by rfl, hAB, hAQ, hBP,
            Ideal.map_mul, hmapQ, hmapP]
        rw [← hIC]
        apply (ClassGroup.mk0_eq_one_iff I.prop).mpr
        rw [mul_comm] at hIQP
        simpa [hIQP] using hPQprincipal
      · right; right; right; right
        have hIQ2 : (I : Ideal _) = Q ^ 2 := by
          apply e.idealComapOrderIso.symm.injective
          change (I : Ideal _).map e = (Q ^ 2).map e
          rw [show (I : Ideal _).map e = J by rfl, hAB, hAQ, hBQ,
            ← pow_two, Ideal.map_pow, hmapQ]
        rw [← hIC]
        change ClassGroup.mk0 I = (c ^ 2)⁻¹
        calc
          ClassGroup.mk0 I = (ClassGroup.mk0 Q0) ^ 2 := by
            rw [show I = Q0 ^ 2 by exact Subtype.ext hIQ2, map_pow]
          _ = (c⁻¹) ^ 2 := by rw [hcQ]
          _ = (c ^ 2)⁻¹ := by rw [inv_pow]
  let f : Fin 5 → ClassGroup (𝓞 (QFModel (-47))) :=
    ![1, c, c⁻¹, c ^ 2, (c ^ 2)⁻¹]
  have hcinv1 : c⁻¹ ≠ 1 := by simpa using hc1
  have hc2inv1 : (c ^ 2)⁻¹ ≠ 1 := by simpa using hc2
  have hc_ne_inv : c ≠ c⁻¹ := by
    intro h
    apply hc2
    calc c ^ 2 = c * c := by simp [pow_two]
      _ = c * c⁻¹ := congrArg (fun z => c * z) h
      _ = 1 := mul_inv_cancel c
  have hc_ne_sq : c ≠ c ^ 2 := by
    intro h
    apply hc1
    have h' := congrArg (fun z => c⁻¹ * z) h
    simpa [pow_two, mul_assoc] using h'.symm
  have hc_ne_invsq : c ≠ (c ^ 2)⁻¹ := by
    intro h
    apply hc3
    calc
      c ^ 3 = c ^ 2 * c := pow_succ c 2
      _ = c ^ 2 * (c ^ 2)⁻¹ := congrArg (fun z => c ^ 2 * z) h
      _ = 1 := mul_inv_cancel _
  have hcinv_ne_sq : c⁻¹ ≠ c ^ 2 := by
    intro h
    apply hc3
    calc
      c ^ 3 = c ^ 2 * c := pow_succ c 2
      _ = c⁻¹ * c := congrArg (fun z => z * c) h.symm
      _ = 1 := inv_mul_cancel _
  have hcinv_ne_invsq : c⁻¹ ≠ (c ^ 2)⁻¹ := by
    intro h
    exact hc_ne_sq (inv_injective h)
  have hsq_ne_invsq : c ^ 2 ≠ (c ^ 2)⁻¹ := by
    intro h
    apply hc4
    calc
      c ^ 4 = (c ^ 2) * (c ^ 2) := by simpa using (pow_add c 2 2)
      _ = (c ^ 2) * (c ^ 2)⁻¹ := congrArg (fun x => c ^ 2 * x) h
      _ = 1 := mul_inv_cancel _
  have hfInjective : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, hc1, hcinv1, hc2, hc2inv1, hc_ne_inv, hc_ne_sq,
        hc_ne_invsq, hcinv_ne_sq, hcinv_ne_invsq, hsq_ne_invsq,
        hc1.symm, hcinv1.symm, hc2.symm, hc2inv1.symm,
        hc_ne_inv.symm, hc_ne_sq.symm, hc_ne_invsq.symm,
        hcinv_ne_sq.symm, hcinv_ne_invsq.symm, hsq_ne_invsq.symm]
  have hfSurjective : Function.Surjective f := by
    intro C
    rcases hall C with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [f]⟩
    · exact ⟨1, by simp [f]⟩
    · exact ⟨2, by simp [f]⟩
    · exact ⟨3, by simp [f]⟩
    · exact ⟨4, by simp [f]⟩
  change Fintype.card (ClassGroup (𝓞 (QFModel (-47)))) = 5
  have hle := Fintype.card_le_of_surjective f hfSurjective
  have hge := Fintype.card_le_of_injective f hfInjective
  simpa using le_antisymm hle hge

/-- Both class-number calculations in Milne's Exercise 4-4. -/
theorem neg2347 :
    CNOne.negativeQuadraticNumber (-23) (by norm_num) = 3 ∧
      CNOne.negativeQuadraticNumber (-47) (by norm_num) = 5 :=
  ⟨neg_twenty_three,
    neg_forty_seven⟩

end

end Towers.NumberTheory.Milne
