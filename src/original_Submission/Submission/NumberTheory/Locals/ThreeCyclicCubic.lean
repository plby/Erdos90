import Submission.NumberTheory.Locals.RamificationGroups
import Submission.NumberTheory.Locals.TotallyRamifiedEisenstein
import Submission.NumberTheory.Ramification.EisensteinRamification
import Mathlib.Algebra.DualNumber
import Mathlib.GroupTheory.PGroup
import Mathlib.NumberTheory.Padics.RingHoms


/-!
# Milne, Algebraic Number Theory, Two-hour examination, Question 5

Writing `π = ζ₃ - 1`, the element `π` satisfies the Eisenstein polynomial
`X² + 3X + 3`.  We construct the resulting quadratic extension of `ℚ₃`, prove
that `π + 1` is a primitive cube root generating it, and identify its Galois
group as cyclic of order two.

On the integral model `ℤ₃[π]`, conjugation sends `π` to `-3 - π`.  Its
displacement lies in `(π)` but not `(π)²`; this computes `G₀` and `G₁`
directly, and monotonicity gives every remaining ramification group.
-/

namespace Submission.NumberTheory.Milne

noncomputable section

open Polynomial
open scoped DualNumber Polynomial

private def examinationIntegralPolynomial : ℤ_[3][X] :=
  X ^ 2 + C 3 * X + C 3

private theorem examination_five_monic :
    examinationIntegralPolynomial.Monic ∧
      examinationIntegralPolynomial.natDegree = 2 := by
  constructor
  · rw [show examinationIntegralPolynomial =
        X ^ 2 + (C 3 * X + C 3) by
          dsimp [examinationIntegralPolynomial]
          ring]
    apply monic_X_pow_add
    compute_degree
    norm_num
  · dsimp [examinationIntegralPolynomial]
    compute_degree
    all_goals norm_num

private theorem examination_five_eisenstein :
    examinationIntegralPolynomial.IsEisensteinAt
      (Ideal.span {(3 : ℤ_[3])}) := by
  have hp : (Ideal.span {(3 : ℤ_[3])}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num : (3 : ℤ_[3]) ≠ 0)).mpr
      PadicInt.prime_p
  refine examination_five_monic.1.isEisensteinAt_of_mem_of_notMem
    hp.ne_top ?_ ?_
  · intro i hi
    rw [examination_five_monic.2] at hi
    interval_cases i <;>
      norm_num [examinationIntegralPolynomial, Ideal.mem_span_singleton]
  · rw [show examinationIntegralPolynomial.coeff 0 = (3 : ℤ_[3]) by
        simp [examinationIntegralPolynomial]]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    rcases h with ⟨c, hc⟩
    have heq : (3 : ℤ_[3]) * ((3 : ℤ_[3]) * c) =
        (3 : ℤ_[3]) * 1 := by
      calc
        (3 : ℤ_[3]) * ((3 : ℤ_[3]) * c) = (3 : ℤ_[3]) ^ 2 * c := by ring
        _ = (3 : ℤ_[3]) := hc.symm
        _ = (3 : ℤ_[3]) * 1 := by ring
    have hcunit : (3 : ℤ_[3]) * c = 1 :=
      mul_left_cancel₀ (by norm_num : (3 : ℤ_[3]) ≠ 0) heq
    exact PadicInt.prime_p.not_unit
      (isUnit_iff_dvd_one.mpr ⟨c, hcunit.symm⟩)

/-- The shifted third-cyclotomic polynomial over the 3-adic rationals. -/
def examinationFivePolynomial : ℚ_[3][X] :=
  X ^ 2 + C 3 * X + C 3

/-- The shifted third-cyclotomic polynomial is Eisenstein at `3`. -/
theorem examin_polyn_irred :
    Irreducible examinationFivePolynomial := by
  have h := eisenstein_irreducible_fraction
    (A := ℤ_[3]) (K := ℚ_[3])
    ((Ideal.span_singleton_prime
      (by norm_num : (3 : ℤ_[3]) ≠ 0)).mpr PadicInt.prime_p)
    examination_five_eisenstein
    examination_five_monic.1
    (by rw [examination_five_monic.2]; norm_num)
  simpa [examinationFivePolynomial, examinationIntegralPolynomial] using h

/-- The concrete 3-adic field `ℚ₃(ζ₃)`, presented using `π = ζ₃ - 1`. -/
abbrev ExaminationFiveField := AdjoinRoot examinationFivePolynomial

noncomputable instance : Fact (Irreducible examinationFivePolynomial) :=
  ⟨examin_polyn_irred⟩

theorem examination_five_degree :
    examinationFivePolynomial.natDegree = 2 := by
  dsimp [examinationFivePolynomial]
  compute_degree
  all_goals norm_num

private theorem examination_polynomial_monic :
    examinationFivePolynomial.Monic := by
  rw [show examinationFivePolynomial =
      X ^ 2 + (C 3 * X + C 3) by
        dsimp [examinationFivePolynomial]
        ring]
  apply monic_X_pow_add
  compute_degree
  norm_num

noncomputable instance :
    Algebra.IsQuadraticExtension ℚ_[3] ExaminationFiveField where
  finrank_eq_two' := by
    rw [PowerBasis.finrank
      (AdjoinRoot.powerBasis examin_polyn_irred.ne_zero),
      AdjoinRoot.powerBasis_dim]
    exact examination_five_degree

/-- The Galois group of `ℚ₃(ζ₃)/ℚ₃` has order two. -/
theorem examination_five_galois :
    Nat.card Gal(ExaminationFiveField / ℚ_[3]) = 2 := by
  simpa [Algebra.IsQuadraticExtension.finrank_eq_two ℚ_[3] ExaminationFiveField] using
    (IsGalois.card_aut_eq_finrank ℚ_[3] ExaminationFiveField)

/-- The Galois group of `ℚ₃(ζ₃)/ℚ₃` is cyclic. -/
theorem examination_five_cyclic :
    IsCyclic Gal(ExaminationFiveField / ℚ_[3]) := by
  infer_instance

/-- A primitive cube root in the shifted-polynomial presentation. -/
def examinationFiveZeta : ExaminationFiveField :=
  AdjoinRoot.root examinationFivePolynomial + 1

theorem examination_five_relation :
    (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField) ^ 2 +
        3 * AdjoinRoot.root examinationFivePolynomial + 3 = 0 := by
  simpa [examinationFivePolynomial] using
    (AdjoinRoot.eval₂_root examinationFivePolynomial)

theorem examination_five_zeta : examinationFiveZeta ^ 3 = 1 := by
  have h := examination_five_relation
  dsimp [examinationFiveZeta] at ⊢
  linear_combination AdjoinRoot.root examinationFivePolynomial * h

theorem examination_five_zero :
    (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField) ≠ 0 := by
  intro hroot
  have h := examination_five_relation
  rw [hroot] at h
  have hthree : (3 : ExaminationFiveField) = 0 := by simpa using h
  have hmapped :
      algebraMap ℚ_[3] ExaminationFiveField (3 : ℚ_[3]) =
        algebraMap ℚ_[3] ExaminationFiveField 0 := by
    rw [map_ofNat, map_zero]
    exact hthree
  have hthreeQ : (3 : ℚ_[3]) = 0 :=
    (algebraMap ℚ_[3] ExaminationFiveField).injective hmapped
  exact (by norm_num : (3 : ℚ_[3]) ≠ 0) hthreeQ

theorem examination_zeta_one : examinationFiveZeta ≠ 1 := by
  intro h
  apply examination_five_zero
  simpa [examinationFiveZeta] using sub_eq_zero.mpr h

/-- The constructed cube root generates the whole quadratic extension. -/
theorem examination_zeta_top :
    Algebra.adjoin ℚ_[3] ({examinationFiveZeta} : Set ExaminationFiveField) = ⊤ := by
  apply top_unique
  rw [← AdjoinRoot.adjoinRoot_eq_top (f := examinationFivePolynomial)]
  apply Algebra.adjoin_le
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  have hzeta : examinationFiveZeta ∈
      Algebra.adjoin ℚ_[3] ({examinationFiveZeta} : Set ExaminationFiveField) :=
    Algebra.subset_adjoin (Set.mem_singleton examinationFiveZeta)
  have hone : (1 : ExaminationFiveField) ∈
      Algebra.adjoin ℚ_[3] ({examinationFiveZeta} : Set ExaminationFiveField) :=
    (Algebra.adjoin ℚ_[3] ({examinationFiveZeta} : Set ExaminationFiveField)).one_mem
  simpa [examinationFiveZeta] using
    (Algebra.adjoin ℚ_[3] ({examinationFiveZeta} : Set ExaminationFiveField)).sub_mem
      hzeta hone

/-- The element `π + 1` is a primitive third root of unity. -/
theorem examination_zeta_primitive :
    IsPrimitiveRoot examinationFiveZeta 3 := by
  apply IsPrimitiveRoot.mk_of_lt examinationFiveZeta (by norm_num)
  · exact examination_five_zeta
  · intro l hl hlt
    have hlcases : l = 1 ∨ l = 2 := by omega
    rcases hlcases with rfl | rfl
    · simpa using examination_zeta_one
    · intro hzeta_sq
      apply examination_zeta_one
      calc
        examinationFiveZeta = examinationFiveZeta ^ 3 := by
          rw [pow_succ, hzeta_sq, one_mul]
        _ = 1 := examination_five_zeta

/-- The integral Eisenstein model `ℤ₃[π]` for `ℚ₃(ζ₃)`. -/
abbrev ExaminationFiveIntegers :=
  AdjoinRoot examinationIntegralPolynomial

/-- The uniformizer `π = ζ₃ - 1` in the integral model. -/
abbrev examinationFivePi : ExaminationFiveIntegers :=
  AdjoinRoot.root examinationIntegralPolynomial

theorem examination_pi_relation :
    examinationFivePi ^ 2 + 3 * examinationFivePi + 3 = 0 := by
  simpa [examinationIntegralPolynomial] using
    AdjoinRoot.eval₂_root examinationIntegralPolynomial

private theorem examination_conjugate_root :
    aeval (-3 - examinationFivePi) examinationIntegralPolynomial = 0 := by
  simp only [examinationIntegralPolynomial, map_add, map_pow, aeval_X,
    aeval_C, map_mul]
  change (-3 - examinationFivePi) ^ 2 +
      3 * (-3 - examinationFivePi) + 3 = 0
  linear_combination examination_pi_relation

private def examinationFiveHom :
    ExaminationFiveIntegers →ₐ[ℤ_[3]] ExaminationFiveIntegers :=
  AdjoinRoot.liftAlgHom examinationIntegralPolynomial (Algebra.ofId _ _)
    (-3 - examinationFivePi) examination_conjugate_root

@[simp]
private theorem examination_conjugation_pi :
    examinationFiveHom examinationFivePi = -3 - examinationFivePi := by
  simp [examinationFiveHom]

private theorem examination_conjugation_comp :
    examinationFiveHom.comp examinationFiveHom =
      AlgHom.id ℤ_[3] ExaminationFiveIntegers := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, examination_conjugation_pi, map_sub,
    map_neg, map_ofNat, AlgHom.id_apply]
  ring

/-- The nontrivial conjugation `π ↦ -3 - π` of the integral model. -/
def examinationFiveConjugation :
    ExaminationFiveIntegers ≃ₐ[ℤ_[3]] ExaminationFiveIntegers :=
  AlgEquiv.ofAlgHom examinationFiveHom examinationFiveHom
    examination_conjugation_comp examination_conjugation_comp

@[simp]
theorem five_conjugation_pi :
    examinationFiveConjugation examinationFivePi = -3 - examinationFivePi := by
  simp [examinationFiveConjugation, examinationFiveHom]

theorem examination_conjugation_sq : examinationFiveConjugation ^ 2 = 1 := by
  apply DFunLike.ext _ _
  intro x
  simpa [pow_two, examinationFiveConjugation] using
    AlgHom.congr_fun examination_conjugation_comp x

private def examinationFiveReduction :
    ExaminationFiveIntegers →+* (ZMod 3)[ε] :=
  AdjoinRoot.lift
    ((TrivSqZeroExt.inlHom (ZMod 3) (ZMod 3)).comp PadicInt.toZMod)
    ε
    (by
      simp only [examinationIntegralPolynomial, map_ofNat, eval₂_add, eval₂_X_pow,
        DualNumber.eps_pow_two,
        eval₂_mul, eval₂_ofNat, eval₂_X, zero_add]
      change (3 : (ZMod 3)[ε]) * ε + 3 = 0
      have hthree : (3 : (ZMod 3)[ε]) = 0 := by
        apply TrivSqZeroExt.ext
        · change (3 : ZMod 3) = 0
          exact ZMod.natCast_self 3
        · rfl
      simp [hthree])

@[simp]
private theorem examination_reduction_pi :
    examinationFiveReduction examinationFivePi = ε := by
  simp [examinationFiveReduction]

/-- The maximal ideal `(π)` in the integral Eisenstein model. -/
def examinationFivePrime : Ideal ExaminationFiveIntegers :=
  Ideal.span {examinationFivePi}

private theorem examination_five_displacement :
    examinationFiveConjugation examinationFivePi - examinationFivePi ∈
      examinationFivePrime := by
  rw [five_conjugation_pi]
  have h : -3 - examinationFivePi - examinationFivePi =
      examinationFivePi * (examinationFivePi + 1) := by
    apply sub_eq_zero.mp
    linear_combination -examination_pi_relation
  rw [h]
  exact Ideal.mul_mem_right _ _
    (Ideal.subset_span (Set.mem_singleton examinationFivePi))

private theorem examination_displacement_sq :
    examinationFiveConjugation examinationFivePi - examinationFivePi ∉
      examinationFivePrime ^ 2 := by
  intro h
  rw [examinationFivePrime, Ideal.span_singleton_pow] at h
  rcases Ideal.mem_span_singleton.mp h with ⟨y, hy⟩
  have hm := congrArg examinationFiveReduction hy
  simp only [five_conjugation_pi, map_sub, map_neg, map_ofNat, examination_reduction_pi, map_mul,
    map_pow,
    DualNumber.eps_pow_two, zero_mul] at hm
  have hthree : (3 : (ZMod 3)[ε]) = 0 := by
    apply TrivSqZeroExt.ext
    · change (3 : ZMod 3) = 0
      exact ZMod.natCast_self 3
    · rfl
  simp only [hthree, neg_zero, zero_sub] at hm
  have hs := congrArg (TrivSqZeroExt.snd : (ZMod 3)[ε] → ZMod 3) hm
  have hs' : (-1 : ZMod 3) - 1 = 0 := by simpa using hs
  exact (by decide : (-1 : ZMod 3) - 1 ≠ 0) hs'

/-- The order-two group generated by conjugation on `ℤ₃[π]`. -/
abbrev ExaminationFiveIntegral :=
  Subgroup.zpowers examinationFiveConjugation

private theorem examination_five_ne :
    examinationFiveConjugation ≠ 1 := by
  intro h
  have hp := DFunLike.congr_fun h examinationFivePi
  have hm := congrArg examinationFiveReduction hp
  simp only [five_conjugation_pi, map_sub, map_neg, map_ofNat, examination_reduction_pi,
    AlgEquiv.one_apply] at hm
  have hthree : (3 : (ZMod 3)[ε]) = 0 := by
    apply TrivSqZeroExt.ext
    · change (3 : ZMod 3) = 0
      exact ZMod.natCast_self 3
    · rfl
  simp only [hthree, neg_zero, zero_sub] at hm
  have hs := congrArg (TrivSqZeroExt.snd : (ZMod 3)[ε] → ZMod 3) hm
  exact (by decide : (-1 : ZMod 3) ≠ 1) hs

private theorem examination_conjugation_order :
    orderOf examinationFiveConjugation = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime examination_conjugation_sq
    examination_five_ne

instance : Finite ExaminationFiveIntegral := by
  have hord : 0 < orderOf examinationFiveConjugation := by
    rw [examination_conjugation_order]
    norm_num
  have hfin :
      (Subgroup.zpowers examinationFiveConjugation :
        Set (ExaminationFiveIntegers ≃ₐ[ℤ_[3]] ExaminationFiveIntegers)).Finite :=
    IsOfFinOrder.finite_zpowers (orderOf_pos_iff.mp hord)
  letI : Fintype ExaminationFiveIntegral := hfin.fintype
  exact inferInstance

/-- The integral conjugation group has the same order two as the field Galois group. -/
theorem examination_five_card :
    Nat.card ExaminationFiveIntegral = 2 := by
  rw [Nat.card_zpowers, examination_conjugation_order]

/-- Abstractly, the integral conjugation group is the field Galois group:
both are cyclic groups of order two. -/
noncomputable def examinationFiveIntegral :
    ExaminationFiveIntegral ≃*
      Gal(ExaminationFiveField / ℚ_[3]) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact mulEquivOfPrimeCardEq examination_five_card
    examination_five_galois

/-- The zeroth ramification group is the whole conjugation group. -/
theorem examination_zero_ramification :
    idealRamificationGroup examinationFivePrime
      ExaminationFiveIntegral 0 = ⊤ := by
  let gen : ExaminationFiveIntegral :=
    ⟨examinationFiveConjugation,
      Subgroup.mem_zpowers examinationFiveConjugation⟩
  have hgen : gen ∈ idealRamificationGroup examinationFivePrime
      ExaminationFiveIntegral 0 := by
    rw [ideal_ramification_uniformizer examinationFivePrime
      examinationFivePi AdjoinRoot.adjoinRoot_eq_top]
    change examinationFiveConjugation examinationFivePi - examinationFivePi ∈
      examinationFivePrime ^ (0 + 1)
    simpa using examination_five_displacement
  have hgen_ne : gen ≠ 1 := by
    intro h
    exact examination_five_ne (congrArg Subtype.val h)
  haveI : Fact (Nat.card ExaminationFiveIntegral).Prime :=
    ⟨by rw [examination_five_card]; norm_num⟩
  rcases (idealRamificationGroup examinationFivePrime
    ExaminationFiveIntegral 0).eq_bot_or_eq_top_of_prime_card with h | h
  · exact (hgen_ne (by simpa [h] using hgen)).elim
  · exact h

/-- The first ramification group is trivial. -/
theorem examination_five_ramification :
    idealRamificationGroup examinationFivePrime
      ExaminationFiveIntegral 1 = ⊥ := by
  let gen : ExaminationFiveIntegral :=
    ⟨examinationFiveConjugation,
      Subgroup.mem_zpowers examinationFiveConjugation⟩
  have hgen_not : gen ∉ idealRamificationGroup examinationFivePrime
      ExaminationFiveIntegral 1 := by
    rw [ideal_ramification_uniformizer examinationFivePrime
      examinationFivePi AdjoinRoot.adjoinRoot_eq_top]
    change examinationFiveConjugation examinationFivePi - examinationFivePi ∉
      examinationFivePrime ^ (1 + 1)
    simpa using examination_displacement_sq
  haveI : Fact (Nat.card ExaminationFiveIntegral).Prime :=
    ⟨by rw [examination_five_card]; norm_num⟩
  rcases (idealRamificationGroup examinationFivePrime
    ExaminationFiveIntegral 1).eq_bot_or_eq_top_of_prime_card with h | h
  · exact h
  · exact (hgen_not (by simp [h])).elim

/-- A `3`-subgroup of a finite group of order two is trivial. -/
theorem subgroup_bot_three
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hcard : Nat.card G = 2) (hH : IsPGroup 3 H) : H = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hdiv : Nat.card H ∣ Nat.card G := H.card_subgroup_dvd_card
  rw [hcard] at hdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hHcard | hHcard
  · exact (Subgroup.eq_bot_iff_card H).2 hHcard
  · obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hH
    rw [hHcard] at hn
    cases n with
    | zero => norm_num at hn
    | succ n =>
        rw [pow_succ] at hn
        have hpow : 1 ≤ 3 ^ n := Nat.one_le_pow' n 2
        omega

/-- Examination Question 5, after the local calculations for `ℚ₃(ζ₃)` have
supplied their three standard outputs: the Galois group has order two,
inertia is the whole group, and the wild inertia group is a `3`-group. -/
theorem examination_ramification_groups
    {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B] [Finite G]
    (P : Ideal B) (hcard : Nat.card G = 2)
    (hzero : idealRamificationGroup P G 0 = ⊤)
    (hwild : IsPGroup 3 (idealRamificationGroup P G 1)) :
    IsCyclic G ∧
      idealRamificationGroup P G 0 = ⊤ ∧
      ∀ i : Nat, 1 ≤ i → idealRamificationGroup P G i = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyclic : IsCyclic G := isCyclic_of_prime_card hcard
  have hone : idealRamificationGroup P G 1 = ⊥ :=
    subgroup_bot_three
      (idealRamificationGroup P G 1) hcard hwild
  refine ⟨hcyclic, hzero, fun i hi => ?_⟩
  apply bot_unique
  exact (ideal_ramification_antitone P hi).trans_eq hone

/-- Examination Question 5 for the concrete integral model of `ℚ₃(ζ₃)`:
the Galois group is cyclic of order two, `G₀` is the whole group, and
`Gᵢ` is trivial for every `i ≥ 1`. -/
theorem examination_five_groups :
    IsCyclic ExaminationFiveIntegral ∧
      idealRamificationGroup examinationFivePrime
        ExaminationFiveIntegral 0 = ⊤ ∧
      ∀ i : Nat, 1 ≤ i →
        idealRamificationGroup examinationFivePrime
          ExaminationFiveIntegral i = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨isCyclic_of_prime_card examination_five_card,
    examination_zero_ramification, fun i hi => ?_⟩
  apply bot_unique
  exact (ideal_ramification_antitone examinationFivePrime hi).trans_eq
    examination_five_ramification

/-! ### Comparison with the actual integral closure -/

/-- The integral closure of `ℤ₃` in the field presentation of
`ℚ₃(ζ₃)`. -/
abbrev ExaminationFiveClosure :=
  integralClosure ℤ_[3] ExaminationFiveField

private theorem examination_five_integral :
    IsIntegral ℤ_[3]
      (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField) := by
  refine ⟨examinationIntegralPolynomial,
    examination_five_monic.1, ?_⟩
  simpa [aeval_def, examinationIntegralPolynomial] using
    examination_five_relation

/-- The uniformizer `π = ζ₃ - 1`, now regarded as an element of the
actual integral closure. -/
def examinationClosurePi : ExaminationFiveClosure :=
  ⟨AdjoinRoot.root examinationFivePolynomial,
    (mem_integralClosure_iff ℤ_[3] ExaminationFiveField).2
      examination_five_integral⟩

private theorem examination_five_irreducible :
    Irreducible examinationIntegralPolynomial := by
  apply examination_five_eisenstein.irreducible
  · exact (Ideal.span_singleton_prime
      (by norm_num : (3 : ℤ_[3]) ≠ 0)).mpr PadicInt.prime_p
  · exact examination_five_monic.1.isPrimitive
  · rw [examination_five_monic.2]
    norm_num

private theorem examination_root_minpoly :
    minpoly ℤ_[3]
        (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField) =
      examinationIntegralPolynomial := by
  apply Polynomial.map_injective
    (algebraMap ℤ_[3] ℚ_[3])
    (IsFractionRing.injective ℤ_[3] ℚ_[3])
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[3]
    examination_five_integral]
  rw [AdjoinRoot.minpoly_root examin_polyn_irred.ne_zero]
  rw [examination_polynomial_monic.leadingCoeff]
  simp [examinationFivePolynomial, examinationIntegralPolynomial, map_ofNat]

private theorem examination_pi_minpoly :
    minpoly ℤ_[3] examinationClosurePi =
      examinationIntegralPolynomial := by
  let inclusion : ExaminationFiveClosure →ₐ[ℤ_[3]] ExaminationFiveField :=
    (integralClosure ℤ_[3] ExaminationFiveField).val
  calc
    minpoly ℤ_[3] examinationClosurePi =
        minpoly ℤ_[3]
          (inclusion examinationClosurePi) :=
      (minpoly.algHom_eq inclusion Subtype.val_injective _).symm
    _ = examinationIntegralPolynomial :=
      examination_root_minpoly

private theorem examination_adjoin_pi :
    Algebra.adjoin ℤ_[3]
      ({examinationClosurePi} : Set ExaminationFiveClosure) = ⊤ := by
  let B : PowerBasis ℚ_[3] ExaminationFiveField :=
    AdjoinRoot.powerBasis examin_polyn_irred.ne_zero
  have hBgen : B.gen =
      (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField) := by
    rfl
  have hBint : IsIntegral ℤ_[3] B.gen := by
    rw [hBgen]
    exact examination_five_integral
  have hmin : minpoly ℤ_[3] B.gen = examinationIntegralPolynomial := by
    rw [hBgen]
    exact examination_root_minpoly
  have heis : (minpoly ℤ_[3] B.gen).IsEisensteinAt
      (Ideal.span {(3 : ℤ_[3])}) := by
    rw [hmin]
    exact examination_five_eisenstein
  have hclosure :
      Algebra.adjoin ℤ_[3]
          ({AdjoinRoot.root examinationFivePolynomial} : Set ExaminationFiveField) =
        integralClosure ℤ_[3] ExaminationFiveField := by
    simpa [hBgen] using
      adjoin_minpoly_eisenstein
        ℤ_[3] ℚ_[3] ExaminationFiveField B hBint PadicInt.irreducible_p heis
  apply top_unique
  intro x _hx
  let inclusion : ExaminationFiveClosure →ₐ[ℤ_[3]] ExaminationFiveField :=
    (integralClosure ℤ_[3] ExaminationFiveField).val
  have hxL : (x : ExaminationFiveField) ∈
      Algebra.adjoin ℤ_[3]
        ({AdjoinRoot.root examinationFivePolynomial} : Set ExaminationFiveField) := by
    rw [hclosure]
    exact x.property
  have hxMap : inclusion x ∈
      (Algebra.adjoin ℤ_[3]
        ({examinationClosurePi} : Set ExaminationFiveClosure)).map
          inclusion := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    exact hxL
  rw [Subalgebra.mem_map] at hxMap
  rcases hxMap with ⟨y, hy, hyx⟩
  have hyx' : y = x := Subtype.ext hyx
  simpa [hyx'] using hy

private noncomputable def examinationFiveMinpoly :
    IsAdjoinRoot ExaminationFiveClosure
      (minpoly ℤ_[3] examinationClosurePi) := by
  have hbaseInjective :
      Function.Injective (algebraMap ℤ_[3] ExaminationFiveField) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[3] ℚ_[3] ExaminationFiveField]
    exact (algebraMap ℚ_[3] ExaminationFiveField).injective.comp
      (IsFractionRing.injective ℤ_[3] ℚ_[3])
  letI : Module.IsTorsionFree ℤ_[3] ExaminationFiveField :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hbaseInjective
  letI : Module.IsTorsionFree ℤ_[3] ExaminationFiveClosure :=
    Subalgebra.instIsTorsionFree (integralClosure ℤ_[3] ExaminationFiveField)
  exact IsAdjoinRoot.mkOfAdjoinEqTop
    (IsIntegralClosure.isIntegral ℤ_[3] ExaminationFiveField
      examinationClosurePi)
    examination_adjoin_pi

private theorem examination_five_minpoly :
    examinationFiveMinpoly.root =
      examinationClosurePi := by
  have hbaseInjective :
      Function.Injective (algebraMap ℤ_[3] ExaminationFiveField) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[3] ℚ_[3] ExaminationFiveField]
    exact (algebraMap ℚ_[3] ExaminationFiveField).injective.comp
      (IsFractionRing.injective ℤ_[3] ℚ_[3])
  letI : Module.IsTorsionFree ℤ_[3] ExaminationFiveField :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hbaseInjective
  letI : Module.IsTorsionFree ℤ_[3] ExaminationFiveClosure :=
    Subalgebra.instIsTorsionFree (integralClosure ℤ_[3] ExaminationFiveField)
  let hInt : IsIntegral ℤ_[3] examinationClosurePi :=
    IsIntegralClosure.isIntegral ℤ_[3] ExaminationFiveField
      examinationClosurePi
  change (IsAdjoinRoot.mkOfAdjoinEqTop hInt
    examination_adjoin_pi).root =
      examinationClosurePi
  exact IsAdjoinRoot.mkOfAdjoinEqTop_root
    (hα := hInt) (hα₂ := examination_adjoin_pi)

/-- The concrete Eisenstein order is canonically the actual integral closure
inside the field `ℚ₃(ζ₃)`. -/
noncomputable def examinationFiveIntegers :
    ExaminationFiveIntegers ≃ₐ[ℤ_[3]] ExaminationFiveClosure :=
  (AdjoinRoot.algEquivOfEq ℤ_[3] examinationIntegralPolynomial
      (minpoly ℤ_[3] examinationClosurePi)
      examination_pi_minpoly.symm).trans
    ((AdjoinRoot.isAdjoinRoot
      (minpoly ℤ_[3] examinationClosurePi)).algEquiv
        examinationFiveMinpoly)

@[simp]
theorem examination_integers_pi :
    examinationFiveIntegers examinationFivePi =
      examinationClosurePi := by
  rw [examinationFiveIntegers, AlgEquiv.trans_apply,
    AdjoinRoot.algEquivOfEq_root, ← AdjoinRoot.isAdjoinRoot_root_eq_root,
    IsAdjoinRoot.algEquiv_root,
    examination_five_minpoly]

/-! ### The actual Galois action and ramification filtration -/

private theorem examination_five_conjugate :
    aeval
      (-3 - (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField))
      examinationFivePolynomial = 0 := by
  have h : (-3 -
      (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField)) ^ 2 +
      3 * (-3 - AdjoinRoot.root examinationFivePolynomial) + 3 = 0
      := by
    linear_combination examination_five_relation
  change aeval
      (-3 - (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField))
      (X ^ 2 + C 3 * X + C 3) = 0
  rw [aeval_add, aeval_add, aeval_mul, aeval_X_pow, aeval_X, aeval_C]
  norm_num only [map_ofNat]
  exact h

private def examinationConjugationHom :
    ExaminationFiveField →ₐ[ℚ_[3]] ExaminationFiveField :=
  AdjoinRoot.liftAlgHom examinationFivePolynomial (Algebra.ofId _ _)
    (-3 - AdjoinRoot.root examinationFivePolynomial)
    examination_five_conjugate

@[simp]
private theorem examination_five_conjugation :
    examinationConjugationHom
        (AdjoinRoot.root examinationFivePolynomial) =
      -3 - AdjoinRoot.root examinationFivePolynomial := by
  simp [examinationConjugationHom]

private theorem examination_five_comp :
    examinationConjugationHom.comp
        examinationConjugationHom =
      AlgHom.id ℚ_[3] ExaminationFiveField := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, examination_five_conjugation,
    map_sub, map_neg, map_ofNat, AlgHom.id_apply]
  ring

/-- The nontrivial field automorphism of `ℚ₃(ζ₃)`, sending
`π` to `-3 - π`. -/
def examinationFieldConjugation : Gal(ExaminationFiveField / ℚ_[3]) :=
  AlgEquiv.ofAlgHom examinationConjugationHom
    examinationConjugationHom
    examination_five_comp
    examination_five_comp

@[simp]
theorem examination_conjugation_root :
    examinationFieldConjugation
        (AdjoinRoot.root examinationFivePolynomial) =
      -3 - AdjoinRoot.root examinationFivePolynomial := by
  simp [examinationFieldConjugation, examinationConjugationHom]

theorem examination_conjugation_ne :
    examinationFieldConjugation ≠ 1 := by
  intro h
  have hroot := DFunLike.congr_fun h
    (AdjoinRoot.root examinationFivePolynomial)
  rw [examination_conjugation_root] at hroot
  change (-3 - (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField)) =
    AdjoinRoot.root examinationFivePolynomial at hroot
  have hlinear :
      2 * (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField) + 3 = 0 := by
    linear_combination -hroot
  have hthree : (3 : ExaminationFiveField) = 0 := by
    linear_combination 4 * examination_five_relation -
      (2 * (AdjoinRoot.root examinationFivePolynomial : ExaminationFiveField) + 3) *
        hlinear
  have hthreeQ : (3 : ℚ_[3]) = 0 := by
    apply (algebraMap ℚ_[3] ExaminationFiveField).injective
    rw [map_ofNat, map_zero]
    exact hthree
  norm_num at hthreeQ

noncomputable instance (priority := 10000)
    examinationFiveIntegralClosureGaloisAction :
    MulSemiringAction Gal(ExaminationFiveField / ℚ_[3])
      ExaminationFiveClosure :=
  IsIntegralClosure.MulSemiringAction
    ℤ_[3] ℚ_[3] ExaminationFiveField ExaminationFiveClosure

noncomputable instance (priority := 10000)
    examinationFiveIntegralClosureGaloisSMul :
    SMul Gal(ExaminationFiveField / ℚ_[3]) ExaminationFiveClosure :=
  examinationFiveIntegralClosureGaloisAction.toDistribMulAction.toMulAction.toSMul

noncomputable instance (priority := 10000)
    examinationFiveIntegralClosureGaloisSMulComm :
    SMulCommClass Gal(ExaminationFiveField / ℚ_[3]) ℤ_[3]
      ExaminationFiveClosure where
  smul_comm σ r x := by
    change (galRestrict ℤ_[3] ℚ_[3] ExaminationFiveField
      ExaminationFiveClosure σ) (r • x) =
        r • (galRestrict ℤ_[3] ℚ_[3] ExaminationFiveField
          ExaminationFiveClosure σ) x
    exact map_smul (galRestrict ℤ_[3] ℚ_[3] ExaminationFiveField
      ExaminationFiveClosure σ) r x

/-- The prime `( π )` in the actual integral closure, transported from the
Eisenstein presentation. -/
def examinationFiveClosure :
    Ideal ExaminationFiveClosure :=
  examinationFivePrime.map
    examinationFiveIntegers.toRingHom

@[simp]
private theorem examination_five_pi :
    examinationFieldConjugation • examinationClosurePi =
      -3 - examinationClosurePi := by
  apply Subtype.ext
  change algebraMap ExaminationFiveClosure ExaminationFiveField
      ((galRestrict ℤ_[3] ℚ_[3] ExaminationFiveField
        ExaminationFiveClosure examinationFieldConjugation)
          examinationClosurePi) = _
  rw [algebraMap_galRestrict_apply ℤ_[3]
    examinationFieldConjugation examinationClosurePi]
  exact examination_conjugation_root

private theorem examination_displacement :
    examinationFiveIntegers
        (examinationFiveConjugation examinationFivePi - examinationFivePi) =
      examinationFieldConjugation • examinationClosurePi -
        examinationClosurePi := by
  rw [map_sub, five_conjugation_pi,
    examination_integers_pi,
    examination_five_pi]
  rw [map_sub, map_neg, map_ofNat,
    examination_integers_pi]

private theorem five_actual_displacement :
    examinationFieldConjugation • examinationClosurePi -
        examinationClosurePi ∈
      examinationFiveClosure := by
  rw [← examination_displacement]
  exact Ideal.mem_map_of_mem
    examinationFiveIntegers.toRingHom
    examination_five_displacement

private theorem examination_actual_displacement :
    examinationFieldConjugation • examinationClosurePi -
        examinationClosurePi ∉
      examinationFiveClosure ^ 2 := by
  intro h
  rw [examinationFiveClosure, ← Ideal.map_pow,
    ← examination_displacement] at h
  rcases (Ideal.mem_map_iff_of_surjective
    examinationFiveIntegers.toRingHom
    examinationFiveIntegers.surjective).1 h with
    ⟨x, hx, hxeq⟩
  have hxdisp : x =
      examinationFiveConjugation examinationFivePi - examinationFivePi :=
    examinationFiveIntegers.injective hxeq
  exact examination_displacement_sq (hxdisp ▸ hx)

/-- For the genuine Galois action on the integral closure, the zeroth
ramification group is the whole Galois group. -/
theorem examination_five_actual :
    idealRamificationGroup examinationFiveClosure
      Gal(ExaminationFiveField / ℚ_[3]) 0 = ⊤ := by
  have hconj : examinationFieldConjugation ∈
      idealRamificationGroup examinationFiveClosure
        Gal(ExaminationFiveField / ℚ_[3]) 0 := by
    rw [ideal_ramification_uniformizer
      examinationFiveClosure examinationClosurePi
      examination_adjoin_pi]
    simpa using five_actual_displacement
  haveI : Fact (Nat.card Gal(ExaminationFiveField / ℚ_[3])).Prime :=
    ⟨by rw [examination_five_galois]; norm_num⟩
  rcases (idealRamificationGroup examinationFiveClosure
    Gal(ExaminationFiveField / ℚ_[3]) 0).eq_bot_or_eq_top_of_prime_card with h | h
  · exact (examination_conjugation_ne
      (by simpa [h] using hconj)).elim
  · exact h

/-- For the genuine Galois action on the integral closure, the first
ramification group is trivial. -/
theorem examination_actual_ramification :
    idealRamificationGroup examinationFiveClosure
      Gal(ExaminationFiveField / ℚ_[3]) 1 = ⊥ := by
  have hconj : examinationFieldConjugation ∉
      idealRamificationGroup examinationFiveClosure
        Gal(ExaminationFiveField / ℚ_[3]) 1 := by
    rw [ideal_ramification_uniformizer
      examinationFiveClosure examinationClosurePi
      examination_adjoin_pi]
    simpa using examination_actual_displacement
  haveI : Fact (Nat.card Gal(ExaminationFiveField / ℚ_[3])).Prime :=
    ⟨by rw [examination_five_galois]; norm_num⟩
  rcases (idealRamificationGroup examinationFiveClosure
    Gal(ExaminationFiveField / ℚ_[3]) 1).eq_bot_or_eq_top_of_prime_card with h | h
  · exact h
  · exact (hconj (by simp [h])).elim

/-- Examination Question 5 for the actual extension `ℚ₃(ζ₃)/ℚ₃` and
its integral closure: its Galois group is cyclic of order two, `G₀` is the
whole group, and `Gᵢ` is trivial for every `i ≥ 1`. -/
theorem examination_actual_groups :
    IsCyclic Gal(ExaminationFiveField / ℚ_[3]) ∧
      idealRamificationGroup examinationFiveClosure
        Gal(ExaminationFiveField / ℚ_[3]) 0 = ⊤ ∧
      ∀ i : Nat, 1 ≤ i →
        idealRamificationGroup examinationFiveClosure
          Gal(ExaminationFiveField / ℚ_[3]) i = ⊥ := by
  refine ⟨examination_five_cyclic,
    examination_five_actual, fun i hi => ?_⟩
  apply bot_unique
  exact (ideal_ramification_antitone examinationFiveClosure hi).trans_eq
    examination_actual_ramification

end

end Submission.NumberTheory.Milne
