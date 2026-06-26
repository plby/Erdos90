import Submission.NumberTheory.Discriminant.PolynomialExamples
import Submission.NumberTheory.Ramification.KummerFactorization
import Submission.NumberTheory.Ramification.RamificationDiscriminant
import Mathlib.NumberTheory.NumberField.Discriminant.Different


/-!
# Milne, Chapter 4, Exercise 3

For the cubic polynomial `X^3 + X + 1`, this file records both parts of the splitting
calculation used in the exercise:

* the elementary classification of positive ramification-index/residue-degree data whose
  weighted sum is three;
* explicit factorizations modulo `3`, `31`, and `47`, together with irreducibility modulo `2`.

Combined with Kummer--Dedekind, these give every splitting pattern for the associated cubic
field except total ramification.  Its discriminant is `-31`, as already proved in
`PolynomialDiscriminantExamples`.
-/

namespace Submission.NumberTheory.Milne

open Polynomial UniqueFactorizationMonoid

noncomputable section

private theorem cubic_natDegree (R : Type*) [CommRing R] [Nontrivial R] :
    (X ^ 3 + X + 1 : R[X]).natDegree = 3 := by
  have hlow : (X + 1 : R[X]).natDegree < 3 := by
    calc
      (X + 1 : R[X]).natDegree ≤ max X.natDegree (1 : R[X]).natDegree :=
        natDegree_add_le _ _
      _ = 1 := by simp
      _ < 3 := by omega
  simpa [add_assoc] using
    ((isMonicOfDegree_X_pow R 3).add_right hlow).natDegree_eq

private theorem quadratic_natDegree (R : Type*) [CommRing R] [Nontrivial R] :
    (X ^ 2 + X - 1 : R[X]).natDegree = 2 := by
  have hlow : (X - 1 : R[X]).natDegree < 2 := by
    calc
      (X - 1 : R[X]).natDegree ≤ max X.natDegree (1 : R[X]).natDegree :=
        natDegree_sub_le _ _
      _ = 1 := by simp
      _ < 2 := by omega
  simpa [sub_eq_add_neg, add_assoc] using
    ((isMonicOfDegree_X_pow R 2).add_right hlow).natDegree_eq

/-- If a degree-three prime factorization has a single prime, its `(e, f)` pair is either
`(1, 3)` or `(3, 1)`. -/
theorem one_prime_patterns {e f : ℕ} (he : 0 < e) (hf : 0 < f)
    (hdegree : e * f = 3) :
    (e = 1 ∧ f = 3) ∨ (e = 3 ∧ f = 1) := by
  have he_le : e ≤ 3 := by
    calc
      e ≤ e * f := Nat.le_mul_of_pos_right e hf
      _ = 3 := hdegree
  have hf_le : f ≤ 3 := by
    calc
      f ≤ e * f := by
        simpa [mul_comm] using Nat.le_mul_of_pos_right f he
      _ = 3 := hdegree
  interval_cases e <;> interval_cases f <;> omega

/-- With two primes above a rational prime in a cubic field, the possible ordered `(e, f)`
data are the unramified `(1,1),(1,2)` pattern or the ramified `(1,1),(2,1)` pattern, in either
order. -/
theorem two_prime_patterns
    {e₁ f₁ e₂ f₂ : ℕ}
    (he₁ : 0 < e₁) (hf₁ : 0 < f₁) (he₂ : 0 < e₂) (hf₂ : 0 < f₂)
    (hdegree : e₁ * f₁ + e₂ * f₂ = 3) :
    ((e₁ = 1 ∧ f₁ = 1) ∧
        ((e₂ = 1 ∧ f₂ = 2) ∨ (e₂ = 2 ∧ f₂ = 1))) ∨
      (((e₁ = 1 ∧ f₁ = 2) ∨ (e₁ = 2 ∧ f₁ = 1)) ∧
        (e₂ = 1 ∧ f₂ = 1)) := by
  have he₁_le : e₁ ≤ 3 := by
    calc
      e₁ ≤ e₁ * f₁ := Nat.le_mul_of_pos_right e₁ hf₁
      _ ≤ e₁ * f₁ + e₂ * f₂ := Nat.le_add_right _ _
      _ = 3 := hdegree
  have hf₁_le : f₁ ≤ 3 := by
    calc
      f₁ ≤ e₁ * f₁ := by
        simpa [mul_comm] using Nat.le_mul_of_pos_right f₁ he₁
      _ ≤ e₁ * f₁ + e₂ * f₂ := Nat.le_add_right _ _
      _ = 3 := hdegree
  have he₂_le : e₂ ≤ 3 := by
    calc
      e₂ ≤ e₂ * f₂ := Nat.le_mul_of_pos_right e₂ hf₂
      _ ≤ e₁ * f₁ + e₂ * f₂ := Nat.le_add_left _ _
      _ = 3 := hdegree
  have hf₂_le : f₂ ≤ 3 := by
    calc
      f₂ ≤ e₂ * f₂ := by
        simpa [mul_comm] using Nat.le_mul_of_pos_right f₂ he₂
      _ ≤ e₁ * f₁ + e₂ * f₂ := Nat.le_add_left _ _
      _ = 3 := hdegree
  interval_cases e₁ <;> interval_cases f₁ <;>
    interval_cases e₂ <;> interval_cases f₂ <;> omega

/-- Three primes above a rational prime in a cubic field must all have ramification index and
residue degree one. -/
theorem three_prime_patterns
    {e₁ f₁ e₂ f₂ e₃ f₃ : ℕ}
    (h₁ : 0 < e₁ * f₁) (h₂ : 0 < e₂ * f₂) (h₃ : 0 < e₃ * f₃)
    (hdegree : e₁ * f₁ + e₂ * f₂ + e₃ * f₃ = 3) :
    e₁ = 1 ∧ f₁ = 1 ∧ e₂ = 1 ∧ f₂ = 1 ∧ e₃ = 1 ∧ f₃ = 1 := by
  have hp₁ : e₁ * f₁ = 1 := by omega
  have hp₂ : e₂ * f₂ = 1 := by omega
  have hp₃ : e₃ * f₃ = 1 := by omega
  have he₁ : e₁ = 1 := Nat.eq_one_of_dvd_one ⟨f₁, hp₁.symm⟩
  have hf₁ : f₁ = 1 :=
    Nat.eq_one_of_dvd_one ⟨e₁, hp₁.symm.trans (mul_comm e₁ f₁)⟩
  have he₂ : e₂ = 1 := Nat.eq_one_of_dvd_one ⟨f₂, hp₂.symm⟩
  have hf₂ : f₂ = 1 :=
    Nat.eq_one_of_dvd_one ⟨e₂, hp₂.symm.trans (mul_comm e₂ f₂)⟩
  have he₃ : e₃ = 1 := Nat.eq_one_of_dvd_one ⟨f₃, hp₃.symm⟩
  have hf₃ : f₃ = 1 :=
    Nat.eq_one_of_dvd_one ⟨e₃, hp₃.symm.trans (mul_comm e₃ f₃)⟩
  exact ⟨he₁, hf₁, he₂, hf₂, he₃, hf₃⟩

/-- Modulo `2`, `X^3 + X + 1` is irreducible, giving an inert prime. -/
theorem irreducible_mod_two :
    Irreducible (X ^ 3 + X + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · norm_num [cubic_natDegree]
  · intro x
    fin_cases x <;> norm_num [IsRoot.def, eval_add, eval_pow] <;> decide

/-- Modulo `3`, the polynomial has one linear and one irreducible quadratic factor. -/
theorem factorization_mod_three :
    (X ^ 3 + X + 1 : (ZMod 3)[X]) =
      (X - 1) * (X ^ 2 + X - 1) := by
  have h : (-2 : ZMod 3) = 1 := by decide
  have hpoly : (-2 : (ZMod 3)[X]) = 1 := by
    calc
      (-2 : (ZMod 3)[X]) = -C (2 : ZMod 3) := by rw [C_ofNat]
      _ = C (-2 : ZMod 3) := by rw [map_neg]
      _ = C 1 := by rw [h]
      _ = 1 := by simp
  calc
    (X ^ 3 + X + 1 : (ZMod 3)[X]) = X ^ 3 + (-2) * X + 1 := by rw [hpoly]; simp
    _ = (X - 1) * (X ^ 2 + X - 1) := by ring

theorem quadratic_irreducible_mod :
    Irreducible (X ^ 2 + X - 1 : (ZMod 3)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · norm_num [quadratic_natDegree]
  · intro x
    fin_cases x <;> norm_num [IsRoot.def, eval_add, eval_sub, eval_pow] <;> decide

/-- The unique ramified rational prime is exhibited by the repeated factor modulo `31`. -/
theorem factorization_mod_thirty :
    (X ^ 3 + X + 1 : (ZMod 31)[X]) =
      (X + 28) * (X + 17) ^ 2 := by
  ring_nf
  reduce_mod_char

/-- Modulo `47`, the polynomial splits into three distinct linear factors. -/
theorem factorization_forty_seven :
    (X ^ 3 + X + 1 : (ZMod 47)[X]) =
      (X + 12) * (X + 13) * (X + 22) := by
  ring_nf
  reduce_mod_char

private theorem normalized_mod_two :
    normalizedFactors (X ^ 3 + X + 1 : (ZMod 2)[X]) =
      ({X ^ 3 + X + 1} : Multiset (ZMod 2)[X]) := by
  rw [normalizedFactors_irreducible irreducible_mod_two]
  rw [(show (X ^ 3 + X + 1 : (ZMod 2)[X]).Monic by monicity ; norm_num).normalize_eq_self]

private theorem normalized_mod_three :
    normalizedFactors (X ^ 3 + X + 1 : (ZMod 3)[X]) =
      ({X - 1, X ^ 2 + X - 1} : Multiset (ZMod 3)[X]) := by
  have hlin : Irreducible (X - 1 : (ZMod 3)[X]) := by
    simpa using (irreducible_X_sub_C (1 : ZMod 3))
  rw [factorization_mod_three,
    normalizedFactors_mul hlin.ne_zero
      quadratic_irreducible_mod.ne_zero,
    normalizedFactors_irreducible hlin,
    normalizedFactors_irreducible quadratic_irreducible_mod]
  rw [(show (X - 1 : (ZMod 3)[X]).Monic by monicity).normalize_eq_self,
    (show (X ^ 2 + X - 1 : (ZMod 3)[X]).Monic by monicity ; norm_num).normalize_eq_self]
  rfl

section
local instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩
private theorem normalized_mod_thirty :
    normalizedFactors (X ^ 3 + X + 1 : (ZMod 31)[X]) =
      ({X + 28} : Multiset (ZMod 31)[X]) + ({X + 17} + {X + 17}) := by
  have h₁ : Irreducible (X + 28 : (ZMod 31)[X]) := by
    simpa [sub_eq_add_neg] using (irreducible_X_sub_C (-28 : ZMod 31))
  have h₂ : Irreducible (X + 17 : (ZMod 31)[X]) := by
    simpa [sub_eq_add_neg] using (irreducible_X_sub_C (-17 : ZMod 31))
  rw [factorization_mod_thirty, pow_two,
    normalizedFactors_mul h₁.ne_zero (mul_ne_zero h₂.ne_zero h₂.ne_zero),
    normalizedFactors_mul h₂.ne_zero h₂.ne_zero,
    normalizedFactors_irreducible h₁, normalizedFactors_irreducible h₂]
  rw [(show (X + 28 : (ZMod 31)[X]).Monic by monicity).normalize_eq_self,
    (show (X + 17 : (ZMod 31)[X]).Monic by monicity).normalize_eq_self]
end

section
local instance : Fact (Nat.Prime 47) := ⟨by norm_num⟩
private theorem normalized_forty_seven :
    normalizedFactors (X ^ 3 + X + 1 : (ZMod 47)[X]) =
      (({X + 12} : Multiset (ZMod 47)[X]) + {X + 13}) + {X + 22} := by
  have h₁ : Irreducible (X + 12 : (ZMod 47)[X]) := by
    simpa [sub_eq_add_neg] using (irreducible_X_sub_C (-12 : ZMod 47))
  have h₂ : Irreducible (X + 13 : (ZMod 47)[X]) := by
    simpa [sub_eq_add_neg] using (irreducible_X_sub_C (-13 : ZMod 47))
  have h₃ : Irreducible (X + 22 : (ZMod 47)[X]) := by
    simpa [sub_eq_add_neg] using (irreducible_X_sub_C (-22 : ZMod 47))
  rw [factorization_forty_seven,
    normalizedFactors_mul (mul_ne_zero h₁.ne_zero h₂.ne_zero) h₃.ne_zero,
    normalizedFactors_mul h₁.ne_zero h₂.ne_zero,
    normalizedFactors_irreducible h₁, normalizedFactors_irreducible h₂,
    normalizedFactors_irreducible h₃]
  rw [(show (X + 12 : (ZMod 47)[X]).Monic by monicity).normalize_eq_self,
    (show (X + 13 : (ZMod 47)[X]).Monic by monicity).normalize_eq_self,
    (show (X + 22 : (ZMod 47)[X]).Monic by monicity).normalize_eq_self]
end

/-- The Kummer--Dedekind bridge used in Exercise 4-3.  A monic irreducible factor of the
reduced minimal polynomial gives a prime above `p`; its multiplicity and degree are exactly
the ramification index and residue degree. -/
theorem factor_gives_data
    {K : Type*} [Field K] [NumberField K]
    (theta : NumberField.RingOfIntegers K)
    (hadjoin : Algebra.adjoin ℤ ({theta} : Set (NumberField.RingOfIntegers K)) = ⊤)
    {p : ℕ} [Fact p.Prime] {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod theta p) :
    ∃ P : Ideal (NumberField.RingOfIntegers K),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
        Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P =
          multiplicity Q ((minpoly ℤ theta).map (Int.castRingHom (ZMod p))) ∧
        Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) P = Q.natDegree := by
  have hexponent : RingOfIntegers.exponent theta = 1 :=
    RingOfIntegers.exponent_eq_one_iff.mpr hadjoin
  have hp : ¬p ∣ RingOfIntegers.exponent theta := by
    rw [hexponent]
    exact (Nat.Prime.not_dvd_one Fact.out)
  let E := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  let q : RingOfIntegers.monicFactorsMod theta p := ⟨Q, hQ⟩
  let P₀ := E.symm q
  refine ⟨P₀, P₀.prop.1, P₀.prop.2, ?_, ?_⟩
  · exact NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ
  · exact NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ

/-- The prime `2` is inert: there is one prime above it, with `(e, f) = (1, 3)`. -/
theorem inert_at_two
    {K : Type*} [Field K] [NumberField K]
    (theta : NumberField.RingOfIntegers K)
    (hadjoin : Algebra.adjoin ℤ ({theta} : Set (NumberField.RingOfIntegers K)) = ⊤)
    (hmin : minpoly ℤ theta = X ^ 3 + X + 1) :
    Nat.card
        (Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K)) = 1 ∧
      ∀ P : Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K),
        Ideal.ramificationIdx (Ideal.span ({(2 : ℤ)} : Set ℤ))
            (P : Ideal (NumberField.RingOfIntegers K)) = 1 ∧
          Ideal.inertiaDeg (Ideal.span ({(2 : ℤ)} : Set ℤ))
            (P : Ideal (NumberField.RingOfIntegers K)) = 3 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hexponent : RingOfIntegers.exponent theta = 1 :=
    RingOfIntegers.exponent_eq_one_iff.mpr hadjoin
  have hp : ¬2 ∣ RingOfIntegers.exponent theta := by simp [hexponent]
  let E := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  have hmap :
      (minpoly ℤ theta).map (Int.castRingHom (ZMod 2)) = X ^ 3 + X + 1 := by
    simp [hmin]
  have hfac :
      normalizedFactors ((minpoly ℤ theta).map (Int.castRingHom (ZMod 2))) =
        ({X ^ 3 + X + 1} : Multiset (ZMod 2)[X]) := by
    rw [hmap]
    exact normalized_mod_two
  constructor
  · calc
      Nat.card
          (Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
            (NumberField.RingOfIntegers K)) =
          Nat.card (RingOfIntegers.monicFactorsMod theta 2) :=
        Nat.card_congr E
      _ = 1 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        simp [RingOfIntegers.monicFactorsMod, hfac]
  · intro P
    let q := E P
    have hq : (q : (ZMod 2)[X]) = X ^ 3 + X + 1 := by
      have hmem := q.prop
      change (q : (ZMod 2)[X]) ∈
        (normalizedFactors ((minpoly ℤ theta).map (Int.castRingHom (ZMod 2)))).toFinset
        at hmem
      rw [hfac] at hmem
      simpa using hmem
    have he :=
      NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hp q.prop
    have hf :=
      NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hp q.prop
    have hmult :
        multiplicity (X ^ 3 + X + 1 : (ZMod 2)[X])
          (X ^ 3 + X + 1) = 1 := by
      rw [multiplicity_self]
    have hP :
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm q :
          Ideal (NumberField.RingOfIntegers K)) = P := by
      exact congrArg Subtype.val (E.symm_apply_apply P)
    have hmultq :
        multiplicity (q : (ZMod 2)[X])
          ((minpoly ℤ theta).map (Int.castRingHom (ZMod 2))) = 1 := by
      rw [hmap, hq]
      exact hmult
    have hdegq : (q : (ZMod 2)[X]).natDegree = 3 := by
      rw [hq, cubic_natDegree]
    constructor
    · rw [← hP]
      exact he.trans hmultq
    · rw [← hP]
      exact hf.trans hdegq

/-- The prime `3` has splitting type `(1, 2)`: two unramified primes, of residue degrees
one and two. -/
theorem splitting_at_three
    {K : Type*} [Field K] [NumberField K]
    (theta : NumberField.RingOfIntegers K)
    (hadjoin : Algebra.adjoin ℤ ({theta} : Set (NumberField.RingOfIntegers K)) = ⊤)
    (hmin : minpoly ℤ theta = X ^ 3 + X + 1) :
    Nat.card
        (Ideal.primesOver (Ideal.span ({(3 : ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K)) = 2 ∧
      ∀ P : Ideal.primesOver (Ideal.span ({(3 : ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K),
        (Ideal.ramificationIdx (Ideal.span ({(3 : ℤ)} : Set ℤ))
              (P : Ideal (NumberField.RingOfIntegers K)) = 1 ∧
            Ideal.inertiaDeg (Ideal.span ({(3 : ℤ)} : Set ℤ))
              (P : Ideal (NumberField.RingOfIntegers K)) = 1) ∨
          (Ideal.ramificationIdx (Ideal.span ({(3 : ℤ)} : Set ℤ))
              (P : Ideal (NumberField.RingOfIntegers K)) = 1 ∧
            Ideal.inertiaDeg (Ideal.span ({(3 : ℤ)} : Set ℤ))
              (P : Ideal (NumberField.RingOfIntegers K)) = 2) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hexponent : RingOfIntegers.exponent theta = 1 :=
    RingOfIntegers.exponent_eq_one_iff.mpr hadjoin
  have hp : ¬3 ∣ RingOfIntegers.exponent theta := by simp [hexponent]
  let E := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  let q₁ : (ZMod 3)[X] := X - 1
  let q₂ : (ZMod 3)[X] := X ^ 2 + X - 1
  have hq₁irr : Irreducible q₁ := by
    simpa [q₁] using (irreducible_X_sub_C (1 : ZMod 3))
  have hq₂irr : Irreducible q₂ := by
    simpa [q₂] using quadratic_irreducible_mod
  have hdeg₁ : q₁.natDegree = 1 := by
    simpa [q₁] using natDegree_X_sub_C (1 : ZMod 3)
  have hdeg₂ : q₂.natDegree = 2 := by
    simpa [q₂] using quadratic_natDegree (ZMod 3)
  have hqne : q₁ ≠ q₂ := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [hdeg₁, hdeg₂] at this
    omega
  have hmonic₁ : q₁.Monic := by
    dsimp [q₁]
    monicity
  have hmonic₂ : q₂.Monic := by
    dsimp [q₂]
    monicity ; norm_num
  have hmap :
      (minpoly ℤ theta).map (Int.castRingHom (ZMod 3)) = X ^ 3 + X + 1 := by
    simp [hmin]
  have hfac :
      normalizedFactors ((minpoly ℤ theta).map (Int.castRingHom (ZMod 3))) =
        ({q₁, q₂} : Multiset (ZMod 3)[X]) := by
    rw [hmap]
    simpa [q₁, q₂] using normalized_mod_three
  have hpoly0 : (X ^ 3 + X + 1 : (ZMod 3)[X]) ≠ 0 := by
    exact (show (X ^ 3 + X + 1 : (ZMod 3)[X]).Monic by
      monicity ; norm_num).ne_zero
  have hmult₁ : multiplicity q₁ (X ^ 3 + X + 1 : (ZMod 3)[X]) = 1 := by
    rw [multiplicity_eq_count_normalizedFactors hq₁irr hpoly0,
      normalized_mod_three, hmonic₁.normalize_eq_self]
    simp [q₁, q₂, hqne]
  have hmult₂ : multiplicity q₂ (X ^ 3 + X + 1 : (ZMod 3)[X]) = 1 := by
    rw [multiplicity_eq_count_normalizedFactors hq₂irr hpoly0,
      normalized_mod_three, hmonic₂.normalize_eq_self]
    simp [q₁, q₂, hqne]
  constructor
  · calc
      Nat.card
          (Ideal.primesOver (Ideal.span ({(3 : ℤ)} : Set ℤ))
            (NumberField.RingOfIntegers K)) =
          Nat.card (RingOfIntegers.monicFactorsMod theta 3) := Nat.card_congr E
      _ = 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        simp [RingOfIntegers.monicFactorsMod, hfac, hqne]
  · intro P
    let q := E P
    have hq : (q : (ZMod 3)[X]) = q₁ ∨ (q : (ZMod 3)[X]) = q₂ := by
      have hmem := q.prop
      change (q : (ZMod 3)[X]) ∈
        (normalizedFactors ((minpoly ℤ theta).map (Int.castRingHom (ZMod 3)))).toFinset
        at hmem
      rw [hfac] at hmem
      simpa [hqne] using hmem
    have he :=
      NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hp q.prop
    have hf :=
      NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hp q.prop
    have hP :
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm q :
          Ideal (NumberField.RingOfIntegers K)) = P := by
      exact congrArg Subtype.val (E.symm_apply_apply P)
    rcases hq with hq | hq
    · left
      constructor
      · rw [← hP]
        exact he.trans (by simpa [hmap, hq] using hmult₁)
      · rw [← hP]
        exact hf.trans (by simpa [hq] using hdeg₁)
    · right
      constructor
      · rw [← hP]
        exact he.trans (by simpa [hmap, hq] using hmult₂)
      · rw [← hP]
        exact hf.trans (by simpa [hq] using hdeg₂)

/-- The discriminant prime `31` has splitting type `(1, 1, 2)`: one unramified prime and
one prime of ramification index two, both of residue degree one. -/
theorem splitting_thirty_one
    {K : Type*} [Field K] [NumberField K]
    (theta : NumberField.RingOfIntegers K)
    (hadjoin : Algebra.adjoin ℤ ({theta} : Set (NumberField.RingOfIntegers K)) = ⊤)
    (hmin : minpoly ℤ theta = X ^ 3 + X + 1) :
    Nat.card
        (Ideal.primesOver (Ideal.span ({(31 : ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K)) = 2 ∧
      ∀ P : Ideal.primesOver (Ideal.span ({(31 : ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K),
        (Ideal.ramificationIdx (Ideal.span ({(31 : ℤ)} : Set ℤ))
              (P : Ideal (NumberField.RingOfIntegers K)) = 1 ∧
            Ideal.inertiaDeg (Ideal.span ({(31 : ℤ)} : Set ℤ))
              (P : Ideal (NumberField.RingOfIntegers K)) = 1) ∨
          (Ideal.ramificationIdx (Ideal.span ({(31 : ℤ)} : Set ℤ))
              (P : Ideal (NumberField.RingOfIntegers K)) = 2 ∧
            Ideal.inertiaDeg (Ideal.span ({(31 : ℤ)} : Set ℤ))
              (P : Ideal (NumberField.RingOfIntegers K)) = 1) := by
  letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hexponent : RingOfIntegers.exponent theta = 1 :=
    RingOfIntegers.exponent_eq_one_iff.mpr hadjoin
  have hp : ¬31 ∣ RingOfIntegers.exponent theta := by simp [hexponent]
  let E := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  let q₁ : (ZMod 31)[X] := X + 28
  let q₂ : (ZMod 31)[X] := X + 17
  have hq₁irr : Irreducible q₁ := by
    simpa [q₁, sub_eq_add_neg] using (irreducible_X_sub_C (-28 : ZMod 31))
  have hq₂irr : Irreducible q₂ := by
    simpa [q₂, sub_eq_add_neg] using (irreducible_X_sub_C (-17 : ZMod 31))
  have hdeg₁ : q₁.natDegree = 1 := by
    change (X + (28 : (ZMod 31)[X])).natDegree = 1
    rw [show (28 : (ZMod 31)[X]) = C (28 : ZMod 31) by
      exact (C_ofNat 28).symm]
    exact natDegree_X_add_C (28 : ZMod 31)
  have hdeg₂ : q₂.natDegree = 1 := by
    change (X + (17 : (ZMod 31)[X])).natDegree = 1
    rw [show (17 : (ZMod 31)[X]) = C (17 : ZMod 31) by
      exact (C_ofNat 17).symm]
    exact natDegree_X_add_C (17 : ZMod 31)
  have hqne : q₁ ≠ q₂ := by
    intro h
    have hc := congrArg (fun f : (ZMod 31)[X] => f.coeff 0) h
    simp only [coeff_add, coeff_X_zero, coeff_ofNat_zero, zero_add, q₁, q₂] at hc
    exact (by decide : (28 : ZMod 31) ≠ 17) hc
  have hmonic₁ : q₁.Monic := by dsimp [q₁]; monicity
  have hmonic₂ : q₂.Monic := by dsimp [q₂]; monicity
  have hmap :
      (minpoly ℤ theta).map (Int.castRingHom (ZMod 31)) = X ^ 3 + X + 1 := by
    simp [hmin]
  have hfac :
      normalizedFactors ((minpoly ℤ theta).map (Int.castRingHom (ZMod 31))) =
        ({q₁} : Multiset (ZMod 31)[X]) + ({q₂} + {q₂}) := by
    rw [hmap]
    simpa [q₁, q₂] using normalized_mod_thirty
  have hpoly0 : (X ^ 3 + X + 1 : (ZMod 31)[X]) ≠ 0 :=
    (show (X ^ 3 + X + 1 : (ZMod 31)[X]).Monic by monicity ; norm_num).ne_zero
  have hmult₁ : multiplicity q₁ (X ^ 3 + X + 1 : (ZMod 31)[X]) = 1 := by
    rw [multiplicity_eq_count_normalizedFactors hq₁irr hpoly0,
      normalized_mod_thirty, hmonic₁.normalize_eq_self]
    simp [q₁, q₂, hqne]
  have hmult₂ : multiplicity q₂ (X ^ 3 + X + 1 : (ZMod 31)[X]) = 2 := by
    rw [multiplicity_eq_count_normalizedFactors hq₂irr hpoly0,
      normalized_mod_thirty, hmonic₂.normalize_eq_self]
    simp [q₁, q₂, hqne]
  constructor
  · calc
      Nat.card
          (Ideal.primesOver (Ideal.span ({(31 : ℤ)} : Set ℤ))
            (NumberField.RingOfIntegers K)) =
          Nat.card (RingOfIntegers.monicFactorsMod theta 31) := Nat.card_congr E
      _ = 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        simp [RingOfIntegers.monicFactorsMod, hfac, hqne]
  · intro P
    let q := E P
    have hq : (q : (ZMod 31)[X]) = q₁ ∨ (q : (ZMod 31)[X]) = q₂ := by
      have hmem := q.prop
      change (q : (ZMod 31)[X]) ∈
        (normalizedFactors ((minpoly ℤ theta).map (Int.castRingHom (ZMod 31)))).toFinset
        at hmem
      rw [hfac] at hmem
      simpa [hqne] using hmem
    have he :=
      NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hp q.prop
    have hf :=
      NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hp q.prop
    have hP :
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm q :
          Ideal (NumberField.RingOfIntegers K)) = P := by
      exact congrArg Subtype.val (E.symm_apply_apply P)
    rcases hq with hq | hq
    · left
      constructor
      · rw [← hP]
        exact he.trans (by simpa [hmap, hq] using hmult₁)
      · rw [← hP]
        exact hf.trans (by simpa [hq] using hdeg₁)
    · right
      constructor
      · rw [← hP]
        exact he.trans (by simpa [hmap, hq] using hmult₂)
      · rw [← hP]
        exact hf.trans (by simpa [hq] using hdeg₂)

/-- The prime `47` splits completely: there are three primes above it and every one has
ramification index and residue degree one. -/
theorem splitting_forty_seven
    {K : Type*} [Field K] [NumberField K]
    (theta : NumberField.RingOfIntegers K)
    (hadjoin : Algebra.adjoin ℤ ({theta} : Set (NumberField.RingOfIntegers K)) = ⊤)
    (hmin : minpoly ℤ theta = X ^ 3 + X + 1) :
    Nat.card
        (Ideal.primesOver (Ideal.span ({(47 : ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K)) = 3 ∧
      ∀ P : Ideal.primesOver (Ideal.span ({(47 : ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K),
        Ideal.ramificationIdx (Ideal.span ({(47 : ℤ)} : Set ℤ))
            (P : Ideal (NumberField.RingOfIntegers K)) = 1 ∧
          Ideal.inertiaDeg (Ideal.span ({(47 : ℤ)} : Set ℤ))
            (P : Ideal (NumberField.RingOfIntegers K)) = 1 := by
  letI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
  have hexponent : RingOfIntegers.exponent theta = 1 :=
    RingOfIntegers.exponent_eq_one_iff.mpr hadjoin
  have hp : ¬47 ∣ RingOfIntegers.exponent theta := by simp [hexponent]
  let E := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  let q₁ : (ZMod 47)[X] := X + 12
  let q₂ : (ZMod 47)[X] := X + 13
  let q₃ : (ZMod 47)[X] := X + 22
  have hq₁irr : Irreducible q₁ := by
    simpa [q₁, sub_eq_add_neg] using (irreducible_X_sub_C (-12 : ZMod 47))
  have hq₂irr : Irreducible q₂ := by
    simpa [q₂, sub_eq_add_neg] using (irreducible_X_sub_C (-13 : ZMod 47))
  have hq₃irr : Irreducible q₃ := by
    simpa [q₃, sub_eq_add_neg] using (irreducible_X_sub_C (-22 : ZMod 47))
  have hdeg₁ : q₁.natDegree = 1 := by
    change (X + (12 : (ZMod 47)[X])).natDegree = 1
    rw [show (12 : (ZMod 47)[X]) = C (12 : ZMod 47) by exact (C_ofNat 12).symm]
    exact natDegree_X_add_C (12 : ZMod 47)
  have hdeg₂ : q₂.natDegree = 1 := by
    change (X + (13 : (ZMod 47)[X])).natDegree = 1
    rw [show (13 : (ZMod 47)[X]) = C (13 : ZMod 47) by exact (C_ofNat 13).symm]
    exact natDegree_X_add_C (13 : ZMod 47)
  have hdeg₃ : q₃.natDegree = 1 := by
    change (X + (22 : (ZMod 47)[X])).natDegree = 1
    rw [show (22 : (ZMod 47)[X]) = C (22 : ZMod 47) by exact (C_ofNat 22).symm]
    exact natDegree_X_add_C (22 : ZMod 47)
  have hq₁₂ : q₁ ≠ q₂ := by
    intro h
    have hc := congrArg (fun f : (ZMod 47)[X] => f.coeff 0) h
    simp only [coeff_add, coeff_X_zero, coeff_ofNat_zero, zero_add, q₁, q₂] at hc
    exact (by decide : (12 : ZMod 47) ≠ 13) hc
  have hq₁₃ : q₁ ≠ q₃ := by
    intro h
    have hc := congrArg (fun f : (ZMod 47)[X] => f.coeff 0) h
    simp only [coeff_add, coeff_X_zero, coeff_ofNat_zero, zero_add, q₁, q₃] at hc
    exact (by decide : (12 : ZMod 47) ≠ 22) hc
  have hq₂₃ : q₂ ≠ q₃ := by
    intro h
    have hc := congrArg (fun f : (ZMod 47)[X] => f.coeff 0) h
    simp only [coeff_add, coeff_X_zero, coeff_ofNat_zero, zero_add, q₂, q₃] at hc
    exact (by decide : (13 : ZMod 47) ≠ 22) hc
  have hmonic₁ : q₁.Monic := by dsimp [q₁]; monicity
  have hmonic₂ : q₂.Monic := by dsimp [q₂]; monicity
  have hmonic₃ : q₃.Monic := by dsimp [q₃]; monicity
  have hmap :
      (minpoly ℤ theta).map (Int.castRingHom (ZMod 47)) = X ^ 3 + X + 1 := by
    simp [hmin]
  have hfac :
      normalizedFactors ((minpoly ℤ theta).map (Int.castRingHom (ZMod 47))) =
        (({q₁} : Multiset (ZMod 47)[X]) + {q₂}) + {q₃} := by
    rw [hmap]
    simpa [q₁, q₂, q₃] using normalized_forty_seven
  have hfacpoly :
      normalizedFactors (X ^ 3 + X + 1 : (ZMod 47)[X]) =
        (({q₁} : Multiset (ZMod 47)[X]) + {q₂}) + {q₃} := by
    simpa [q₁, q₂, q₃] using normalized_forty_seven
  have hpoly0 : (X ^ 3 + X + 1 : (ZMod 47)[X]) ≠ 0 :=
    (show (X ^ 3 + X + 1 : (ZMod 47)[X]).Monic by monicity ; norm_num).ne_zero
  have hmult₁ : multiplicity q₁ (X ^ 3 + X + 1 : (ZMod 47)[X]) = 1 := by
    rw [multiplicity_eq_count_normalizedFactors hq₁irr hpoly0,
      hfacpoly, hmonic₁.normalize_eq_self]
    simp [hq₁₂, hq₁₃]
  have hmult₂ : multiplicity q₂ (X ^ 3 + X + 1 : (ZMod 47)[X]) = 1 := by
    rw [multiplicity_eq_count_normalizedFactors hq₂irr hpoly0,
      hfacpoly, hmonic₂.normalize_eq_self]
    simp [hq₁₂.symm, hq₂₃]
  have hmult₃ : multiplicity q₃ (X ^ 3 + X + 1 : (ZMod 47)[X]) = 1 := by
    rw [multiplicity_eq_count_normalizedFactors hq₃irr hpoly0,
      hfacpoly, hmonic₃.normalize_eq_self]
    simp [hq₁₃.symm, hq₂₃.symm]
  constructor
  · calc
      Nat.card
          (Ideal.primesOver (Ideal.span ({(47 : ℤ)} : Set ℤ))
            (NumberField.RingOfIntegers K)) =
          Nat.card (RingOfIntegers.monicFactorsMod theta 47) := Nat.card_congr E
      _ = 3 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        simp [RingOfIntegers.monicFactorsMod, hfac, hq₁₂, hq₁₃, hq₂₃]
  · intro P
    let q := E P
    have hq : (q : (ZMod 47)[X]) = q₁ ∨ (q : (ZMod 47)[X]) = q₂ ∨
        (q : (ZMod 47)[X]) = q₃ := by
      have hmem := q.prop
      change (q : (ZMod 47)[X]) ∈
        (normalizedFactors ((minpoly ℤ theta).map (Int.castRingHom (ZMod 47)))).toFinset
        at hmem
      rw [hfac] at hmem
      simpa [hq₁₂, hq₁₃, hq₂₃] using hmem
    have he :=
      NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hp q.prop
    have hf :=
      NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hp q.prop
    have hP :
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm q :
          Ideal (NumberField.RingOfIntegers K)) = P := by
      exact congrArg Subtype.val (E.symm_apply_apply P)
    rcases hq with hq | hq | hq
    · constructor
      · rw [← hP]
        exact he.trans (by simpa [hmap, hq] using hmult₁)
      · rw [← hP]
        exact hf.trans (by simpa [hq] using hdeg₁)
    · constructor
      · rw [← hP]
        exact he.trans (by simpa [hmap, hq] using hmult₂)
      · rw [← hP]
        exact hf.trans (by simpa [hq] using hdeg₂)
    · constructor
      · rw [← hP]
        exact he.trans (by simpa [hmap, hq] using hmult₃)
      · rw [← hP]
        exact hf.trans (by simpa [hq] using hdeg₃)

/-- Total ramification does not occur in the cubic field of Exercise 4-3.  Indeed, a totally
ramified rational prime would divide the field discriminant `-31`, hence would be `31`; the
explicit Kummer--Dedekind calculation at `31` has ramification indices only one and two. -/
theorem not_totally_ramified
    {K : Type*} [Field K] [NumberField K]
    (theta : NumberField.RingOfIntegers K)
    (hadjoin : Algebra.adjoin ℤ ({theta} : Set (NumberField.RingOfIntegers K)) = ⊤)
    (hmin : minpoly ℤ theta = X ^ 3 + X + 1)
    (hdiscr : NumberField.discr K = -31)
    {p : ℕ} [Fact p.Prime]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Ideal.ramificationIdx (Ideal.span ({(p : ℤ)} : Set ℤ)) P ≠ 3 := by
  intro heq
  have hp0 : Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊥ := by
    simp [NeZero.ne p]
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have hramified : Ideal.ramificationIdx (P.under ℤ) P ≠ 1 := by
    rw [← Ideal.over_def P (Ideal.span ({(p : ℤ)} : Set ℤ))]
    omega
  have hdvd : P ∣ differentIdeal ℤ (NumberField.RingOfIntegers K) :=
    (ramifies_dvd_different ℤ (NumberField.RingOfIntegers K) P hP0).mp
      hramified
  have hdiscP :
      algebraMap ℤ (NumberField.RingOfIntegers K) (NumberField.discr K) ∈ P := by
    exact Ideal.dvd_iff_le.mp hdvd (NumberField.discr_mem_differentIdeal K _)
  have hdiscBase : NumberField.discr K ∈ Ideal.span ({(p : ℤ)} : Set ℤ) :=
    (Ideal.mem_of_liesOver P (Ideal.span ({(p : ℤ)} : Set ℤ)) _).mpr hdiscP
  rw [hdiscr, Ideal.mem_span_singleton] at hdiscBase
  have hpdivZ : (p : ℤ) ∣ (31 : ℤ) := dvd_neg.mp hdiscBase
  have hpdiv : p ∣ 31 := Int.natCast_dvd_natCast.mp hpdivZ
  have hp31 : p = 31 :=
    ((Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hpdiv).resolve_left
      (show Nat.Prime p from Fact.out).ne_one
  subst p
  let P₀ : Ideal.primesOver (Ideal.span ({(31 : ℤ)} : Set ℤ))
      (NumberField.RingOfIntegers K) := ⟨P, inferInstance, inferInstance⟩
  have hsplit := (splitting_thirty_one theta hadjoin hmin).2 P₀
  change
    (Ideal.ramificationIdx (Ideal.span ({(31 : ℤ)} : Set ℤ)) P = 1 ∧
      Ideal.inertiaDeg (Ideal.span ({(31 : ℤ)} : Set ℤ)) P = 1) ∨
    (Ideal.ramificationIdx (Ideal.span ({(31 : ℤ)} : Set ℤ)) P = 2 ∧
      Ideal.inertiaDeg (Ideal.span ({(31 : ℤ)} : Set ℤ)) P = 1) at hsplit
  rcases hsplit with ⟨he', -⟩ | ⟨he', -⟩
  · have : (3 : ℕ) = 1 := heq.symm.trans he'
    norm_num at this
  · have : (3 : ℕ) = 2 := heq.symm.trans he'
    norm_num at this

end

end Submission.NumberTheory.Milne
