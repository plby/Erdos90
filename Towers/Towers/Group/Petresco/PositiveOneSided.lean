import Towers.Group.Petresco.CertifiedFactors

/-!
# Positive one-sided Petresco collection

This file formalizes the positive coefficient arithmetic and the exact
one-sided orbit expansion used in `docs/a.tex`.
-/

namespace Towers
namespace Edmonton

universe u

/-- The product of the positive binomial coefficients selected by a list of
block degrees. -/
def positiveAdmissibleProduct (M : ℕ) (degrees : List ℕ) : ℤ :=
  (degrees.map fun k => (Nat.choose M k : ℤ)).prod

/-- Products of positive binomial coefficients with prescribed total left
and right degrees. -/
def positiveAdmissibleGenerators
    (M N r s : ℕ) : Set ℤ :=
  { E |
    ∃ left right : List ℕ,
      left.sum = r ∧
        right.sum = s ∧
          positiveAdmissibleProduct M left *
            positiveAdmissibleProduct N right = E }

/-- The positive admissible coefficient module `A⁺_{r,s}(M,N)`. -/
def positiveAdmissibleCoefficients
    (M N r s : ℕ) : Submodule ℤ ℤ :=
  Submodule.span ℤ (positiveAdmissibleGenerators M N r s)

@[simp]
lemma admissible_degree_positive (degrees : List ℕ) :
    admissibleBlockDegree
        (degrees.map fun k => ({ sign := .positive, degree := k } :
          AdmissibleCoefficientBlock)) =
      degrees.sum := by
  simp [admissibleBlockDegree, List.map_map, Function.comp_def]

@[simp]
lemma admissible_block_positive (M : ℕ) (degrees : List ℕ) :
    admissibleBlockProduct M
        (degrees.map fun k => ({ sign := .positive, degree := k } :
          AdmissibleCoefficientBlock)) =
      positiveAdmissibleProduct M degrees := by
  simp [admissibleBlockProduct, positiveAdmissibleProduct,
    signedChoose, List.map_map, Function.comp_def]

/-- A positive block pattern is also a signed block pattern, with every sign
set to `positive`. -/
lemma admissible_coefficients
    (M N r s : ℕ) :
    positiveAdmissibleCoefficients M N r s ≤
      admissibleCoefficients M N r s := by
  rw [positiveAdmissibleCoefficients, Submodule.span_le]
  rintro E ⟨left, right, hr, hs, rfl⟩
  apply Submodule.subset_span
  refine
    ⟨left.map fun k => ({ sign := .positive, degree := k } :
        AdmissibleCoefficientBlock),
      right.map fun k => ({ sign := .positive, degree := k } :
        AdmissibleCoefficientBlock), ?_, ?_, ?_⟩
  · simpa using hr
  · simpa using hs
  · simp

/-- The empty positive block pattern has coefficient one and bidegree zero. -/
lemma positive_admissible_coefficients
    (M N : ℕ) :
    (1 : ℤ) ∈ positiveAdmissibleCoefficients M N 0 0 := by
  apply Submodule.subset_span
  exact
    ⟨[], [], by simp, by simp,
      by simp [positiveAdmissibleProduct]⟩

/-- A single positive left and right block gives the corresponding product
of binomial coefficients. -/
lemma choose_admissible_coefficients
    (M N k l : ℕ) :
    (Nat.choose M k : ℤ) * Nat.choose N l ∈
      positiveAdmissibleCoefficients M N k l := by
  apply Submodule.subset_span
  refine ⟨[k], [l], by simp, by simp, ?_⟩
  simp [positiveAdmissibleProduct]

/-- Multiplication concatenates positive block certificates and adds their
exact bidegrees. -/
lemma mul_admissible_coefficients
    {M N r s r' s' : ℕ} {E F : ℤ}
    (hE : E ∈ positiveAdmissibleCoefficients M N r s)
    (hF : F ∈ positiveAdmissibleCoefficients M N r' s') :
    E * F ∈ positiveAdmissibleCoefficients M N (r + r') (s + s') := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
      rcases hE with ⟨left, right, hr, hs, rfl⟩
      induction hF using Submodule.span_induction with
      | mem F hF =>
          rcases hF with ⟨left', right', hr', hs', rfl⟩
          apply Submodule.subset_span
          refine ⟨left ++ left', right ++ right', ?_, ?_, ?_⟩
          · simpa using congrArg₂ Nat.add hr hr'
          · simpa using congrArg₂ Nat.add hs hs'
          · simp [positiveAdmissibleProduct]
            ring
      | zero =>
          simp
      | add E F _ _ ihE ihF =>
          simpa [mul_add] using
            (positiveAdmissibleCoefficients M N (r + r') (s + s')).add_mem
              ihE ihF
      | smul c E _ ihE =>
          convert
            (positiveAdmissibleCoefficients M N (r + r') (s + s')).smul_mem
              c ihE using 1
          simp
          ring
  | zero =>
      simp
  | add E F _ _ ihE ihF =>
      simpa [add_mul] using
        (positiveAdmissibleCoefficients M N (r + r') (s + s')).add_mem
          ihE ihF
  | smul c E _ ihE =>
      convert
        (positiveAdmissibleCoefficients M N (r + r') (s + s')).smul_mem
          c ihE using 1
      simp
      ring

/-- Positive admissibility implies the same two divisibility laws as signed
admissibility. -/
theorem positive_admissible_divisibility
    {M N r s : ℕ} {E : ℤ}
    (hE : E ∈ positiveAdmissibleCoefficients M N r s) :
    (M : ℤ) ∣ (r : ℤ) * E ∧
      (N : ℤ) ∣ (s : ℤ) * E :=
  admissibleCoefficient_divisibility
    (admissible_coefficients M N r s hE)

/-- A mixed collected factor carrying positive-binomial provenance. -/
structure PCFactor (M N : ℕ) where
  word : FormalCommutator Bool
  exponent : ℤ
  conjugator : FreeGroup Bool
  mixed : 0 < leftDegree word ∧ 0 < rightDegree word
  admissible :
    exponent ∈
      positiveAdmissibleCoefficients M N
        (leftDegree word) (rightDegree word)

namespace PCFactor

/-- Forgetting positivity gives an ordinary signed certified factor. -/
def toCFactor
    {M N : ℕ} (factor : PCFactor M N) :
    CFactor M N where
  word := factor.word
  exponent := factor.exponent
  conjugator := factor.conjugator
  mixed := factor.mixed
  admissible :=
    admissible_coefficients
      M N (leftDegree factor.word) (rightDegree factor.word)
      factor.admissible

/-- The correction produced by crossing two aggregate families has product
coefficient and summed exact bidegree. -/
def correction
    {M N : ℕ}
    (left right : PCFactor M N)
    (conjugator : FreeGroup Bool) :
    PCFactor M N where
  word := formalBracket left.word right.word
  exponent := left.exponent * right.exponent
  conjugator := conjugator
  mixed := by
    constructor
    · change 0 < leftDegree left.word + leftDegree right.word
      have hleft := left.mixed.1
      omega
    · change 0 < rightDegree left.word + rightDegree right.word
      have hright := left.mixed.2
      omega
  admissible := by
    simpa [leftDegree, rightDegree] using
      mul_admissible_coefficients
        left.admissible right.admissible

/-- Negating an aggregate coefficient preserves positive admissibility. -/
def neg
    {M N : ℕ} (factor : PCFactor M N) :
    PCFactor M N where
  word := factor.word
  exponent := -factor.exponent
  conjugator := factor.conjugator
  mixed := factor.mixed
  admissible :=
    (positiveAdmissibleCoefficients M N
      (leftDegree factor.word) (rightDegree factor.word)).neg_mem
        factor.admissible

/-- Changing only the outer conjugator preserves every arithmetic
certificate. -/
def withConjugator
    {M N : ℕ} (factor : PCFactor M N)
    (conjugator : FreeGroup Bool) :
    PCFactor M N where
  word := factor.word
  exponent := factor.exponent
  conjugator := conjugator
  mixed := factor.mixed
  admissible := factor.admissible

/-- The divisibility conclusion attached to a positive certified factor. -/
lemma exponent_divisibility
    {M N : ℕ} (factor : PCFactor M N) :
    (M : ℤ) ∣ (leftDegree factor.word : ℤ) * factor.exponent ∧
      (N : ℤ) ∣ (rightDegree factor.word : ℤ) * factor.exponent :=
  positive_admissible_divisibility factor.admissible

end PCFactor

/-- The normal subgroup generated by positive-admissible mixed commutator
powers. -/
def positiveAdmissibleSubgroup
    {G : Type u} [Group G] (M N : ℕ) (x y : G) : Subgroup G :=
  Subgroup.normalClosure
    { z |
      ∃ word : FormalCommutator Bool, ∃ exponent : ℤ,
        0 < leftDegree word ∧
          0 < rightDegree word ∧
            exponent ∈
              positiveAdmissibleCoefficients M N
                (leftDegree word) (rightDegree word) ∧
              generatorFormalCommutator x y word ^ exponent = z }

instance positive_admissible_normal
    {G : Type u} [Group G] (M N : ℕ) (x y : G) :
    (positiveAdmissibleSubgroup M N x y).Normal :=
  Subgroup.normalClosure_normal

/-- Positive admissibility is stronger than signed admissibility, so the
positive target is contained in the general Edmonton target. -/
lemma positive_admissible_subgroup
    {G : Type u} [Group G] (M N : ℕ) (x y : G) :
    positiveAdmissibleSubgroup M N x y ≤
      admissibleHallSubgroup M N x y := by
  apply Subgroup.normalClosure_le_normal
  rintro z ⟨word, exponent, hleft, hright, hadmissible, rfl⟩
  exact admissible_hall_generator ⟨hleft, hright⟩
    (admissible_coefficients
      M N (leftDegree word) (rightDegree word) hadmissible)

/-- Every positive certified factor evaluates in the positive admissible
normal subgroup. -/
lemma PCFactor.evalmem_posadmissible_hallsubgroup
    {G : Type u} [Group G] {M N : ℕ} {x y : G}
    (factor : PCFactor M N) :
    factor.toCFactor.eval x y ∈
      positiveAdmissibleSubgroup M N x y := by
  have hcore :
      generatorFormalCommutator x y factor.word ^ factor.exponent ∈
        positiveAdmissibleSubgroup M N x y := by
    apply Subgroup.subset_normalClosure
    exact
      ⟨factor.word, factor.exponent, factor.mixed.1, factor.mixed.2,
        factor.admissible, rfl⟩
  exact
    (inferInstance : (positiveAdmissibleSubgroup M N x y).Normal).conj_mem
      _ hcore (twoGeneratorFree x y factor.conjugator)

/-- The basic mixed formal commutator `[x,y]`. -/
def positiveSidedWord : FormalCommutator Bool :=
  formalBracket (FreeMagma.of false) (FreeMagma.of true)

/-- Replace a formal factor `u` by the two factors in
`u^x = u [u,x]`. -/
def formalConjugateLeft
    (u : FormalCommutator Bool) : List (FormalCommutator Bool) :=
  [u, formalBracket u (FreeMagma.of false)]

/-- The exact formal word obtained by repeatedly expanding the conjugation
orbit in `[x^M,y]`. -/
def positiveSidedOrbit : ℕ → List (FormalCommutator Bool)
  | 0 => []
  | n + 1 =>
      (positiveSidedOrbit n).flatMap formalConjugateLeft ++
        [positiveSidedWord]

@[simp]
lemma formalConjugateExpansion
    {G : Type u} [Group G] (x y : G)
    (word : FormalCommutator Bool) :
    evalFormalWord
        (fun
          | false => x
          | true => y)
        (formalConjugateLeft word) =
      hallConjugate (generatorFormalCommutator x y word) x := by
  simp [formalConjugateLeft,
    generatorFormalCommutator,
    hall_conjugate_commutator]
  rfl

/-- Expanding every factor by `u^x = u [u,x]` conjugates the value of the
whole formal word by `x`. -/
lemma formal_flat_conjugate
    {G : Type u} [Group G] (x y : G)
    (words : List (FormalCommutator Bool)) :
    evalFormalWord
        (fun
          | false => x
          | true => y)
        (words.flatMap formalConjugateLeft) =
      hallConjugate
        (evalFormalWord
          (fun
            | false => x
            | true => y)
          words)
        x := by
  induction words with
  | nil =>
      simp [hallConjugate]
  | cons word words ih =>
      simp only [List.flatMap_cons, eval_formal_append,
        eval_formal_cons]
      rw [formalConjugateExpansion, ih]
      change
        hallConjugate
              (formalGroupCommutator
                (fun
                  | false => x
                  | true => y)
                word)
              x *
            hallConjugate
              (evalFormalWord
                (fun
                  | false => x
                  | true => y)
                words)
              x =
          hallConjugate
            (formalGroupCommutator
                (fun
                  | false => x
                  | true => y)
                word *
              evalFormalWord
                (fun
                  | false => x
                  | true => y)
                words)
            x
      simp [hallConjugate, mul_assoc]

/-- The orbit expansion evaluates exactly to the one-sided power
commutator. -/
theorem positive_sided_orbit
    {G : Type u} [Group G] (x y : G) :
    ∀ M : ℕ,
      evalFormalWord
          (fun
            | false => x
            | true => y)
          (positiveSidedOrbit M) =
        hallCommutator (x ^ M) y := by
  intro M
  induction M with
  | zero =>
      simp [positiveSidedOrbit, hallCommutator]
  | succ M ih =>
      rw [positiveSidedOrbit, eval_formal_append,
        formal_flat_conjugate, ih]
      simp only [eval_formal_cons, eval_formal_nil, mul_one]
      change
        hallConjugate (hallCommutator (x ^ M) y) x *
            hallCommutator x y =
          hallCommutator (x ^ (M + 1)) y
      rw [pow_succ, commutator_mul_left]

/-- Every factor in the exact orbit expansion is mixed. -/
lemma positive_sided_mixed :
    ∀ M : ℕ, ∀ word ∈ positiveSidedOrbit M,
      0 < leftDegree word ∧ 0 < rightDegree word := by
  intro M
  induction M with
  | zero =>
      simp [positiveSidedOrbit]
  | succ M ih =>
      intro word hword
      simp only [positiveSidedOrbit, List.mem_append,
        List.mem_flatMap, List.mem_singleton] at hword
      rcases hword with ⟨source, hsource, hword⟩ | rfl
      · have hsourceMixed := ih source hsource
        simp only [formalConjugateLeft, List.mem_cons,
          List.not_mem_nil, or_false] at hword
        rcases hword with rfl | rfl
        · exact hsourceMixed
        · constructor
          · change 0 < leftDegree source + 1
            omega
          · change 0 < rightDegree source + 0
            omega
      · simp [positiveSidedWord, leftDegree, rightDegree,
          formalBidegree, formalGrade, formalBracket]

/-- A completed positive one-sided collection is an exact factor list whose
members carry the positive-binomial invariant from `docs/a.tex`. -/
structure PSColl (M : ℕ) where
  factors : List (PCFactor M 1)
  eval_eq :
    ∀ {G : Type u} [Group G] (x y : G),
      (factors.map fun factor => factor.toCFactor.eval x y).prod =
        hallCommutator (x ^ M) y

namespace PSColl

/-- The zero power has the empty positive collection. -/
def zero : PSColl.{u} 0 where
  factors := []
  eval_eq := by
    intro G _inst x y
    simp [hallCommutator]

/-- The basic commutator is a positive certified factor at block size one. -/
def basicFactor : PCFactor 1 1 where
  word := positiveSidedWord
  exponent := 1
  conjugator := 1
  mixed := by
    simp [positiveSidedWord, leftDegree, rightDegree,
      formalBidegree, formalGrade, formalBracket]
  admissible := by
    simpa using
      choose_admissible_coefficients 1 1 1 1

/-- The one-sided theorem at `M = 1`. -/
def one : PSColl.{u} 1 where
  factors := [basicFactor]
  eval_eq := by
    intro G _inst x y
    simp [basicFactor, PCFactor.toCFactor,
      CFactor.eval, positiveSidedWord]

/-- The free-group word evaluating to the basic Hall commutator. -/
def basicFreeCommutator : FreeGroup Bool :=
  hallCommutator (FreeGroup.of false) (FreeGroup.of true)

/-- The coefficient-two basic factor in the `M = 2` collection. -/
def twoBasicFactor : PCFactor 2 1 where
  word := positiveSidedWord
  exponent := 2
  conjugator := 1
  mixed := basicFactor.mixed
  admissible := by
    simpa using
      choose_admissible_coefficients 2 1 1 1

/-- The bidegree `(2,1)` correction in the `M = 2` collection. -/
def twoCorrectionFactor : PCFactor 2 1 where
  word :=
    formalBracket positiveSidedWord (FreeMagma.of false)
  exponent := 1
  conjugator := basicFreeCommutator⁻¹
  mixed := by
    simp [positiveSidedWord, leftDegree, rightDegree,
      formalBidegree, formalGrade, formalBracket]
  admissible := by
    simpa [leftDegree, rightDegree, positiveSidedWord] using
      choose_admissible_coefficients 2 1 2 1

/-- The first nontrivial positive one-sided collection:
`[x²,y] = [x,y]² [[x,y],x]^[x,y]`. -/
def two : PSColl.{u} 2 where
  factors := [twoBasicFactor, twoCorrectionFactor]
  eval_eq := by
    intro G _inst x y
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    simp only [twoBasicFactor, twoCorrectionFactor,
      PCFactor.toCFactor, CFactor.eval,
      generator_formal_bracket,
      generator_formal_false,
      generator_formal_true,
      positiveSidedWord]
    simp only [map_one, one_mul, inv_one, mul_one]
    simp only [map_inv, inv_inv]
    have hfree :
        twoGeneratorFree x y basicFreeCommutator =
          hallCommutator x y := by
      simp [basicFreeCommutator, hallCommutator,
        twoGeneratorFree]
    rw [hfree]
    rw [show (2 : ℤ) = (2 : ℕ) by norm_num, zpow_natCast, pow_two]
    rw [show x ^ 2 = x * x by simp [pow_two], commutator_mul_left]
    rw [hall_conjugate_commutator]
    group

/-- The semantic conclusion of a completed positive one-sided collection. -/
theorem hall_commutator_pow
    {M : ℕ} (collection : PSColl.{u} M)
    {G : Type u} [Group G] (x y : G) :
    hallCommutator (x ^ M) y ∈
      positiveAdmissibleSubgroup M 1 x y := by
  rw [← collection.eval_eq x y]
  induction collection.factors with
  | nil =>
      simp
  | cons factor factors ih =>
      simp only [List.map_cons, List.prod_cons]
      exact
        (positiveAdmissibleSubgroup M 1 x y).mul_mem
          factor.evalmem_posadmissible_hallsubgroup ih

end PSColl

/-- The theorem from `docs/a.tex` in its exact normal-closure form, once the
correlated orbit prefix has been normalized into a positive collection. -/
theorem sided_theorem_collection
    {M : ℕ} (collection : PSColl.{u} M)
    {G : Type u} [Group G] (x y : G) :
    hallCommutator (x ^ M) y ∈
      positiveAdmissibleSubgroup M 1 x y :=
  collection.hall_commutator_pow x y

end Edmonton
end Towers
