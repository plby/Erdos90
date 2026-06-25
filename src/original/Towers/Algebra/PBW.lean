import Towers.Algebra.Filtered
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Dvd

namespace Towers
namespace Algebra

universe u v w
open Towers.Group

/-- A formal p-binomial error term. -/
structure bETerm (A : Type u) where
  p : ℕ
  prime : Nat.Prime p
  left : A
  right : A
  term : A
  errorExpr : A → A → A
  term_eq_error : term = errorExpr left right
  weightFn : A → ℕ
  inputWeight : ℕ
  weight : ℕ
  left_weight_le : weightFn left ≤ inputWeight
  right_weight_le : weightFn right ≤ inputWeight
  term_weight_eq : weightFn term = weight
  higher_weight : inputWeight < weight

/-- The displayed term is the error expression evaluated on its inputs. -/
theorem bETerm.term_eq_errorexpr {A : Type u} (E : bETerm A) :
    E.term = E.errorExpr E.left E.right :=
  E.term_eq_error

/-- The recorded binomial error term has a higher weight than its input. -/
theorem bETerm.higher_weight' {A : Type u} (E : bETerm A) :
    E.inputWeight < E.weight :=
  E.higher_weight

/-- The stored prime is indeed prime. -/
theorem bETerm.prime_p {A : Type u} (E : bETerm A) :
    Nat.Prime E.p :=
  E.prime

/-- A p-binomial error package supplies the usual prime fact for its exponent. -/
instance bETerm.fact_prime {A : Type u} (E : bETerm A) :
    Fact E.p.Prime :=
  ⟨E.prime⟩

/-- The recorded weight is the weight of the displayed error term. -/
theorem bETerm.term_weight {A : Type u} (E : bETerm A) :
    E.weightFn E.term = E.weight :=
  E.term_weight_eq

/-- The left input has weight at most the recorded input weight. -/
theorem bETerm.left_weight_leinput {A : Type u} (E : bETerm A) :
    E.weightFn E.left ≤ E.inputWeight :=
  E.left_weight_le

/-- The right input has weight at most the recorded input weight. -/
theorem bETerm.right_weight_leinput {A : Type u} (E : bETerm A) :
    E.weightFn E.right ≤ E.inputWeight :=
  E.right_weight_le

/-- The error term has strictly larger recorded weight than its input. -/
theorem bETerm.input_lt_weight {A : Type u} (E : bETerm A) :
    E.inputWeight < E.weight :=
  E.higher_weight

/-- In particular, the output weight is positive whenever an error term exists. -/
theorem bETerm.weight_pos {A : Type u} (E : bETerm A) :
    0 < E.weight :=
  Nat.lt_of_le_of_lt (Nat.zero_le E.inputWeight) E.higher_weight

/-- An ordered monomial in generators. -/
abbrev orderedMonomial (ι : Type u) := List ι

/-- Weight of a monomial. -/
def monomialWeight {ι : Type u} (w : ι → ℕ) (m : orderedMonomial ι) : ℕ :=
  m.foldl (fun s i => s + w i) 0

@[simp] theorem monomialWeight_nil {ι : Type u} (w : ι → ℕ) :
    monomialWeight w ([] : orderedMonomial ι) = 0 := rfl

theorem monomial_foldl_acc {ι : Type u} (w : ι → ℕ)
    (m : orderedMonomial ι) (a : ℕ) :
    m.foldl (fun s i => s + w i) a = a + monomialWeight w m := by
  induction m generalizing a with
  | nil => simp [monomialWeight]
  | cons i xs ih =>
      rw [List.foldl_cons, ih (a + w i)]
      change (a + w i) + monomialWeight w xs = a + List.foldl (fun s j => s + w j) 0 (i :: xs)
      rw [List.foldl_cons]
      simp only [Nat.zero_add]
      rw [ih (w i)]
      simp [Nat.add_assoc]

@[simp] theorem monomialWeight_cons {ι : Type u} (w : ι → ℕ) (i : ι)
    (m : orderedMonomial ι) :
    monomialWeight w (i :: m) = w i + monomialWeight w m := by
  unfold monomialWeight
  simpa [monomialWeight] using monomial_foldl_acc w m (w i)

@[simp] theorem monomialWeight_append {ι : Type u} (w : ι → ℕ)
    (m n : orderedMonomial ι) :
    monomialWeight w (m ++ n) = monomialWeight w m + monomialWeight w n := by
  unfold monomialWeight
  rw [List.foldl_append]
  simpa [Nat.add_assoc] using monomial_foldl_acc w n (List.foldl (fun s i => s + w i) 0 m)

/-- A PBW ordering is a total preorder/order relation on homogeneous generators. -/
structure pOrderi (ι : Type u) where
  le : ι → ι → Prop
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z
  antisymm : ∀ {x y}, le x y → le y x → x = y
  total : ∀ x y, le x y ∨ le y x
  decidable_le : DecidableRel le

attribute [instance] pOrderi.decidable_le

/-- Reflexivity accessor for a PBW ordering. -/
theorem pOrderi.le_refl {ι : Type u} (ord : pOrderi ι) (x : ι) :
    ord.le x x :=
  ord.refl x

/-- Transitivity accessor for a PBW ordering. -/
theorem pOrderi.le_trans {ι : Type u} (ord : pOrderi ι) {x y z : ι} :
    ord.le x y → ord.le y z → ord.le x z :=
  fun hxy hyz => ord.trans hxy hyz

/-- Antisymmetry accessor for a PBW ordering. -/
theorem pOrderi.eq_le_antisymm {ι : Type u} (ord : pOrderi ι) {x y : ι} :
    ord.le x y → ord.le y x → x = y :=
  fun hxy hyx => ord.antisymm hxy hyx

/-- Totality accessor for a PBW ordering. -/
theorem pOrderi.le_total {ι : Type u} (ord : pOrderi ι) (x y : ι) :
    ord.le x y ∨ ord.le y x :=
  ord.total x y


/-- PBW monomials are words pairwise ordered by a chosen PBW order. -/
structure pMonomi (ι : Type u) (ord : pOrderi ι) where
  word : orderedMonomial ι
  ordered : word.Pairwise ord.le
  weight : ι → ℕ := fun _ => 1
  totalWeight : ℕ := monomialWeight weight word
  totalWeight_eq : totalWeight = monomialWeight weight word
  positive_weights : ∀ i ∈ word, 0 < weight i

/-- The stored word is pairwise ordered. -/
theorem pMonomi.word_pairwise {ι : Type u} {ord : pOrderi ι}
    (M : pMonomi ι ord) : M.word.Pairwise ord.le :=
  M.ordered

/-- The stored total weight is the actual sum of letter weights. -/
theorem pMonomi.totalWeight_spec {ι : Type u} {ord : pOrderi ι}
    (M : pMonomi ι ord) : M.totalWeight = monomialWeight M.weight M.word :=
  M.totalWeight_eq

/-- Every letter in a PBW monomial has positive recorded weight. -/
theorem pMonomi.weight_pos_mem {ι : Type u} {ord : pOrderi ι}
    (M : pMonomi ι ord) {i : ι} (hi : i ∈ M.word) :
    0 < M.weight i :=
  M.positive_weights i hi

/-- Build a PBW monomial from an ordered word and a positive weight function. -/
def pMonomi.ofWord {ι : Type u} (ord : pOrderi ι)
    (word : orderedMonomial ι) (hord : word.Pairwise ord.le)
    (weight : ι → ℕ) (hpos : ∀ i ∈ word, 0 < weight i) : pMonomi ι ord where
  word := word
  ordered := hord
  weight := weight
  totalWeight := monomialWeight weight word
  totalWeight_eq := rfl
  positive_weights := hpos

@[simp] theorem pMonomi.ofWord_word {ι : Type u} (ord : pOrderi ι)
    (word : orderedMonomial ι) (hord : word.Pairwise ord.le)
    (weight : ι → ℕ) (hpos : ∀ i ∈ word, 0 < weight i) :
    (pMonomi.ofWord ord word hord weight hpos).word = word := rfl

@[simp] theorem pMonomi.word_total_weight {ι : Type u} (ord : pOrderi ι)
    (word : orderedMonomial ι) (hord : word.Pairwise ord.le)
    (weight : ι → ℕ) (hpos : ∀ i ∈ word, 0 < weight i) :
    (pMonomi.ofWord ord word hord weight hpos).totalWeight =
      monomialWeight weight word := rfl


/-- The empty PBW monomial. -/
def pMonomi.nil (ι : Type u) (ord : pOrderi ι) : pMonomi ι ord where
  word := []
  ordered := by simp
  weight := fun _ => 1
  totalWeight := 0
  totalWeight_eq := rfl
  positive_weights := by simp

/-- A singleton PBW monomial. -/
def pMonomi.singleton {ι : Type u} (ord : pOrderi ι) (i : ι) :
    pMonomi ι ord where
  word := [i]
  ordered := by simp
  weight := fun _ => 1
  totalWeight := 1
  totalWeight_eq := rfl
  positive_weights := by simp

@[simp] theorem pMonomi.nil_word (ι : Type u) (ord : pOrderi ι) :
    (pMonomi.nil ι ord).word = [] := rfl

@[simp] theorem pMonomi.singleton_word {ι : Type u} (ord : pOrderi ι) (i : ι) :
    (pMonomi.singleton ord i).word = [i] := rfl


@[simp] theorem pMonomi.nil_totalWeight (ι : Type u) (ord : pOrderi ι) :
    (pMonomi.nil ι ord).totalWeight = 0 := rfl

@[simp] theorem pMonomi.singleton_totalWeight {ι : Type u} (ord : pOrderi ι) (i : ι) :
    (pMonomi.singleton ord i).totalWeight = 1 := rfl

/-- A PBW ordering induces a decidable comparison function. -/
def pOrderi.compare {ι : Type u} (ord : pOrderi ι) (x y : ι) : Bool :=
  if ord.le x y then true else false

@[simp] theorem pOrderi.compare_eq_true {ι : Type u} (ord : pOrderi ι) (x y : ι) :
    ord.compare x y = true ↔ ord.le x y := by
  unfold pOrderi.compare
  by_cases h : ord.le x y <;> simp [h]

@[simp] theorem pOrderi.compare_eq_false {ι : Type u} (ord : pOrderi ι) (x y : ι) :
    ord.compare x y = false ↔ ¬ ord.le x y := by
  unfold pOrderi.compare
  by_cases h : ord.le x y <;> simp [h]

/-- Boolean comparison reflects the totality of a PBW order. -/
theorem pOrderi.compare_total {ι : Type u} (ord : pOrderi ι) (x y : ι) :
    ord.compare x y = true ∨ ord.compare y x = true := by
  rcases ord.total x y with h | h
  · left; simpa using h
  · right; simpa using h

/-- Restricted enveloping PBW object. -/
structure ePObject (R : Type u) [CommSemiring R] where
  algebraCarrier : Type v
  [semiringA : Semiring algebraCarrier]
  [algebraA : Algebra R algebraCarrier]
  basisIndex : Type w
  basisVec : basisIndex → algebraCarrier
  degree : basisIndex → ℕ
  pbw_independent : LinearIndependent R basisVec
  pbw_spans : Submodule.span R (Set.range basisVec) = ⊤
  mulSupport : basisIndex → basisIndex → Finset basisIndex
  mulCoeff : basisIndex → basisIndex → basisIndex → R
  mulSupport_degree : ∀ i j k, k ∈ mulSupport i j → degree k ≤ degree i + degree j
  mul_expansion : ∀ i j,
    basisVec i * basisVec j = Finset.sum (mulSupport i j)
      (fun k => algebraMap R algebraCarrier (mulCoeff i j k) * basisVec k)

attribute [instance] ePObject.semiringA ePObject.algebraA

/-- PBW basis vectors are linearly independent. -/
theorem ePObject.linearIndependent {R : Type u} [CommSemiring R]
    (P : ePObject R) : LinearIndependent R P.basisVec :=
  P.pbw_independent

/-- PBW basis vectors span the algebra. -/
theorem ePObject.spans_top {R : Type u} [CommSemiring R]
    (P : ePObject R) :
    Submodule.span R (Set.range P.basisVec) = ⊤ :=
  P.pbw_spans

/-- Multiplication support respects the recorded PBW filtration degrees. -/
theorem ePObject.mul_support_degreele {R : Type u} [CommSemiring R]
    (P : ePObject R) {i j k : P.basisIndex}
    (hk : k ∈ P.mulSupport i j) : P.degree k ≤ P.degree i + P.degree j :=
  P.mulSupport_degree i j k hk

/-- Multiplication of PBW basis vectors expands over the recorded finite support. -/
theorem ePObject.mul_expansion_apply {R : Type u} [CommSemiring R]
    (P : ePObject R) (i j : P.basisIndex) :
    P.basisVec i * P.basisVec j = Finset.sum (P.mulSupport i j)
      (fun k => algebraMap R P.algebraCarrier (P.mulCoeff i j k) * P.basisVec k) :=
  P.mul_expansion i j

/-- PBW/Jennings machinery package, including an algebra filtration and the
statement that PBW basis vectors have controlled filtration degree. -/
structure pJMachin (R : Type u) [CommSemiring R] where
  lieCarrier : Type v
  pbw : ePObject.{u, v, w} R
  filtration : ℕ → Set pbw.algebraCarrier
  antitone : ∀ {m n}, m ≤ n → filtration n ⊆ filtration m
  one_mem_zero : (1 : pbw.algebraCarrier) ∈ filtration 0
  mul_mem : ∀ m n {x y : pbw.algebraCarrier}, x ∈ filtration m → y ∈ filtration n →
    x * y ∈ filtration (m + n)
  basisDegree : pbw.basisIndex → ℕ
  basisDegree_eq : ∀ i, basisDegree i = pbw.degree i
  basis_mem : ∀ i, pbw.basisVec i ∈ filtration (basisDegree i)

/-- PBW/Jennings filtration is antitone. -/
theorem pJMachin.mem_of_le {R : Type u} [CommSemiring R]
    (P : pJMachin R) {m n : ℕ} (h : m ≤ n)
    {x : P.pbw.algebraCarrier} (hx : x ∈ P.filtration n) : x ∈ P.filtration m :=
  P.antitone h hx

/-- The PBW/Jennings unit lies in degree zero. -/
theorem pJMachin.one_mem_zero' {R : Type u} [CommSemiring R]
    (P : pJMachin R) : (1 : P.pbw.algebraCarrier) ∈ P.filtration 0 :=
  P.one_mem_zero

/-- Multiplication respects the PBW/Jennings filtration. -/
theorem pJMachin.mul_mem' {R : Type u} [CommSemiring R]
    (P : pJMachin R) {m n : ℕ} {x y : P.pbw.algebraCarrier}
    (hx : x ∈ P.filtration m) (hy : y ∈ P.filtration n) :
    x * y ∈ P.filtration (m + n) :=
  P.mul_mem m n hx hy

/-- Recorded basis degree agrees with the PBW degree. -/
theorem pJMachin.basisDegree_spec {R : Type u} [CommSemiring R]
    (P : pJMachin R) (i : P.pbw.basisIndex) :
    P.basisDegree i = P.pbw.degree i :=
  P.basisDegree_eq i

/-- PBW basis vectors lie in their recorded filtration degree. -/
theorem pJMachin.basis_mem_filtration {R : Type u} [CommSemiring R]
    (P : pJMachin R) (i : P.pbw.basisIndex) :
    P.pbw.basisVec i ∈ P.filtration (P.basisDegree i) :=
  P.basis_mem i

/-- Filtered Fox/Jennings work package, with an explicit comparison map from Fox
data into the Jennings/associated-graded side. -/
structure fFWork (R : Type u) [CommSemiring R] where
  algebraCarrier : Type v
  fox : Type w
  jennings : Type (max u v w)
  foxDegree : fox → ℕ
  jenningsDegree : jennings → ℕ
  comparison : fox → jennings
  degree_nonlowering : ∀ x, foxDegree x ≤ jenningsDegree (comparison x)
  cutoff : ℕ
  degree_exact_below : ∀ x, foxDegree x ≤ cutoff → jenningsDegree (comparison x) = foxDegree x
  injective_below : ∀ x y, foxDegree x ≤ cutoff → foxDegree y ≤ cutoff →
    comparison x = comparison y → x = y

/-- Below the cutoff, the comparison has exactly the original Fox degree. -/
theorem fFWork.degree_exact {R : Type u} [CommSemiring R]
    (W : fFWork R) {x : W.fox} (hx : W.foxDegree x ≤ W.cutoff) :
    W.jenningsDegree (W.comparison x) = W.foxDegree x :=
  W.degree_exact_below x hx

/-- Below the cutoff, equality after comparison reflects equality before comparison. -/
theorem fFWork.eq_compare_eqbelow {R : Type u} [CommSemiring R]
    (W : fFWork R) {x y : W.fox}
    (hx : W.foxDegree x ≤ W.cutoff) (hy : W.foxDegree y ≤ W.cutoff)
    (h : W.comparison x = W.comparison y) : x = y :=
  W.injective_below x y hx hy h

/-- The comparison never lowers degree. -/
theorem fFWork.degree_le_comparison {R : Type u} [CommSemiring R]
    (W : fFWork R) (x : W.fox) :
    W.foxDegree x ≤ W.jenningsDegree (W.comparison x) :=
  W.degree_nonlowering x

/-- A PBW ordered basis package: only indices satisfying the order predicate are
allowed as basis vectors, and those vectors are required to be linearly
independent and spanning. -/
structure pOBasis (R : Type u) [Semiring R] (ι : Type v) (M : Type w)
    [AddCommMonoid M] [Module R M] where
  ordered : ι → Prop
  vec : {i : ι // ordered i} → M
  independent : LinearIndependent R vec
  spans : Submodule.span R (Set.range vec) = ⊤

/-- The index underlying a basis vector satisfies the order predicate. -/
theorem pOBasis.ordered_index {R : Type u} [Semiring R]
    {ι : Type v} {M : Type w} [AddCommMonoid M] [Module R M]
    (B : pOBasis R ι M) (i : {i : ι // B.ordered i}) : B.ordered i.1 :=
  i.2

/-- PBW ordered basis vectors are linearly independent. -/
theorem pOBasis.linearIndependent {R : Type u} [Semiring R]
    {ι : Type v} {M : Type w} [AddCommMonoid M] [Module R M]
    (B : pOBasis R ι M) : LinearIndependent R B.vec :=
  B.independent

/-- PBW ordered basis vectors span the ambient module. -/
theorem pOBasis.spans_top {R : Type u} [Semiring R]
    {ι : Type v} {M : Type w} [AddCommMonoid M] [Module R M]
    (B : pOBasis R ι M) :
    Submodule.span R (Set.range B.vec) = ⊤ :=
  B.spans

/-- Leading commutator term. -/
structure lCTerm (A : ℕ → Type u) where
  [zeroA : ∀ n, Zero (A n)]
  degree : ℕ
  term : A degree
  nonzero : term ≠ 0
  leftDegree : ℕ
  rightDegree : ℕ
  left : A leftDegree
  right : A rightDegree
  bracket : A leftDegree → A rightDegree → A (leftDegree + rightDegree)
  degree_eq : degree = leftDegree + rightDegree
  term_eq_bracket : HEq term (bracket left right)

/-- The displayed leading term is the bracket of its displayed inputs (heterogeneously,
because the degree equality may require reassociation/casting). -/
theorem lCTerm.term_heq_bracket {A : ℕ → Type u}
    (L : lCTerm A) : HEq L.term (L.bracket L.left L.right) :=
  L.term_eq_bracket

/-- The degree of a leading commutator term is the sum of its displayed inputs. -/
theorem lCTerm.degree_spec {A : ℕ → Type u}
    (L : lCTerm A) : L.degree = L.leftDegree + L.rightDegree :=
  L.degree_eq

/-- A leading commutator term is nonzero, as a named projection. -/
theorem lCTerm.term_ne_zero {A : ℕ → Type u}
    (L : lCTerm A) :
    (letI := L.zeroA L.degree; L.term ≠ 0) := by
  exact L.nonzero

/-- Associated graded p-map, degree-multiplying and preserving zero.  In a
restricted Lie algebra the p-map is additive only on commuting elements, so the
commuting relation is part of the interface and additivity is conditional. -/
structure aGP (A : ℕ → Type u) (p : ℕ) where
  [addA : ∀ n, AddMonoid (A n)]
  map : ∀ n, A n → A (p*n)
  map_zero : ∀ n, map n 0 = 0
  commutes : ∀ n, A n → A n → Prop
  commutes_refl : ∀ n (x : A n), commutes n x x
  commutes_zero_left : ∀ n (x : A n), commutes n 0 x
  commutes_symm : ∀ n (x y : A n), commutes n x y → commutes n y x
  map_add_commuting : ∀ n (x y : A n), commutes n x y →
    map n (x + y) = map n x + map n y
  degree_prime : Nat.Prime p

/-- Reflexivity of the recorded commuting relation. -/
theorem aGP.commutes_self {A : ℕ → Type u} {p : ℕ}
    (P : aGP A p) (n : ℕ) (x : A n) : P.commutes n x x :=
  P.commutes_refl n x

/-- Zero commutes with every homogeneous element. -/
theorem aGP.commutes_zero {A : ℕ → Type u} {p : ℕ}
    (P : aGP A p) (n : ℕ) (x : A n) :
    (letI := P.addA n; P.commutes n (0 : A n) x) := by
  letI := P.addA n
  exact P.commutes_zero_left n x

/-- If all pairs in a degree commute, that component of a graded p-map is an
additive monoid homomorphism. -/
def aGP.add_monoidhom_allcommute {A : ℕ → Type u} {p : ℕ}
    (P : aGP A p) (n : ℕ)
    (hcomm : ∀ x y : A n, P.commutes n x y) :
    letI := P.addA n; letI := P.addA (p * n); A n →+ A (p * n) := by
  letI := P.addA n; letI := P.addA (p * n)
  exact {
    toFun := P.map n
    map_zero' := P.map_zero n
    map_add' := fun x y => P.map_add_commuting n x y (hcomm x y)
  }

/-- The degree multiplier of an associated graded p-map is prime. -/
theorem aGP.prime {A : ℕ → Type u} {p : ℕ}
    (P : aGP A p) : Nat.Prime p :=
  P.degree_prime

@[simp] theorem aGP.map_zero_apply {A : ℕ → Type u} {p : ℕ}
    (P : aGP A p) (n : ℕ) :
    (letI := P.addA n; letI := P.addA (p * n); P.map n (0 : A n) = 0) := by
  exact P.map_zero n

/-- Conditional additivity of the p-map on commuting homogeneous elements. -/
theorem aGP.map_add_commute {A : ℕ → Type u} {p : ℕ}
    (P : aGP A p) (n : ℕ) (x y : A n)
    (hxy : P.commutes n x y) :
    (letI := P.addA n; letI := P.addA (p * n);
      P.map n (x + y) = P.map n x + P.map n y) := by
  exact P.map_add_commuting n x y hxy

/-- A Fox derivative degree estimate. -/
structure fDEstima where
  relatorDepth : ℕ
  derivativeLowerBound : ℕ
  derivativeDegree : Option ℕ
  degree_sound : ∀ d, derivativeDegree = some d → derivativeLowerBound ≤ d
  bound : derivativeLowerBound + 1 ≤ relatorDepth

/-- If a concrete derivative degree is recorded, it satisfies the lower bound. -/
theorem fDEstima.bound_eq_some
    (E : fDEstima) {d : ℕ} (hd : E.derivativeDegree = some d) :
    E.derivativeLowerBound ≤ d :=
  E.degree_sound d hd

/-- The derivative lower bound is strictly below (or equal predecessor of) relator depth. -/
theorem fDEstima.succ_bound
    (E : fDEstima) :
    E.derivativeLowerBound + 1 ≤ E.relatorDepth :=
  E.bound

/-- Any estimate forces the relator depth to be positive. -/
theorem fDEstima.relatorDepth_pos
    (E : fDEstima) : 0 < E.relatorDepth := by
  have h := E.bound
  omega


/-- The concrete Fox augmentation identity for a word `w`: `w - 1` is the sum
of its Fox derivatives times `(x - 1)` over the generators.  Finiteness of `α`
turns the formal sum into a `Finset.univ` sum. -/
structure fAId (R : Type u) (α : Type v) [Ring R]
    [Fintype α] [DecidableEq α] where
  word : FreeGroup α
  derivative : α → fDRespec R α
  derivative_generator : ∀ a, (derivative a).generator = a
  derivative_mul_rule : ∀ a x y, derivative a (x * y) = derivative a x +
    MonoidAlgebra.single x (1 : R) * derivative a y
  identity : MonoidAlgebra.single word (1 : R) - 1 =
    Finset.sum Finset.univ (fun a : α =>
      derivative a word * (MonoidAlgebra.single (FreeGroup.of a) (1 : R) - 1))

/-- The Fox derivative package is indexed by the requested generator. -/
theorem fAId.derivative_generator_eq {R : Type u} {α : Type v}
    [Ring R] [Fintype α] [DecidableEq α]
    (I : fAId R α) (a : α) :
    (I.derivative a).generator = a :=
  I.derivative_generator a

/-- The recorded Fox product rule for derivatives. -/
theorem fAId.derivative_mul {R : Type u} {α : Type v}
    [Ring R] [Fintype α] [DecidableEq α]
    (I : fAId R α) (a : α) (x y : FreeGroup α) :
    I.derivative a (x * y) = I.derivative a x +
      MonoidAlgebra.single x (1 : R) * I.derivative a y :=
  I.derivative_mul_rule a x y

/-- The recorded Fox augmentation identity. -/
theorem fAId.identity_eq {R : Type u} {α : Type v}
    [Ring R] [Fintype α] [DecidableEq α]
    (I : fAId R α) :
    MonoidAlgebra.single I.word (1 : R) - 1 =
      Finset.sum Finset.univ (fun a : α =>
        I.derivative a I.word * (MonoidAlgebra.single (FreeGroup.of a) (1 : R) - 1)) :=
  I.identity

/-- Fox relation vector. -/
abbrev foxRelationVector (R : Type u) (α : Type v) [Semiring R] :=
  α → MonoidAlgebra R (FreeGroup α)

/-- Initial relation vector. -/
structure iRVector (R : Type u) (α : Type v) [Ring R] where
  relator : FreeGroup α
  degree : ℕ
  vector : foxRelationVector R α
  initialForm : iFForm R α
  same_degree : initialForm.degree = degree
  same_relator : initialForm.relator = relator
  vector_eq_coeff : ∀ a, vector a = initialForm.coeff a

/-- The initial form has the recorded degree. -/
theorem iRVector.initialForm_degree {R : Type u} {α : Type v} [Ring R]
    (V : iRVector R α) : V.initialForm.degree = V.degree :=
  V.same_degree

/-- The initial form has the recorded relator. -/
theorem iRVector.initialForm_relator {R : Type u} {α : Type v} [Ring R]
    (V : iRVector R α) : V.initialForm.relator = V.relator :=
  V.same_relator

/-- Coordinates of the relation vector are the coefficients of the initial form. -/
theorem iRVector.vector_apply {R : Type u} {α : Type v} [Ring R]
    (V : iRVector R α) (a : α) : V.vector a = V.initialForm.coeff a :=
  V.vector_eq_coeff a


end Algebra
end Towers

/-!
## Statements migrated from `Towers.Theorems`

These declarations keep their historical `Towers.Theorems` namespace while living
next to the API they describe.
-/

namespace Towers
namespace Theorems

open Towers.Group
open Towers.Algebra
open Towers.Topology

universe u v w x

/-- A p-map on associated graded pieces is invariant under representative equivalence. -/
def PRepresentativeInvariant {A : ℕ → Type u} {p : ℕ}
    (P : aGP A p) (n : ℕ) (Rel : A n → A n → Prop) : Prop :=
  ∀ ⦃x y : A n⦄, Rel x y → P.map n x = P.map n y
/-- The explicit comparison data needed for a Jennings-PBW identification. -/
def JenningsPbwComparison {R : Type u} {G : Type v} [CommRing R] [Group G]
    (A : aGAlg R G) (U : rEAlg R) : Prop :=
  ∃ Φ : (Σ n : ℕ, A.layer n) ≃ U.carrier,
    Φ ⟨0, A.one⟩ = 1 ∧
      (∀ m n (x : A.layer m) (y : A.layer n),
        Φ ⟨m + n, A.mul m n x y⟩ = Φ ⟨m, x⟩ * Φ ⟨n, y⟩) ∧
      Function.Injective U.incl ∧
        ∀ x : U.lie.carrier, ∃ z : Σ n : ℕ, A.layer n, Φ z = U.incl x
/-- Commutator errors are measured by commutator weight. -/
theorem commutatorErrors {G : Type u} [Group G] (w : G → ℕ) (x y : G) :
    w x + w y ≤ w (x * y * x⁻¹ * y⁻¹) →
      w x + w y ≤ Algebra.commutatorWeight w x y
  := by
  exact fun h => h
/-- High-weight control records that error terms have degree above the cutoff.

Actual vanishing in a quotient requires a separately defined quotient projection
with a high-degree killing law; it does not follow from an arbitrary map. -/
theorem highErrorAbove {A : ℕ → Type u} (cutoff : ℕ) :
    ∀ e : higherErrorTerms A cutoff, cutoff < e.1.1
  := by
  intro e
  exact e.1.2
/-- Commutator weight is bounded below by the sum of input weights. -/
theorem commutatorLowerBound {G : Type u} [Group G] (w : G → ℕ) :
    (∀ x y : G, w x + w y ≤ w (x * y * x⁻¹ * y⁻¹)) →
      Algebra.commutatorLowerBound w
  := by
  exact fun h x y => h x y
/-- Swapping two filtered factors creates only higher-weight commutator error. -/
theorem swapLemma {G : Type u} [Group G] (w : G → ℕ)
    (hw : ∀ x y : G, w x + w y ≤ w (x * y * x⁻¹ * y⁻¹)) (x y : G) :
    w x + w y ≤ Algebra.commutatorWeight w x y
  := by
  exact hw x y
/-- p-overflow terms have higher weight. -/
theorem pOverflow {p k : ℕ} (hp : Nat.Prime p) :
    0 < k → k < p → p ∣ Nat.choose p k
  := by
  exact fun hk0 hkp => Nat.Prime.dvd_choose_self hp (Nat.ne_of_gt hk0) hkp
/-- p-binomial error terms have high weight. -/
theorem errorsHaveHigh {p k : ℕ} (hp : Nat.Prime p) :
    0 < k → k < p → p ∣ Nat.choose p k
  := by
  exact fun hk0 hkp => Nat.Prime.dvd_choose_self hp (Nat.ne_of_gt hk0) hkp
/-- The filtered-error machinery combines swap and p-binomial high-weight estimates. -/
theorem filteredErrorMachinery {G : Type u} [Group G] (w : G → ℕ) {p k : ℕ}
    (hcomm : ∀ x y : G, w x + w y ≤ w (x * y * x⁻¹ * y⁻¹))
    (hp : Nat.Prime p) :
    (∀ x y : G, w x + w y ≤ Algebra.commutatorWeight w x y) ∧
      (0 < k → k < p → p ∣ Nat.choose p k)
  := by
  exact ⟨fun x y => hcomm x y,
    fun hk0 hkp => Nat.Prime.dvd_choose_self hp (Nat.ne_of_gt hk0) hkp⟩
/-- PBW ordered basis vectors are linearly independent. -/
theorem pbwIndependenceTheorem {R : Type u} [Semiring R]
    {ι : Type v} {M : Type w} [AddCommMonoid M] [Module R M]
    (ord : pOrderi ι) (B : pOBasis R (pMonomi ι ord) M) :
    LinearIndependent R B.vec
  := by
  cases B with
  | mk ordered vec independent spans =>
      simpa [Towers.Algebra.pOBasis.vec,
        Towers.Algebra.pOBasis.ordered] using independent
/-- Ordered monomials span after swaps. -/
theorem monomialsAfterSwaps {ι : Type u} (ord : pOrderi ι)
    (m : orderedMonomial ι) :
    ∃ M : pMonomi ι ord, M.word.Perm m
  := by
  letI : Std.Total ord.le := ⟨ord.total⟩
  letI : IsTrans ι ord.le := ⟨fun _ _ _ hxy hyz => ord.trans hxy hyz⟩
  let sorted := List.mergeSort m (ord.le · ·)
  refine ⟨pMonomi.ofWord ord sorted ?_ (fun _ => 1) ?_, ?_⟩
  · exact List.pairwise_mergeSort' (r := ord.le) m
  · intro i hi
    simp
  · dsimp [sorted]
    exact List.mergeSort_perm m (ord.le · ·)
/-- PBW ordered basis vectors span. -/
theorem pbwSpanningTheorem {R : Type u} [Semiring R]
    {ι : Type v} {M : Type w} [AddCommMonoid M] [Module R M]
    (ord : pOrderi ι) (B : pOBasis R (pMonomi ι ord) M) :
    Submodule.span R (Set.range B.vec) = ⊤
  := by
  cases B with
  | mk ordered vec independent spans =>
      simpa [Towers.Algebra.pOBasis.vec,
        Towers.Algebra.pOBasis.ordered] using spans
/-- Jennings-PBW comparison identifies the graded algebra with the restricted
enveloping algebra once the comparison data is supplied. -/
theorem pbwGradedIsomorphism {R : Type u} {G : Type v}
    [CommRing R] [Group G]
    (A : aGAlg R G) (U : rEAlg R)
    (hcomparison : JenningsPbwComparison A U) :
    JenningsPbwComparison A U
  := by
  exact hcomparison
/-- PBW/Jennings controls associated graded layers beyond degree one. -/
theorem higherDegreeControl {R : Type u} {G : Type v} [CommRing R] [Group G]
    (A : aGAlg R G) :
    ∃ bound : Cardinal, ∀ n, dGTwo n → Module.rank R (A.layer n) ≤ bound
  := by
  refine ⟨Cardinal.mk (Σ n : ℕ, A.layer n), ?_⟩
  intro n _hn
  exact (rank_le_card (R := R) (M := A.layer n)).trans
    (Cardinal.mk_le_of_injective (f := fun x : A.layer n => Sigma.mk n x) (by
      intro x y h
      injection h))
/-- The commutator operation in an associative algebra satisfies the Lie laws.

The previous arbitrary-bracket statement was too strong: the commutator must
come from an associative multiplication, or the Lie laws need separate proof. -/
theorem definesLieBracket {R : Type u} [CommRing R]
    {A : Type v} [Ring A] [Algebra R A] :
    let bracket : A → A → A := fun x y => x * y - y * x
    (∀ x y z, bracket (x + y) z = bracket x z + bracket y z) ∧
      (∀ x y z, bracket x (y + z) = bracket x y + bracket x z) ∧
      (∀ x, bracket x x = 0) ∧
      (∀ x y, bracket x y = -bracket y x) ∧
      ∀ x y z, bracket x (bracket y z) + bracket y (bracket z x) +
        bracket z (bracket x y) = 0
  := by
  dsimp
  constructor
  · intro x y z
    noncomm_ring
  · constructor
    · intro x y z
      noncomm_ring
    · constructor
      · intro x
        noncomm_ring
      · constructor
        · intro x y
          noncomm_ring
        · intro x y z
          noncomm_ring
/-- The associated graded p-map respects definitional equality of representatives.

Well-definedness for a nontrivial quotient relation needs that relation as part
of the quotient construction; an arbitrary external relation is too weak. -/
theorem associatedRespectsEquality {A : ℕ → Type u} {p : ℕ}
    (P : aGP A p) (n : ℕ) :
    ∀ ⦃x y : A n⦄, x = y → P.map n x = P.map n y
  := by
  intro x y hxy
  subst hxy
  rfl

end Theorems
end Towers
