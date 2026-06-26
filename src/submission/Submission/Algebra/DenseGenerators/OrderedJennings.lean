import Mathlib
import Submission.Algebra.DenseGenerators.DimensionSubgroup


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

/-- Ordered product over `Fin r`, multiplying factors from left to right. -/
def finOrderedProd {M : Type*} [Monoid M] :
    (r : ℕ) → (Fin r → M) → M
  | 0, _ => 1
  | r + 1, f =>
      finOrderedProd r (fun i : Fin r => f i.castSucc) *
        f (Fin.last r)

/-- An ordered product whose factors are all `1` is `1`. -/
lemma fin_ordered_forall
    {M : Type*} [Monoid M]
    (r : ℕ)
    (f : Fin r → M)
    (hf : ∀ i, f i = 1) :
    finOrderedProd r f = 1 := by
  induction r with
  | zero =>
      rfl
  | succ r ih =>
      have hprefix :
          finOrderedProd r (fun i : Fin r => f i.castSucc) = 1 :=
        ih (fun i : Fin r => f i.castSucc) (fun i => hf i.castSucc)
      simp [finOrderedProd, hprefix, hf (Fin.last r)]

/-- Ordered products distribute over finite sums in each factor. -/
lemma fin_prod_sum
    {A κ : Type*} [Semiring A] [Fintype κ]
    (r : ℕ)
    (f : Fin r → κ → A) :
    finOrderedProd r (fun i => ∑ a : κ, f i a) =
      ∑ e : Fin r → κ, finOrderedProd r (fun i => f i (e i)) := by
  induction r with
  | zero =>
      simp [finOrderedProd]
  | succ r ih =>
      rw [finOrderedProd, ih]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [← Fintype.sum_prod_type']
      apply Fintype.sum_equiv
        ((Equiv.prodComm (Fin r → κ) κ).trans
          (Fin.snocEquiv (fun _ : Fin (r + 1) => κ)))
      intro e
      simp [finOrderedProd]

/-- Scalars can be pulled out of an ordered product. -/
lemma fin_prod_smul
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (r : ℕ)
    (c : Fin r → R)
    (f : Fin r → A) :
    finOrderedProd r (fun i => c i • f i) =
      (∏ i : Fin r, c i) • finOrderedProd r f := by
  induction r with
  | zero =>
      simp [finOrderedProd]
  | succ r ih =>
      rw [finOrderedProd, ih, Fin.prod_univ_castSucc, finOrderedProd]
      simp [smul_smul, mul_comm]

/-- Ordered products of finite linear combinations expand as a sum indexed by exponent
vectors. -/
lemma fin_sum_smul
    {R A κ : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Fintype κ]
    (r : ℕ)
    (c : Fin r → κ → R)
    (f : Fin r → κ → A) :
    finOrderedProd r (fun i => ∑ a : κ, c i a • f i a) =
      ∑ e : Fin r → κ,
        (∏ i : Fin r, c i (e i)) • finOrderedProd r (fun i => f i (e i)) := by
  rw [fin_prod_sum]
  apply Finset.sum_congr rfl
  intro e _he
  exact fin_prod_smul r (fun i => c i (e i)) (fun i => f i (e i))

/-- Binomial expansion of `(1 + Y)^e`, padded with zero coefficients up to `p - 1`. -/
lemma sum_choose_smul
    {p : ℕ} [Fact p.Prime]
    {A : Type*} [Semiring A] [Algebra (ZMod p) A]
    (Y : A)
    (e : Fin p) :
    (1 + Y) ^ e.val =
      ∑ a : Fin p, ((Nat.choose e.val a.val : ℕ) : ZMod p) • Y ^ a.val := by
  have hsubset :
      Finset.range (e.val + 1) ⊆ Finset.range p :=
    Finset.range_mono (Nat.succ_le_of_lt e.isLt)
  have hsum :
      ∑ a ∈ Finset.range (e.val + 1),
          ((Nat.choose e.val a : ℕ) : ZMod p) • Y ^ a =
        ∑ a ∈ Finset.range p,
          ((Nat.choose e.val a : ℕ) : ZMod p) • Y ^ a := by
    apply Finset.sum_subset hsubset
    intro a _ha hnot
    have hea : e.val < a := by
      simpa [Finset.mem_range] using hnot
    simp [Nat.choose_eq_zero_of_lt hea]
  calc
    (1 + Y) ^ e.val = (Y + 1) ^ e.val := by rw [add_comm]
    _ =
        ∑ a ∈ Finset.range (e.val + 1),
          ((Nat.choose e.val a : ℕ) : ZMod p) • Y ^ a := by
      rw [Commute.add_pow (Commute.one_right Y)]
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [one_pow, mul_one]
      rw [Algebra.smul_def, Algebra.commutes]
      simp
    _ =
        ∑ a ∈ Finset.range p,
          ((Nat.choose e.val a : ℕ) : ZMod p) • Y ^ a := hsum
    _ =
        ∑ a : Fin p,
          ((Nat.choose e.val a.val : ℕ) : ZMod p) • Y ^ a.val := by
      exact
        (Fin.sum_univ_eq_sum_range
          (fun a : ℕ => ((Nat.choose e.val a : ℕ) : ZMod p) • Y ^ a)
          p).symm

/-- The ordered group word with natural exponents. -/
def orderedWord
    {Q : Type u} [Monoid Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → ℕ) :
    Q :=
  finOrderedProd r (fun i => x i ^ e i)

/-- The ordered group word with exponents reduced to the range `0, ..., p - 1`. -/
def orderedWordFin
    {p r : ℕ}
    {Q : Type u} [Monoid Q]
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    Q :=
  orderedWord x (fun i => (e i).val)

/-- Canonical group-algebra basis elements commute with ordered products. -/
lemma algebra_fin_prod
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (f : Fin r → Q) :
    denseGeneratorsElement p Q (finOrderedProd r f) =
      finOrderedProd r
        (fun i => denseGeneratorsElement p Q (f i)) := by
  induction r with
  | zero =>
      simp [finOrderedProd, dense_canonical_element]
  | succ r ih =>
      simp [finOrderedProd, dense_element_mul, ih]

/-- The canonical element of an ordered word is the ordered product of `1 + ([x_i] - 1)`. -/
lemma algebra_fin_sub
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    denseGeneratorsElement p Q (orderedWordFin x e) =
      finOrderedProd r
        (fun i => (1 + groupAlgebraSub p Q (x i)) ^ (e i).val) := by
  unfold orderedWordFin orderedWord
  rw [algebra_fin_prod]
  apply congrArg
  funext i
  simp [groupAlgebraSub]

/-- Expand an exponent vector into the ordered list of repeated indices that realizes the same
ordered group word. -/
def orderedExponentList {p : ℕ} :
    (r : ℕ) → (Fin r → Fin p) → List (Fin r)
  | 0, _ => []
  | r + 1, e =>
      (orderedExponentList r (fun i : Fin r => e i.castSucc)).map Fin.castSucc ++
        List.replicate (e (Fin.last r)).val (Fin.last r)

/-- The expanded exponent list evaluates to the same ordered group word. -/
lemma ordered_exponent_fin
    {p r : ℕ}
    {Q : Type u} [Monoid Q]
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    ((orderedExponentList r e).map x).prod = orderedWordFin x e := by
  induction r with
  | zero =>
      simp [orderedExponentList, orderedWordFin, orderedWord, finOrderedProd]
  | succ r ih =>
      have hprefix :=
        ih (fun i : Fin r => x i.castSucc) (fun i : Fin r => e i.castSucc)
      simp [
        orderedExponentList,
        orderedWordFin,
        orderedWord,
        finOrderedProd,
        hprefix,
        List.map_map,
        Function.comp_def
      ]

/-- If every nonzero exponent has weight at least `t`, then every index appearing in the
expanded exponent list has weight at least `t`. -/
lemma ordered_exponent_forall
    {p : ℕ} :
    ∀ (r : ℕ) (wt : Fin r → ℕ) (e : Fin r → Fin p) {t : ℕ},
      (∀ i, (e i).val ≠ 0 → t ≤ wt i) →
        ∀ i, i ∈ orderedExponentList r e → t ≤ wt i
  | 0, _wt, _e, _t, _he => by
      intro i hi
      simp [orderedExponentList] at hi
  | r + 1, wt, e, t, he => by
      intro i hi
      have hi' :
          (∃ j : Fin r,
              j ∈ orderedExponentList r (fun j : Fin r => e j.castSucc) ∧
                j.castSucc = i) ∨
            (e (Fin.last r)).val ≠ 0 ∧ i = Fin.last r := by
        simpa [orderedExponentList] using hi
      rcases hi' with ⟨j, hj, hji⟩ | ⟨hval_ne, hlast⟩
      · cases hji
        exact
          ordered_exponent_forall
            r
            (fun j : Fin r => wt j.castSucc)
            (fun j : Fin r => e j.castSucc)
            (fun j hjne => he j.castSucc hjne)
            j
            hj
      · cases hlast
        exact he (Fin.last r) hval_ne

/-- The ordered Jennings monomial attached to exponent vector `e`. -/
def jenningsMonomialFin
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    denseGroupAlgebra p Q :=
  finOrderedProd r
    (fun i =>
      groupAlgebraSub p Q (x i) ^ (e i).val)

/-- The all-zero Jennings exponent gives the constant monomial. -/
@[simp]
lemma jennings_monomial_zero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q) :
    jenningsMonomialFin p Q x (0 : Fin r → Fin p) = 1 := by
  unfold jenningsMonomialFin
  apply fin_ordered_forall
  intro i
  simp

/-- The Jennings weight of an exponent vector. -/
def expWeight
    {p r : ℕ}
    (wt : Fin r → ℕ)
    (e : Fin r → Fin p) :
    ℕ :=
  ∑ i : Fin r, (e i).val * wt i

/-- The weight sum of the expanded ordered exponent list is the Jennings weight of the exponent
vector. -/
lemma ordered_exponent_exp
    {p : ℕ} :
    ∀ (r : ℕ) (wt : Fin r → ℕ) (e : Fin r → Fin p),
      ((orderedExponentList r e).map wt).sum =
        expWeight (p := p) (r := r) wt e
  | 0, _wt, _e => by
      simp [orderedExponentList, expWeight]
  | r + 1, wt, e => by
      have ih :=
        ordered_exponent_exp
          (p := p) r
          (fun i : Fin r => wt i.castSucc)
          (fun i : Fin r => e i.castSucc)
      rw [expWeight, Fin.sum_univ_castSucc]
      simp only [
        orderedExponentList,
        List.map_append,
        List.sum_append,
        List.map_map,
        List.map_replicate,
        List.sum_replicate,
      ]
      have ih' :
          (List.map (wt ∘ Fin.castSucc)
              (orderedExponentList r (fun i : Fin r => e i.castSucc))).sum =
            ∑ i : Fin r, (e i.castSucc).val * wt i.castSucc := by
        simpa only [Function.comp_apply, expWeight] using ih
      rw [ih']
      simp

/-- Each index occurs in the ordered exponent list exactly as many times as its exponent. -/
lemma ordered_exponent_count
    {p : ℕ} :
    ∀ (r : ℕ) (e : Fin r → Fin p) (i : Fin r),
      (orderedExponentList r e).count i = (e i).val
  | 0, _e, i => Fin.elim0 i
  | r + 1, e, i => by
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · let L : List (Fin r) :=
          orderedExponentList r (fun j : Fin r => e j.castSucc)
        have hmap :
            (L.map Fin.castSucc).count j.castSucc = L.count j := by
          simpa using
            (List.count_map_of_injective L Fin.castSucc
              (Fin.castSucc_injective r) j)
        have hrep :
            (List.replicate (e (Fin.last r)).val (Fin.last r)).count
                j.castSucc = 0 := by
          rw [List.count_replicate]
          rw [show (Fin.last r == j.castSucc) = false by
            exact beq_false_of_ne (Fin.castSucc_ne_last j).symm]
          simp
        simp [
          orderedExponentList,
          L,
          hmap,
          hrep,
          ordered_exponent_count (p := p) r
            (fun j : Fin r => e j.castSucc) j
        ]
      · have hnot :
          Fin.last r ∉
            (orderedExponentList r (fun j : Fin r => e j.castSucc)).map
              Fin.castSucc := by
          intro hmem
          rcases List.mem_map.mp hmem with ⟨j, _hj_mem, hj⟩
          exact Fin.castSucc_ne_last j hj
        simp [
          orderedExponentList,
          List.count_eq_zero_of_not_mem hnot
        ]

/-- Ordered representatives for the surviving Zassenhaus layers below a killed level `m`.

This is the group-theoretic normal-form data that should later be constructed from the finite
Zassenhaus layers. The PBW/Jennings monomial basis will be indexed by the exponent vectors in
`Fin r → Fin p`. -/
structure OZReps
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q]
    (m : ℕ) where
  r : ℕ
  gen : Fin r → Q
  weight : Fin r → ℕ
  weight_pos : ∀ i, 0 < weight i
  weight_lt : ∀ i, weight i < m
  gen_mem : ∀ i, gen i ∈ zassenhausFiltration p Q (weight i)
  wordEquiv : (Fin r → Fin p) ≃ Q
  wordEquiv_apply :
    ∀ e, wordEquiv e = orderedWordFin gen e
  mem_iff_below :
    ∀ {t : ℕ} (_ht : t ≤ m) (e : Fin r → Fin p),
      wordEquiv e ∈ zassenhausFiltration p Q t ↔
        ∀ i, weight i < t → e i = 0

/-- The exponent vector which is `1` at `i` and `0` elsewhere. -/
def jenningsExpFin
    {p r : ℕ} [Fact p.Prime]
    (i : Fin r) :
    Fin r → Fin p :=
  fun j =>
    if j = i then
      ⟨1, (Fact.out : Nat.Prime p).one_lt⟩
    else
      ⟨0, (Fact.out : Nat.Prime p).pos⟩

@[simp]
lemma jennings_exp_self
    {p r : ℕ} [Fact p.Prime]
    (i : Fin r) :
    jenningsExpFin (p := p) i i =
      ⟨1, (Fact.out : Nat.Prime p).one_lt⟩ := by
  simp [jenningsExpFin]

@[simp]
lemma jennings_exp_ne
    {p r : ℕ} [Fact p.Prime]
    {i j : Fin r}
    (h : j ≠ i) :
    jenningsExpFin (p := p) i j =
      ⟨0, (Fact.out : Nat.Prime p).pos⟩ := by
  simp [jenningsExpFin, h]

@[simp]
lemma exp_single_fin
    {p r : ℕ} [Fact p.Prime]
    (wt : Fin r → ℕ)
    (i : Fin r) :
    expWeight (p := p) (r := r) wt (jenningsExpFin (p := p) i) = wt i := by
  classical
  rw [expWeight]
  rw [Finset.sum_eq_single i]
  · simp [jenningsExpFin]
  · intro j _hj hji
    simp [jenningsExpFin, hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The coefficient of the Jennings monomial with exponent `a` in the formal binomial expansion
of the ordered word with exponent `e`. -/
def jenningsExpansionCoeff
    {p r : ℕ}
    (e a : Fin r → Fin p) :
    ZMod p :=
  ∏ i : Fin r, ((Nat.choose (e i).val (a i).val : ℕ) : ZMod p)

@[simp]
lemma jennings_expansion_coeff
    {p r : ℕ} [Fact p.Prime]
    (e : Fin r → Fin p) :
    jenningsExpansionCoeff (p := p) e (0 : Fin r → Fin p) = 1 := by
  classical
  simp [jenningsExpansionCoeff]

@[simp]
lemma jennings_single_exp
    {p r : ℕ} [Fact p.Prime]
    (i : Fin r) :
    jenningsExpFin (p := p) i ≠ (0 : Fin r → Fin p) := by
  intro h
  have hval : (1 : ℕ) = 0 := by
    have h' := congrArg Fin.val (congrFun h i)
    simp [jenningsExpFin] at h'
  exact Nat.succ_ne_zero 0 hval

@[simp]
lemma ordered_jennings_single
    {p r : ℕ} [Fact p.Prime]
    (e : Fin r → Fin p)
    (i : Fin r) :
    jenningsExpansionCoeff (p := p) e
        (jenningsExpFin (p := p) i)
      =
        ((e i).val : ZMod p) := by
  classical
  rw [jenningsExpansionCoeff]
  rw [Finset.prod_eq_single i]
  · simp [jenningsExpFin]
  · intro j _hj hji
    simp [jenningsExpFin, hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- If one coordinate of `a` is larger than the corresponding coordinate of `e`, then the
formal ordered-Jennings expansion coefficient vanishes. -/
lemma jennings_coeff_coord
    {p r : ℕ}
    (e a : Fin r → Fin p)
    {i : Fin r}
    (hi : (e i).val < (a i).val) :
    jenningsExpansionCoeff (p := p) e a = 0 := by
  rw [jenningsExpansionCoeff]
  exact
    Finset.prod_eq_zero (Finset.mem_univ i)
      (by
        have hchoose :
            Nat.choose (e i).val (a i).val = 0 :=
          Nat.choose_eq_zero_of_lt hi
        simp [hchoose])

/-- A nonzero ordered-Jennings expansion coefficient is coordinatewise supported below the input
normal-form exponent. -/
lemma jennings_expansion_coord
    {p r : ℕ}
    {e a : Fin r → Fin p}
    (hcoeff : jenningsExpansionCoeff (p := p) e a ≠ 0)
    (i : Fin r) :
    (a i).val ≤ (e i).val := by
  by_contra hle
  exact
    hcoeff
      (jennings_coeff_coord
        (p := p) e a (Nat.lt_of_not_ge hle))

/-- The canonical element of an ordered word expands in the ordered Jennings monomials with
the expected product of binomial coefficients. -/
lemma algebra_jennings_monomial
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    denseGeneratorsElement p Q (orderedWordFin x e) =
      ∑ a : Fin r → Fin p,
        jenningsExpansionCoeff e a • jenningsMonomialFin p Q x a := by
  rw [algebra_fin_sub]
  simp_rw [sum_choose_smul]
  rw [fin_sum_smul]
  rfl

/-- The coefficient function for expanding `[orderedWord e] - 1` rather than `[orderedWord e]`.
The constant term is killed; all nonzero Jennings exponents keep their binomial coefficient. -/
noncomputable def orderedJenningsCoeff
    {p r : ℕ} [Fact p.Prime]
    (e a : Fin r → Fin p) :
    ZMod p := by
  classical
  exact
    if a = 0 then
      0
    else
      jenningsExpansionCoeff (p := p) e a

@[simp]
lemma ordered_jennings_coeff
    {p r : ℕ} [Fact p.Prime]
    (e : Fin r → Fin p) :
    orderedJenningsCoeff (p := p) e (0 : Fin r → Fin p) = 0 := by
  classical
  simp [orderedJenningsCoeff]

@[simp]
lemma jennings_coeff_single
    {p r : ℕ} [Fact p.Prime]
    (e : Fin r → Fin p)
    (i : Fin r) :
    orderedJenningsCoeff (p := p) e
        (jenningsExpFin (p := p) i)
      =
        ((e i).val : ZMod p) := by
  classical
  simp [orderedJenningsCoeff]

lemma jennings_coeff_ne
    {p r : ℕ} [Fact p.Prime]
    {e a : Fin r → Fin p}
    (ha : a ≠ 0) :
    orderedJenningsCoeff (p := p) e a =
      jenningsExpansionCoeff (p := p) e a := by
  classical
  simp [orderedJenningsCoeff, ha]

/-- A nonzero coefficient in the `[orderedWord e] - 1` expansion is coordinatewise supported
below `e`. -/
lemma ordered_jennings_coord
    {p r : ℕ} [Fact p.Prime]
    {e a : Fin r → Fin p}
    (hcoeff : orderedJenningsCoeff (p := p) e a ≠ 0)
    (i : Fin r) :
    (a i).val ≤ (e i).val := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · have hcoeff_exp :
        jenningsExpansionCoeff (p := p) e a ≠ 0 := by
      simpa [jennings_coeff_ne
        (p := p) (e := e) (a := a) ha] using hcoeff
    exact jennings_expansion_coord hcoeff_exp i

/-- Subtracting the constant term from the canonical ordered-word expansion gives the
corresponding expansion of `[orderedWord e] - 1`. -/
lemma fin_jennings_monomial
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    groupAlgebraSub p Q (orderedWordFin x e) =
      ∑ a : Fin r → Fin p,
        orderedJenningsCoeff e a • jenningsMonomialFin p Q x a := by
  classical
  rw [groupAlgebraSub, algebra_jennings_monomial]
  have hone :
      (1 : denseGroupAlgebra p Q) =
        ∑ a : Fin r → Fin p, if a = 0 then 1 else 0 := by
    simp
  rw [hone, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases ha : a = 0
  · subst a
    simp
  · simp [orderedJenningsCoeff, ha]

/-- Coordinates of an explicitly written finite linear combination of basis vectors. -/
lemma repr_fintype_sum
    {R : Type*} [Semiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {κ : Type*} [Fintype κ]
    (B : Module.Basis κ R M)
    (c : κ → R)
    (i : κ) :
    B.repr (∑ j : κ, c j • B j) i = c i := by
  classical
  simpa using congrFun (B.repr_sum_self c) i

/-- Coordinate extraction from a finite basis expansion. -/
lemma basis_repr_fintype
    {R : Type*} [Semiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {κ : Type*} [Fintype κ]
    (B : Module.Basis κ R M)
    {x : M}
    (c : κ → R)
    (hx : x = ∑ j : κ, c j • B j)
    (i : κ) :
    B.repr x i = c i := by
  rw [hx]
  exact repr_fintype_sum B c i

/-- If the normal-form exponent vector `e` is zero in all weights below `t`, then in the formal
expansion of `[word e] - 1`, all coefficients of total Jennings weight `< t` vanish. -/
lemma ordered_jennings_below
    {p r : ℕ} [Fact p.Prime]
    {wt : Fin r → ℕ}
    {t : ℕ}
    {e a : Fin r → Fin p}
    (hzero : ∀ i : Fin r, wt i < t → e i = 0)
    (ha : expWeight (p := p) (r := r) wt a < t) :
    orderedJenningsCoeff (p := p) e a = 0 := by
  classical
  by_cases h0 : a = 0
  · simp [orderedJenningsCoeff, h0]
  · have hexists : ∃ i : Fin r, a i ≠ 0 := by
      by_contra hnone
      apply h0
      funext i
      by_contra hi
      exact hnone ⟨i, hi⟩
    rcases hexists with ⟨i, hai⟩
    have hai_val_ne : (a i).val ≠ 0 := by
      intro hv
      exact hai (Fin.ext hv)
    have hai_pos : 0 < (a i).val :=
      Nat.pos_of_ne_zero hai_val_ne
    have hterm_le :
        (a i).val * wt i ≤ expWeight (p := p) (r := r) wt a := by
      rw [expWeight]
      exact Finset.single_le_sum
        (fun j _ => Nat.zero_le ((a j).val * wt j))
        (Finset.mem_univ i)
    have hterm_lt : (a i).val * wt i < t :=
      lt_of_le_of_lt hterm_le ha
    have hwi_lt : wt i < t := by
      have hone_le : 1 ≤ (a i).val :=
        Nat.succ_le_of_lt hai_pos
      have hmul_le : wt i ≤ (a i).val * wt i := by
        simpa [one_mul] using Nat.mul_le_mul_right (wt i) hone_le
      exact lt_of_le_of_lt hmul_le hterm_lt
    have hfactor :
        ((Nat.choose (e i).val (a i).val : ℕ) : ZMod p) = 0 := by
      have heval : (e i).val = 0 := by
        simpa using congrArg Fin.val (hzero i hwi_lt)
      have hchoose_nat : Nat.choose (e i).val (a i).val = 0 := by
        rw [heval]
        cases hval : (a i).val with
        | zero =>
            exact False.elim (hai_val_ne hval)
        | succ k =>
            simp
      simp [hchoose_nat]
    have hprod :
        jenningsExpansionCoeff (p := p) e a = 0 := by
      rw [jenningsExpansionCoeff]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hfactor
    simpa [orderedJenningsCoeff, h0] using hprod

namespace OZReps

variable {p : ℕ} [Fact p.Prime]
variable {Q : Type u} [Group Q]
variable {m : ℕ}

/-- The ordered Jennings monomials span the group algebra and have the correct cardinality,
so they form a basis. -/
noncomputable def jenningsMonomialBasis
    [Finite Q]
    (O : OZReps (p := p) Q m) :
    Module.Basis (Fin O.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q) := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  apply basisOfTopLeSpanOfCardEqFinrank
    (fun a : Fin O.r → Fin p => jenningsMonomialFin p Q O.gen a)
  · calc
      ⊤ =
          Submodule.span (ZMod p)
            (Set.range
              (Finsupp.basisSingleOne : Module.Basis Q (ZMod p)
                (denseGroupAlgebra p Q))) :=
        (Finsupp.basisSingleOne : Module.Basis Q (ZMod p)
          (denseGroupAlgebra p Q)).span_eq.symm
      _ ≤
          Submodule.span (ZMod p)
            (Set.range fun a : Fin O.r → Fin p =>
              jenningsMonomialFin p Q O.gen a) := by
        apply Submodule.span_le.2
        intro y hy
        rcases hy with ⟨q, rfl⟩
        have hexp :=
          algebra_jennings_monomial
            (p := p) (Q := Q) O.gen (O.wordEquiv.symm q)
        have hword :
            orderedWordFin O.gen (O.wordEquiv.symm q) = q := by
          rw [← O.wordEquiv_apply]
          simp
        rw [hword] at hexp
        change denseGeneratorsElement p Q q ∈
          Submodule.span (ZMod p)
            (Set.range fun a : Fin O.r → Fin p =>
              jenningsMonomialFin p Q O.gen a)
        rw [hexp]
        apply Submodule.sum_mem
        intro a _ha
        exact
          Submodule.smul_mem _ _
            (Submodule.subset_span ⟨a, rfl⟩)
  · calc
      Fintype.card (Fin O.r → Fin p) = Fintype.card Q :=
        Fintype.card_congr O.wordEquiv
      _ = Module.finrank (ZMod p) (denseGroupAlgebra p Q) := by
        exact (Module.finrank_finsupp_self (ZMod p) (ι := Q)).symm

@[simp]
lemma monomial_basis
    [Finite Q]
    (O : OZReps (p := p) Q m)
    (a : Fin O.r → Fin p) :
    O.jenningsMonomialBasis a =
      jenningsMonomialFin p Q O.gen a := by
  classical
  simp [jenningsMonomialBasis]

/-- The `[word] - 1` expansion in the ordered Jennings monomial basis. -/
lemma jennings_monomial_basis
    [Finite Q]
    (O : OZReps (p := p) Q m)
    (e : Fin O.r → Fin p) :
    groupAlgebraSub p Q (O.wordEquiv e) =
      ∑ a : Fin O.r → Fin p,
        orderedJenningsCoeff e a • O.jenningsMonomialBasis a := by
  rw [O.wordEquiv_apply]
  simpa using
    (fin_jennings_monomial
      (p := p) (Q := Q) O.gen e)

/-- The exponent of a group element in the ordered normal form. -/
def coord
    (O : OZReps (p := p) Q m)
    (q : Q)
    (i : Fin O.r) :
    Fin p :=
  O.wordEquiv.symm q i

/-- The membership criterion from the ordered normal form, phrased in terms of coordinates. -/
lemma zassenhaus_coords
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (ht : t ≤ m)
    (q : Q) :
    q ∈ zassenhausFiltration p Q t ↔
      ∀ i, O.weight i < t → O.coord q i = 0 := by
  classical
  simpa [coord] using
    O.mem_iff_below ht (O.wordEquiv.symm q)

/-- If an element lies in `D_n` but not `D_(n+1)`, then its normal form has a
nonzero coordinate of exact weight `n`. -/
lemma coord_d_dsucc
    (O : OZReps (p := p) Q m)
    {n : ℕ}
    (hnm : n + 1 ≤ m)
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hqNot : q ∉ zassenhausFiltration p Q (n + 1)) :
    ∃ i : Fin O.r, O.weight i = n ∧ O.coord q i ≠ 0 := by
  classical
  have hn_le_m : n ≤ m := le_trans (Nat.le_succ n) hnm
  have hzero_n :
      ∀ i, O.weight i < n → O.coord q i = 0 :=
    (O.zassenhaus_coords hn_le_m q).1 hqD
  have hnot_zero_succ :
      ¬ ∀ i, O.weight i < n + 1 → O.coord q i = 0 := by
    intro hzero_succ
    exact hqNot ((O.zassenhaus_coords hnm q).2 hzero_succ)
  push Not at hnot_zero_succ
  rcases hnot_zero_succ with ⟨i, hi_lt_succ, hci⟩
  have hi_le : O.weight i ≤ n := Nat.lt_succ_iff.mp hi_lt_succ
  have hn_le : n ≤ O.weight i := by
    by_contra hlt
    exact hci (hzero_n i (Nat.lt_of_not_ge hlt))
  exact ⟨i, le_antisymm hi_le hn_le, hci⟩

/-- The zero element of `Fin p`, avoiding an extra `NeZero p` typeclass search. -/
def zeroFin
    (p : ℕ) [Fact p.Prime] :
    Fin p :=
  ⟨0, (Fact.out : Nat.Prime p).pos⟩

/-- The one element of `Fin p`, avoiding an extra `NeZero p` typeclass search. -/
def oneFin
    (p : ℕ) [Fact p.Prime] :
    Fin p :=
  ⟨1, (Fact.out : Nat.Prime p).one_lt⟩

/-- The exponent vector with a single `1` in coordinate `i`. -/
def eps
    (O : OZReps (p := p) Q m)
    (i : Fin O.r) :
    Fin O.r → Fin p :=
  Function.update (fun _ => zeroFin p) i (oneFin p)

/-- The all-zero exponent vector. -/
def zeroExp
    (O : OZReps (p := p) Q m) :
    Fin O.r → Fin p :=
  fun _ => zeroFin p

/-- The Jennings weight of a single-coordinate exponent vector. -/
lemma expWeight_eps
    (O : OZReps (p := p) Q m)
    (i : Fin O.r) :
    expWeight O.weight (O.eps i) = O.weight i := by
  classical
  unfold expWeight eps zeroFin oneFin
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [Function.update_of_ne hji]
  · intro hi
    simp at hi

/-- A nonzero exponent in `Fin p` is nonzero after coercion to `ZMod p`. -/
lemma fin_cast_zmod
    {a : Fin p}
    (ha : a ≠ 0) :
    ((a : ℕ) : ZMod p) ≠ 0 := by
  intro hzero
  have hp : Nat.Prime p := Fact.out
  have hdiv : p ∣ (a : ℕ) := by
    exact (ZMod.natCast_eq_zero_iff (a : ℕ) p).mp hzero
  have hval0 : (a : ℕ) = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdiv a.isLt
  exact ha (Fin.ext hval0)

/-- The all-zero exponent vector evaluates to the identity word. -/
lemma ordered_fin_exp
    (O : OZReps (p := p) Q m) :
    orderedWordFin O.gen O.zeroExp = 1 := by
  unfold orderedWordFin orderedWord zeroExp zeroFin
  refine fin_ordered_forall O.r _ ?_
  intro i
  simp

/-- The ordered normal-form equivalence sends the all-zero exponent vector to `1`. -/
lemma word_zero_exp
    (O : OZReps (p := p) Q m) :
    O.wordEquiv O.zeroExp = 1 := by
  rw [O.wordEquiv_apply, O.ordered_fin_exp]

/-- If every normal-form coordinate of `q` is zero, then `q = 1`. -/
lemma forall_coord_zero
    (O : OZReps (p := p) Q m)
    {q : Q}
    (hzero : ∀ i, O.coord q i = 0) :
    q = 1 := by
  have hsymm : O.wordEquiv.symm q = O.zeroExp := by
    funext i
    simpa [zeroExp, zeroFin] using hzero i
  calc
    q = O.wordEquiv (O.wordEquiv.symm q) := by
      exact (O.wordEquiv.apply_symm_apply q).symm
    _ = O.wordEquiv O.zeroExp := by
      rw [hsymm]
    _ = 1 := O.word_zero_exp

/-- A nontrivial group element has some nonzero normal-form coordinate. -/
lemma coord_ne_one
    (O : OZReps (p := p) Q m)
    {q : Q}
    (hq : q ≠ 1) :
    ∃ i : Fin O.r, O.coord q i ≠ 0 := by
  by_contra hnone
  have hzero : ∀ i, O.coord q i = 0 := by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  exact hq (O.forall_coord_zero hzero)

/-- A nonzero coordinate of an element of `D_t` must have weight at least `t`. -/
lemma coord_d_one
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (ht : t ≤ m)
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q t)
    (hq : q ≠ 1) :
    ∃ i : Fin O.r, t ≤ O.weight i ∧ O.coord q i ≠ 0 := by
  obtain ⟨i, hi⟩ := O.coord_ne_one hq
  have hzero_low :
      ∀ j, O.weight j < t → O.coord q j = 0 :=
    (O.zassenhaus_coords ht q).1 hqD
  have hit : t ≤ O.weight i := by
    by_contra hnot
    exact hi (hzero_low i (Nat.lt_of_not_ge hnot))
  exact ⟨i, hit, hi⟩

/-- If `wordEquiv e ∈ D_t`, then all formal sub-one expansion coefficients of Jennings
weight `< t` vanish. -/
lemma sub_expansion_coeff
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (ht : t ≤ m)
    {e a : Fin O.r → Fin p}
    (heD : O.wordEquiv e ∈ zassenhausFiltration p Q t)
    (ha : expWeight (p := p) (r := O.r) O.weight a < t) :
    orderedJenningsCoeff (p := p) e a = 0 := by
  exact
    ordered_jennings_below
      (p := p) (r := O.r) (wt := O.weight) (t := t)
      (e := e) (a := a)
      ((O.mem_iff_below (t := t) ht e).1 heD)
      ha

/-- Same vanishing statement, written for an arbitrary group element via its normal-form
exponent vector. -/
lemma sub_coeff_zero
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (ht : t ≤ m)
    {q : Q}
    {a : Fin O.r → Fin p}
    (hq : q ∈ zassenhausFiltration p Q t)
    (ha : expWeight (p := p) (r := O.r) O.weight a < t) :
    orderedJenningsCoeff (p := p) (O.wordEquiv.symm q) a = 0 := by
  have hword :
      O.wordEquiv (O.wordEquiv.symm q) ∈ zassenhausFiltration p Q t := by
    simpa using hq
  exact
    O.sub_expansion_coeff
      (t := t) (e := O.wordEquiv.symm q) (a := a) ht hword ha

/-- If the last Zassenhaus subgroup has been killed, then a nontrivial ordered normal-form word
has some nonzero exponent of weight `< m`. -/
lemma nonzero_coord_below
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    {q : Q}
    (hq : q ≠ 1) :
    ∃ i : Fin O.r, O.weight i < m ∧ O.wordEquiv.symm q i ≠ 0 := by
  classical
  by_contra h
  have hall :
      ∀ i : Fin O.r, O.weight i < m → O.wordEquiv.symm q i = 0 := by
    intro i hi
    by_contra hne
    exact h ⟨i, hi, hne⟩
  have hmem' :
      O.wordEquiv (O.wordEquiv.symm q) ∈ zassenhausFiltration p Q m :=
    (O.mem_iff_below (t := m) le_rfl (O.wordEquiv.symm q)).2 hall
  have hmem : q ∈ zassenhausFiltration p Q m := by
    simpa using hmem'
  have hmem_bot : q ∈ (⊥ : Subgroup Q) := by
    simpa [hbot] using hmem
  exact hq (Subgroup.mem_bot.mp hmem_bot)

/-- In the truncated normal form modulo `D_(n+1)`, a nontrivial element of `D_n` has a nonzero
normal-form exponent of exactly weight `n`. -/
lemma coord_d_ne
    (n : ℕ)
    (O : OZReps (p := p) Q (n + 1))
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hq : q ≠ 1) :
    ∃ i : Fin O.r, O.weight i = n ∧ O.wordEquiv.symm q i ≠ 0 := by
  classical
  have hqD' :
      O.wordEquiv (O.wordEquiv.symm q) ∈ zassenhausFiltration p Q n := by
    simpa using hqD
  have hzero_below :
      ∀ i : Fin O.r, O.weight i < n → O.wordEquiv.symm q i = 0 :=
    (O.mem_iff_below (t := n) (Nat.le_succ n) (O.wordEquiv.symm q)).1 hqD'
  rcases O.nonzero_coord_below hbot hq with ⟨i, hi_lt, hi_ne⟩
  refine ⟨i, ?_, hi_ne⟩
  have hnot_lt : ¬ O.weight i < n := by
    intro hi
    exact hi_ne (hzero_below i hi)
  have hle : O.weight i ≤ n := Nat.le_of_lt_succ hi_lt
  have hge : n ≤ O.weight i := le_of_not_gt hnot_lt
  exact le_antisymm hle hge

/-- Singleton-exponent version of `coord_d_ne`. -/
lemma single_exp_d
    (n : ℕ)
    (O : OZReps (p := p) Q (n + 1))
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hq : q ≠ 1) :
    ∃ a : Fin O.r → Fin p,
      expWeight (p := p) (r := O.r) O.weight a = n ∧
        ∃ i : Fin O.r,
          a = jenningsExpFin (p := p) i ∧
            O.wordEquiv.symm q i ≠ 0 := by
  classical
  rcases coord_d_ne (p := p) (Q := Q) n O hbot hqD hq with
    ⟨i, hwi, hi_ne⟩
  refine ⟨jenningsExpFin (p := p) i, ?_, ⟨i, rfl, hi_ne⟩⟩
  simp [hwi]

/-- Once `[O.wordEquiv e] - 1` has been expanded in a Jennings-indexed basis with the binomial
`subOne` coefficients, the singleton coordinate is the corresponding normal-form exponent. -/
lemma singleton_coord_expansion
    (O : OZReps (p := p) Q m)
    (B : Module.Basis (Fin O.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (hexp :
      ∀ e : Fin O.r → Fin p,
        groupAlgebraSub p Q (O.wordEquiv e) =
          ∑ a : Fin O.r → Fin p,
            orderedJenningsCoeff (p := p) e a • B a)
    (q : Q)
    (i : Fin O.r) :
    B.repr (groupAlgebraSub p Q q)
        (jenningsExpFin (p := p) i)
      =
        ((O.wordEquiv.symm q i).val : ZMod p) := by
  classical
  let e : Fin O.r → Fin p := O.wordEquiv.symm q
  have hq : O.wordEquiv e = q := by
    dsimp [e]
    simp
  rw [← hq, hexp e]
  simpa [e] using
    (repr_fintype_sum
      (B := B)
      (c := fun a : Fin O.r → Fin p =>
        orderedJenningsCoeff (p := p) e a)
      (i := jenningsExpFin (p := p) i))

/-- If the explicit Jennings-basis expansion of `[O.wordEquiv e] - 1` is known, then every
nonzero normal-form exponent gives a nonzero singleton Jennings coordinate. -/
lemma singleton_coeff_expansion
    (O : OZReps (p := p) Q m)
    (B : Module.Basis (Fin O.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (hexp :
      ∀ e : Fin O.r → Fin p,
        groupAlgebraSub p Q (O.wordEquiv e) =
          ∑ a : Fin O.r → Fin p,
            orderedJenningsCoeff (p := p) e a • B a)
    {q : Q}
    {i : Fin O.r}
    (hi : O.wordEquiv.symm q i ≠ 0) :
    B.repr (groupAlgebraSub p Q q)
        (jenningsExpFin (p := p) i) ≠ 0 := by
  rw [O.singleton_coord_expansion B hexp q i]
  simpa using fin_cast_zmod (p := p) hi

/-- To prove the `separates` coordinate criterion for a Jennings basis indexed by exponent
vectors, it is enough to prove that every nonzero normal-form exponent gives a nonzero singleton
coordinate of `q - 1`. -/
lemma separates_singleton_coeff
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (B : Module.Basis (Fin O.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (hsingle :
      ∀ {q : Q} {i : Fin O.r},
        O.wordEquiv.symm q i ≠ 0 →
          B.repr (groupAlgebraSub p Q q)
            (jenningsExpFin (p := p) i) ≠ 0) :
    ∀ q : Q, q ≠ 1 →
      ∃ e : Fin O.r → Fin p,
        expWeight (p := p) (r := O.r) O.weight e < m ∧
          B.repr (groupAlgebraSub p Q q) e ≠ 0 := by
  classical
  intro q hq
  rcases O.nonzero_coord_below hbot hq with ⟨i, hi_wt, hi_ne⟩
  refine ⟨jenningsExpFin (p := p) i, ?_, ?_⟩
  · simpa using
      (show
        expWeight (p := p) (r := O.r) O.weight
          (jenningsExpFin (p := p) i) < m
        from by
          rw [exp_single_fin]
          exact hi_wt)
  · exact hsingle hi_ne

/-- The `separates` coordinate criterion follows from the explicit binomial expansion of
`[O.wordEquiv e] - 1` in a Jennings-indexed basis. -/
lemma separates_sub_expansion
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (B : Module.Basis (Fin O.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (hexp :
      ∀ e : Fin O.r → Fin p,
        groupAlgebraSub p Q (O.wordEquiv e) =
          ∑ a : Fin O.r → Fin p,
            orderedJenningsCoeff (p := p) e a • B a) :
    ∀ q : Q, q ≠ 1 →
      ∃ e : Fin O.r → Fin p,
        expWeight (p := p) (r := O.r) O.weight e < m ∧
          B.repr (groupAlgebraSub p Q q) e ≠ 0 := by
  classical
  exact
    O.separates_singleton_coeff hbot B
      (by
        intro q i hi
        exact O.singleton_coeff_expansion B hexp hi)

/-- A noncommutative word in the ordered augmentation letters. -/
def wordEval
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r)) :
    denseGroupAlgebra p Q :=
  (w.map fun i => groupAlgebraSub p Q (O.gen i)).prod

/-- The total Zassenhaus weight of a word in the ordered representatives. -/
def wordWeight
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r)) :
    ℕ :=
  (w.map O.weight).sum

/-- The span of ordered-letter words of weight at least `s`. -/
def wordSpan
    (O : OZReps (p := p) Q m)
    (s : ℕ) :
    Submodule (ZMod p) (denseGroupAlgebra p Q) :=
  Submodule.span (ZMod p)
    { x | ∃ w : List (Fin O.r), s ≤ O.wordWeight w ∧ O.wordEval w = x }

/-- The corresponding group word in the ordered representatives. -/
def groupWordEval
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r)) :
    Q :=
  (w.map O.gen).prod

@[simp]
lemma wordEval_nil
    (O : OZReps (p := p) Q m) :
    O.wordEval [] = 1 := by
  simp [wordEval]

@[simp]
lemma wordWeight_nil
    (O : OZReps (p := p) Q m) :
    O.wordWeight [] = 0 := by
  simp [wordWeight]

@[simp]
lemma wordEval_singleton
    (O : OZReps (p := p) Q m)
    (i : Fin O.r) :
    O.wordEval [i] = groupAlgebraSub p Q (O.gen i) := by
  simp [wordEval]

@[simp]
lemma wordWeight_singleton
    (O : OZReps (p := p) Q m)
    (i : Fin O.r) :
    O.wordWeight [i] = O.weight i := by
  simp [wordWeight]

/-- Evaluation of concatenated words is multiplication in the group algebra. -/
lemma wordEval_append
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r)) :
    O.wordEval (u ++ v) = O.wordEval u * O.wordEval v := by
  simp [wordEval, List.map_append, List.prod_append]

/-- Word weights add under concatenation. -/
lemma wordWeight_append
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r)) :
    O.wordWeight (u ++ v) = O.wordWeight u + O.wordWeight v := by
  simp [wordWeight, List.map_append]

/-- The ordered exponent list evaluates, as an augmentation word, to the corresponding ordered
Jennings monomial. -/
lemma word_exponent_list
    (O : OZReps (p := p) Q m)
    (e : Fin O.r → Fin p) :
    O.wordEval (orderedExponentList O.r e) =
      jenningsMonomialFin p Q O.gen e := by
  simpa [wordEval, jenningsMonomialFin, orderedWordFin, orderedWord] using
    (ordered_exponent_fin
      (p := p)
      (x := fun i : Fin O.r => groupAlgebraSub p Q (O.gen i))
      e)

/-- The ordered exponent list has total word weight equal to the Jennings weight of its exponent
vector. -/
lemma ordered_exponent_list
    (O : OZReps (p := p) Q m)
    (e : Fin O.r → Fin p) :
    O.wordWeight (orderedExponentList O.r e) =
      expWeight (p := p) (r := O.r) O.weight e := by
  simpa [wordWeight] using
    ordered_exponent_exp (p := p) O.r O.weight e

/-- An already ordered exponent word has no off-diagonal coordinate in the canonical Jennings
monomial basis. -/
lemma monomial_repr_ne
    [Finite Q]
    (O : OZReps (p := p) Q m)
    {e a : Fin O.r → Fin p}
    (hae : a ≠ e) :
    O.jenningsMonomialBasis.repr (O.wordEval (orderedExponentList O.r e)) a = 0 := by
  classical
  rw [O.word_exponent_list]
  have hbasis :
      jenningsMonomialFin p Q O.gen e = O.jenningsMonomialBasis e := by
    rw [O.monomial_basis]
  have hea : e ≠ a := fun h => hae h.symm
  calc
    O.jenningsMonomialBasis.repr
          (jenningsMonomialFin p Q O.gen e) a =
        O.jenningsMonomialBasis.repr (O.jenningsMonomialBasis e) a := by
          rw [hbasis]
    _ = 0 := by
      rw [O.jenningsMonomialBasis.repr_self]
      simp [hea]

/-- The ordered exponent-list case of the PBW word-coordinate vanishing statement. -/
lemma jennings_monomial_repr
    [Finite Q]
    (O : OZReps (p := p) Q m)
    {e a : Fin O.r → Fin p}
    {s : ℕ}
    (hw : s ≤ O.wordWeight (orderedExponentList O.r e))
    (ha : expWeight (p := p) (r := O.r) O.weight a < s) :
    O.jenningsMonomialBasis.repr (O.wordEval (orderedExponentList O.r e)) a = 0 := by
  have he_weight : s ≤ expWeight (p := p) (r := O.r) O.weight e := by
    simpa [O.ordered_exponent_list e] using hw
  have hne : a ≠ e := by
    intro hae
    subst a
    omega
  exact O.monomial_repr_ne hne

/-- The word spans are antitone in the lower weight cutoff. -/
lemma wordSpan_antitone
    (O : OZReps (p := p) Q m)
    {s t : ℕ}
    (hst : s ≤ t) :
    O.wordSpan t ≤ O.wordSpan s := by
  unfold wordSpan
  refine Submodule.span_mono ?_
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, le_trans hst hw, rfl⟩

/-- A word of weight at least `s` lies in the corresponding word span. -/
lemma word_eval_span
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    (w : List (Fin O.r))
    (hw : s ≤ O.wordWeight w) :
    O.wordEval w ∈ O.wordSpan s := by
  exact Submodule.subset_span ⟨w, hw, rfl⟩

/-- Each ordered representative contributes its augmentation letter to the word span at its
own weight. -/
lemma algebra_gen_span
    (O : OZReps (p := p) Q m)
    (i : Fin O.r) :
    groupAlgebraSub p Q (O.gen i) ∈ O.wordSpan (O.weight i) := by
  simpa using
    O.word_eval_span [i] (by simp)

/-- Products of elements in word spans lie in the span with added cutoff. -/
lemma mul_word_span
    (O : OZReps (p := p) Q m)
    {a b : ℕ}
    {x y : denseGroupAlgebra p Q}
    (hx : x ∈ O.wordSpan a)
    (hy : y ∈ O.wordSpan b) :
    x * y ∈ O.wordSpan (a + b) := by
  classical
  refine Submodule.span_induction
    (s := { x | ∃ w : List (Fin O.r), a ≤ O.wordWeight w ∧ O.wordEval w = x })
    (p := fun x _ => x * y ∈ O.wordSpan (a + b))
    ?base_left ?zero_left ?add_left ?smul_left hx
  · intro x hxset
    rcases hxset with ⟨wx, hwa, rfl⟩
    refine Submodule.span_induction
      (s := { y | ∃ w : List (Fin O.r), b ≤ O.wordWeight w ∧ O.wordEval w = y })
      (p := fun y _ => O.wordEval wx * y ∈ O.wordSpan (a + b))
      ?base_right ?zero_right ?add_right ?smul_right hy
    · intro y hyset
      rcases hyset with ⟨wy, hwb, rfl⟩
      rw [← O.wordEval_append]
      exact
        O.word_eval_span (wx ++ wy)
          (by
            rw [O.wordWeight_append]
            exact add_le_add hwa hwb)
    · simp
    · intro y₁ y₂ _hy₁ _hy₂ hy₁ hy₂
      simpa [mul_add] using (O.wordSpan (a + b)).add_mem hy₁ hy₂
    · intro c y _hy hy_mem
      simpa [mul_smul_comm] using (O.wordSpan (a + b)).smul_mem c hy_mem
  · simp
  · intro x₁ x₂ _hx₁ _hx₂ hx₁ hx₂
    simpa [add_mul] using (O.wordSpan (a + b)).add_mem hx₁ hx₂
  · intro c x _hx hx_mem
    simpa [smul_mul_assoc] using (O.wordSpan (a + b)).smul_mem c hx_mem

/-- The empty word puts `1` in the zero-cutoff word span. -/
lemma one_span_zero
    (O : OZReps (p := p) Q m) :
    (1 : denseGroupAlgebra p Q) ∈ O.wordSpan 0 := by
  simpa using O.word_eval_span [] (by simp)

/-- Powers of an element in a word span stay in the word span with multiplied cutoff. -/
lemma pow_word_span
    (O : OZReps (p := p) Q m)
    {a : ℕ}
    {x : denseGroupAlgebra p Q}
    (hx : x ∈ O.wordSpan a)
    (k : ℕ) :
    x ^ k ∈ O.wordSpan (a * k) := by
  induction k with
  | zero =>
      simpa using O.one_span_zero
  | succ k ih =>
      have hmul : x ^ k * x ∈ O.wordSpan (a * k + a) :=
        O.mul_word_span ih hx
      simpa [pow_succ, Nat.mul_succ] using hmul

@[simp]
lemma wordEval_replicate
    (O : OZReps (p := p) Q m)
    (i : Fin O.r)
    (k : ℕ) :
    O.wordEval (List.replicate k i) =
      groupAlgebraSub p Q (O.gen i) ^ k := by
  simp [wordEval]

@[simp]
lemma wordWeight_replicate
    (O : OZReps (p := p) Q m)
    (i : Fin O.r)
    (k : ℕ) :
    O.wordWeight (List.replicate k i) = k * O.weight i := by
  simp [wordWeight]

/-- Powers of a single ordered augmentation letter lie in the word span at the expected weight. -/
lemma sub_gen_span
    (O : OZReps (p := p) Q m)
    (i : Fin O.r)
    (k : ℕ) :
    groupAlgebraSub p Q (O.gen i) ^ k ∈ O.wordSpan (k * O.weight i) := by
  have hpow :=
    O.pow_word_span (O.algebra_gen_span i) k
  simpa [Nat.mul_comm] using hpow

/-- If the ordered representative has weight at least `t`, then every group power of it has
augmentation difference in the cutoff-`t` word span. -/
lemma gen_span_weight
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (i : Fin O.r)
    (hti : t ≤ O.weight i)
    (k : ℕ) :
    groupAlgebraSub p Q (O.gen i ^ k) ∈ O.wordSpan t := by
  induction k with
  | zero =>
      simp [algebra_sub_one]
  | succ k ih =>
      rw [pow_succ]
      rw [algebra_sub_right]
      have hletter_weight :
          groupAlgebraSub p Q (O.gen i) ∈ O.wordSpan (O.weight i) :=
        O.algebra_gen_span i
      have hletter_t :
          groupAlgebraSub p Q (O.gen i) ∈ O.wordSpan t :=
        O.wordSpan_antitone hti hletter_weight
      have hprod :
          groupAlgebraSub p Q (O.gen i ^ k) *
              groupAlgebraSub p Q (O.gen i) ∈
            O.wordSpan (t + O.weight i) :=
        O.mul_word_span ih hletter_weight
      have hprod_t :
          groupAlgebraSub p Q (O.gen i ^ k) *
              groupAlgebraSub p Q (O.gen i) ∈ O.wordSpan t :=
        O.wordSpan_antitone (by omega) hprod
      have hcanonical :
          denseGeneratorsElement p Q (O.gen i) =
            groupAlgebraSub p Q (O.gen i) + 1 := by
        simp [groupAlgebraSub]
      have hleft :
          groupAlgebraSub p Q (O.gen i ^ k) *
              denseGeneratorsElement p Q (O.gen i) ∈
            O.wordSpan t := by
        rw [hcanonical, mul_add, mul_one]
        exact (O.wordSpan t).add_mem hprod_t ih
      exact (O.wordSpan t).add_mem hleft hletter_t

/-- Left multiplication by the canonical group-algebra element of a high-weight generator
preserves the cutoff word span. -/
lemma canonical_gen_span
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (i : Fin O.r)
    (hti : t ≤ O.weight i)
    {a : denseGroupAlgebra p Q}
    (ha : a ∈ O.wordSpan t) :
    denseGeneratorsElement p Q (O.gen i) * a ∈
      O.wordSpan t := by
  have hletter_weight :
      groupAlgebraSub p Q (O.gen i) ∈ O.wordSpan (O.weight i) :=
    O.algebra_gen_span i
  have hprod :
      groupAlgebraSub p Q (O.gen i) * a ∈ O.wordSpan (O.weight i + t) :=
    O.mul_word_span hletter_weight ha
  have hprod_t :
      groupAlgebraSub p Q (O.gen i) * a ∈ O.wordSpan t :=
    O.wordSpan_antitone (by omega) hprod
  have hcanonical :
      denseGeneratorsElement p Q (O.gen i) =
        groupAlgebraSub p Q (O.gen i) + 1 := by
    simp [groupAlgebraSub]
  rw [hcanonical, add_mul, one_mul]
  exact (O.wordSpan t).add_mem hprod_t ha

/-- Right multiplication by the canonical group-algebra element of a high-weight generator
preserves the cutoff word span. -/
lemma canonical_gen_weight
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (i : Fin O.r)
    (hti : t ≤ O.weight i)
    {a : denseGroupAlgebra p Q}
    (ha : a ∈ O.wordSpan t) :
    a * denseGeneratorsElement p Q (O.gen i) ∈
      O.wordSpan t := by
  have hletter_weight :
      groupAlgebraSub p Q (O.gen i) ∈ O.wordSpan (O.weight i) :=
    O.algebra_gen_span i
  have hprod :
      a * groupAlgebraSub p Q (O.gen i) ∈ O.wordSpan (t + O.weight i) :=
    O.mul_word_span ha hletter_weight
  have hprod_t :
      a * groupAlgebraSub p Q (O.gen i) ∈ O.wordSpan t :=
    O.wordSpan_antitone (by omega) hprod
  have hcanonical :
      denseGeneratorsElement p Q (O.gen i) =
        groupAlgebraSub p Q (O.gen i) + 1 := by
    simp [groupAlgebraSub]
  rw [hcanonical, mul_add, mul_one]
  exact (O.wordSpan t).add_mem hprod_t ha

/-- If every letter in a group word has weight at least `t`, then `[word] - 1` lies in
the cutoff-`t` word span. -/
lemma span_forall_weight
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (w : List (Fin O.r))
    (hw : ∀ i, i ∈ w → t ≤ O.weight i) :
    groupAlgebraSub p Q (O.groupWordEval w) ∈ O.wordSpan t := by
  induction w with
  | nil =>
      simp [groupWordEval, algebra_sub_one]
  | cons i w ih =>
      have hhead : t ≤ O.weight i := hw i (by simp)
      have htail : ∀ j, j ∈ w → t ≤ O.weight j := by
        intro j hj
        exact hw j (by simp [hj])
      have hword :
          groupAlgebraSub p Q (O.groupWordEval w) ∈ O.wordSpan t :=
        ih htail
      have hleft :
          denseGeneratorsElement p Q (O.gen i) *
              groupAlgebraSub p Q (O.groupWordEval w) ∈ O.wordSpan t :=
        O.canonical_gen_span i hhead hword
      have hletter :
          groupAlgebraSub p Q (O.gen i) ∈ O.wordSpan t :=
        O.wordSpan_antitone hhead (O.algebra_gen_span i)
      change
        groupAlgebraSub p Q (O.gen i * O.groupWordEval w) ∈ O.wordSpan t
      rw [algebra_sub_left]
      exact (O.wordSpan t).add_mem hleft hletter

/-- Normal-form words whose nonzero coordinates all have weight at least `t` have augmentation
difference in the cutoff-`t` word span. -/
lemma sub_span_forall
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (e : Fin O.r → Fin p)
    (he : ∀ i, e i ≠ 0 → t ≤ O.weight i) :
    groupAlgebraSub p Q (O.wordEquiv e) ∈ O.wordSpan t := by
  have hweights :
      ∀ i, i ∈ orderedExponentList O.r e → t ≤ O.weight i :=
    ordered_exponent_forall O.r O.weight e
      (fun i hval_ne =>
        he i
          (by
            intro hzero
            exact hval_ne (by simp [hzero])))
  have hword :
      groupAlgebraSub p Q (O.groupWordEval (orderedExponentList O.r e)) ∈
        O.wordSpan t :=
    O.span_forall_weight
      (orderedExponentList O.r e) hweights
  have heval :
      O.groupWordEval (orderedExponentList O.r e) = O.wordEquiv e := by
    calc
      O.groupWordEval (orderedExponentList O.r e) =
          orderedWordFin O.gen e := by
            exact ordered_exponent_fin O.gen e
      _ = O.wordEquiv e := (O.wordEquiv_apply e).symm
  simpa [heval] using hword

/-- Elements of `D_t` have augmentation difference in the ordered word span of cutoff `t`. -/
lemma sub_span_zassenhaus
    (O : OZReps (p := p) Q m)
    {t : ℕ}
    (ht : t ≤ m)
    {q : Q}
    (hq : q ∈ zassenhausFiltration p Q t) :
    groupAlgebraSub p Q q ∈ O.wordSpan t := by
  have hzero :
      ∀ i, O.weight i < t → O.coord q i = 0 :=
    (O.zassenhaus_coords ht q).1 hq
  have hweights :
      ∀ i, O.wordEquiv.symm q i ≠ 0 → t ≤ O.weight i := by
    intro i hi
    by_contra hnot
    exact hi (hzero i (Nat.lt_of_not_ge hnot))
  have hword :
      groupAlgebraSub p Q (O.wordEquiv (O.wordEquiv.symm q)) ∈
        O.wordSpan t :=
    O.sub_span_forall
      (O.wordEquiv.symm q) hweights
  simpa using hword

/-- Every group element has augmentation difference in the ordered word span of cutoff `1`. -/
lemma algebra_sub_span
    (O : OZReps (p := p) Q m)
    (hm : 1 ≤ m)
    (q : Q) :
    groupAlgebraSub p Q q ∈ O.wordSpan 1 := by
  exact
    O.sub_span_zassenhaus
      hm
      (zassenhaus_filtration_one p Q (by norm_num) q)

/-- A product of arbitrary augmentation letters of length `s` lies in the ordered word span
of cutoff `s`. -/
lemma augmentation_factors_span
    (O : OZReps (p := p) Q m)
    (hm : 1 ≤ m)
    (l : List Q) :
    (l.map fun q => groupAlgebraSub p Q q).prod ∈ O.wordSpan l.length := by
  induction l with
  | nil =>
      simpa using O.one_span_zero
  | cons q l ih =>
      have hq : groupAlgebraSub p Q q ∈ O.wordSpan 1 :=
        O.algebra_sub_span hm q
      have hmul :
          groupAlgebraSub p Q q *
              (l.map fun q => groupAlgebraSub p Q q).prod ∈
            O.wordSpan (1 + l.length) :=
        O.mul_word_span hq ih
      simpa [Nat.add_comm] using hmul

/-- A generic fixed-length augmentation word lies in the ordered word span of the same cutoff. -/
lemma augmentation_generator_span
    (O : OZReps (p := p) Q m)
    (hm : 1 ≤ m)
    {s : ℕ}
    (w : List.Vector Q s) :
    denseGeneratorsGenerator p Q w ∈
      O.wordSpan s := by
  have h :=
    O.augmentation_factors_span hm w.toList
  simpa [denseGeneratorsGenerator, groupAlgebraSub]
    using h

/-- The generic fixed-length augmentation-word span is contained in the ordered word span. -/
lemma augmentation_span_ordered
    (O : OZReps (p := p) Q m)
    (hm : 1 ≤ m)
    (s : ℕ) :
    denseGeneratorsSpan p Q s ≤ O.wordSpan s := by
  let T : Set (denseGroupAlgebra p Q) :=
    { y | ∃ w : List.Vector Q s,
        denseGeneratorsGenerator p Q w = y }
  intro y hy
  have hyspan : y ∈ Submodule.span (ZMod p) T := by
    simpa [denseGeneratorsSpan, T] using hy
  refine Submodule.span_induction
    (s := T)
    (p := fun z _ => z ∈ O.wordSpan s)
    ?mem ?zero ?add ?smul hyspan
  · rintro z ⟨w, rfl⟩
    exact O.augmentation_generator_span hm w
  · exact (O.wordSpan s).zero_mem
  · intro x y _hx _hy hx_mem hy_mem
    exact (O.wordSpan s).add_mem hx_mem hy_mem
  · intro c x _hx hx_mem
    exact (O.wordSpan s).smul_mem c hx_mem

/-- The word-span version of the characteristic-`p` power collection step for one letter. -/
lemma pth_letter_span
    (O : OZReps (p := p) Q m)
    (i : Fin O.r) :
    groupAlgebraSub p Q (O.gen i) ^ p ∈ O.wordSpan (p * O.weight i) :=
  O.sub_gen_span i p

/-- A block of `p` equal adjacent augmentation letters is already high-weight, even inside a
larger word. This is the local truncation move paired with adjacent swaps in the PBW collection
argument. -/
lemma pth_block_span
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r))
    (i : Fin O.r) :
    O.wordEval (u ++ List.replicate p i ++ v) ∈
      O.wordSpan (O.wordWeight u + p * O.weight i + O.wordWeight v) := by
  have hprefix :
      O.wordEval u ∈ O.wordSpan (O.wordWeight u) :=
    O.word_eval_span u le_rfl
  have hmiddle :
      O.wordEval (List.replicate p i) ∈ O.wordSpan (p * O.weight i) := by
    simpa using O.pth_letter_span i
  have hsuffix :
      O.wordEval v ∈ O.wordSpan (O.wordWeight v) :=
    O.word_eval_span v le_rfl
  have hleft :
      O.wordEval u * O.wordEval (List.replicate p i) ∈
        O.wordSpan (O.wordWeight u + p * O.weight i) :=
    O.mul_word_span hprefix hmiddle
  have htotal :
      O.wordEval u * O.wordEval (List.replicate p i) * O.wordEval v ∈
        O.wordSpan (O.wordWeight u + p * O.weight i + O.wordWeight v) :=
    O.mul_word_span hleft hsuffix
  simpa only [O.wordEval_append, mul_assoc] using htotal

/-- A contextual `p`-th power block is high-weight with respect to the actual word weight of the
word containing that block. -/
lemma pth_span_weight
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r))
    (i : Fin O.r) :
    O.wordEval (u ++ List.replicate p i ++ v) ∈
      O.wordSpan (O.wordWeight (u ++ List.replicate p i ++ v)) := by
  have h := O.pth_block_span u v i
  simpa [
    O.wordWeight_append,
    wordWeight,
    List.sum_replicate,
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm,
    Nat.mul_comm
  ] using h

/-- Swapping two adjacent augmentation letters changes the word by an element of the word span
at the combined weight. -/
lemma swap_defect_span
    (O : OZReps (p := p) Q m)
    (i j : Fin O.r) :
    groupAlgebraSub p Q (O.gen j) *
          groupAlgebraSub p Q (O.gen i) -
        groupAlgebraSub p Q (O.gen i) *
          groupAlgebraSub p Q (O.gen j) ∈
      O.wordSpan (O.weight i + O.weight j) := by
  have hji :
      groupAlgebraSub p Q (O.gen j) *
          groupAlgebraSub p Q (O.gen i) ∈
        O.wordSpan (O.weight i + O.weight j) := by
    have h :=
      O.mul_word_span
        (O.algebra_gen_span j)
        (O.algebra_gen_span i)
    simpa [Nat.add_comm] using h
  have hij :
      groupAlgebraSub p Q (O.gen i) *
          groupAlgebraSub p Q (O.gen j) ∈
        O.wordSpan (O.weight i + O.weight j) :=
    O.mul_word_span
      (O.algebra_gen_span i)
      (O.algebra_gen_span j)
  exact (O.wordSpan (O.weight i + O.weight j)).sub_mem hji hij

/-- Swapping two adjacent letters inside a larger augmentation word changes the word by an
element of the word span at the same total weight.

This is the local collection move needed to turn arbitrary augmentation words into ordered
Jennings monomials modulo the high-weight span. -/
lemma adjacent_swap_span
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r))
    (i j : Fin O.r) :
    O.wordEval (u ++ j :: i :: v) - O.wordEval (u ++ i :: j :: v) ∈
      O.wordSpan (O.wordWeight u + (O.weight i + O.weight j) + O.wordWeight v) := by
  have hprefix :
      O.wordEval u ∈ O.wordSpan (O.wordWeight u) :=
    O.word_eval_span u le_rfl
  have hmiddle :
      O.wordEval [j, i] - O.wordEval [i, j] ∈
        O.wordSpan (O.weight i + O.weight j) := by
    simpa [wordEval, Nat.add_comm] using O.swap_defect_span i j
  have hsuffix :
      O.wordEval v ∈ O.wordSpan (O.wordWeight v) :=
    O.word_eval_span v le_rfl
  have hleft :
      O.wordEval u * (O.wordEval [j, i] - O.wordEval [i, j]) ∈
        O.wordSpan (O.wordWeight u + (O.weight i + O.weight j)) :=
    O.mul_word_span hprefix hmiddle
  have htotal :
      O.wordEval u * (O.wordEval [j, i] - O.wordEval [i, j]) *
          O.wordEval v ∈
        O.wordSpan (O.wordWeight u + (O.weight i + O.weight j) + O.wordWeight v) :=
    O.mul_word_span hleft hsuffix
  have hrewrite :
      O.wordEval (u ++ j :: i :: v) - O.wordEval (u ++ i :: j :: v) =
        O.wordEval u * (O.wordEval [j, i] - O.wordEval [i, j]) *
          O.wordEval v := by
    calc
      O.wordEval (u ++ j :: i :: v) - O.wordEval (u ++ i :: j :: v) =
          O.wordEval u * O.wordEval ([j, i] ++ v) -
            O.wordEval u * O.wordEval ([i, j] ++ v) := by
            simp [O.wordEval_append]
      _ =
          O.wordEval u * (O.wordEval [j, i] * O.wordEval v) -
            O.wordEval u * (O.wordEval [i, j] * O.wordEval v) := by
            rw [O.wordEval_append [j, i] v, O.wordEval_append [i, j] v]
      _ =
          O.wordEval u * (O.wordEval [j, i] - O.wordEval [i, j]) *
            O.wordEval v := by
            simp [mul_sub, sub_mul, mul_assoc]
  simpa [hrewrite]
    using htotal

/-- Adjacent swaps are high-weight with respect to the actual word weight of the word being
swapped. -/
lemma adjacent_swap_sub
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r))
    (i j : Fin O.r) :
    O.wordEval (u ++ j :: i :: v) - O.wordEval (u ++ i :: j :: v) ∈
      O.wordSpan (O.wordWeight (u ++ j :: i :: v)) := by
  have h :=
    O.adjacent_swap_span u v i j
  simpa [
    O.wordWeight_append,
    wordWeight,
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ] using h

/-- Adjacent swaps preserve total word weight. -/
lemma word_adjacent_swap
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r))
    (i j : Fin O.r) :
    O.wordWeight (u ++ j :: i :: v) =
      O.wordWeight (u ++ i :: j :: v) := by
  simp [
    wordWeight,
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ]

/-- Congruence of algebra elements modulo the ordered high-weight word span. -/
def AlgebraCongruentSpan
    (O : OZReps (p := p) Q m)
    (s : ℕ)
    (x y : denseGroupAlgebra p Q) : Prop :=
  x - y ∈ O.wordSpan s

/-- Congruence of word evaluations modulo the ordered high-weight word span. -/
def CongruentModSpan
    (O : OZReps (p := p) Q m)
    (s : ℕ)
    (w₁ w₂ : List (Fin O.r)) : Prop :=
  O.AlgebraCongruentSpan s (O.wordEval w₁) (O.wordEval w₂)

lemma algebra_congruent_refl
    (O : OZReps (p := p) Q m)
    (s : ℕ)
    (x : denseGroupAlgebra p Q) :
    O.AlgebraCongruentSpan s x x := by
  simp [AlgebraCongruentSpan]

lemma algebra_congruent_symm
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    {x y : denseGroupAlgebra p Q}
    (h : O.AlgebraCongruentSpan s x y) :
    O.AlgebraCongruentSpan s y x := by
  dsimp [AlgebraCongruentSpan] at h ⊢
  have hneg : -(x - y) ∈ O.wordSpan s :=
    (O.wordSpan s).neg_mem h
  convert hneg using 1
  abel

lemma algebra_congruent_trans
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    {x y z : denseGroupAlgebra p Q}
    (hxy : O.AlgebraCongruentSpan s x y)
    (hyz : O.AlgebraCongruentSpan s y z) :
    O.AlgebraCongruentSpan s x z := by
  dsimp [AlgebraCongruentSpan] at hxy hyz ⊢
  have hadd : (x - y) + (y - z) ∈ O.wordSpan s :=
    (O.wordSpan s).add_mem hxy hyz
  convert hadd using 1
  abel

lemma algebra_congruent_antitone
    (O : OZReps (p := p) Q m)
    {s t : ℕ}
    {x y : denseGroupAlgebra p Q}
    (hst : s ≤ t)
    (h : O.AlgebraCongruentSpan t x y) :
    O.AlgebraCongruentSpan s x y :=
  O.wordSpan_antitone hst h

lemma algebra_congruent_left
    (O : OZReps (p := p) Q m)
    {s t : ℕ}
    {a x y : denseGroupAlgebra p Q}
    (ha : a ∈ O.wordSpan t)
    (hxy : O.AlgebraCongruentSpan s x y) :
    O.AlgebraCongruentSpan (t + s) (a * x) (a * y) := by
  dsimp [AlgebraCongruentSpan] at hxy ⊢
  have hmul : a * (x - y) ∈ O.wordSpan (t + s) :=
    O.mul_word_span ha hxy
  simpa [mul_sub] using hmul

lemma algebra_congruent_mod
    (O : OZReps (p := p) Q m)
    {s t : ℕ}
    {a x y : denseGroupAlgebra p Q}
    (hxy : O.AlgebraCongruentSpan s x y)
    (ha : a ∈ O.wordSpan t) :
    O.AlgebraCongruentSpan (s + t) (x * a) (y * a) := by
  dsimp [AlgebraCongruentSpan] at hxy ⊢
  have hmul : (x - y) * a ∈ O.wordSpan (s + t) :=
    O.mul_word_span hxy ha
  simpa [sub_mul] using hmul

lemma congruent_span_refl
    (O : OZReps (p := p) Q m)
    (s : ℕ)
    (w : List (Fin O.r)) :
    O.CongruentModSpan s w w :=
  O.algebra_congruent_refl s (O.wordEval w)

lemma congruent_span_symm
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    {w₁ w₂ : List (Fin O.r)}
    (h : O.CongruentModSpan s w₁ w₂) :
    O.CongruentModSpan s w₂ w₁ :=
  O.algebra_congruent_symm h

lemma congruent_span_trans
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    {w₁ w₂ w₃ : List (Fin O.r)}
    (h₁₂ : O.CongruentModSpan s w₁ w₂)
    (h₂₃ : O.CongruentModSpan s w₂ w₃) :
    O.CongruentModSpan s w₁ w₃ :=
  O.algebra_congruent_trans h₁₂ h₂₃

lemma congruent_span_antitone
    (O : OZReps (p := p) Q m)
    {s t : ℕ}
    {w₁ w₂ : List (Fin O.r)}
    (hst : s ≤ t)
    (h : O.CongruentModSpan t w₁ w₂) :
    O.CongruentModSpan s w₁ w₂ :=
  O.algebra_congruent_antitone hst h

lemma congruent_span_prefix
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    (u w₁ w₂ : List (Fin O.r))
    (h : O.CongruentModSpan s w₁ w₂) :
    O.CongruentModSpan (O.wordWeight u + s) (u ++ w₁) (u ++ w₂) := by
  simpa [CongruentModSpan, O.wordEval_append] using
    O.algebra_congruent_left
      (O.word_eval_span u le_rfl)
      h

lemma congruent_span_suffix
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    (w₁ w₂ v : List (Fin O.r))
    (h : O.CongruentModSpan s w₁ w₂) :
    O.CongruentModSpan (s + O.wordWeight v) (w₁ ++ v) (w₂ ++ v) := by
  simpa [CongruentModSpan, O.wordEval_append] using
    O.algebra_congruent_mod
      h
      (O.word_eval_span v le_rfl)

lemma congruent_span_context
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    (u w₁ w₂ v : List (Fin O.r))
    (h : O.CongruentModSpan s w₁ w₂) :
    O.CongruentModSpan
      (O.wordWeight u + s + O.wordWeight v)
      (u ++ w₁ ++ v)
      (u ++ w₂ ++ v) := by
  have hprefix :
      O.CongruentModSpan (O.wordWeight u + s)
        (u ++ w₁) (u ++ w₂) :=
    O.congruent_span_prefix u w₁ w₂ h
  simpa [List.append_assoc, Nat.add_assoc] using
    O.congruent_span_suffix (u ++ w₁) (u ++ w₂) v hprefix

lemma pth_congruent_span
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r))
    (i : Fin O.r) :
    O.AlgebraCongruentSpan
      (O.wordWeight u + p * O.weight i + O.wordWeight v)
      (O.wordEval (u ++ List.replicate p i ++ v))
      0 := by
  dsimp [AlgebraCongruentSpan]
  simpa using O.pth_block_span u v i

lemma pth_block_congruent
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r))
    (i : Fin O.r) :
    O.AlgebraCongruentSpan
      (O.wordWeight (u ++ List.replicate p i ++ v))
      (O.wordEval (u ++ List.replicate p i ++ v))
      0 := by
  dsimp [AlgebraCongruentSpan]
  simpa using O.pth_span_weight u v i

lemma adjacent_congruent_span
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r))
    (i j : Fin O.r) :
    O.CongruentModSpan
      (O.wordWeight u + (O.weight i + O.weight j) + O.wordWeight v)
      (u ++ j :: i :: v)
      (u ++ i :: j :: v) := by
  simpa [CongruentModSpan, AlgebraCongruentSpan] using
    O.adjacent_swap_span u v i j

lemma adjacent_swap_congruent
    (O : OZReps (p := p) Q m)
    (u v : List (Fin O.r))
    (i j : Fin O.r) :
    O.CongruentModSpan
      (O.wordWeight (u ++ j :: i :: v))
      (u ++ j :: i :: v)
      (u ++ i :: j :: v) := by
  simpa [CongruentModSpan, AlgebraCongruentSpan] using
    O.adjacent_swap_sub u v i j

/-- Permuting a word preserves its total weight. -/
lemma word_weight_perm
    (O : OZReps (p := p) Q m)
    {w₁ w₂ : List (Fin O.r)}
    (h : w₁.Perm w₂) :
    O.wordWeight w₁ = O.wordWeight w₂ := by
  induction h with
  | nil =>
      rfl
  | cons i _h ih =>
      simpa [wordWeight] using congrArg (fun n => O.weight i + n) ih
  | swap i j w =>
      simp [
        wordWeight,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ]
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

/-- Any permutation of the letters of a word is congruent to the original word modulo the word
span at that word's total weight. This packages adjacent swaps into the global permutation step of
the PBW collection argument. -/
lemma congruent_span_perm
    (O : OZReps (p := p) Q m)
    {w₁ w₂ : List (Fin O.r)}
    (h : w₁.Perm w₂) :
    O.CongruentModSpan (O.wordWeight w₁) w₁ w₂ := by
  induction h with
  | nil =>
      exact O.congruent_span_refl (O.wordWeight []) []
  | cons i _h ih =>
      have hprefix :=
        O.congruent_span_prefix [i] _ _ ih
      simpa [
        wordWeight,
        CongruentModSpan,
        AlgebraCongruentSpan
      ] using hprefix
  | swap i j w =>
      have hswap :=
        O.adjacent_swap_congruent [] w i j
      simpa [
        wordWeight,
        CongruentModSpan,
        AlgebraCongruentSpan,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ] using hswap
  | trans h₁₂ h₂₃ ih₁₂ ih₂₃ =>
      exact
        O.congruent_span_trans ih₁₂
          (by
            simpa [O.word_weight_perm h₁₂] using ih₂₃)

/-- If `x` is congruent to an element of the high-weight word span, then `x` is itself in that
span. -/
lemma algebra_congruent_right
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    {x y : denseGroupAlgebra p Q}
    (hxy : O.AlgebraCongruentSpan s x y)
    (hy : y ∈ O.wordSpan s) :
    x ∈ O.wordSpan s := by
  dsimp [AlgebraCongruentSpan] at hxy
  have hadd : (x - y) + y ∈ O.wordSpan s :=
    (O.wordSpan s).add_mem hxy hy
  convert hadd using 1
  abel

/-- A word congruent to a word already in the high-weight word span is itself in that span. -/
lemma congruent_mod_right
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    {w₁ w₂ : List (Fin O.r)}
    (hxy : O.CongruentModSpan s w₁ w₂)
    (hy : O.wordEval w₂ ∈ O.wordSpan s) :
    O.wordEval w₁ ∈ O.wordSpan s :=
  O.algebra_congruent_right hxy hy

/-- Sorting a word by the natural order on `Fin O.r` is obtained by high-weight adjacent-swap
congruences. -/
lemma congruent_merge_sort
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r)) :
    O.CongruentModSpan
      (O.wordWeight w)
      w
      (List.mergeSort w (fun i j : Fin O.r => i ≤ j)) := by
  exact
    O.congruent_span_perm
      ((List.mergeSort_perm w (fun i j : Fin O.r => i ≤ j)).symm)

/-- Sorting by the natural order on `Fin O.r` preserves total word weight. -/
lemma word_merge_sort
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r)) :
    O.wordWeight (List.mergeSort w (fun i j : Fin O.r => i ≤ j)) =
      O.wordWeight w := by
  exact
    O.word_weight_perm
      (List.mergeSort_perm w (fun i j : Fin O.r => i ≤ j))

/-- A word which is a permutation of an ordered exponent list is congruent to that ordered
Jennings word modulo the word span at the original word weight. -/
lemma congruent_perm_list
    (O : OZReps (p := p) Q m)
    {w : List (Fin O.r)}
    {e : Fin O.r → Fin p}
    (h : w.Perm (orderedExponentList O.r e)) :
    O.CongruentModSpan
      (O.wordWeight w)
      w
      (orderedExponentList O.r e) :=
  O.congruent_span_perm h

/-- A word permuting to an ordered exponent list has the corresponding Jennings weight. -/
lemma exp_perm_list
    (O : OZReps (p := p) Q m)
    {w : List (Fin O.r)}
    {e : Fin O.r → Fin p}
    (h : w.Perm (orderedExponentList O.r e)) :
    O.wordWeight w =
      expWeight (p := p) (r := O.r) O.weight e := by
  exact
    (O.word_weight_perm h).trans
      (O.ordered_exponent_list e)

/-- The overflow PBW branch: if a word permutes to a word with `p` identical adjacent letters,
then the original word evaluation is already in the high-weight word span. -/
lemma perm_pth_block
    (O : OZReps (p := p) Q m)
    {w u v : List (Fin O.r)}
    {i : Fin O.r}
    (hperm : w.Perm (u ++ List.replicate p i ++ v)) :
    O.wordEval w ∈ O.wordSpan (O.wordWeight w) := by
  have hcong :
      O.CongruentModSpan
        (O.wordWeight w)
        w
        (u ++ List.replicate p i ++ v) :=
    O.congruent_span_perm hperm
  have hblock :
      O.wordEval (u ++ List.replicate p i ++ v) ∈
        O.wordSpan (O.wordWeight w) := by
    have hmem :=
      O.pth_span_weight u v i
    simpa [O.word_weight_perm hperm] using hmem
  exact
    O.congruent_mod_right hcong hblock

/-- A word has bounded multiplicity if no ordered generator occurs `p` times. This is the
non-overflow branch in the PBW collection argument. -/
def WordMultiplicityBounded
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r)) : Prop :=
  ∀ i : Fin O.r, w.count i < p

/-- If multiplicity is not bounded by `p`, then the word can be permuted to expose a block of
`p` equal letters. -/
lemma perm_pth_bounded
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r))
    (hnot : ¬ O.WordMultiplicityBounded w) :
    ∃ (i : Fin O.r) (u v : List (Fin O.r)),
      w.Perm (u ++ List.replicate p i ++ v) := by
  classical
  rw [WordMultiplicityBounded] at hnot
  rcases not_forall.mp hnot with ⟨i, hi_not⟩
  have hi_le : p ≤ w.count i :=
    Nat.le_of_not_gt hi_not
  refine ⟨i, [], w.diff (List.replicate p i), ?_⟩
  have hcounts :
      ∀ x ∈ List.replicate p i,
        (List.replicate p i).count x ≤ w.count x := by
    intro x hx
    have hxi : x = i := List.eq_of_mem_replicate hx
    subst x
    simpa [List.count_replicate] using hi_le
  have hperm :
      (List.replicate p i ++ w.diff (List.replicate p i)).Perm w :=
    List.subperm_append_diff_self_of_count_le hcounts
  simpa using hperm.symm

/-- Every word is either bounded by the `p`-truncation exponent, or it can be permuted to expose
a `p`-fold equal-letter block. -/
lemma or_perm_pth
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r)) :
    O.WordMultiplicityBounded w ∨
      ∃ (i : Fin O.r) (u v : List (Fin O.r)),
        w.Perm (u ++ List.replicate p i ++ v) := by
  classical
  by_cases hbounded : O.WordMultiplicityBounded w
  · exact Or.inl hbounded
  · exact Or.inr (O.perm_pth_bounded w hbounded)

/-- The exponent vector obtained from a bounded-multiplicity word by counting occurrences. -/
def exponentBoundedMultiplicity
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r))
    (hbounded : O.WordMultiplicityBounded w) :
    Fin O.r → Fin p :=
  fun i => ⟨w.count i, hbounded i⟩

@[simp]
lemma bounded_multiplicity_val
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r))
    (hbounded : O.WordMultiplicityBounded w)
    (i : Fin O.r) :
    (O.exponentBoundedMultiplicity w hbounded i).val = w.count i :=
  rfl

/-- In the non-overflow branch, the count vector gives an ordered exponent-list permutation of
the original word. -/
lemma perm_bounded_multiplicity
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r))
    (hbounded : O.WordMultiplicityBounded w) :
    w.Perm
      (orderedExponentList O.r
        (O.exponentBoundedMultiplicity w hbounded)) := by
  rw [List.perm_iff_count]
  intro i
  simp [
    ordered_exponent_count,
    exponentBoundedMultiplicity
  ]

/-- One PBW collection step in normal-form language: either the word is congruent to the ordered
monomial attached to its count vector, or a `p`-fold block makes the word evaluation high-weight. -/
lemma congruent_or_span
    (O : OZReps (p := p) Q m)
    (w : List (Fin O.r)) :
    (∃ (hbounded : O.WordMultiplicityBounded w),
      O.CongruentModSpan
        (O.wordWeight w)
        w
        (orderedExponentList O.r
          (O.exponentBoundedMultiplicity w hbounded))) ∨
      O.wordEval w ∈ O.wordSpan (O.wordWeight w) := by
  rcases O.or_perm_pth w with
    hbounded | ⟨i, u, v, hperm⟩
  · refine Or.inl ⟨hbounded, ?_⟩
    exact
      O.congruent_perm_list
        (O.perm_bounded_multiplicity w hbounded)
  · exact Or.inr (O.perm_pth_block hperm)

end OZReps

/-- If the last Zassenhaus subgroup has been killed, then a nontrivial ordered normal-form word has
some nonzero exponent of weight `< m`. -/
lemma OZReps.exists_nonzerocoord_neone
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (R : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    {q : Q}
    (hq : q ≠ 1) :
    ∃ i : Fin R.r, R.weight i < m ∧ R.wordEquiv.symm q i ≠ 0 := by
  classical
  by_contra h
  have hall :
      ∀ i : Fin R.r, R.weight i < m → R.wordEquiv.symm q i = 0 := by
    intro i hi
    by_contra hne
    exact h ⟨i, hi, hne⟩
  have hmem' :
      R.wordEquiv (R.wordEquiv.symm q) ∈ zassenhausFiltration p Q m :=
    (R.mem_iff_below (t := m) le_rfl (R.wordEquiv.symm q)).2 hall
  have hmem : q ∈ zassenhausFiltration p Q m := by
    simpa using hmem'
  have hmem_bot : q ∈ (⊥ : Subgroup Q) := by
    simpa [hbot] using hmem
  exact hq (Subgroup.mem_bot.mp hmem_bot)

/-- Reformulation of the previous lemma using the singleton exponent vector. This is the index that
should later give the nonzero Jennings-basis coordinate of `q - 1`. -/
lemma OZReps.existslow_singleexp_neone
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (R : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    {q : Q}
    (hq : q ≠ 1) :
    ∃ a : Fin R.r → Fin p,
      expWeight (p := p) (r := R.r) R.weight a < m ∧
        ∃ i : Fin R.r,
          a = jenningsExpFin (p := p) i ∧
            R.wordEquiv.symm q i ≠ 0 := by
  classical
  rcases R.exists_nonzerocoord_neone hbot hq with ⟨i, hi, hne⟩
  refine ⟨jenningsExpFin (p := p) i, ?_, ?_⟩
  · simpa using hi
  · exact ⟨i, rfl, hne⟩

/-- In the truncated normal form modulo `D_(n+1)`, a nontrivial element of `D_n`
has a nonzero normal-form exponent of exactly weight `n`. -/
lemma OZReps.existsweight_eqmem_dneone
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {n : ℕ}
    (R : OZReps (p := p) Q (n + 1))
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hq : q ≠ 1) :
    ∃ i : Fin R.r, R.weight i = n ∧ R.wordEquiv.symm q i ≠ 0 := by
  classical
  have hqD' :
      R.wordEquiv (R.wordEquiv.symm q) ∈ zassenhausFiltration p Q n := by
    simpa using hqD
  have hzero_below :
      ∀ i : Fin R.r, R.weight i < n → R.wordEquiv.symm q i = 0 :=
    (R.mem_iff_below (t := n) (Nat.le_succ n) (R.wordEquiv.symm q)).1 hqD'
  rcases R.exists_nonzerocoord_neone hbot hq with ⟨i, hi_lt, hi_ne⟩
  refine ⟨i, ?_, hi_ne⟩
  have hnot_lt : ¬ R.weight i < n := by
    intro hi
    exact hi_ne (hzero_below i hi)
  have hle : R.weight i ≤ n := Nat.le_of_lt_succ hi_lt
  have hge : n ≤ R.weight i := le_of_not_gt hnot_lt
  exact le_antisymm hle hge


end Submission
