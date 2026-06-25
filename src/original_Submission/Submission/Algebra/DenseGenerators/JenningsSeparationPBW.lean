import Submission.Algebra.DenseGenerators.JenningsSeparation
import Submission.Algebra.TruncatedJennings.OrderedWords
import Submission.Algebra.TruncatedJennings.CyclicFiltrationBasis

open scoped Topology Pointwise BigOperators

noncomputable section

namespace Submission

universe u v

/-- The index type for Jennings monomials associated to `r` ordered generators. -/
abbrev JenningsIndex (p r : ℕ) : Type :=
  Fin r → Fin p

/-- The element `1 : Fin p`, using primality of `p`. -/
def finOnePrime (p : ℕ) [Fact p.Prime] : Fin p :=
  ⟨1, (Fact.out : Nat.Prime p).one_lt⟩

/-- The zero multi-index. -/
def zeroExponent (p r : ℕ) [Fact p.Prime] : JenningsIndex p r :=
  fun _ => 0

/-- The multi-index with a single `1` at coordinate `i`. -/
def oneHotExponent (p : ℕ) [Fact p.Prime] {r : ℕ} (i : Fin r) :
    JenningsIndex p r :=
  fun j => if j = i then finOnePrime p else 0

/-- The Jennings weight of a multi-index. -/
def jenningsWeight {p r : ℕ}
    (weight : Fin r → ℕ)
    (e : JenningsIndex p r) : ℕ :=
  ∑ i : Fin r, (e i).val * weight i

/-- The Jennings monomial
`([x₀]-1)^e₀ ... ([x_{r-1}]-1)^e_{r-1}`. -/
def jenningsMonomial
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (gen : Fin r → Q)
    (e : JenningsIndex p r) :
    denseGroupAlgebra p Q :=
  finOrderedProd r
    (fun i : Fin r => (groupAlgebraSub p Q (gen i)) ^ (e i).val)

/-- The high-weight span associated to a Jennings basis. -/
abbrev jenningsHighSpan
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q))
    (weight : Fin r → ℕ)
    (s : ℕ) :
    Submodule (ZMod p) (denseGroupAlgebra p Q) :=
  basisHighSpan (p := p) (Q := Q) B
    (jenningsWeight (p := p) weight) s

/-- The coefficient appearing in the expansion
`∏ᵢ (1 + Yᵢ)^{eᵢ}`. -/
def jenningsBinomialCoefficient {p r : ℕ}
    (e f : JenningsIndex p r) : ZMod p :=
  ∏ i : Fin r, (Nat.choose (e i).val (f i).val : ZMod p)

/-- The group element measuring the error in swapping `x` and `y`. -/
def swapComm {G : Type u} [Group G] (x y : G) : G :=
  (x * y)⁻¹ * (y * x)

section BasicCombinatorics

theorem fin_ne_zero
    (p : ℕ) [Fact p.Prime] :
    finOnePrime p ≠ 0 := by
  intro h
  have hval := congrArg Fin.val h
  simp [finOnePrime] at hval

theorem zeroExponent_apply
    (p r : ℕ) [Fact p.Prime]
    (i : Fin r) :
    zeroExponent p r i = 0 := by
  rfl

theorem zero_exponent
    {p r : ℕ} [Fact p.Prime]
    {e : JenningsIndex p r} :
    e = zeroExponent p r ↔ ∀ i, e i = 0 := by
  constructor
  · intro h i
    rw [h]
    rfl
  · intro h
    funext i
    exact h i

theorem hot_exponent_self
    {p r : ℕ} [Fact p.Prime]
    (i : Fin r) :
    oneHotExponent p i i = finOnePrime p := by
  simp [oneHotExponent]

theorem hot_exponent_ne
    {p r : ℕ} [Fact p.Prime]
    (i : Fin r) :
    oneHotExponent p i ≠ zeroExponent p r := by
  intro h
  have hi := congrFun h i
  rw [hot_exponent_self, zeroExponent_apply] at hi
  exact fin_ne_zero p hi

theorem jenningsWeight_zero
    {p r : ℕ} [Fact p.Prime]
    (weight : Fin r → ℕ) :
    jenningsWeight (p := p) weight (zeroExponent p r) = 0 := by
  simp [jenningsWeight, zeroExponent]

theorem jennings_one_hot
    {p r : ℕ} [Fact p.Prime]
    (weight : Fin r → ℕ)
    (i : Fin r) :
    jenningsWeight (p := p) weight (oneHotExponent p i) = weight i := by
  classical
  rw [jenningsWeight, Finset.sum_eq_single i]
  · simp [oneHotExponent, finOnePrime]
  · intro j _hj hji
    simp [oneHotExponent, hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem jennings_weight_hot
    {p r m : ℕ} [Fact p.Prime]
    {weight : Fin r → ℕ}
    (weight_lt : ∀ i, weight i < m)
    (i : Fin r) :
    jenningsWeight (p := p) weight (oneHotExponent p i) < m := by
  simpa [jennings_one_hot] using weight_lt i

theorem jennings_ne_zero
    {p r : ℕ} [Fact p.Prime]
    {weight : Fin r → ℕ}
    (weight_pos : ∀ i, 0 < weight i)
    {e : JenningsIndex p r}
    (he : e ≠ zeroExponent p r) :
    1 ≤ jenningsWeight (p := p) weight e := by
  have hexists : ∃ i, e i ≠ 0 := by
    by_contra h
    apply he
    rw [zero_exponent]
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  rcases hexists with ⟨i, hi⟩
  have hval : 0 < (e i).val := by
    exact Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
  have hterm : 1 ≤ (e i).val * weight i := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hval.ne' (weight_pos i).ne')
  exact hterm.trans (Finset.single_le_sum (fun j _ => Nat.zero_le ((e j).val * weight j))
    (Finset.mem_univ i))

theorem jennings_below_ne
    {p r t : ℕ} [Fact p.Prime]
    {weight : Fin r → ℕ}
    {e f : JenningsIndex p r}
    (hzero : ∀ i, weight i < t → e i = 0)
    (hfne : f ≠ zeroExponent p r)
    (hle : ∀ i, (f i).val ≤ (e i).val) :
    t ≤ jenningsWeight (p := p) weight f := by
  have hexists : ∃ i, f i ≠ 0 := by
    by_contra h
    apply hfne
    rw [zero_exponent]
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  rcases hexists with ⟨i, hi⟩
  have hval : 0 < (f i).val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
  have hweight : t ≤ weight i := by
    by_contra hnot
    have hei : e i = 0 := hzero i (Nat.lt_of_not_ge hnot)
    have : (f i).val = 0 := Nat.eq_zero_of_le_zero (by simpa [hei] using hle i)
    exact hi (Fin.ext this)
  have hterm : weight i ≤ (f i).val * weight i := by
    simpa [one_mul] using Nat.mul_le_mul_right (weight i) (Nat.succ_le_of_lt hval)
  exact hweight.trans (hterm.trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((f j).val * weight j))
      (Finset.mem_univ i)))

theorem jennings_binomial_support
    {p r : ℕ} [Fact p.Prime]
    {e f : JenningsIndex p r}
    (hcoeff : jenningsBinomialCoefficient (p := p) e f ≠ 0) :
    ∀ i, (f i).val ≤ (e i).val := by
  intro i
  exact jennings_expansion_coord
    (p := p) (e := e) (a := f) (by simpa [jenningsBinomialCoefficient,
      jenningsExpansionCoeff] using hcoeff) i

end BasicCombinatorics

section OrderedWords

theorem ordered_fin_zero
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q) :
    orderedWordFin (p := p) (r := r) gen (zeroExponent p r) = 1 := by
  unfold orderedWordFin orderedWord
  apply fin_ordered_forall
  intro i
  simp [zeroExponent]

theorem word_zero_one
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e) :
    wordEquiv (zeroExponent p r) = 1 := by
  rw [wordEquiv_apply]
  exact ordered_fin_zero gen

theorem ordered_fin_bijective
    {p r : ℕ}
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e) :
    Function.Bijective
      (fun e : JenningsIndex p r =>
        orderedWordFin (p := p) (r := r) gen e) := by
  constructor
  · intro e f h
    apply wordEquiv.injective
    simpa [wordEquiv_apply] using h
  · intro q
    refine ⟨wordEquiv.symm q, ?_⟩
    change orderedWordFin (p := p) (r := r) gen (wordEquiv.symm q) = q
    rw [← wordEquiv_apply]
    simp

theorem ordered_word_fin
    {p r : ℕ}
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e)
    (e f : JenningsIndex p r) :
    orderedWordFin (p := p) (r := r) gen e =
      orderedWordFin (p := p) (r := r) gen f ↔
      e = f := by
  constructor
  · intro h
    exact (ordered_fin_bijective wordEquiv wordEquiv_apply).1 h
  · exact congrArg _

theorem ordered_fin_one
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e)
    (e : JenningsIndex p r) :
    orderedWordFin (p := p) (r := r) gen e = 1 ↔
      e = zeroExponent p r := by
  rw [← ordered_fin_zero (p := p) gen]
  exact ordered_word_fin wordEquiv wordEquiv_apply e (zeroExponent p r)

theorem nonzero_coordinate_symm
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e)
    {q : Q}
    (hq : q ≠ 1) :
    ∃ i : Fin r, (wordEquiv.symm q) i ≠ 0 := by
  by_contra h
  apply hq
  have heq : wordEquiv.symm q = zeroExponent p r := by
    rw [zero_exponent]
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hword :
      orderedWordFin (p := p) (r := r) gen (wordEquiv.symm q) = 1 := by
    rw [ordered_fin_one wordEquiv wordEquiv_apply]
    exact heq
  simpa [← wordEquiv_apply] using hword

end OrderedWords

section JenningsBasis

theorem jenningsMonomial_zero
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q) :
    jenningsMonomial (p := p) (Q := Q) gen (zeroExponent p r) = 1 := by
  unfold jenningsMonomial
  apply fin_ordered_forall
  intro i
  simp [zeroExponent]

theorem jennings_monomial_hot
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (i : Fin r) :
    jenningsMonomial (p := p) (Q := Q) gen (oneHotExponent p i) =
      groupAlgebraSub p Q (gen i) := by
  classical
  unfold jenningsMonomial
  rw [TJennin.fin_single_off _ i]
  · simp [oneHotExponent, finOnePrime]
  · intro j hji
    simp [oneHotExponent, hji]

theorem jennings_monomial_independent
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e) :
    LinearIndependent (ZMod p)
      (fun e : JenningsIndex p r =>
        jenningsMonomial (p := p) (Q := Q) gen e) := by
  classical
  letI : Fintype Q := Fintype.ofEquiv (JenningsIndex p r) wordEquiv
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
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
            (Set.range fun e : JenningsIndex p r =>
              jenningsMonomial (p := p) (Q := Q) gen e) := by
        apply Submodule.span_le.2
        intro y hy
        rcases hy with ⟨q, rfl⟩
        have hexp :=
          algebra_jennings_monomial
            (p := p) (Q := Q) gen (wordEquiv.symm q)
        have hword :
            orderedWordFin gen (wordEquiv.symm q) = q := by
          rw [← wordEquiv_apply]
          simp
        rw [hword] at hexp
        change denseGeneratorsElement p Q q ∈
          Submodule.span (ZMod p)
            (Set.range fun e : JenningsIndex p r =>
              jenningsMonomial (p := p) (Q := Q) gen e)
        rw [hexp]
        apply Submodule.sum_mem
        intro e _he
        exact Submodule.smul_mem _ _
          (Submodule.subset_span ⟨e, by simp [jenningsMonomial,
            jenningsMonomialFin]⟩)
  · calc
      Fintype.card (JenningsIndex p r) = Fintype.card Q :=
        Fintype.card_congr wordEquiv
      _ = Module.finrank (ZMod p) (denseGroupAlgebra p Q) := by
        exact (Module.finrank_finsupp_self (ZMod p) (ι := Q)).symm

theorem jennings_monomial_top
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e) :
    Submodule.span (ZMod p)
      (Set.range
        (fun e : JenningsIndex p r =>
          jenningsMonomial (p := p) (Q := Q) gen e)) = ⊤ := by
  classical
  letI : Fintype Q := Fintype.ofEquiv (JenningsIndex p r) wordEquiv
  apply top_unique
  calc
    ⊤ =
        Submodule.span (ZMod p)
          (Set.range
            (Finsupp.basisSingleOne : Module.Basis Q (ZMod p)
              (denseGroupAlgebra p Q))) :=
      (Finsupp.basisSingleOne : Module.Basis Q (ZMod p)
        (denseGroupAlgebra p Q)).span_eq.symm
    _ ≤
        Submodule.span (ZMod p)
          (Set.range fun e : JenningsIndex p r =>
            jenningsMonomial (p := p) (Q := Q) gen e) := by
      apply Submodule.span_le.2
      intro y hy
      rcases hy with ⟨q, rfl⟩
      have hexp :=
        algebra_jennings_monomial
          (p := p) (Q := Q) gen (wordEquiv.symm q)
      have hword :
          orderedWordFin gen (wordEquiv.symm q) = q := by
        rw [← wordEquiv_apply]
        simp
      rw [hword] at hexp
      change denseGeneratorsElement p Q q ∈
        Submodule.span (ZMod p)
          (Set.range fun e : JenningsIndex p r =>
            jenningsMonomial (p := p) (Q := Q) gen e)
      rw [hexp]
      apply Submodule.sum_mem
      intro e _he
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨e, by simp [jenningsMonomial,
          jenningsMonomialFin]⟩)

theorem jennings_monomial
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e) :
    ∃ B : Module.Basis (JenningsIndex p r) (ZMod p)
        (denseGroupAlgebra p Q),
      ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e := by
  classical
  let B :=
    Module.Basis.mk
      (jennings_monomial_independent gen wordEquiv wordEquiv_apply)
      (by rw [jennings_monomial_top gen wordEquiv wordEquiv_apply])
  refine ⟨B, ?_⟩
  intro e
  simp [B]

theorem repr_jenningsMonomial
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    (hB : ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e)
    (e f : JenningsIndex p r) :
    B.repr (jenningsMonomial (p := p) (Q := Q) gen e) f =
      if f = e then (1 : ZMod p) else 0 := by
  rw [← hB e, B.repr_self]
  simp [Finsupp.single_apply, eq_comm]

end JenningsBasis

section HighWeightSpans

theorem jennings_high_antitone
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q))
    (weight : Fin r → ℕ)
    {s t : ℕ}
    (hst : s ≤ t) :
    jenningsHighSpan (p := p) (Q := Q) B weight t ≤
      jenningsHighSpan (p := p) (Q := Q) B weight s := by
  exact basis_high_antitone (B := B)
    (wt := jenningsWeight (p := p) weight) hst

theorem jennings_high_top
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q))
    (weight : Fin r → ℕ) :
    jenningsHighSpan (p := p) (Q := Q) B weight 0 = ⊤ := by
  apply top_unique
  rw [← B.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨e, rfl⟩
  exact ⟨e, Nat.zero_le _, rfl⟩

theorem jennings_high_repr
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q))
    (weight : Fin r → ℕ)
    (s : ℕ)
    (x : denseGroupAlgebra p Q) :
    x ∈ jenningsHighSpan (p := p) (Q := Q) B weight s ↔
      ∀ e : JenningsIndex p r,
        jenningsWeight (p := p) weight e < s →
          B.repr x e = 0 := by
  exact basis_high_repr B
    (jenningsWeight (p := p) weight)

theorem repr_high_span
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    {weight : Fin r → ℕ}
    {s : ℕ}
    {x : denseGroupAlgebra p Q}
    (hx : x ∈ jenningsHighSpan (p := p) (Q := Q) B weight s)
    {e : JenningsIndex p r}
    (he : jenningsWeight (p := p) weight e < s) :
    B.repr x e = 0 := by
  exact basis_repr_high
    (B := B) (wt := jenningsWeight (p := p) weight) hx he

theorem jennings_monomial_span
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    {weight : Fin r → ℕ}
    (hB : ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e)
    {s : ℕ}
    {e : JenningsIndex p r}
    (he : s ≤ jenningsWeight (p := p) weight e) :
    jenningsMonomial (p := p) (Q := Q) gen e ∈
      jenningsHighSpan (p := p) (Q := Q) B weight s := by
  rw [← hB e]
  exact basis_high_weight B (jenningsWeight (p := p) weight) he

end HighWeightSpans

section GroupAlgebraExpansion

theorem canonical_fin_prod
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (e : JenningsIndex p r) :
    denseGeneratorsElement p Q
        (orderedWordFin (p := p) (r := r) gen e) =
      finOrderedProd r
        (fun i : Fin r =>
          (denseGeneratorsElement p Q (gen i)) ^
            (e i).val) := by
  unfold orderedWordFin orderedWord
  rw [algebra_fin_prod]
  apply congrArg
  funext i
  simp

theorem canonical_fin_sub
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (e : JenningsIndex p r) :
    denseGeneratorsElement p Q
        (orderedWordFin (p := p) (r := r) gen e) =
      finOrderedProd r
        (fun i : Fin r =>
          (1 + groupAlgebraSub p Q (gen i)) ^ (e i).val) := by
  exact algebra_fin_sub gen e

theorem sub_fin_prod
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (e : JenningsIndex p r) :
    groupAlgebraSub p Q (orderedWordFin (p := p) (r := r) gen e) =
      finOrderedProd r
        (fun i : Fin r =>
          (1 + groupAlgebraSub p Q (gen i)) ^ (e i).val) - 1 := by
  rw [groupAlgebraSub,
    canonical_fin_sub gen e]

theorem repr_canonical_fin
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    (hB : ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e)
    (e f : JenningsIndex p r) :
    B.repr
        (denseGeneratorsElement p Q
          (orderedWordFin (p := p) (r := r) gen e)) f =
      jenningsBinomialCoefficient (p := p) e f := by
  rw [algebra_jennings_monomial]
  simp_rw [show ∀ a : JenningsIndex p r,
      jenningsMonomialFin p Q gen a = B a by
    intro a
    rw [hB]
    rfl]
  simpa [jenningsBinomialCoefficient, jenningsExpansionCoeff] using
    (repr_fintype_sum
      (B := B)
      (c := fun a : JenningsIndex p r =>
        jenningsExpansionCoeff (p := p) e a)
      (i := f))

theorem repr_sub_fin
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    (hB : ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e)
    (e f : JenningsIndex p r) :
    B.repr
        (groupAlgebraSub p Q
          (orderedWordFin (p := p) (r := r) gen e)) f =
      jenningsBinomialCoefficient (p := p) e f -
        (if f = zeroExponent p r then (1 : ZMod p) else 0) := by
  rw [groupAlgebraSub, map_sub]
  change
    B.repr
          (denseGeneratorsElement p Q
            (orderedWordFin (p := p) (r := r) gen e)) f -
        B.repr 1 f =
      jenningsBinomialCoefficient (p := p) e f -
        (if f = zeroExponent p r then (1 : ZMod p) else 0)
  rw [repr_canonical_fin hB]
  have hone :
      (1 : denseGroupAlgebra p Q) =
        jenningsMonomial (p := p) (Q := Q) gen (zeroExponent p r) := by
    symm
    exact jenningsMonomial_zero gen
  rw [hone, repr_jenningsMonomial hB]

theorem repr_fin_hot
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    (hB : ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e)
    (e : JenningsIndex p r)
    (i : Fin r) :
    B.repr
        (groupAlgebraSub p Q
          (orderedWordFin (p := p) (r := r) gen e))
        (oneHotExponent p i) =
      ((e i).val : ZMod p) := by
  rw [repr_sub_fin hB]
  simp only [hot_exponent_ne, if_false, sub_zero]
  rw [jenningsBinomialCoefficient, Finset.prod_eq_single i]
  · simp [oneHotExponent, finOnePrime]
  · intro j _hj hji
    simp [oneHotExponent, hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem repr_hot_ne
    {p r : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    (hB : ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e)
    {e : JenningsIndex p r}
    {i : Fin r}
    (hi : e i ≠ 0) :
    B.repr
        (groupAlgebraSub p Q
          (orderedWordFin (p := p) (r := r) gen e))
        (oneHotExponent p i) ≠ 0 := by
  rw [repr_fin_hot hB]
  exact zmod_nat_val hi

theorem fin_high_below
    {p r t : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {weight : Fin r → ℕ}
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    (hB : ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e)
    {e : JenningsIndex p r}
    (hzero : ∀ i, weight i < t → e i = 0) :
    groupAlgebraSub p Q
        (orderedWordFin (p := p) (r := r) gen e) ∈
      jenningsHighSpan (p := p) (Q := Q) B weight t := by
  rw [jennings_high_repr]
  intro f hf
  rw [repr_sub_fin hB]
  by_cases hfzero : f = zeroExponent p r
  · subst f
    simp [jenningsBinomialCoefficient, zeroExponent]
  · rw [if_neg hfzero, sub_zero]
    by_contra hcoeff
    have hle :
        ∀ i, (f i).val ≤ (e i).val :=
      jennings_binomial_support hcoeff
    have ht :
        t ≤ jenningsWeight (p := p) weight f :=
      jennings_below_ne hzero hfzero hle
    omega

end GroupAlgebraExpansion

section ZassenhausFiltration

theorem zassenhaus_filtration_pow
    {p : ℕ}
    {G : Type u} [Group G]
    {n i j : ℕ}
    {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hn : n ≤ (i + 1) * p ^ j) :
    x ^ (p ^ j) ∈ zassenhausFiltration p G n := by
  exact
    zassenhausFiltration_antitone p G hn
      (lower_central_filtration (p := p) hx)

theorem high_span_zassenhaus
    {p r m : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {weight : Fin r → ℕ}
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e)
    (mem_iff_below :
      ∀ {t : ℕ} (_ht : t ≤ m) (e : JenningsIndex p r),
        wordEquiv e ∈ zassenhausFiltration p Q t ↔
          ∀ i, weight i < t → e i = 0)
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    (hB : ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e)
    {t : ℕ}
    (ht : t ≤ m)
    {q : Q}
    (hq : q ∈ zassenhausFiltration p Q t) :
    groupAlgebraSub p Q q ∈
      jenningsHighSpan (p := p) (Q := Q) B weight t := by
  let e : JenningsIndex p r := wordEquiv.symm q
  have heq : q = orderedWordFin (p := p) (r := r) gen e := by
    rw [← wordEquiv_apply]
    exact (wordEquiv.apply_symm_apply q).symm
  rw [heq]
  apply fin_high_below hB
  exact
    (mem_iff_below ht e).mp
      (by simpa [e] using hq)

theorem sub_high_min
    {p r m : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {weight : Fin r → ℕ}
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e)
    (mem_iff_below :
      ∀ {t : ℕ} (_ht : t ≤ m) (e : JenningsIndex p r),
        wordEquiv e ∈ zassenhausFiltration p Q t ↔
          ∀ i, weight i < t → e i = 0)
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    (hB : ∀ e, B e = jenningsMonomial (p := p) (Q := Q) gen e)
    {s : ℕ}
    {q : Q}
    (hq : q ∈ zassenhausFiltration p Q s) :
    groupAlgebraSub p Q q ∈
      jenningsHighSpan (p := p) (Q := Q) B weight (min s m) := by
  apply
    high_span_zassenhaus
      wordEquiv wordEquiv_apply mem_iff_below hB (min_le_right s m)
  exact zassenhausFiltration_antitone p Q (min_le_left s m) hq

theorem filtration_bot_fields
    {p r m : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {gen : Fin r → Q}
    {weight : Fin r → ℕ}
    (weight_lt : ∀ i, weight i < m)
    (wordEquiv : JenningsIndex p r ≃ Q)
    (wordEquiv_apply :
      ∀ e, wordEquiv e = orderedWordFin (p := p) (r := r) gen e)
    (mem_iff_below :
      ∀ {t : ℕ} (_ht : t ≤ m) (e : JenningsIndex p r),
        wordEquiv e ∈ zassenhausFiltration p Q t ↔
          ∀ i, weight i < t → e i = 0) :
    zassenhausFiltration p Q m = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  let e : JenningsIndex p r := wordEquiv.symm q
  have hzero : ∀ i, e i = 0 := by
    have hcoords :=
      (mem_iff_below (le_refl m) e).mp
        (by simpa [e] using hq)
    intro i
    exact hcoords i (weight_lt i)
  have he : e = zeroExponent p r := zero_exponent.mpr hzero
  calc
    q = wordEquiv e := by simp [e]
    _ = wordEquiv (zeroExponent p r) := by rw [he]
    _ = 1 := word_zero_one wordEquiv wordEquiv_apply

end ZassenhausFiltration

section FinalAssembly

theorem mk_separation_basis
    {p r m : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {B : Module.Basis (JenningsIndex p r) (ZMod p)
      (denseGroupAlgebra p Q)}
    {weight : Fin r → ℕ}
    (haug :
      augmentationIdealPower p Q m ≤
        jenningsHighSpan (p := p) (Q := Q) B weight m)
    (hsep :
      ∀ {q : Q}, q ≠ 1 →
        ∃ e : JenningsIndex p r,
          jenningsWeight (p := p) weight e < m ∧
            B.repr (groupAlgebraSub p Q q) e ≠ 0) :
    Nonempty (JSData.{u, 0} (p := p) Q m) := by
  classical
  exact
    ⟨{ ι := JenningsIndex p r
       decEq := inferInstance
       basis := B
       weight := jenningsWeight (p := p) weight
       aug_power := haug
       separates := hsep }⟩

theorem reps_filtration_bot
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m) :
    zassenhausFiltration p Q m = ⊥ := by
  exact
    filtration_bot_fields
      O.weight_lt O.wordEquiv O.wordEquiv_apply O.mem_iff_below

end FinalAssembly

end Submission
