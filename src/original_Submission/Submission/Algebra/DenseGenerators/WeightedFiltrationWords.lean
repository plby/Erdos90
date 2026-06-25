import Submission.Algebra.DenseGenerators.OrderedJennings
import Submission.Algebra.DenseGenerators.WeightedConjugation


open scoped commutatorElement

noncomputable section

namespace Submission

universe u

namespace WFilt

/-- Left multiplication by a group-basis element preserves weight once its augmentation
letter has a declared weight. -/
lemma ga_mul_mem
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {wx r : ℕ}
    (hx : groupAlgebraSub p G x ∈ W.J wx)
    {a : denseGroupAlgebra p G}
    (ha : a ∈ W.J r) :
    ga p G x * a ∈ W.J r := by
  have hprod :
      groupAlgebraSub p G x * a ∈ W.J (wx + r) :=
    W.mul_mem hx ha
  have hprod' :
      groupAlgebraSub p G x * a ∈ W.J r :=
    W.anti (Nat.le_add_left r wx) hprod
  have hsum :
      groupAlgebraSub p G x * a + a ∈ W.J r :=
    (W.J r).add_mem hprod' ha
  simpa [groupAlgebraSub, ga, sub_mul] using hsum

/-- Right multiplication by a group-basis element preserves weight once its augmentation
letter has a declared weight. -/
lemma mul_ga_mem
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {wx r : ℕ}
    (hx : groupAlgebraSub p G x ∈ W.J wx)
    {a : denseGroupAlgebra p G}
    (ha : a ∈ W.J r) :
    a * ga p G x ∈ W.J r := by
  have hprod :
      a * groupAlgebraSub p G x ∈ W.J (r + wx) :=
    W.mul_mem ha hx
  have hprod' :
      a * groupAlgebraSub p G x ∈ W.J r :=
    W.anti (Nat.le_add_right r wx) hprod
  have hsum :
      a * groupAlgebraSub p G x + a ∈ W.J r :=
    (W.J r).add_mem hprod' ha
  simpa [groupAlgebraSub, ga, mul_sub] using hsum

/-- Augmentation letters of group products stay in a common filtration depth. -/
lemma algebra_sub_mul
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {r : ℕ} {x y : G}
    (hx : groupAlgebraSub p G x ∈ W.J r)
    (hy : groupAlgebraSub p G y ∈ W.J r) :
    groupAlgebraSub p G (x * y) ∈ W.J r := by
  rw [algebra_sub_left]
  exact (W.J r).add_mem (W.ga_mul_mem hx hy) hx

/-- Augmentation letters of group powers stay in a common filtration depth. -/
lemma algebra_sub_pow
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {r : ℕ} {x : G}
    (hx : groupAlgebraSub p G x ∈ W.J r)
    (n : ℕ) :
    groupAlgebraSub p G (x ^ n) ∈ W.J r := by
  induction n with
  | zero =>
      simp [groupAlgebraSub]
  | succ n ih =>
      rw [pow_succ]
      exact W.algebra_sub_mul ih hx

/-- An ordered group product stays in a common filtration depth when all of its letters do. -/
lemma algebra_sub_prod
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {r t : ℕ}
    (x : Fin r → G)
    (hx : ∀ i, groupAlgebraSub p G (x i) ∈ W.J t) :
    groupAlgebraSub p G (finOrderedProd r x) ∈ W.J t := by
  induction r with
  | zero =>
      simp [finOrderedProd, groupAlgebraSub]
  | succ r ih =>
      rw [finOrderedProd]
      exact
        W.algebra_sub_mul
          (ih (fun i : Fin r => x i.castSucc) (fun i => hx i.castSucc))
          (hx (Fin.last r))

/-- An ordered normal form using no letters below `t` has augmentation letter of weight at
least `t`. -/
lemma sub_fin_below
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {r t : ℕ}
    (gen : Fin r → G)
    (weight : Fin r → ℕ)
    (hgen :
      ∀ i, groupAlgebraSub p G (gen i) ∈ W.J (weight i))
    (e : Fin r → Fin p)
    (hzero : ∀ i, weight i < t → e i = 0) :
    groupAlgebraSub p G (orderedWordFin gen e) ∈ W.J t := by
  unfold orderedWordFin orderedWord
  apply W.algebra_sub_prod
  intro i
  by_cases hi : weight i < t
  · simp [hzero i hi, groupAlgebraSub]
  · exact
      W.algebra_sub_pow
        (W.anti (Nat.le_of_not_gt hi) (hgen i))
        (e i).val

/-- An ordered normal form has augmentation letter of weight at least `t` when every coordinate
that actually occurs is attached to a letter of weight at least `t`.

This is the form needed while constructing a descending prefix filtration: shallow letters have
not been adjoined yet, but their coordinates vanish in the deeper normal forms under
consideration. -/
lemma sub_fin_nonzero
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {r t : ℕ}
    (gen : Fin r → G)
    (weight : Fin r → ℕ)
    (e : Fin r → Fin p)
    (hgen :
      ∀ i, e i ≠ 0 →
        groupAlgebraSub p G (gen i) ∈ W.J (weight i))
    (hweight : ∀ i, e i ≠ 0 → t ≤ weight i) :
    groupAlgebraSub p G (orderedWordFin gen e) ∈ W.J t := by
  unfold orderedWordFin orderedWord
  apply W.algebra_sub_prod
  intro i
  by_cases hi : e i = 0
  · simp [hi, groupAlgebraSub]
  · exact
      W.algebra_sub_pow
        (W.anti (hweight i hi) (hgen i hi))
        (e i).val

/-- A commutator-letter estimate gives the corresponding conjugation-error estimate. -/
lemma conj_ga_sub
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x y : G} {wx wy : ℕ}
    (hy : groupAlgebraSub p G y ∈ W.J wy)
    (hcomm :
      groupAlgebraSub p G ⁅x, y⁆ ∈ W.J (wx + wy)) :
    conjGA p G x (groupAlgebraSub p G y) -
        groupAlgebraSub p G y ∈ W.J (wx + wy) := by
  rw [conj_ga_algebra]
  exact W.mul_ga_mem hy hcomm

end WFilt

/-- The span of bounded ordered Jennings monomials in a weighted generator prefix whose
total declared weight is at least `s`. -/
def jenningsMonomialSpan
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {r : ℕ}
    (gen : Fin r → G)
    (weight : Fin r → ℕ)
    (s : ℕ) :
    Submodule (ZMod p) (denseGroupAlgebra p G) :=
  Submodule.span (ZMod p)
    { a | ∃ e : Fin r → Fin p,
        s ≤ expWeight (p := p) (r := r) weight e ∧
          jenningsMonomialFin p G gen e = a }

/-- Increasing the cutoff only shrinks the bounded-prefix monomial span. -/
lemma jennings_monomial_antitone
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {r : ℕ}
    (gen : Fin r → G)
    (weight : Fin r → ℕ) :
    Antitone (jenningsMonomialSpan (p := p) gen weight) := by
  intro s t hst
  apply Submodule.span_mono
  rintro a ⟨e, he, rfl⟩
  exact ⟨e, hst.trans he, rfl⟩

/-- Appending one bounded exponent splits the declared weight into prefix and final terms. -/
@[simp]
lemma expWeight_snoc
    {p r : ℕ}
    (weight : Fin r → ℕ)
    (w : ℕ)
    (e : Fin (r + 1) → Fin p) :
    expWeight (Fin.snoc weight w) e =
      expWeight weight (fun i : Fin r => e i.castSucc) +
        (e (Fin.last r)).val * w := by
  rw [expWeight, Fin.sum_univ_castSucc]
  simp [expWeight]

/-- Appending one generator splits its ordered Jennings monomial into prefix and final
factors. -/
@[simp]
lemma jennings_monomial_snoc
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {r : ℕ}
    (gen : Fin r → G)
    (x : G)
    (e : Fin (r + 1) → Fin p) :
    jenningsMonomialFin p G (Fin.snoc gen x) e =
      jenningsMonomialFin p G gen (fun i : Fin r => e i.castSucc) *
        groupAlgebraSub p G x ^ (e (Fin.last r)).val := by
  simp [jenningsMonomialFin, finOrderedProd]

/-- An ordered Jennings monomial belongs to the sum of the declared generator weights counted
with multiplicity. -/
lemma WFilt.ordered_jenningmonomia_finmem
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G) :
    ∀ {r : ℕ}
      (gen : Fin r → G)
      (weight : Fin r → ℕ)
      (_hgen :
        ∀ i, groupAlgebraSub p G (gen i) ∈ W.J (weight i))
      (e : Fin r → Fin p),
      jenningsMonomialFin p G gen e ∈
        W.J (expWeight (p := p) (r := r) weight e)
  | 0, _gen, _weight, _hgen, _e => by
      simpa [jenningsMonomialFin, finOrderedProd, expWeight] using W.one_mem
  | r + 1, gen, weight, hgen, e => by
      rw [← Fin.snoc_init_self gen, ← Fin.snoc_init_self weight]
      rw [jennings_monomial_snoc]
      rw [expWeight_snoc]
      exact
        W.mul_mem
          (W.ordered_jenningmonomia_finmem
            (fun i : Fin r => gen i.castSucc)
            (fun i : Fin r => weight i.castSucc)
            (fun i : Fin r => hgen i.castSucc)
            (fun i : Fin r => e i.castSucc))
          (W.pow_mem (hgen (Fin.last r)) (e (Fin.last r)).val)

/-- A cyclic extension of a bounded-prefix monomial span is exactly the bounded-prefix
monomial span obtained by appending the new weighted generator. -/
lemma extend_j_monomial
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {r : ℕ}
    (gen : Fin r → G)
    (weight : Fin r → ℕ)
    (x : G)
    (w s : ℕ) :
    cyclicExtendJ
        (jenningsMonomialSpan (p := p) gen weight) x w s =
      jenningsMonomialSpan (p := p) (Fin.snoc gen x) (Fin.snoc weight w) s := by
  apply le_antisymm
  · unfold cyclicExtendJ
    refine iSup_le ?_
    intro e
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro a ⟨f, hf, rfl⟩
    change
      jenningsMonomialFin p G gen f *
          groupAlgebraSub p G x ^ (e : ℕ) ∈
        jenningsMonomialSpan (p := p) (Fin.snoc gen x) (Fin.snoc weight w) s
    apply Submodule.subset_span
    refine ⟨Fin.snoc f e, ?_, ?_⟩
    · simpa [Nat.sub_le_iff_le_add] using hf
    · simp
  · apply Submodule.span_le.mpr
    rintro a ⟨e, he, rfl⟩
    rw [jennings_monomial_snoc]
    apply extend_j
      (jennings_monomial_antitone (p := p) gen weight)
      (s := expWeight weight (fun i : Fin r => e i.castSucc))
    · apply Submodule.subset_span
      exact ⟨fun i : Fin r => e i.castSucc, le_rfl, rfl⟩
    · simpa using he

/-- The scalar base filtration is the bounded-monomial span for the empty prefix. -/
lemma j_monomial_empty
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (s : ℕ) :
    baseJ p G s =
      jenningsMonomialSpan (p := p)
        (fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i)
        s := by
  by_cases hs : s = 0
  · subst s
    simp [baseJ, jenningsMonomialSpan, expWeight,
      jenningsMonomialFin, finOrderedProd]
  · simp [baseJ, jenningsMonomialSpan, expWeight,
      jenningsMonomialFin, finOrderedProd, hs]

/-- The declared weights in a certified prefix, listed in extension order. -/
def PWFilt.extensionWeights
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] :
    {W : WFilt p G} → PWFilt p G W → List ℕ
  | _, PWFilt.base => []
  | _, PWFilt.extend P S => P.extensionWeights.concat S.w

/-- Every certified prefix filtration has an exact description as the span of bounded ordered
Jennings monomials in its extension order. -/
lemma PWFilt.existsbounded_jenningmonomia_spaneq
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (P : PWFilt p G W) :
    ∃ (r : ℕ) (gen : Fin r → G) (weight : Fin r → ℕ),
      List.ofFn weight = P.extensionWeights ∧
        ∀ s,
          W.J s =
            jenningsMonomialSpan (p := p) gen weight s := by
  induction P with
  | base =>
      refine ⟨0, (fun i : Fin 0 => Fin.elim0 i), (fun i : Fin 0 => Fin.elim0 i), ?_⟩
      exact ⟨rfl, j_monomial_empty⟩
  | @extend W P S ih =>
      rcases ih with ⟨r, gen, weight, hweight, hspan⟩
      refine ⟨r + 1, Fin.snoc gen S.x, Fin.snoc weight S.w, ?_⟩
      constructor
      · rw [List.ofFn_succ']
        simpa [PWFilt.extensionWeights] using congrArg (List.concat · S.w) hweight
      · intro s
        change cyclicExtendJ W.J S.x S.w s = _
        have hspan' :
            W.J =
              jenningsMonomialSpan (p := p) gen weight :=
          funext hspan
        rw [hspan']
        exact extend_j_monomial gen weight S.x S.w s

/-- If the augmentation letter of `x ^ p` has the expected weight, then so does the `p`th power
of the augmentation letter of `x`. -/
lemma WFilt.groupalg_subone_powprimemem
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {r : ℕ}
    (hx : groupAlgebraSub p G (x ^ p) ∈ W.J r) :
    groupAlgebraSub p G x ^ p ∈ W.J r := by
  rw [algebra_sub_prime]
  exact hx

namespace CEDataa

/-- Every old weighted element remains weighted after one certified cyclic extension. -/
lemma old_mem_next
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (S : CEDataa p G W)
    {r : ℕ}
    {a : denseGroupAlgebra p G}
    (ha : a ∈ W.J r) :
    a ∈ S.next.J r := by
  change a ∈ cyclicExtendJ W.J S.x S.w r
  exact cyclic_j_old W ha

/-- The newly adjoined augmentation letter has its declared weight in the extended filtration. -/
lemma new_mem_next
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (S : CEDataa p G W) :
    groupAlgebraSub p G S.x ∈ S.next.J S.w := by
  change groupAlgebraSub p G S.x ∈ cyclicExtendJ W.J S.x S.w S.w
  exact cyclic_extend_j W

/-- A commutator-letter estimate extends a conjugation-error estimate across one certified
cyclic layer.

This is the induction move used when letters are adjoined from deeper Zassenhaus layers toward
shallower ones: the old-prefix estimate is inherited recursively, while the error on the newest
old letter is controlled by `[x, S.x]`. -/
lemma ga_next_old
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (S : CEDataa p G W)
    {x : G} {wx r : ℕ}
    (herrorOld :
      ∀ {s : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J s →
          conjGA p G x a - a ∈ W.J (s + wx))
    (hcomm :
      groupAlgebraSub p G ⁅x, S.x⁆ ∈ S.next.J (wx + S.w))
    {a : denseGroupAlgebra p G}
    (ha : a ∈ S.next.J r) :
    conjGA p G x a - a ∈ S.next.J (r + wx) := by
  apply conj_ga_extension S herrorOld
  · simpa [Nat.add_comm] using
      (S.next.conj_ga_sub
        (x := x) (y := S.x) (wx := wx) (wy := S.w)
        S.new_mem_next hcomm)
  · exact ha

/-- Build the next cyclic-extension certificate from an overflow estimate, an old-prefix
conjugation estimate, and the commutator estimate for the newest old letter. -/
def old_error_commutator
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (S : CEDataa p G W)
    (x : G)
    (wx : ℕ)
    (hpow :
      groupAlgebraSub p G x ^ p ∈ S.next.J (p * wx))
    (herrorOld :
      ∀ {s : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J s →
          conjGA p G x a - a ∈ W.J (s + wx))
    (hcomm :
      groupAlgebraSub p G ⁅x, S.x⁆ ∈ S.next.J (wx + S.w)) :
    CEDataa p G S.next :=
  cyclic_extension_error S.next x wx hpow
    (fun ha => S.ga_next_old herrorOld hcomm ha)

/-- Group-level control of `x ^ p` is enough for the overflow input in the preceding cyclic
extension constructor. -/
def next_old_error
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (S : CEDataa p G W)
    (x : G)
    (wx : ℕ)
    (hpow :
      groupAlgebraSub p G (x ^ p) ∈ S.next.J (p * wx))
    (herrorOld :
      ∀ {s : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J s →
          conjGA p G x a - a ∈ W.J (s + wx))
    (hcomm :
      groupAlgebraSub p G ⁅x, S.x⁆ ∈ S.next.J (wx + S.w)) :
    CEDataa p G S.next :=
  S.old_error_commutator x wx
    (S.next.groupalg_subone_powprimemem hpow) herrorOld hcomm

end CEDataa

namespace PWFilt

/-- The commutator estimates needed to conjugate a certified prefix filtration by one more
weighted group element.

The base filtration contains only scalars.  At an extension step, the recursive hypothesis
controls all old coefficients and the displayed commutator estimate controls the newest
augmentation letter. -/
inductive CContro
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G)
    (wx : ℕ) :
    {W : WFilt p G} → PWFilt p G W → Prop
  | base :
      CContro x wx PWFilt.base
  | extend
      {W : WFilt p G}
      {P : PWFilt p G W}
      {S : CEDataa p G W}
      (hP : CContro x wx P)
      (hcomm :
        groupAlgebraSub p G ⁅x, S.x⁆ ∈ S.next.J (wx + S.w)) :
      CContro x wx (PWFilt.extend P S)

/-- Certified commutator control against every old prefix letter gives the required
conjugation-error estimate on the whole prefix filtration. -/
lemma CContro.conj_ga_submem
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {x : G}
    {wx : ℕ}
    {W : WFilt p G}
    {P : PWFilt p G W}
    (hP : CContro x wx P)
    {r : ℕ}
    {a : denseGroupAlgebra p G}
    (ha : a ∈ W.J r) :
    conjGA p G x a - a ∈ W.J (r + wx) := by
  induction hP generalizing r a with
  | base =>
      change a ∈ baseJ p G r at ha
      change conjGA p G x a - a ∈ baseJ p G (r + wx)
      rw [ga_self_j x ha]
      simp
  | extend hP hcomm ih =>
      exact
        CEDataa.ga_next_old
          _ ih hcomm ha

/-- Adjoin one more weighted group element once its group `p`th power has the expected
weight and its commutators with every old prefix letter satisfy the additive weight bound. -/
def extension_data_control
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (P : PWFilt p G W)
    (x : G)
    (wx : ℕ)
    (hpow :
      groupAlgebraSub p G (x ^ p) ∈ W.J (p * wx))
    (hcomm : CContro x wx P) :
    CEDataa p G W :=
  cyclic_extension_error W x wx
    (W.groupalg_subone_powprimemem hpow)
    (fun ha => hcomm.conj_ga_submem ha)

end PWFilt

/-- A Zassenhaus element has the expected augmentation weight in a partial descending prefix
filtration as soon as every nonzero normal-form coordinate is already available in that prefix. -/
lemma OZReps.groupalgsub_onememweight_filtmemnonzero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (W : WFilt p Q)
    {t : ℕ} (ht : t ≤ m)
    {q : Q} (hq : q ∈ zassenhausFiltration p Q t)
    (hgen :
      ∀ i, O.wordEquiv.symm q i ≠ 0 →
        groupAlgebraSub p Q (O.gen i) ∈ W.J (O.weight i)) :
    groupAlgebraSub p Q q ∈ W.J t := by
  let e : Fin O.r → Fin p := O.wordEquiv.symm q
  have heq : O.wordEquiv e = q :=
    O.wordEquiv.apply_symm_apply q
  have hweight : ∀ i, e i ≠ 0 → t ≤ O.weight i := by
    intro i hi
    by_contra hnot
    have hzero : e i = 0 :=
      (O.mem_iff_below ht e).mp (heq ▸ hq) i (Nat.lt_of_not_ge hnot)
    exact hi hzero
  rw [← heq, O.wordEquiv_apply]
  exact
    W.sub_fin_nonzero
      O.gen O.weight e hgen hweight

/-- In a descending prefix filtration, letters strictly above a boundary suffice to control every
strictly deeper Zassenhaus element. -/
lemma OZReps.groupalgsub_onememweight_filtmemgt
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (W : WFilt p Q)
    {b t : ℕ}
    (hbt : b < t)
    (ht : t ≤ m)
    (hgen :
      ∀ i, b < O.weight i →
        groupAlgebraSub p Q (O.gen i) ∈ W.J (O.weight i))
    {q : Q}
    (hq : q ∈ zassenhausFiltration p Q t) :
    groupAlgebraSub p Q q ∈ W.J t := by
  apply O.groupalgsub_onememweight_filtmemnonzero W ht hq
  intro i hi
  apply hgen i
  have hweight : t ≤ O.weight i := by
    by_contra hnot
    have hword :
        O.wordEquiv (O.wordEquiv.symm q) ∈ zassenhausFiltration p Q t := by
      simpa using hq
    have hzero :
        O.wordEquiv.symm q i = 0 :=
      (O.mem_iff_below ht (O.wordEquiv.symm q)).mp
        hword
        i
        (Nat.lt_of_not_ge hnot)
    exact hi hzero
  exact lt_of_lt_of_le hbt hweight

/-- The descending-prefix estimate remains valid past the killed level: in that case the group
element is already trivial. -/
lemma OZReps.groupalgsub_onememweifil_memgteqbot
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (W : WFilt p Q)
    (hbot : zassenhausFiltration p Q m = ⊥)
    {b t : ℕ}
    (hbt : b < t)
    (hgen :
      ∀ i, b < O.weight i →
        groupAlgebraSub p Q (O.gen i) ∈ W.J (O.weight i))
    {q : Q}
    (hq : q ∈ zassenhausFiltration p Q t) :
    groupAlgebraSub p Q q ∈ W.J t := by
  by_cases ht : t ≤ m
  · exact
      O.groupalgsub_onememweight_filtmemgt
        W hbt ht hgen hq
  · have hmt : m ≤ t := Nat.le_of_not_ge ht
    have hqm : q ∈ zassenhausFiltration p Q m :=
      zassenhausFiltration_antitone p Q hmt hq
    have hq_one : q = 1 := by
      apply Subgroup.mem_bot.mp
      simpa [hbot] using hqm
    simp [hq_one, groupAlgebraSub]

namespace OZReps

/-- The selected ordered representatives have the weighted `p`th-power bounds needed by the
descending cyclic-extension construction. -/
def SelectedGeneratorBound
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m) :
    Prop :=
  ∀ i, O.gen i ^ p ∈ zassenhausFiltration p Q (p * O.weight i)

/-- A prefix filtration built by adjoining weighted representatives only after every strictly
deeper representative is already available.

The stored `hdeep` field is the point of the history: when a future shallower letter is adjoined,
its commutator with `S.x` has depth strictly larger than `S.w`, so its augmentation letter can be
expanded using representatives already present at this stage. -/
inductive DPContro
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m) :
    {W : WFilt p Q} →
      PWFilt p Q W → Prop
  | base :
      DPContro O PWFilt.base
  | extend
      {W : WFilt p Q}
      {P : PWFilt p Q W}
      (hP : DPContro O P)
      (S : CEDataa p Q W)
      (hx : S.x ∈ zassenhausFiltration p Q S.w)
      (hdeep :
        ∀ i, S.w < O.weight i →
          groupAlgebraSub p Q (O.gen i) ∈ S.next.J (O.weight i)) :
      DPContro O (PWFilt.extend P S)

/-- A genuinely descending prefix history converts the additive group-level commutator law into
the algebra-level conjugation control required for one more cyclic extension. -/
lemma DPContro.commutatorControl
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    {W : WFilt p Q}
    {P : PWFilt p Q W}
    (hP : DPContro O P)
    {x : Q}
    {wx : ℕ}
    (hxpos : 0 < wx)
    (hx : x ∈ zassenhausFiltration p Q wx) :
    PWFilt.CContro x wx P := by
  induction hP with
  | base =>
      exact PWFilt.CContro.base
  | extend hP S hy hdeep ih =>
      apply PWFilt.CContro.extend ih
      exact
        O.groupalgsub_onememweifil_memgteqbot
          S.next hbot (by omega) hdeep (hcomm hx hy)

/-- Adjoin one selected representative to a descending prefix once the genuine explicit
Zassenhaus commutator and `p`-power laws are available. -/
def DPContro.extensionData_gen
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    {W : WFilt p Q}
    {P : PWFilt p Q W}
    (hP : DPContro O P)
    (i : Fin O.r)
    (hdeep :
      ∀ j, O.weight i < O.weight j →
        groupAlgebraSub p Q (O.gen j) ∈ W.J (O.weight j)) :
    CEDataa p Q W := by
  apply
    PWFilt.extension_data_control
      P (O.gen i) (O.weight i)
  · apply
      O.groupalgsub_onememweifil_memgteqbot
        W hbot
    · have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
      have hp_two : 2 ≤ p := hp
      have hdouble : O.weight i < 2 * O.weight i := by
        have hi_pos : 0 < O.weight i := O.weight_pos i
        omega
      exact hdouble.trans_le (Nat.mul_le_mul_right (O.weight i) hp_two)
    · exact hdeep
    · exact hpow i
  · exact
      hP.commutatorControl O hbot hcomm (O.weight_pos i) (O.gen_mem i)

/-- The extension constructed above again has a descending history.  Representatives strictly
deeper than the newly adjoined one remain available by inclusion of the old prefix. -/
def DPContro.extendGen
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    {W : WFilt p Q}
    {P : PWFilt p Q W}
    (hP : DPContro O P)
    (i : Fin O.r)
    (hdeep :
      ∀ j, O.weight i < O.weight j →
        groupAlgebraSub p Q (O.gen j) ∈ W.J (O.weight j)) :
    { S : CEDataa p Q W //
      DPContro O (PWFilt.extend P S) } := by
  let S : CEDataa p Q W :=
    hP.extensionData_gen O hbot hpow hcomm i hdeep
  refine ⟨S, DPContro.extend hP S (O.gen_mem i) ?_⟩
  intro j hj
  exact S.old_mem_next (hdeep j hj)

/-- A descending prefix stopped at boundary `b`: every chosen representative of weight strictly
larger than `b` has already been adjoined with its declared augmentation weight. -/
structure DPAt
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (b : ℕ) where
  W : WFilt p Q
  P : PWFilt p Q W
  control : DPContro O P
  deep_mem :
    ∀ i, b < O.weight i →
      groupAlgebraSub p Q (O.gen i) ∈ W.J (O.weight i)

/-- Above the killed level there are no representatives, so the scalar filtration is the initial
descending prefix. -/
def descending_prefix_top
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m) :
    DPAt O m where
  W := base_weightFiltration p Q
  P := PWFilt.base
  control := DPContro.base
  deep_mem := by
    intro i hi
    have hlt : O.weight i < m := O.weight_lt i
    omega

/-- Adjoin one representative of exact boundary weight while retaining the same boundary
invariant.  Iterating this operation across the finite boundary layer prepares the next descent
step. -/
def DPAt.extend_gen_weighteq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    (i : Fin O.r)
    (hi : O.weight i = b) :
    DPAt O b := by
  let E :=
    A.control.extendGen O hbot hpow hcomm i
      (fun j hj => A.deep_mem j (by simpa [hi] using hj))
  exact
    { W := E.val.next
      P := PWFilt.extend A.P E.val
      control := E.property
      deep_mem := fun j hj => E.val.old_mem_next (A.deep_mem j hj) }

/-- Every weighted element already present before an exact-boundary extension remains present
afterward. -/
lemma DPAt.oldmem_extendgen_weighteq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    (i : Fin O.r)
    (hi : O.weight i = b)
    {r : ℕ}
    {a : denseGroupAlgebra p Q}
    (ha : a ∈ A.W.J r) :
    a ∈ (A.extend_gen_weighteq O hbot hpow hcomm i hi).W.J r := by
  dsimp [DPAt.extend_gen_weighteq]
  exact CEDataa.old_mem_next _ ha

/-- The exact-boundary representative adjoined by `extend_gen_weighteq` has its declared
augmentation weight afterward. -/
lemma DPAt.newmem_extendgen_weighteq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    (i : Fin O.r)
    (hi : O.weight i = b) :
    groupAlgebraSub p Q (O.gen i) ∈
      (A.extend_gen_weighteq O hbot hpow hcomm i hi).W.J (O.weight i) := by
  dsimp [DPAt.extend_gen_weighteq]
  exact CEDataa.new_mem_next _

/-- Extending by one exact-boundary representative appends precisely its declared weight to the
prefix trace. -/
lemma DPAt.extweights_extendgen_weighteq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    (i : Fin O.r)
    (hi : O.weight i = b) :
    (A.extend_gen_weighteq O hbot hpow hcomm i hi).P.extensionWeights =
      A.P.extensionWeights.concat (O.weight i) := by
  rfl

/-- Adjoin a finite list of representatives belonging to one boundary layer. -/
def DPAt.extend_genlist_weighteq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    (l : List (Fin O.r))
    (hl : ∀ i, i ∈ l → O.weight i = b) :
    DPAt O b :=
  match l with
  | [] => A
  | i :: l =>
      (A.extend_gen_weighteq O hbot hpow hcomm i (hl i (by simp))).extend_genlist_weighteq
        O hbot hpow hcomm l (fun j hj => hl j (by simp [hj]))
termination_by l.length

/-- Every weighted element already present before a finite exact-boundary extension remains
present afterward. -/
lemma DPAt.oldmem_extendgen_listweighteq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    (l : List (Fin O.r))
    (hl : ∀ i, i ∈ l → O.weight i = b)
    {r : ℕ}
    {a : denseGroupAlgebra p Q}
    (ha : a ∈ A.W.J r) :
    a ∈ (A.extend_genlist_weighteq O hbot hpow hcomm l hl).W.J r := by
  induction l generalizing A with
  | nil =>
      simpa [DPAt.extend_genlist_weighteq] using ha
  | cons i l ih =>
      rw [DPAt.extend_genlist_weighteq]
      apply ih
      exact
        A.oldmem_extendgen_weighteq O hbot hpow hcomm i
          (hl i (by simp)) ha

/-- Every representative listed in a finite exact-boundary extension has its declared
augmentation weight afterward. -/
lemma DPAt.newmem_extendgen_listweighteq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    (l : List (Fin O.r))
    (hl : ∀ i, i ∈ l → O.weight i = b)
    {i : Fin O.r}
    (hi : i ∈ l) :
    groupAlgebraSub p Q (O.gen i) ∈
      (A.extend_genlist_weighteq O hbot hpow hcomm l hl).W.J (O.weight i) := by
  induction l generalizing A with
  | nil =>
      simp at hi
  | cons j l ih =>
      have hj : O.weight j = b := hl j (by simp)
      have hl' : ∀ i, i ∈ l → O.weight i = b :=
        fun i hi => hl i (by simp [hi])
      let A' : DPAt O b :=
        A.extend_gen_weighteq O hbot hpow hcomm j hj
      have hnew :
          groupAlgebraSub p Q (O.gen j) ∈ A'.W.J (O.weight j) := by
        exact A.newmem_extendgen_weighteq O hbot hpow hcomm j hj
      rcases List.mem_cons.mp hi with rfl | hi
      · simpa only [DPAt.extend_genlist_weighteq] using
          (DPAt.oldmem_extendgen_listweighteq
            O hbot hpow hcomm A' l hl' hnew)
      · simpa only [DPAt.extend_genlist_weighteq] using
          (ih (A := A') hl' hi)

/-- Extending by a finite exact-boundary list appends precisely its mapped declared weights to
the prefix trace. -/
lemma DPAt.extweights_extendgen_listweighteq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    (l : List (Fin O.r))
    (hl : ∀ i, i ∈ l → O.weight i = b) :
    (A.extend_genlist_weighteq O hbot hpow hcomm l hl).P.extensionWeights =
      A.P.extensionWeights ++ l.map O.weight := by
  induction l generalizing A with
  | nil =>
      rw [DPAt.extend_genlist_weighteq]
      simp
  | cons i l ih =>
      rw [DPAt.extend_genlist_weighteq, ih]
      rw [A.extweights_extendgen_weighteq O hbot hpow hcomm i (hl i (by simp))]
      simp [List.concat_eq_append, List.append_assoc]

/-- The finite list of selected representatives lying in one exact weight layer. -/
def boundaryLayer
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (b : ℕ) :
    List (Fin O.r) :=
  (Finset.univ.filter fun i => O.weight i = b).toList

lemma boundary_layer
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (b : ℕ)
    (i : Fin O.r) :
    i ∈ O.boundaryLayer b ↔ O.weight i = b := by
  simp [boundaryLayer]

/-- The selected indices in boundaries `b, b - 1, ..., 1`, listed in descending-weight order. -/
def descendingBoundaryIndices
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m) :
    ℕ → List (Fin O.r)
  | 0 => []
  | b + 1 => O.boundaryLayer (b + 1) ++ O.descendingBoundaryIndices b

/-- The descending boundary list through `b` contains exactly the positive-weight indices of
weight at most `b`. -/
lemma descending_boundary_indices
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (b : ℕ)
    (i : Fin O.r) :
    i ∈ O.descendingBoundaryIndices b ↔
      0 < O.weight i ∧ O.weight i ≤ b := by
  induction b with
  | zero =>
      simp [descendingBoundaryIndices]
      omega
  | succ b ih =>
      rw [descendingBoundaryIndices, List.mem_append, O.boundary_layer, ih]
      omega

/-- No selected representative is repeated while descending through the boundary layers. -/
lemma descending_indices_nodup
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (b : ℕ) :
    (O.descendingBoundaryIndices b).Nodup := by
  induction b with
  | zero =>
      simp [descendingBoundaryIndices]
  | succ b ih =>
      rw [descendingBoundaryIndices]
      apply List.Nodup.append (Finset.nodup_toList _) ih
      rw [List.disjoint_left]
      intro i hi hrest
      have hi_weight : O.weight i = b + 1 :=
        (O.boundary_layer (b + 1) i).mp hi
      have hrest_weight : O.weight i ≤ b :=
        (O.descending_boundary_indices b i).mp hrest |>.2
      omega

/-- Descending through all boundaries below the killed level visits every selected
representative exactly once. -/
lemma descending_indices_fn
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m) :
    (O.descendingBoundaryIndices m).Perm (List.ofFn (fun i : Fin O.r => i)) := by
  apply
    (List.perm_ext_iff_of_nodup
      (O.descending_indices_nodup m)
      (List.nodup_ofFn_ofInjective Function.injective_id)).mpr
  intro i
  rw [O.descending_boundary_indices]
  simp [O.weight_pos i, le_of_lt (O.weight_lt i)]

/-- Boundary-list positions are equivalent to the selected representative indices. -/
noncomputable def descendingBoundaryEquiv
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m) :
    Fin (O.descendingBoundaryIndices m).length ≃ Fin O.r :=
  (O.descending_indices_nodup m).getEquivOfForallMemList
    (O.descendingBoundaryIndices m)
    (fun i =>
      (O.descending_boundary_indices m i).mpr
        ⟨O.weight_pos i, le_of_lt (O.weight_lt i)⟩)

@[simp]
lemma descending_boundary_equiv
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (i : Fin (O.descendingBoundaryIndices m).length) :
    O.descendingBoundaryEquiv i =
      (O.descendingBoundaryIndices m).get i := by
  rfl

/-- Adjoin every selected representative belonging to one exact boundary layer. -/
def DPAt.extendBoundaryLayer
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b) :
    DPAt O b :=
  A.extend_genlist_weighteq O hbot hpow hcomm (O.boundaryLayer b)
    (fun i hi => (O.boundary_layer b i).mp hi)

/-- Every weighted element already present survives extension by an exact boundary layer. -/
lemma DPAt.old_memextend_boundlayer
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    {r : ℕ}
    {a : denseGroupAlgebra p Q}
    (ha : a ∈ A.W.J r) :
    a ∈ (A.extendBoundaryLayer O hbot hpow hcomm).W.J r := by
  exact A.oldmem_extendgen_listweighteq O hbot hpow hcomm _ _ ha

/-- Every selected representative of exact boundary weight is present after extending that
boundary layer. -/
lemma DPAt.new_memextend_boundlayer
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b)
    (i : Fin O.r)
    (hi : O.weight i = b) :
    groupAlgebraSub p Q (O.gen i) ∈
      (A.extendBoundaryLayer O hbot hpow hcomm).W.J (O.weight i) := by
  apply A.newmem_extendgen_listweighteq O hbot hpow hcomm
  exact (O.boundary_layer b i).mpr hi

/-- Extending one boundary layer appends precisely that boundary's mapped declared weights to
the prefix trace. -/
lemma DPAt.ext_weightsextend_boundlayer
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b) :
    (A.extendBoundaryLayer O hbot hpow hcomm).P.extensionWeights =
      A.P.extensionWeights ++ (O.boundaryLayer b).map O.weight := by
  exact A.extweights_extendgen_listweighteq O hbot hpow hcomm _ _

/-- Descend one boundary after adjoining the entire next layer. -/
def DPAt.lowerSuccBoundary
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O (b + 1)) :
    DPAt O b := by
  let A' : DPAt O (b + 1) :=
    A.extendBoundaryLayer O hbot hpow hcomm
  exact
    { W := A'.W
      P := A'.P
      control := A'.control
      deep_mem := by
        intro i hi
        by_cases hi_eq : O.weight i = b + 1
        · exact A.new_memextend_boundlayer O hbot hpow hcomm i hi_eq
        · exact A'.deep_mem i (by omega) }

/-- Lowering one successor boundary records exactly the newly adjoined boundary layer. -/
lemma DPAt.ext_weightslower_succbound
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O (b + 1)) :
    (A.lowerSuccBoundary O hbot hpow hcomm).P.extensionWeights =
      A.P.extensionWeights ++ (O.boundaryLayer (b + 1)).map O.weight := by
  simpa [DPAt.lowerSuccBoundary] using
    A.ext_weightsextend_boundlayer O hbot hpow hcomm

/-- Repeatedly descend a verified prefix construction to boundary zero. -/
def DPAt.toZero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b) :
    DPAt O 0 :=
  match b with
  | 0 => A
  | b + 1 =>
      (A.lowerSuccBoundary O hbot hpow hcomm).toZero O hbot hpow hcomm
termination_by b

/-- Descending a certified prefix to zero appends precisely the recursively listed positive
boundary indices. -/
lemma DPAt.ext_weights_zero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m b : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (A : DPAt O b) :
    (A.toZero O hbot hpow hcomm).P.extensionWeights =
      A.P.extensionWeights ++ (O.descendingBoundaryIndices b).map O.weight := by
  induction b with
  | zero =>
      rw [DPAt.toZero]
      simp [descendingBoundaryIndices]
  | succ b ih =>
      rw [DPAt.toZero, ih]
      rw [A.ext_weightslower_succbound O hbot hpow hcomm]
      simp [descendingBoundaryIndices, List.map_append, List.append_assoc]

/-- The descending cyclic-extension construction started above the killed level and continued
through every selected representative. -/
def descending_prefix_zero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    DPAt O 0 :=
  (descending_prefix_top O).toZero O hbot hpow hcomm

/-- The final descending prefix trace is exactly the mapped descending boundary-index list. -/
lemma descending_prefix_weights
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    (descending_prefix_zero O hbot hpow hcomm).P.extensionWeights =
      (O.descendingBoundaryIndices m).map O.weight := by
  rw [descending_prefix_zero,
    (descending_prefix_top O).ext_weights_zero O hbot hpow hcomm]
  rfl

/-- The final descending prefix trace is a permutation of the declared representative weights. -/
lemma descending_weights_perm
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    ((descending_prefix_zero O hbot hpow hcomm).P.extensionWeights).Perm
      (List.ofFn O.weight) := by
  rw [descending_prefix_zero,
    (descending_prefix_top O).ext_weights_zero O hbot hpow hcomm]
  change
    ([] ++ (O.descendingBoundaryIndices m).map O.weight).Perm (List.ofFn O.weight)
  rw [List.nil_append]
  simpa only [← List.ofFn_comp', Function.comp_apply] using
    (O.descending_indices_fn).map O.weight

/-- The final descending prefix admits an exact bounded-monomial description whose declared
weights are a permutation of the ordered normal form's weights. -/
lemma descending_monomial_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    ∃ (r : ℕ) (gen : Fin r → Q) (weight : Fin r → ℕ),
      (List.ofFn weight).Perm (List.ofFn O.weight) ∧
        ∀ s,
          (descending_prefix_zero O hbot hpow hcomm).W.J s =
            jenningsMonomialSpan (p := p) gen weight s := by
  rcases
      (descending_prefix_zero O hbot hpow hcomm).P.existsbounded_jenningmonomia_spaneq with
    ⟨r, gen, weight, hweight, hspan⟩
  exact
    ⟨r, gen, weight,
      (List.Perm.of_eq hweight).trans
        (O.descending_weights_perm hbot hpow hcomm),
      hspan⟩

/-- The final descending prefix admits an exact bounded-monomial description indexed in the
same order as the concrete descending boundary list. -/
lemma descending_monomial_indices
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    ∃ (r : ℕ) (gen : Fin r → Q) (weight : Fin r → ℕ),
      List.ofFn weight = (O.descendingBoundaryIndices m).map O.weight ∧
        ∀ s,
          (descending_prefix_zero O hbot hpow hcomm).W.J s =
            jenningsMonomialSpan (p := p) gen weight s := by
  rcases
      (descending_prefix_zero O hbot hpow hcomm).P.existsbounded_jenningmonomia_spaneq with
    ⟨r, gen, weight, hweight, hspan⟩
  exact
    ⟨r, gen, weight,
      hweight.trans
        (O.descending_prefix_weights hbot hpow hcomm),
      hspan⟩

/-- Every selected representative has its declared augmentation weight in the filtration built
by descending cyclic extensions. -/
lemma descending_prefix_gen
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (i : Fin O.r) :
    groupAlgebraSub p Q (O.gen i) ∈
      (descending_prefix_zero O hbot hpow hcomm).W.J (O.weight i) := by
  exact
    (descending_prefix_zero O hbot hpow hcomm).deep_mem i
      (O.weight_pos i)

end OZReps

/-- Once the weighted generators of an ordered Zassenhaus normal form lie in a weight
filtration, every element of `D_t` has augmentation letter in weight `t`. -/
lemma OZReps.groupalg_subonemem_weightfiltmem
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (W : WFilt p Q)
    (hgen :
      ∀ i, groupAlgebraSub p Q (O.gen i) ∈ W.J (O.weight i))
    {t : ℕ} (ht : t ≤ m)
    {q : Q} (hq : q ∈ zassenhausFiltration p Q t) :
    groupAlgebraSub p Q q ∈ W.J t := by
  exact
    O.groupalgsub_onememweight_filtmemnonzero W ht hq
      (fun i _hi => hgen i)

/-- The descending cyclic-extension filtration assigns weight `t` to every augmentation letter
coming from `D_t`, provided the explicit Zassenhaus power and commutator laws hold. -/
lemma OZReps.groupalgsub_onememdesc_prefixzeromem
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    {t : ℕ}
    (ht : t ≤ m)
    {q : Q}
    (hq : q ∈ zassenhausFiltration p Q t) :
    groupAlgebraSub p Q q ∈
      (OZReps.descending_prefix_zero O hbot hpow hcomm).W.J t := by
  apply O.groupalg_subonemem_weightfiltmem
  · exact fun i => O.descending_prefix_gen hbot hpow hcomm i
  · exact ht
  · exact hq

end Submission
