import Towers.Algebra.TruncatedJennings.OrderedWords
import Towers.Group.CyclicPC


open scoped commutatorElement

noncomputable section

namespace Towers
namespace TJennin

universe u

/-- The cyclic-PC word is the ordered word used by the Jennings basis. -/
lemma cyclic_pc_fin
    {p r : ℕ}
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (e : Fin r → Fin p) :
    cyclicPCWord r gen e = orderedWordFin gen e := by
  induction r with
  | zero =>
      rfl
  | succ r ih =>
      rw [cyclicPCWord]
      unfold orderedWordFin orderedWord
      rw [finOrderedProd]
      exact congrArg (fun z => z * gen (Fin.last r) ^ (e (Fin.last r)).val)
        (ih (fun i : Fin r => gen i.castSucc) (fun i : Fin r => e i.castSucc))

/-- A cyclic-PC normal form whose selected generators carry positive Zassenhaus weights below
the killed cutoff. -/
structure WPForm
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q]
    (m : ℕ) where
  pc : CPForm p Q
  weight : Fin pc.r → ℕ
  weight_pos : ∀ i, 0 < weight i
  weight_lt : ∀ i, weight i < m
  gen_mem : ∀ i, pc.gen i ∈ zassenhausFiltration p Q (weight i)
  gen_exact_mem : ∀ i, pc.gen i ∈ exactGeneratorSet p Q (weight i)

namespace WPForm

/-- The one-sided commutator input needed by the cyclic-PC construction: an exact generator is
central modulo the successor filtration term. -/
def ExactSuccBound
    (p : ℕ)
    (Q : Type u) [Group Q]
    (m : ℕ) :
    Prop :=
  ∀ {n : ℕ} {x : Q},
    n < m →
    x ∈ exactGeneratorSet p Q n →
      ∀ y : Q, ⁅x, y⁆ ∈ zassenhausFiltration p Q (n + 1)

/-- The empty cyclic-PC prefix. -/
noncomputable def empty
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q]
    (m : ℕ) :
    WPForm p Q m where
  pc := CPForm.empty p Q
  weight := fun i => Fin.elim0 i
  weight_pos := fun i => Fin.elim0 i
  weight_lt := fun i => Fin.elim0 i
  gen_mem := fun i => Fin.elim0 i
  gen_exact_mem := fun i => Fin.elim0 i

@[simp]
lemma base_subgroup
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ} :
    (empty p Q m).pc.subgroup = ⊥ :=
  rfl

/-- Append one genuinely new central-modulo-prefix order-`p` class, carrying its declared
Zassenhaus weight. -/
noncomputable def extend
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (P : WPForm p Q m)
    (x : Q)
    (w : ℕ)
    (hw_pos : 0 < w)
    (hw_lt : w < m)
    (hx : x ∈ exactGeneratorSet p Q w)
    (hpow : x ^ p ∈ P.pc.subgroup)
    (hnot : x ∉ P.pc.subgroup)
    (hcomm : ∀ y : Q, ⁅x, y⁆ ∈ P.pc.subgroup) :
    WPForm p Q m where
  pc := P.pc.extend x hpow hnot hcomm
  weight := Fin.snoc P.weight w
  weight_pos := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa
    · simpa using P.weight_pos j
  weight_lt := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa
    · simpa using P.weight_lt j
  gen_mem := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [CPForm.extend, Fin.snoc_last] using
        exact_subset_filtration hx
    · simpa only [CPForm.extend, Fin.snoc_castSucc] using P.gen_mem j
  gen_exact_mem := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [CPForm.extend, Fin.snoc_last] using hx
    · simpa only [CPForm.extend, Fin.snoc_castSucc] using P.gen_exact_mem j

@[simp]
lemma extend_subgroup
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m w : ℕ}
    (P : WPForm p Q m)
    (x : Q)
    (hw_pos : 0 < w)
    (hw_lt : w < m)
    (hx : x ∈ exactGeneratorSet p Q w)
    (hpow : x ^ p ∈ P.pc.subgroup)
    (hnot : x ∉ P.pc.subgroup)
    (hcomm : ∀ y : Q, ⁅x, y⁆ ∈ P.pc.subgroup) :
    (P.extend x w hw_pos hw_lt hx hpow hnot hcomm).pc.subgroup =
      cyclicPrefixSubgroup P.pc.subgroup x :=
  rfl

/-- The old prefix is contained in a genuine one-class extension. -/
lemma le_extend
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m w : ℕ}
    (P : WPForm p Q m)
    (x : Q)
    (hw_pos : 0 < w)
    (hw_lt : w < m)
    (hx : x ∈ exactGeneratorSet p Q w)
    (hpow : x ^ p ∈ P.pc.subgroup)
    (hnot : x ∉ P.pc.subgroup)
    (hcomm : ∀ y : Q, ⁅x, y⁆ ∈ P.pc.subgroup) :
    P.pc.subgroup ≤
      (P.extend x w hw_pos hw_lt hx hpow hnot hcomm).pc.subgroup := by
  rw [extend_subgroup]
  exact cyclic_subgroup P.pc.subgroup x

/-- A genuine one-class extension remains in any ambient subgroup containing the old prefix and
the newly adjoined generator. -/
lemma extend_subgroup_le
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m w : ℕ}
    (P : WPForm p Q m)
    (x : Q)
    (hw_pos : 0 < w)
    (hw_lt : w < m)
    (hx : x ∈ exactGeneratorSet p Q w)
    (hpow : x ^ p ∈ P.pc.subgroup)
    (hnot : x ∉ P.pc.subgroup)
    (hcomm : ∀ y : Q, ⁅x, y⁆ ∈ P.pc.subgroup)
    (H : Subgroup Q)
    (hP : P.pc.subgroup ≤ H)
    (hxH : x ∈ H) :
    (P.extend x w hw_pos hw_lt hx hpow hnot hcomm).pc.subgroup ≤ H := by
  rw [extend_subgroup]
  intro y hy
  rcases
      cyclic_prefix_subgroup
        P.pc.subgroup hpow hnot hy with
    ⟨k, e, rfl⟩
  exact H.mul_mem (hP k.property) (H.pow_mem hxH e.val)

/-- Appending a weight-`n` cyclic-PC class preserves the coordinate description of every
strictly deeper Zassenhaus term.  Membership in a deeper term puts the extended word back in the
old prefix, and uniqueness of the cyclic-prefix exponent forces the new coordinate to be zero. -/
lemma extend_zero_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (x : Q)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hx : x ∈ exactGeneratorSet p Q n)
    (hpow : x ^ p ∈ P.pc.subgroup)
    (hnot : x ∉ P.pc.subgroup)
    (hcomm : ∀ y : Q, ⁅x, y⁆ ∈ P.pc.subgroup)
    (hdeep : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hmem :
      ∀ {t : ℕ}, n < t → t ≤ m → ∀ e : Fin P.pc.r → Fin p,
        ((P.pc.wordEquiv e : P.pc.subgroup) : Q) ∈
            zassenhausFiltration p Q t ↔
          ∀ i, P.weight i < t → e i = 0)
    {t : ℕ}
    (hnt : n < t)
    (htm : t ≤ m)
    (e : Fin (P.pc.r + 1) → Fin p) :
    ((((P.extend x n hn_pos hn_lt hx hpow hnot hcomm).pc.wordEquiv e :
        (P.extend x n hn_pos hn_lt hx hpow hnot hcomm).pc.subgroup) : Q) ∈
          zassenhausFiltration p Q t) ↔
      ∀ i, (P.extend x n hn_pos hn_lt hx hpow hnot hcomm).weight i < t →
        e i = 0 := by
  let e0 : Fin P.pc.r → Fin p :=
    fun i => e i.castSucc
  have ht_succ : n + 1 ≤ t := by
    omega
  have hDt_le_old :
      zassenhausFiltration p Q t ≤ P.pc.subgroup :=
    fun z hz =>
      hdeep (zassenhausFiltration_antitone p Q ht_succ hz)
  have hword :
      ((((P.extend x n hn_pos hn_lt hx hpow hnot hcomm).pc.wordEquiv e :
          (P.extend x n hn_pos hn_lt hx hpow hnot hcomm).pc.subgroup) : Q)) =
        ((P.pc.wordEquiv e0 : P.pc.subgroup) : Q) *
          x ^ (e (Fin.last P.pc.r)).val := by
    exact
      CPForm.extend_word_equiv
        P.pc x hpow hnot hcomm e
  constructor
  · intro heD
    have heOld :
        ((((P.extend x n hn_pos hn_lt hx hpow hnot hcomm).pc.wordEquiv e :
            (P.extend x n hn_pos hn_lt hx hpow hnot hcomm).pc.subgroup) : Q)) ∈
          P.pc.subgroup :=
      hDt_le_old heD
    let k : P.pc.subgroup :=
      P.pc.wordEquiv e0
    let l : P.pc.subgroup :=
      ⟨(((P.extend x n hn_pos hn_lt hx hpow hnot hcomm).pc.wordEquiv e :
          (P.extend x n hn_pos hn_lt hx hpow hnot hcomm).pc.subgroup) : Q),
        heOld⟩
    have helast :
        e (Fin.last P.pc.r) = 0 := by
      apply
        fin_mul_pow
          P.pc.subgroup hpow hnot
          (k := k) (l := l)
          (e := e (Fin.last P.pc.r)) (f := 0)
      simpa [k, l] using hword.symm
    have he0D :
        ((P.pc.wordEquiv e0 : P.pc.subgroup) : Q) ∈
          zassenhausFiltration p Q t := by
      rw [hword, helast] at heD
      simpa using heD
    have he0zero :
        ∀ i, P.weight i < t → e0 i = 0 :=
      (hmem hnt htm e0).mp he0D
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro _hi
      exact helast
    · intro hi
      exact he0zero j (by
        simpa only [WPForm.extend, Fin.snoc_castSucc] using hi)
  · intro hezero
    have helast :
        e (Fin.last P.pc.r) = 0 := by
      apply hezero
      simpa only [WPForm.extend, Fin.snoc_last] using hnt
    have he0zero :
        ∀ i, P.weight i < t → e0 i = 0 := by
      intro i hi
      apply hezero i.castSucc
      simpa only [WPForm.extend, Fin.snoc_castSucc] using hi
    have he0D :
        ((P.pc.wordEquiv e0 : P.pc.subgroup) : Q) ∈
          zassenhausFiltration p Q t :=
      (hmem hnt htm e0).mpr he0zero
    rw [hword, helast]
    simpa using he0D

/-- The genuine append branch only needs successor centrality for the exact-weight generator
being adjoined. -/
noncomputable def appendExactSucc
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (x : Q)
    (hx : x ∈ exactGeneratorSet p Q n)
    (hcomm : ∀ y : Q, ⁅x, y⁆ ∈ zassenhausFiltration p Q (n + 1))
    (hnot : x ∉ P.pc.subgroup) :
    WPForm p Q m :=
  P.extend x n hn_pos hn_lt
    hx
    (hnext (exact_filtration_succ hn_pos hx))
    hnot
    (fun y => hnext (hcomm y))

/-- The genuine append branch for an exact-weight generator whose class is not already
represented by the current cyclic-PC prefix. -/
noncomputable def appendExactGenerator
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (x : Q)
    (hx : x ∈ exactGeneratorSet p Q n)
    (hnot : x ∉ P.pc.subgroup) :
    WPForm p Q m :=
  P.extend x n hn_pos hn_lt
    hx
    (hnext (exact_filtration_succ hn_pos hx))
    hnot
    (fun y =>
      hnext
        (hcomm
          (exact_subset_filtration hx)
          (by
            rw [filtration_one_top]
            exact Subgroup.mem_top y)))

/-- Conditionally append one exact-weight generator if its class is not already represented by
the current cyclic-PC prefix. -/
noncomputable def extendExactGenerator
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (x : Q)
    (hx : x ∈ exactGeneratorSet p Q n) :
    WPForm p Q m := by
  classical
  exact
    if hmem : x ∈ P.pc.subgroup then
      P
    else
      P.appendExactSucc hn_pos hn_lt hnext x hx
        (hcomm hn_lt hx) hmem

@[simp]
lemma extend_exact
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (x : Q)
    (hx : x ∈ exactGeneratorSet p Q n)
    (hmem : x ∈ P.pc.subgroup) :
    P.extendExactGenerator hn_pos hn_lt hnext hcomm x hx = P := by
  simp [extendExactGenerator, hmem]

@[simp]
lemma extend_exact_not
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (x : Q)
    (hx : x ∈ exactGeneratorSet p Q n)
    (hnot : x ∉ P.pc.subgroup) :
    P.extendExactGenerator hn_pos hn_lt hnext hcomm x hx =
      P.appendExactSucc hn_pos hn_lt hnext x hx
        (hcomm hn_lt hx) hnot := by
  simp [extendExactGenerator, hnot]

/-- One conditional exact-generator extension contains the old prefix. -/
lemma exact_generator
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (x : Q)
    (hx : x ∈ exactGeneratorSet p Q n) :
    P.pc.subgroup ≤
      (P.extendExactGenerator hn_pos hn_lt hnext hcomm x hx).pc.subgroup := by
  classical
  unfold extendExactGenerator
  split
  · exact le_rfl
  · exact P.le_extend x hn_pos hn_lt _ _ _ _

/-- The conditionally adjoined exact generator belongs to the resulting prefix. -/
lemma extend_generator
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (x : Q)
    (hx : x ∈ exactGeneratorSet p Q n) :
    x ∈ (P.extendExactGenerator hn_pos hn_lt hnext hcomm x hx).pc.subgroup := by
  classical
  unfold extendExactGenerator
  split
  · assumption
  · simp only [appendExactSucc, extend_subgroup]
    exact cyclic_prefix P.pc.subgroup x

/-- One conditional exact-generator extension remains in `D_n` if the old prefix does. -/
lemma extend_exact_generator
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (x : Q)
    (hx : x ∈ exactGeneratorSet p Q n)
    (hP : P.pc.subgroup ≤ zassenhausFiltration p Q n) :
    (P.extendExactGenerator hn_pos hn_lt hnext hcomm x hx).pc.subgroup ≤
      zassenhausFiltration p Q n := by
  classical
  unfold extendExactGenerator
  split
  · exact hP
  · apply P.extend_subgroup_le
    · exact hP
    · exact exact_subset_filtration hx

/-- Conditionally adjoin a finite list of exact-weight generators. -/
noncomputable def extendExactList
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m) :
    (l : List Q) →
      (∀ x, x ∈ l → x ∈ exactGeneratorSet p Q n) →
        WPForm p Q m
  | [], _ => P
  | x :: l, hl =>
      let P' :=
        P.extendExactGenerator hn_pos hn_lt hnext hcomm x
          (hl x (by simp))
      P'.extendExactList hn_pos hn_lt
        (fun z hz =>
          P.exact_generator hn_pos hn_lt hnext hcomm x
            (hl x (by simp)) (hnext hz))
        hcomm l
        (fun z hz => hl z (by simp [hz]))

/-- A finite exact-generator fold contains its initial prefix. -/
lemma extend_generator_list
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (l : List Q)
    (hl : ∀ x, x ∈ l → x ∈ exactGeneratorSet p Q n) :
    P.pc.subgroup ≤
      (P.extendExactList hn_pos hn_lt hnext hcomm l hl).pc.subgroup := by
  induction l generalizing P with
  | nil =>
      exact le_rfl
  | cons x l ih =>
      rw [extendExactList]
      exact
        (P.exact_generator hn_pos hn_lt hnext hcomm x
          (hl x (by simp))).trans
          (ih
            (P := P.extendExactGenerator hn_pos hn_lt hnext hcomm x
              (hl x (by simp)))
            (fun z hz =>
              P.exact_generator hn_pos hn_lt hnext hcomm x
                (hl x (by simp)) (hnext hz))
            (fun z hz => hl z (by simp [hz])))

/-- A finite exact-generator fold remains in `D_n` if its initial prefix does. -/
lemma extend_exact_subgroup
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (l : List Q)
    (hl : ∀ x, x ∈ l → x ∈ exactGeneratorSet p Q n)
    (hP : P.pc.subgroup ≤ zassenhausFiltration p Q n) :
    (P.extendExactList hn_pos hn_lt hnext hcomm l hl).pc.subgroup ≤
      zassenhausFiltration p Q n := by
  induction l generalizing P with
  | nil =>
      exact hP
  | cons x l ih =>
      rw [extendExactList]
      let hx :
          x ∈ exactGeneratorSet p Q n :=
        hl x (by simp)
      let P' :=
        P.extendExactGenerator hn_pos hn_lt hnext hcomm x hx
      have hnext' :
          zassenhausFiltration p Q (n + 1) ≤ P'.pc.subgroup :=
        fun z hz =>
          P.exact_generator hn_pos hn_lt hnext hcomm x hx (hnext hz)
      have hl' :
          ∀ z, z ∈ l → z ∈ exactGeneratorSet p Q n :=
        fun z hz => hl z (by simp [hz])
      have hP' :
          P'.pc.subgroup ≤ zassenhausFiltration p Q n :=
        P.extend_exact_generator hn_pos hn_lt hnext hcomm x hx hP
      exact ih (P := P') hnext' hl' hP'

/-- Every listed exact generator belongs to the final finite fold. -/
lemma extend_exact_list
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (l : List Q)
    (hl : ∀ x, x ∈ l → x ∈ exactGeneratorSet p Q n)
    {x : Q}
    (hx : x ∈ l) :
    x ∈ (P.extendExactList hn_pos hn_lt hnext hcomm l hl).pc.subgroup := by
  induction l generalizing P with
  | nil =>
      simp at hx
  | cons y l ih =>
      rw [extendExactList]
      have hy :
          y ∈ exactGeneratorSet p Q n :=
        hl y (by simp)
      let P' := P.extendExactGenerator hn_pos hn_lt hnext hcomm y hy
      have hnext' :
          zassenhausFiltration p Q (n + 1) ≤ P'.pc.subgroup :=
        fun z hz =>
          P.exact_generator hn_pos hn_lt hnext hcomm y hy (hnext hz)
      rcases List.mem_cons.mp hx with hxy | hx
      · subst x
        exact
          P'.extend_generator_list hn_pos hn_lt hnext' hcomm l
            (fun z hz => hl z (by simp [hz]))
            (P.extend_generator hn_pos hn_lt hnext hcomm y hy)
      · exact
          ih
            (P := P')
            hnext'
            (fun z hz => hl z (by simp [hz]))
            hx

/-- A finite exact-generator fold preserves the current lower bound on selected weights. -/
lemma extend_exact_weight
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (l : List Q)
    (hl : ∀ x, x ∈ l → x ∈ exactGeneratorSet p Q n)
    (hweight : ∀ i, n ≤ P.weight i) :
    ∀ i,
      n ≤ (P.extendExactList hn_pos hn_lt hnext hcomm l hl).weight i := by
  induction l generalizing P with
  | nil =>
      exact hweight
  | cons x l ih =>
      rw [extendExactList]
      let hx :
          x ∈ exactGeneratorSet p Q n :=
        hl x (by simp)
      let P' :=
        P.extendExactGenerator hn_pos hn_lt hnext hcomm x hx
      have hnext' :
          zassenhausFiltration p Q (n + 1) ≤ P'.pc.subgroup :=
        fun z hz =>
          P.exact_generator hn_pos hn_lt hnext hcomm x hx (hnext hz)
      have hweight' :
          ∀ i, n ≤ P'.weight i := by
        classical
        by_cases hxP : x ∈ P.pc.subgroup
        · rw [show P' = P from
            P.extend_exact hn_pos hn_lt hnext hcomm x hx hxP]
          exact hweight
        · rw [show P' =
              P.appendExactSucc hn_pos hn_lt hnext x hx
                (hcomm hn_lt hx) hxP from
            P.extend_exact_not hn_pos hn_lt hnext hcomm x hx hxP]
          simp only [appendExactSucc]
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp [WPForm.extend]
          · simpa only [WPForm.extend, Fin.snoc_castSucc] using
              hweight j
      exact
        ih
          (P := P')
          hnext'
          (fun z hz => hl z (by simp [hz]))
          hweight'

/-- A finite exact-generator fold preserves the coordinate description of every strictly deeper
term. -/
lemma extend_exact_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (l : List Q)
    (hl : ∀ x, x ∈ l → x ∈ exactGeneratorSet p Q n)
    (hmem :
      ∀ {t : ℕ}, n < t → t ≤ m → ∀ e : Fin P.pc.r → Fin p,
        ((P.pc.wordEquiv e : P.pc.subgroup) : Q) ∈
            zassenhausFiltration p Q t ↔
          ∀ i, P.weight i < t → e i = 0)
    {t : ℕ}
    (hnt : n < t)
    (htm : t ≤ m)
    (e :
      Fin (P.extendExactList hn_pos hn_lt hnext hcomm l hl).pc.r → Fin p) :
    (((P.extendExactList hn_pos hn_lt hnext hcomm l hl).pc.wordEquiv e :
        (P.extendExactList hn_pos hn_lt hnext hcomm l hl).pc.subgroup) : Q) ∈
          zassenhausFiltration p Q t ↔
      ∀ i,
        (P.extendExactList hn_pos hn_lt hnext hcomm l hl).weight i < t →
          e i = 0 := by
  induction l generalizing P with
  | nil =>
      exact hmem hnt htm e
  | cons x l ih =>
      simp only [extendExactList] at e ⊢
      let hx :
          x ∈ exactGeneratorSet p Q n :=
        hl x (by simp)
      let P' :=
        P.extendExactGenerator hn_pos hn_lt hnext hcomm x hx
      have hnext' :
          zassenhausFiltration p Q (n + 1) ≤ P'.pc.subgroup :=
        fun z hz =>
          P.exact_generator hn_pos hn_lt hnext hcomm x hx (hnext hz)
      have hmem' :
          ∀ {t : ℕ}, n < t → t ≤ m → ∀ e : Fin P'.pc.r → Fin p,
            ((P'.pc.wordEquiv e : P'.pc.subgroup) : Q) ∈
                zassenhausFiltration p Q t ↔
              ∀ i, P'.weight i < t → e i = 0 := by
        classical
        by_cases hxP : x ∈ P.pc.subgroup
        · rw [show P' = P from
            P.extend_exact hn_pos hn_lt hnext hcomm x hx hxP]
          exact hmem
        · rw [show P' =
              P.appendExactSucc hn_pos hn_lt hnext x hx
                (hcomm hn_lt hx) hxP from
            P.extend_exact_not hn_pos hn_lt hnext hcomm x hx hxP]
          simp only [appendExactSucc]
          intro hnt htm e
          exact
            P.extend_zero_below
              x hn_pos hn_lt
              hx
              (hnext
                (exact_filtration_succ hn_pos hx))
              hxP
              (fun y => hnext (hcomm hn_lt hx y))
              hnext hmem hnt htm e
      apply ih
      exact hmem'

/-- The finite list of all exact-weight generators in a finite group. -/
noncomputable def exactGeneratorList
    {p : ℕ}
    (Q : Type u) [Group Q] [Fintype Q]
    (n : ℕ) :
    List Q := by
  classical
  exact
    (Finset.univ.filter fun x => x ∈ exactGeneratorSet p Q n).toList

lemma exact_generator_list
    {p : ℕ}
    {Q : Type u} [Group Q] [Fintype Q]
    {n : ℕ}
    {x : Q} :
    x ∈ exactGeneratorList (p := p) Q n ↔
      x ∈ exactGeneratorSet p Q n := by
  classical
  simp [exactGeneratorList]

/-- Folding over all exact generators upgrades a cyclic-PC prefix for `D_(n+1)` to a cyclic-PC
prefix for `D_n`. -/
lemma extend_boundary_subgroup
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hP : P.pc.subgroup ≤ zassenhausFiltration p Q n)
    (hcomm : ExactSuccBound p Q m) :
    (P.extendExactList hn_pos hn_lt hnext hcomm
        (exactGeneratorList (p := p) Q n)
        (fun _ hx => exact_generator_list.mp hx)).pc.subgroup =
      zassenhausFiltration p Q n := by
  apply le_antisymm
  · exact
      P.extend_exact_subgroup hn_pos hn_lt hnext hcomm
        (exactGeneratorList (p := p) Q n)
        (fun x hx => exact_generator_list.mp hx)
        hP
  · rw [exact_sup_succ]
    apply sup_le
    · rw [Subgroup.closure_le]
      intro x hx
      exact
        P.extend_exact_list hn_pos hn_lt hnext hcomm
          (exactGeneratorList (p := p) Q n)
          (fun z hz => exact_generator_list.mp hz)
          (exact_generator_list.mpr hx)
    · exact
        fun x hx =>
          P.extend_generator_list hn_pos hn_lt hnext hcomm
            (exactGeneratorList (p := p) Q n)
            (fun z hz => exact_generator_list.mp hz)
            (hnext hx)

/-- Adjoin all exact generators from one boundary layer. -/
noncomputable def extendExactBoundary
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m) :
    WPForm p Q m :=
  P.extendExactList hn_pos hn_lt hnext hcomm
    (exactGeneratorList (p := p) Q n)
    (fun _ hx => exact_generator_list.mp hx)

/-- The one-boundary constructor has subgroup exactly `D_n` when its input lies between
`D_(n+1)` and `D_n`. -/
lemma extend_exact_boundary
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hP : P.pc.subgroup ≤ zassenhausFiltration p Q n)
    (hcomm : ExactSuccBound p Q m) :
    (P.extendExactBoundary hn_pos hn_lt hnext hcomm).pc.subgroup =
      zassenhausFiltration p Q n := by
  exact P.extend_boundary_subgroup hn_pos hn_lt hnext hP hcomm

/-- Adjoining one exact boundary preserves the current lower bound on selected weights. -/
lemma extend_boundary_weight
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (hweight : ∀ i, n ≤ P.weight i) :
    ∀ i, n ≤ (P.extendExactBoundary hn_pos hn_lt hnext hcomm).weight i := by
  exact
    P.extend_exact_weight hn_pos hn_lt hnext hcomm
      (exactGeneratorList (p := p) Q n)
      (fun _ hx => exact_generator_list.mp hx)
      hweight

/-- Adjoining one exact boundary preserves the coordinate description of every strictly deeper
term. -/
lemma extend_boundary_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m n : ℕ}
    (P : WPForm p Q m)
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hnext : zassenhausFiltration p Q (n + 1) ≤ P.pc.subgroup)
    (hcomm : ExactSuccBound p Q m)
    (hmem :
      ∀ {t : ℕ}, n < t → t ≤ m → ∀ e : Fin P.pc.r → Fin p,
        ((P.pc.wordEquiv e : P.pc.subgroup) : Q) ∈
            zassenhausFiltration p Q t ↔
          ∀ i, P.weight i < t → e i = 0)
    {t : ℕ}
    (hnt : n < t)
    (htm : t ≤ m)
    (e : Fin (P.extendExactBoundary hn_pos hn_lt hnext hcomm).pc.r → Fin p) :
    (((P.extendExactBoundary hn_pos hn_lt hnext hcomm).pc.wordEquiv e :
        (P.extendExactBoundary hn_pos hn_lt hnext hcomm).pc.subgroup) : Q) ∈
          zassenhausFiltration p Q t ↔
      ∀ i, (P.extendExactBoundary hn_pos hn_lt hnext hcomm).weight i < t →
        e i = 0 := by
  exact
    P.extend_exact_below
      hn_pos hn_lt hnext hcomm
      (exactGeneratorList (p := p) Q n)
      (fun _ hx => exact_generator_list.mp hx)
      hmem hnt htm e

/-- A cyclic-PC prefix at one exact filtration boundary, together with the coordinate invariant
for all deeper terms. -/
structure BState
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q]
    (m b : ℕ) where
  P : WPForm p Q m
  subgroup_eq : P.pc.subgroup = zassenhausFiltration p Q b
  weight_ge : ∀ i, b ≤ P.weight i
  mem_iff_below :
    ∀ {t : ℕ}, b ≤ t → t ≤ m → ∀ e : Fin P.pc.r → Fin p,
      ((P.pc.wordEquiv e : P.pc.subgroup) : Q) ∈
          zassenhausFiltration p Q t ↔
        ∀ i, P.weight i < t → e i = 0

namespace BState

/-- The empty cyclic-PC prefix is the boundary state at a killed cutoff. -/
noncomputable def atCutoff
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (hbot : zassenhausFiltration p Q m = ⊥) :
    BState p Q m m := by
  let P : WPForm p Q m := empty p Q m
  refine
    { P := P
      subgroup_eq := ?_
      weight_ge := ?_
      mem_iff_below := ?_ }
  · change (empty p Q m).pc.subgroup = zassenhausFiltration p Q m
    rw [base_subgroup, hbot]
  · intro i
    exact Fin.elim0 i
  · intro t _hmt _htm e
    constructor
    · intro _he i
      exact Fin.elim0 i
    · intro _he
      have hone : ((P.pc.wordEquiv e : P.pc.subgroup) : Q) = 1 := by
        rw [P.pc.wordEquiv_apply]
        rfl
      rw [hone]
      exact Subgroup.one_mem _

/-- Lower one positive boundary by adjoining every exact generator of that weight. -/
noncomputable def lowerSucc
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m n : ℕ}
    (S : BState p Q m (n + 1))
    (hn_pos : 0 < n)
    (hn_lt : n < m)
    (hcomm : ExactSuccBound p Q m) :
    BState p Q m n := by
  let hnext :
      zassenhausFiltration p Q (n + 1) ≤ S.P.pc.subgroup := by
    rw [S.subgroup_eq]
  let hP :
      S.P.pc.subgroup ≤ zassenhausFiltration p Q n := by
    rw [S.subgroup_eq]
    exact zassenhausFiltration_antitone p Q (Nat.le_succ n)
  let R : WPForm p Q m :=
    S.P.extendExactBoundary hn_pos hn_lt hnext hcomm
  have hR :
      R.pc.subgroup = zassenhausFiltration p Q n :=
    S.P.extend_exact_boundary hn_pos hn_lt hnext hP hcomm
  have hRweight :
      ∀ i, n ≤ R.weight i :=
    S.P.extend_boundary_weight hn_pos hn_lt hnext hcomm
      (fun i => (Nat.le_succ n).trans (S.weight_ge i))
  refine
    { P := R
      subgroup_eq := hR
      weight_ge := hRweight
      mem_iff_below := ?_ }
  intro t hnt htm e
  rcases lt_or_eq_of_le hnt with hnt | rfl
  · exact
      S.P.extend_boundary_below
        hn_pos hn_lt hnext hcomm
        (fun {u} hnu hum a => S.mem_iff_below (by omega) hum a)
        hnt htm e
  · constructor
    · intro _he i hi
      exact ((Nat.not_lt_of_ge (hRweight i)) hi).elim
    · intro _he
      rw [← hR]
      exact (R.pc.wordEquiv e).property

/-- Descend a positive boundary state to the whole-group boundary `D₁`. -/
noncomputable def descendToOne
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m : ℕ}
    (hcomm : ExactSuccBound p Q m) :
    (b : ℕ) → 1 ≤ b → b ≤ m → BState p Q m b → BState p Q m 1
  | 0, hb, _hbm, _S => by omega
  | b + 1, _hb, hbm, S =>
      if hbzero : b = 0 then by
        subst b
        exact S
      else
        descendToOne hcomm b
          (Nat.one_le_iff_ne_zero.mpr hbzero)
          ((Nat.le_succ b).trans hbm)
          (S.lowerSucc
            (Nat.pos_of_ne_zero hbzero)
            ((Nat.lt_succ_self b).trans_le hbm)
            hcomm)

/-- A killed cutoff and exact-generator successor centrality give a boundary state for the
whole finite group. -/
noncomputable def full
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hcomm : ExactSuccBound p Q m) :
    BState p Q m 1 :=
  descendToOne hcomm m hm le_rfl (atCutoff hbot)

end BState

/-- Recursively adjoin exact generators in descending weight order, starting from a cyclic-PC
prefix for `D_(b+1)` and ending with a cyclic-PC normal form for `D₁`. -/
noncomputable def descendExactBoundaries
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m : ℕ}
    (hcomm : ExactSuccBound p Q m) :
    (b : ℕ) →
      b < m →
        (P : WPForm p Q m) →
          P.pc.subgroup = zassenhausFiltration p Q (b + 1) →
            { R : WPForm p Q m //
              R.pc.subgroup = zassenhausFiltration p Q 1 }
  | 0, _hb, P, hP => ⟨P, hP⟩
  | b + 1, hb, P, hP =>
      let P' : WPForm p Q m :=
        P.extendExactBoundary (Nat.succ_pos b) hb
          (by
            rw [hP])
          hcomm
      have hP' :
          P'.pc.subgroup = zassenhausFiltration p Q (b + 1) := by
        apply P.extend_exact_boundary
        rw [hP]
        exact zassenhausFiltration_antitone p Q (Nat.le_succ (b + 1))
      descendExactBoundaries hcomm b (by omega) P' hP'

/-- A killed positive Zassenhaus cutoff and exact-generator successor centrality produce a
weighted cyclic-PC normal form for the whole finite group. -/
noncomputable def fullPCForm
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hcomm : ExactSuccBound p Q m) :
    { R : WPForm p Q m //
      R.pc.subgroup = ⊤ } := by
  let P : WPForm p Q m :=
    empty p Q m
  have hP :
      P.pc.subgroup = zassenhausFiltration p Q (m - 1 + 1) := by
    rw [Nat.sub_add_cancel hm, hbot]
    rfl
  let R :=
    descendExactBoundaries hcomm (m - 1) (by omega) P hP
  refine ⟨R.1, ?_⟩
  rw [R.2, filtration_one_top]

/-- Coercion identifies a subgroup known to be top with the ambient group. -/
noncomputable def subgroupEquivTop
    {Q : Type u} [Group Q]
    (H : Subgroup Q)
    (hH : H = ⊤) :
    H ≃ Q := by
  apply Equiv.ofBijective (fun x : H => (x : Q))
  constructor
  · exact Subtype.coe_injective
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [hH]
    exact Subgroup.mem_top x

@[simp]
lemma subgroup_equiv_top
    {Q : Type u} [Group Q]
    (H : Subgroup Q)
    (hH : H = ⊤)
    (x : H) :
    subgroupEquivTop H hH x = (x : Q) :=
  rfl

/-- Package a top weighted cyclic-PC prefix as ordered Zassenhaus representatives once its
coordinates detect filtration membership. -/
noncomputable def orderedZassenhausReps
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (P : WPForm p Q m)
    (hPtop : P.pc.subgroup = ⊤)
    (hmem :
      ∀ {t : ℕ} (_ht : t ≤ m) (e : Fin P.pc.r → Fin p),
        ((P.pc.wordEquiv e : P.pc.subgroup) : Q) ∈
            zassenhausFiltration p Q t ↔
          ∀ i, P.weight i < t → e i = 0) :
    OZReps p Q m where
  r := P.pc.r
  gen := P.pc.gen
  weight := P.weight
  weight_pos := P.weight_pos
  weight_lt := P.weight_lt
  gen_mem := P.gen_mem
  wordEquiv := P.pc.wordEquiv.trans (subgroupEquivTop P.pc.subgroup hPtop)
  wordEquiv_apply := by
    intro e
    rw [Equiv.trans_apply, subgroup_equiv_top, P.pc.wordEquiv_apply]
    exact cyclic_pc_fin P.pc.gen e
  mem_iff_below := by
    intro t ht e
    simpa only [Equiv.trans_apply, subgroup_equiv_top] using hmem ht e

/-- Ordered Zassenhaus representatives together with the exact-weight provenance of every
selected generator. -/
structure ExactOrderedReps
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q]
    (m : ℕ) where
  reps : OZReps p Q m
  gen_exact_mem :
    ∀ i, reps.gen i ∈ exactGeneratorSet p Q (reps.weight i)

/-- Package a top weighted cyclic-PC prefix as exact ordered representatives. -/
noncomputable def exactOrderedReps
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (P : WPForm p Q m)
    (hPtop : P.pc.subgroup = ⊤)
    (hmem :
      ∀ {t : ℕ} (_ht : t ≤ m) (e : Fin P.pc.r → Fin p),
        ((P.pc.wordEquiv e : P.pc.subgroup) : Q) ∈
            zassenhausFiltration p Q t ↔
          ∀ i, P.weight i < t → e i = 0) :
    ExactOrderedReps p Q m where
  reps := P.orderedZassenhausReps hPtop hmem
  gen_exact_mem := P.gen_exact_mem

/-- A killed finite Zassenhaus cutoff and exact-generator successor centrality produce ordered
Zassenhaus representatives with exact filtration coordinates and exact-weight provenance. -/
theorem nonempty_exact_succ
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hcomm : ExactSuccBound p Q m) :
    Nonempty (ExactOrderedReps (p := p) Q m) := by
  letI := Fintype.ofFinite Q
  let S : BState p Q m 1 :=
    BState.full hm hbot hcomm
  have htop : S.P.pc.subgroup = ⊤ := by
    rw [S.subgroup_eq, filtration_one_top]
  refine ⟨S.P.exactOrderedReps htop ?_⟩
  intro t htm e
  by_cases ht : 1 ≤ t
  · exact S.mem_iff_below ht htm e
  · have htzero : t = 0 := by omega
    subst t
    constructor
    · intro _he i hi
      omega
    · intro _he
      rw [filtration_zero_top]
      exact Subgroup.mem_top _

/-- A killed finite Zassenhaus cutoff and the additive commutator law produce ordered
Zassenhaus representatives with exact filtration coordinates and exact-weight provenance. -/
theorem nonempty_reps_law
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    Nonempty (ExactOrderedReps (p := p) Q m) := by
  apply
    nonempty_exact_succ
      hm hbot
  intro n x _hn hx y
  exact
    hcomm
      (exact_subset_filtration hx)
      (by
        rw [filtration_one_top]
        exact Subgroup.mem_top y)

/-- A killed finite Zassenhaus cutoff and the additive commutator law produce ordered
Zassenhaus representatives with exact filtration coordinates. -/
theorem reps_commutator_law
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    Nonempty (OZReps (p := p) Q m) := by
  rcases
      nonempty_reps_law
        hm hbot hcomm with
    ⟨O⟩
  exact ⟨O.reps⟩

end WPForm

end TJennin
end Towers
