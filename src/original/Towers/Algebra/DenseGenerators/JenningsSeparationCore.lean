import Mathlib
import Towers.Algebra.DenseGenerators.OrderedJennings


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

/-- Minimal fixed-degree Jennings certificate.

This deliberately avoids coordinates, bases, associated gradeds, PBW maps, and any extra quotient
linear algebra. It stores only the kernel consequence needed downstream. -/
structure JenningsLayerCertificate
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [Finite G]
    (n : ℕ) where
  drop_sub_next :
    ∀ {g : G},
      g ∈ zassenhausFiltration p G n →
      groupAlgebraSub p G g ∈ augmentationIdealPower p G (n + 1) →
        g ∈ zassenhausFiltration p G (n + 1)

/-- Truncated Jennings separation, as a formal wrapper around the exact finite Jennings step.

With the generator-set definition of `zassenhausFiltration`, the hypothesis `hstep` is the hard
PBW/Jennings input. Once that step is available, the quotient case where `D_(n+1)` has been killed
is just subgroup bookkeeping. -/
theorem separation_d_step
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {n : ℕ}
    (_hn : 0 < n)
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    (hstep :
      ∀ {x : Q},
        x ∈ zassenhausFiltration p Q n →
        groupAlgebraSub p Q x ∈ augmentationIdealPower p Q (n + 1) →
          x ∈ zassenhausFiltration p Q (n + 1))
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hqI :
      groupAlgebraSub p Q q ∈ augmentationIdealPower p Q (n + 1)) :
    q = 1 := by
  have hqDsucc : q ∈ zassenhausFiltration p Q (n + 1) :=
    hstep hqD hqI
  have hqbot : q ∈ (⊥ : Subgroup Q) := by
    simpa [hbot] using hqDsucc
  exact Subgroup.mem_bot.mp hqbot

/-- The span of basis vectors whose Jennings weight is at least `s`. -/
def basisHighSpan
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (s : ℕ) :
    Submodule (ZMod p) (denseGroupAlgebra p Q) :=
  Submodule.span (ZMod p) (B '' { e : κ | s ≤ wt e })

/-- The high-weight spans are antitone in the lower weight cutoff. -/
lemma basis_high_antitone
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    {s t : ℕ}
    (hst : s ≤ t) :
    basisHighSpan (p := p) (Q := Q) B wt t ≤
      basisHighSpan (p := p) (Q := Q) B wt s := by
  unfold basisHighSpan
  refine Submodule.span_mono ?_
  rintro x ⟨e, he, rfl⟩
  exact ⟨e, le_trans hst he, rfl⟩

/-- A basis vector of weight at least `s` lies in the high-weight span. -/
lemma basis_high_weight
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    {s : ℕ} {e : κ}
    (he : s ≤ wt e) :
    B e ∈ basisHighSpan (p := p) (Q := Q) B wt s := by
  exact Submodule.subset_span ⟨e, he, rfl⟩

/-- A vector in the span of selected basis vectors has zero coordinates outside the selection. -/
lemma basis_repr_image
    {R : Type*} [Semiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {κ : Type*}
    (B : Module.Basis κ R M)
    {S : Set κ}
    {v : M} {i : κ}
    (hv : v ∈ Submodule.span R (B '' S))
    (hi : i ∉ S) :
    B.repr v i = 0 := by
  classical
  refine Submodule.span_induction
    (s := B '' S)
    (p := fun x _ => B.repr x i = 0)
    ?_ ?_ ?_ ?_ hv
  · intro x hx
    rcases hx with ⟨j, hj, rfl⟩
    by_cases hji : j = i
    · exact False.elim (hi (hji ▸ hj))
    · rw [B.repr_self]
      simp [hji]
  · simp
  · intro x y _hx _hy hx_zero hy_zero
    simp [hx_zero, hy_zero]
  · intro a x _hx hx_zero
    simp [hx_zero]

/-- Coordinates below the cutoff vanish for vectors in the high-weight span. -/
lemma basis_repr_high
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    {s : ℕ}
    {a : denseGroupAlgebra p Q}
    {e : κ}
    (ha : a ∈ basisHighSpan (p := p) (Q := Q) B wt s)
    (he : wt e < s) :
    B.repr a e = 0 := by
  exact
    basis_repr_image
      (B := B)
      (S := { e : κ | s ≤ wt e })
      ha
      (not_le_of_gt he)

/-- Membership in a high-weight basis span is equivalent to vanishing of all lower-weight
coordinates. -/
lemma basis_high_repr
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    {s : ℕ}
    {a : denseGroupAlgebra p Q} :
    a ∈ basisHighSpan (p := p) (Q := Q) B wt s ↔
      ∀ e : κ, wt e < s → B.repr a e = 0 := by
  constructor
  · intro ha e he
    exact basis_repr_high (B := B) (wt := wt) ha he
  · intro hzero
    unfold basisHighSpan
    rw [B.mem_span_image]
    intro e he
    by_contra hnot
    have he_zero : B.repr a e = 0 := hzero e (Nat.lt_of_not_ge hnot)
    have he_ne : B.repr a e ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using he
    exact he_ne he_zero

/-- If every ordered word of cutoff `s` has zero coordinates below `s`, then the ordered word span
is contained in the corresponding high-weight basis span. -/
lemma OZReps.wordspanle_basishighweight_spanwordcoords
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    {s : ℕ}
    (hword :
      ∀ w : List (Fin O.r),
        s ≤ O.wordWeight w →
          ∀ e : κ, wt e < s → B.repr (O.wordEval w) e = 0) :
    O.wordSpan s ≤ basisHighSpan (p := p) (Q := Q) B wt s := by
  intro x hx
  refine
    (basis_high_repr
      (B := B) (wt := wt) (s := s) (a := x)).2 ?_
  intro e he
  have hxspan :
      x ∈ Submodule.span (ZMod p)
        { x | ∃ w : List (Fin O.r), s ≤ O.wordWeight w ∧ O.wordEval w = x } := by
    simpa [OZReps.wordSpan] using hx
  refine Submodule.span_induction
    (s := { x | ∃ w : List (Fin O.r), s ≤ O.wordWeight w ∧ O.wordEval w = x })
    (p := fun z _ => B.repr z e = 0)
    ?mem ?zero ?add ?smul hxspan
  · rintro z ⟨w, hw, rfl⟩
    exact hword w hw e he
  · simp
  · intro x y _hx _hy hx_zero hy_zero
    simp [hx_zero, hy_zero]
  · intro c x _hx hx_zero
    simp [hx_zero]

/-- Congruent algebra elements have the same low coordinates once the word-span generators at
that cutoff have zero low coordinates. -/
lemma OZReps.basisrepr_eqalgcongruent_modwordspan
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    {s : ℕ}
    {x y : denseGroupAlgebra p Q}
    (hword :
      ∀ w : List (Fin O.r),
        s ≤ O.wordWeight w →
          ∀ e : κ, wt e < s → B.repr (O.wordEval w) e = 0)
    (hxy : O.AlgebraCongruentSpan s x y)
    {e : κ}
    (he : wt e < s) :
    B.repr x e = B.repr y e := by
  have hdiff_word : x - y ∈ O.wordSpan s := by
    simpa [OZReps.AlgebraCongruentSpan] using hxy
  have hdiff_high :
      x - y ∈ basisHighSpan (p := p) (Q := Q) B wt s :=
    O.wordspanle_basishighweight_spanwordcoords B wt hword hdiff_word
  have hzero :
      B.repr (x - y) e = 0 :=
    basis_repr_high
      (B := B) (wt := wt) hdiff_high he
  have hsub : B.repr x e - B.repr y e = 0 := by
    simpa using hzero
  exact sub_eq_zero.mp hsub

/-- Word-evaluation congruence is a coordinate equality statement below the cutoff, once the
cutoff word-span generators are known to have zero low coordinates. -/
lemma OZReps.basisreprword_evaleqwordeval_conmodworspa
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    {s : ℕ}
    {w₁ w₂ : List (Fin O.r)}
    (hword :
      ∀ w : List (Fin O.r),
        s ≤ O.wordWeight w →
          ∀ e : κ, wt e < s → B.repr (O.wordEval w) e = 0)
    (hxy : O.CongruentModSpan s w₁ w₂)
    {e : κ}
    (he : wt e < s) :
    B.repr (O.wordEval w₁) e = B.repr (O.wordEval w₂) e :=
  O.basisrepr_eqalgcongruent_modwordspan B wt hword hxy he

/-- The generic positive augmentation power is contained in a high-weight basis span once the
ordered word-span generators have the corresponding coordinate vanishing. -/
lemma OZReps.augidealpower_succlebasishigh_weispaworcoo
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hm : 1 ≤ m)
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (s : ℕ)
    (hword :
      ∀ w : List (Fin O.r),
        s + 1 ≤ O.wordWeight w →
          ∀ e : κ, wt e < s + 1 → B.repr (O.wordEval w) e = 0) :
    augmentationIdealPower p Q (s + 1) ≤
      basisHighSpan (p := p) (Q := Q) B wt (s + 1) := by
  intro y hy
  have hyI :
      y ∈ denseGeneratorsIdeal p Q ^ (s + 1) :=
    (Submodule.restrictScalars_mem (ZMod p)
      (denseGeneratorsIdeal p Q ^ (s + 1)) y).mp
      (by simpa [augmentationIdealPower] using hy)
  have hyWord :
      y ∈ denseGeneratorsSpan p Q (s + 1) :=
    (dense_algebra_span
      (p := p) (Λ := Q) (n := s) (x := y)).1 hyI
  have hyOrdered : y ∈ O.wordSpan (s + 1) :=
    O.augmentation_span_ordered hm (s + 1) hyWord
  exact
    O.wordspanle_basishighweight_spanwordcoords B wt hword hyOrdered

/-- The exact finite Jennings/PBW data needed by the final kernel argument.

The hard future task is to construct this from ordered representatives of the surviving
Zassenhaus layers. Once it is available, the kernel calculation below is just linear algebra. -/
structure JSData
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q]
    (m : ℕ) : Type (max (u + 1) (v + 1)) where
  ι : Type v
  decEq : DecidableEq ι
  basis : Module.Basis ι (ZMod p) (denseGroupAlgebra p Q)
  weight : ι → ℕ
  aug_power :
    augmentationIdealPower p Q m ≤
      basisHighSpan (p := p) (Q := Q) basis weight m
  separates :
    ∀ {q : Q}, q ≠ 1 →
      ∃ e : ι,
        weight e < m ∧
          basis.repr (groupAlgebraSub p Q q) e ≠ 0

/-- A coordinate criterion for constructing `JSData`.

The hard `aug_power` field can be supplied by proving that every element of `I^m` has all
coordinates of weight `< m` equal to zero. -/
lemma nonempty_separation_criteria
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    {ι : Type v}
    (B : Module.Basis ι (ZMod p) (denseGroupAlgebra p Q))
    (wt : ι → ℕ)
    (haug :
      ∀ a : denseGroupAlgebra p Q,
        a ∈ augmentationIdealPower p Q m →
          ∀ e : ι, wt e < m → B.repr a e = 0)
    (hsep :
      ∀ q : Q, q ≠ 1 →
        ∃ e : ι,
          wt e < m ∧
            B.repr (groupAlgebraSub p Q q) e ≠ 0) :
    Nonempty (JSData.{u, v} (p := p) Q m) := by
  classical
  refine
    ⟨{ ι := ι
       decEq := Classical.decEq ι
       basis := B
       weight := wt
       aug_power := ?_
       separates := fun {q} hq => hsep q hq }⟩
  · intro a ha
    exact
      (basis_high_repr
        (B := B) (wt := wt) (s := m) (a := a)).2
        (by
          intro e he
          exact haug a ha e he)

/-- A killed-layer kernel theorem gives Jennings separation data.

This is only linear algebra: choose a complement to `I^m`, use bases on the two summands, and
assign weight `m` to the `I^m` summand and weight zero to its complement. -/
lemma nonempty_jennings_separation
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 0 < m)
    (hker :
      ∀ {q : Q},
        groupAlgebraSub p Q q ∈ augmentationIdealPower p Q m →
          q = 1) :
    Nonempty (JSData.{u, 0} (p := p) Q m) := by
  classical
  let I := augmentationIdealPower p Q m
  obtain ⟨C, hIC⟩ := Submodule.exists_isCompl I
  let bI := Module.finBasis (ZMod p) I
  let bC := Module.finBasis (ZMod p) C
  let B :
      Module.Basis
        (Fin (Module.finrank (ZMod p) I) ⊕ Fin (Module.finrank (ZMod p) C))
        (ZMod p)
        (denseGroupAlgebra p Q) :=
    (bI.prod bC).map (Submodule.prodEquivOfIsCompl I C hIC)
  let wt :
      (Fin (Module.finrank (ZMod p) I) ⊕ Fin (Module.finrank (ZMod p) C)) → ℕ :=
    Sum.elim (fun _ => m) (fun _ => 0)
  refine
    nonempty_separation_criteria
      (B := B) (wt := wt) ?_ ?_
  · intro a ha e he
    cases e with
    | inl i =>
        simp [wt] at he
    | inr i =>
        have haI : a ∈ I := by
          simpa [I] using ha
        simp [B, Submodule.prodEquivOfIsCompl_symm_apply_left I C hIC ⟨a, haI⟩]
  · intro q hq
    have hsnd :
        ((Submodule.prodEquivOfIsCompl I C hIC).symm
          (groupAlgebraSub p Q q)).2 ≠ 0 := by
      intro hsnd
      apply hq
      apply hker
      change groupAlgebraSub p Q q ∈ I
      exact
        (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero I C hIC).mp hsnd
    have hcoord :
        ∃ i : Fin (Module.finrank (ZMod p) C),
          bC.repr
            ((Submodule.prodEquivOfIsCompl I C hIC).symm
              (groupAlgebraSub p Q q)).2 i ≠ 0 := by
      by_contra hnone
      apply hsnd
      apply (bC.forall_coord_eq_zero_iff).mp
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hcoord
    refine ⟨Sum.inr i, ?_, ?_⟩
    · simpa [wt] using hm
    · simpa [B] using hi

/-- If `I^m` lies in the high-weight span and every nontrivial group element has a low nonzero
coordinate, then membership in `I^m` forces the element to be trivial. -/
theorem aug_high_span
    {κ : Type v}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (B : Module.Basis κ (ZMod p) (denseGroupAlgebra p Q))
    (wt : κ → ℕ)
    (hI :
      augmentationIdealPower p Q m ≤
        basisHighSpan (p := p) (Q := Q) B wt m)
    (hsep :
      ∀ {q : Q}, q ≠ 1 →
        ∃ e : κ,
          wt e < m ∧
            B.repr (groupAlgebraSub p Q q) e ≠ 0)
    {q : Q}
    (hqI : groupAlgebraSub p Q q ∈ augmentationIdealPower p Q m) :
    q = 1 := by
  by_contra hq
  obtain ⟨e, hewt, hcoeff⟩ := hsep hq
  have hzero :
      B.repr (groupAlgebraSub p Q q) e = 0 :=
    basis_repr_high
      (B := B) (wt := wt) (hI hqI) hewt
  exact hcoeff hzero

/-- Kernel consequence of the packaged Jennings separation data. -/
theorem JSData.kernel
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (D : JSData (p := p) Q m)
    {q : Q}
    (hqI : groupAlgebraSub p Q q ∈ augmentationIdealPower p Q m) :
    q = 1 := by
  exact
    aug_high_span
      (B := D.basis)
      (wt := D.weight)
      D.aug_power
      D.separates
      hqI

/-- Kernel theorem from the existence of Jennings separation data. -/
theorem truncated_separation_data
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (hdata : Nonempty (JSData (p := p) Q m))
    {q : Q}
    (hqI : groupAlgebraSub p Q q ∈ augmentationIdealPower p Q m) :
    q = 1 := by
  rcases hdata with ⟨D⟩
  exact D.kernel hqI

/-- Jennings separation data for every finite group with killed `D_n` gives the finite
trivial-Zassenhaus upper theorem.

This repackages the already-proved kernel consequence of `JSData` into the finite
ordinary group-algebra interface used by the profinite reduction. -/
def trivial_separation_data
    {p : ℕ} [Fact p.Prime]
    {n : ℕ}
    (Hdata :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          Nonempty (JSData (p := p) Q n)) :
    TUBound.{u} (p := p) n := by
  refine
    { one_trivial_zassenhaus := ?_ }
  intro Q _instGroupQ _instFiniteQ hbot q hq
  have hqI_ideal :
      groupAlgebraSub p Q q ∈
        denseGeneratorsIdeal p Q ^ n := by
    simpa [groupAlgebraSub, dDCongru] using hq
  have hqI :
      groupAlgebraSub p Q q ∈ augmentationIdealPower p Q n := by
    simpa [augmentationIdealPower] using
      (Submodule.restrictScalars_mem (ZMod p)
        (denseGeneratorsIdeal p Q ^ n)
        (groupAlgebraSub p Q q)).mpr hqI_ideal
  exact
    truncated_separation_data
      (p := p) (Q := Q) (m := n) (Hdata hbot) hqI

/-- Jennings separation data for every finite killed `D_n` quotient gives the finite positive
dimension upper bound at level `n`.

The passage from the killed case to an arbitrary finite group is the existing
self-quotient reduction in
`TUBound.pos_dim_upperbound`. -/
def jennings_separation_data
    {p : ℕ} [Fact p.Prime]
    {n : ℕ}
    (Hdata :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          Nonempty (JSData (p := p) Q n)) :
    DenseUpperBound.{u} (p := p) n :=
  (trivial_separation_data
    (p := p) (n := n) Hdata).pos_dim_upperbound

/-- The target theorem reduced to constructing finite Jennings separation data. -/
theorem jennings_separation_d
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {n : ℕ}
    (_hn : 0 < n)
    (_hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    (hdata :
      Nonempty (JSData (p := p) Q (n + 1)))
    {q : Q}
    (_hqD : q ∈ zassenhausFiltration p Q n)
    (hqI :
      groupAlgebraSub p Q q ∈ augmentationIdealPower p Q (n + 1)) :
    q = 1 := by
  exact
    truncated_separation_data
      (p := p) (Q := Q) (m := n + 1) hdata hqI

/-- The target theorem reduced to coordinate criteria for a Jennings-weighted basis. -/
theorem separation_d_criteria
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {n : ℕ}
    (hn : 0 < n)
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {ι : Type v}
    (B : Module.Basis ι (ZMod p) (denseGroupAlgebra p Q))
    (wt : ι → ℕ)
    (haug :
      ∀ a : denseGroupAlgebra p Q,
        a ∈ augmentationIdealPower p Q (n + 1) →
          ∀ e : ι, wt e < n + 1 → B.repr a e = 0)
    (hsep :
      ∀ q : Q, q ≠ 1 →
        ∃ e : ι,
          wt e < n + 1 ∧
            B.repr (groupAlgebraSub p Q q) e ≠ 0)
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hqI :
      groupAlgebraSub p Q q ∈ augmentationIdealPower p Q (n + 1)) :
    q = 1 := by
  have hdata :
      Nonempty (JSData.{u, v} (p := p) Q (n + 1)) :=
    nonempty_separation_criteria
      (p := p) (Q := Q) (m := n + 1) B wt haug hsep
  exact
    jennings_separation_d
      (p := p) (Q := Q) (n := n) hn hbot hdata hqD hqI

/-- Once an ordered normal form, a Jennings-indexed basis, the high-weight vanishing for `I^m`,
and the explicit expansion of `[word] - 1` are available, they produce
`JSData`. -/
lemma OZReps.nonemptjenning_sepdata_basisexpansion
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (B : Module.Basis (Fin O.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (haug :
      ∀ a : denseGroupAlgebra p Q,
        a ∈ augmentationIdealPower p Q m →
          ∀ e : Fin O.r → Fin p,
            expWeight (p := p) (r := O.r) O.weight e < m →
              B.repr a e = 0)
    (hexp :
      ∀ e : Fin O.r → Fin p,
        groupAlgebraSub p Q (O.wordEquiv e) =
          ∑ a : Fin O.r → Fin p,
            orderedJenningsCoeff (p := p) e a • B a) :
    Nonempty (JSData.{u, 0} (p := p) Q m) := by
  classical
  exact
    nonempty_separation_criteria
      (p := p) (Q := Q) (m := m)
      B
      (fun e : Fin O.r → Fin p =>
        expWeight (p := p) (r := O.r) O.weight e)
      haug
      (O.separates_sub_expansion hbot B hexp)

/-- In the successor cutoff case, it is enough to prove coordinate vanishing for the ordered
augmentation words.  The generic augmentation-power vanishing is supplied by the ordered word-span
bridge. -/
lemma OZReps.nonemptjenning_sepdatasucc_basiwordexpa
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {s : ℕ}
    (O : OZReps (p := p) Q (s + 1))
    (hbot : zassenhausFiltration p Q (s + 1) = ⊥)
    (B : Module.Basis (Fin O.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (hword :
      ∀ w : List (Fin O.r),
        s + 1 ≤ O.wordWeight w →
          ∀ e : Fin O.r → Fin p,
            expWeight (p := p) (r := O.r) O.weight e < s + 1 →
              B.repr (O.wordEval w) e = 0)
    (hexp :
      ∀ e : Fin O.r → Fin p,
        groupAlgebraSub p Q (O.wordEquiv e) =
          ∑ a : Fin O.r → Fin p,
            orderedJenningsCoeff (p := p) e a • B a) :
    Nonempty (JSData.{u, 0} (p := p) Q (s + 1)) := by
  classical
  refine
    O.nonemptjenning_sepdata_basisexpansion
      hbot B ?_ hexp
  intro a ha e he
  exact
    basis_repr_high
      (B := B)
      (wt := fun e : Fin O.r → Fin p =>
        expWeight (p := p) (r := O.r) O.weight e)
      ((O.augidealpower_succlebasishigh_weispaworcoo
          (Nat.succ_le_succ (Nat.zero_le s))
          B
          (fun e : Fin O.r → Fin p =>
            expWeight (p := p) (r := O.r) O.weight e)
          s
          hword) ha)
      he

/-- The remaining PBW word-coordinate statement for the canonical ordered Jennings monomial
basis.

It says that a noncommutative word in the ordered augmentation letters, whose total Zassenhaus
weight is at least the cutoff, has no coordinates in canonical Jennings monomials of lower weight.
This is the exact finite Jennings construction still needed to remove the early placeholder. -/
def OZReps.LowWeightwordCoordsvanish
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m) : Prop :=
  ∀ w : List (Fin O.r),
    m ≤ O.wordWeight w →
      ∀ e : Fin O.r → Fin p,
        expWeight (p := p) (r := O.r) O.weight e < m →
          O.jenningsMonomialBasis.repr (O.wordEval w) e = 0

/-- The same coordinate-vanishing target for one fixed word and one fixed cutoff. -/
def OZReps.LowWeightcoordsVanishword
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (s : ℕ)
    (w : List (Fin O.r)) : Prop :=
  ∀ e : Fin O.r → Fin p,
    expWeight (p := p) (r := O.r) O.weight e < s →
      O.jenningsMonomialBasis.repr (O.wordEval w) e = 0

/-- It suffices to prove each word has no coordinates below its own total weight. -/
lemma OZReps.lowweight_wordcoorvani_forawordweig
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (H :
      ∀ w : List (Fin O.r),
        O.LowWeightcoordsVanishword (O.wordWeight w) w) :
    O.LowWeightwordCoordsvanish := by
  intro w hmw e he
  exact H w e (lt_of_lt_of_le he hmw)

/-- The base case for the PBW collection induction: already ordered exponent-list words have the
claimed low-coordinate vanishing. -/
lemma OZReps.lowweight_coorvaniword_ordeexpolist
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (e : Fin O.r → Fin p) :
    O.LowWeightcoordsVanishword
      (O.wordWeight (orderedExponentList O.r e))
      (orderedExponentList O.r e) := by
  intro a ha
  exact
    O.jennings_monomial_repr
      (hw := le_rfl)
      ha

/-- If a word has been collected, modulo the cutoff word span, to an ordered exponent word of
weight at least that cutoff, then it satisfies the low-coordinate vanishing statement at that
cutoff. -/
lemma OZReps.lowweightcoords_vaniwordcong_ordeexpolist
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    {w : List (Fin O.r)}
    {e : Fin O.r → Fin p}
    (hword :
      ∀ v : List (Fin O.r),
        s ≤ O.wordWeight v →
          ∀ a : Fin O.r → Fin p,
            expWeight (p := p) (r := O.r) O.weight a < s →
              O.jenningsMonomialBasis.repr (O.wordEval v) a = 0)
    (hcong :
      O.CongruentModSpan s w (orderedExponentList O.r e))
    (hordered : s ≤ O.wordWeight (orderedExponentList O.r e)) :
    O.LowWeightcoordsVanishword s w := by
  intro a ha
  have hcoord :
      O.jenningsMonomialBasis.repr (O.wordEval w) a =
        O.jenningsMonomialBasis.repr
          (O.wordEval (orderedExponentList O.r e)) a :=
    O.basisreprword_evaleqwordeval_conmodworspa
      O.jenningsMonomialBasis
      (fun a : Fin O.r → Fin p =>
        expWeight (p := p) (r := O.r) O.weight a)
      hword
      hcong
      ha
  rw [hcoord]
  exact
    O.jennings_monomial_repr
      (hw := hordered)
      ha

/-- If a word is only an adjacent-swap permutation away from an ordered exponent-list word, then
the low-coordinate target follows from the ordered base case and the permutation congruence. -/
lemma OZReps.lowweightcoords_vanishwordperm_ordeexpolist
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    {w : List (Fin O.r)}
    {e : Fin O.r → Fin p}
    (hword :
      ∀ v : List (Fin O.r),
        O.wordWeight w ≤ O.wordWeight v →
          ∀ a : Fin O.r → Fin p,
            expWeight (p := p) (r := O.r) O.weight a < O.wordWeight w →
              O.jenningsMonomialBasis.repr (O.wordEval v) a = 0)
    (hperm : w.Perm (orderedExponentList O.r e)) :
    O.LowWeightcoordsVanishword (O.wordWeight w) w := by
  exact
    O.lowweightcoords_vaniwordcong_ordeexpolist
      hword
      (O.congruent_perm_list hperm)
      (le_of_eq (O.word_weight_perm hperm))

/-- The non-overflow PBW branch: if no letter occurs `p` times, the occurrence-count exponent
vector is a genuine `Fin p` normal form, so the word reduces to the ordered exponent-list case. -/
lemma OZReps.lowweight_coordsvanish_wordbounmult
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    {w : List (Fin O.r)}
    (hword :
      ∀ v : List (Fin O.r),
        O.wordWeight w ≤ O.wordWeight v →
          ∀ a : Fin O.r → Fin p,
            expWeight (p := p) (r := O.r) O.weight a < O.wordWeight w →
              O.jenningsMonomialBasis.repr (O.wordEval v) a = 0)
    (hbounded : O.WordMultiplicityBounded w) :
    O.LowWeightcoordsVanishword (O.wordWeight w) w := by
  exact
    O.lowweightcoords_vanishwordperm_ordeexpolist
      hword
      (O.perm_bounded_multiplicity w hbounded)

/-- If a word evaluation already lies in the high-weight word span, then it has no low Jennings
coordinates, assuming the cutoff word-span generators have that vanishing. -/
lemma OZReps.lowwei_vanis_evalm
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    {s : ℕ}
    {w : List (Fin O.r)}
    (hword :
      ∀ v : List (Fin O.r),
        s ≤ O.wordWeight v →
          ∀ a : Fin O.r → Fin p,
            expWeight (p := p) (r := O.r) O.weight a < s →
              O.jenningsMonomialBasis.repr (O.wordEval v) a = 0)
    (hw : O.wordEval w ∈ O.wordSpan s) :
    O.LowWeightcoordsVanishword s w := by
  intro a ha
  have hhigh :
      O.wordEval w ∈
        basisHighSpan
          (p := p)
          (Q := Q)
          O.jenningsMonomialBasis
          (fun a : Fin O.r → Fin p =>
            expWeight (p := p) (r := O.r) O.weight a)
          s :=
    O.wordspanle_basishighweight_spanwordcoords
      O.jenningsMonomialBasis
      (fun a : Fin O.r → Fin p =>
        expWeight (p := p) (r := O.r) O.weight a)
      hword
      hw
  exact
    basis_repr_high
      (B := O.jenningsMonomialBasis)
      (wt := fun a : Fin O.r → Fin p =>
        expWeight (p := p) (r := O.r) O.weight a)
      hhigh
      ha

/-- The overflow PBW branch at the coordinate level: if a word can be permuted to expose a
`p`-fold block, the block is already high-weight and hence has no low Jennings coordinates. -/
lemma OZReps.lowweightcoords_vanishwordperm_pthpowerblock
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    {w u v : List (Fin O.r)}
    {i : Fin O.r}
    (hword :
      ∀ z : List (Fin O.r),
        O.wordWeight w ≤ O.wordWeight z →
          ∀ a : Fin O.r → Fin p,
            expWeight (p := p) (r := O.r) O.weight a < O.wordWeight w →
              O.jenningsMonomialBasis.repr (O.wordEval z) a = 0)
    (hperm : w.Perm (u ++ List.replicate p i ++ v)) :
    O.LowWeightcoordsVanishword (O.wordWeight w) w := by
  exact
    O.lowwei_vanis_evalm
      hword
      (O.perm_pth_block hperm)

/-- The two PBW collection branches, packaged at the coordinate level. A word either has bounded
exponents and therefore reduces to its ordered count-vector monomial, or it exposes a `p`-block
which is already high-weight. -/
lemma OZReps.lowweight_coordsvanish_wordmultspli
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    {w : List (Fin O.r)}
    (hword :
      ∀ z : List (Fin O.r),
        O.wordWeight w ≤ O.wordWeight z →
          ∀ a : Fin O.r → Fin p,
            expWeight (p := p) (r := O.r) O.weight a < O.wordWeight w →
              O.jenningsMonomialBasis.repr (O.wordEval z) a = 0) :
    O.LowWeightcoordsVanishword (O.wordWeight w) w := by
  rcases O.or_perm_pth w with
    hbounded | ⟨i, u, v, hperm⟩
  · exact O.lowweight_coordsvanish_wordbounmult hword hbounded
  · exact O.lowweightcoords_vanishwordperm_pthpowerblock hword hperm

/-- At cutoff `0`, the killed-Zassenhaus hypothesis already makes the group trivial, so the
Jennings separation package is immediate. -/
lemma OZReps.nonempty_jenningssep_datazero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (O : OZReps (p := p) Q 0)
    (hbot : zassenhausFiltration p Q 0 = ⊥) :
    Nonempty (JSData.{u, 0} (p := p) Q 0) := by
  classical
  refine
    ⟨{ ι := Fin O.r → Fin p
       decEq := inferInstance
       basis := O.jenningsMonomialBasis
       weight := fun e : Fin O.r → Fin p =>
         expWeight (p := p) (r := O.r) O.weight e
       aug_power := ?_
       separates := ?_ }⟩
  · intro a _ha
    exact
      (basis_high_repr
        (B := O.jenningsMonomialBasis)
        (wt := fun e : Fin O.r → Fin p =>
          expWeight (p := p) (r := O.r) O.weight e)
        (s := 0)
        (a := a)).2
        (by
          intro e he
          omega)
  · intro q hq
    have hqtop : q ∈ zassenhausFiltration p Q 0 := by
      rw [filtration_zero_top]
      exact Subgroup.mem_top q
    have hqbot : q ∈ (⊥ : Subgroup Q) := by
      simpa [hbot] using hqtop
    exact False.elim (hq (Subgroup.mem_bot.mp hqbot))

/-- For a positive successor cutoff, the canonical Jennings monomial basis and its built-in
`[word] - 1` expansion reduce separation data to the PBW word-coordinate statement alone. -/
lemma OZReps.nonejennsep_datasucclow_weiworcoovan
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {s : ℕ}
    (O : OZReps (p := p) Q (s + 1))
    (hbot : zassenhausFiltration p Q (s + 1) = ⊥)
    (Hword : O.LowWeightwordCoordsvanish) :
    Nonempty (JSData.{u, 0} (p := p) Q (s + 1)) := by
  classical
  exact
    O.nonemptjenning_sepdatasucc_basiwordexpa
      hbot
      O.jenningsMonomialBasis
      (by
        intro w hw e he
        exact Hword w hw e he)
      (fun e => O.jennings_monomial_basis e)

/-- Once the PBW word-coordinate statement is available for the canonical Jennings monomial
basis, ordered representatives yield the finite Jennings separation data consumed downstream. -/
lemma OZReps.nonejennsep_datalowweight_wordcoorvani
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (Hword : O.LowWeightwordCoordsvanish) :
    Nonempty (JSData.{u, 0} (p := p) Q m) := by
  classical
  by_cases hm : m = 0
  · subst m
    exact O.nonempty_jenningssep_datazero hbot
  · rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨s, rfl⟩
    exact
      O.nonejennsep_datasucclow_weiworcoovan
        hbot Hword

/-- Kernel theorem from a minimal fixed-degree Jennings certificate. -/
theorem jennings_layer_certificate
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    {n : ℕ}
    (C : JenningsLayerCertificate p G n)
    {g : G}
    (hgD : g ∈ D p G n) :
    groupAlgebraSub p G g ∈ Ipow p G (n + 1) ↔
      g ∈ D p G (n + 1) := by
  constructor
  · intro hgI_next
    exact C.drop_sub_next hgD hgI_next
  · intro hgD_next
    exact
      zassenhaus_implies_sub
        (p := p) (G := G) (n := n + 1) hgD_next

/-- If `g ∉ D_n`, then there is a last layer before `n` in which `g` survives. -/
lemma drop_index_not
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ} {g : G}
    (hgnot :
      g ∉ zassenhausFiltration p G n) :
    ∃ k : ℕ,
      k < n ∧
        g ∈ zassenhausFiltration p G k ∧
          g ∉ zassenhausFiltration p G (k + 1) := by
  classical
  have hgmem0 : g ∈ zassenhausFiltration p G 0 := by
    rw [filtration_zero_top]
    exact Subgroup.mem_top g
  let P : ℕ → Prop := fun k => g ∉ zassenhausFiltration p G k
  have hP : ∃ k : ℕ, P k := ⟨n, hgnot⟩
  let k : ℕ := Nat.find hP
  have hknot : P k := Nat.find_spec hP
  dsimp [P] at hknot
  have hkpos : 0 < k := by
    have hnotP0 : ¬ P 0 := by
      intro h
      exact h hgmem0
    exact (Nat.find_pos hP).2 hnotP0
  have hkle : k ≤ n := Nat.find_min' hP hgnot
  have hpred_lt : k - 1 < k := Nat.pred_lt (Nat.ne_of_gt hkpos)
  have hpred_mem : g ∈ zassenhausFiltration p G (k - 1) := by
    have hnotPpred : ¬ P (k - 1) := Nat.find_min hP hpred_lt
    by_contra hnot
    exact hnotPpred hnot
  refine ⟨k - 1, ?_, hpred_mem, ?_⟩
  · omega
  · have hpred_succ : k - 1 + 1 = k := by
      omega
    simpa [hpred_succ] using hknot

/-- Linear-algebra separation: if `v ∉ W`, a linear functional kills `W` and detects `v`. -/
lemma killing_submodule_detecting
    {K : Type v} [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    (W : Submodule K V)
    {v : V}
    (hv : v ∉ W) :
    ∃ φ : V →ₗ[K] K,
      (∀ z, z ∈ W → φ z = 0) ∧
        φ v ≠ 0 := by
  classical
  let q : V ⧸ W := W.mkQ v
  have hq : q ≠ 0 := by
    intro hqzero
    apply hv
    have hmk :
        Submodule.Quotient.mk v =
          (0 : V ⧸ W) := by
      simpa [q, Submodule.mkQ_apply] using hqzero
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := W) (x := v)).1 hmk
  obtain ⟨⟨ι, b⟩⟩ :=
    Module.Free.exists_basis
      (R := K)
      (M := V ⧸ W)
  have hcoord_exists : ∃ i : ι, b.coord i q ≠ 0 := by
    by_contra hnone
    apply hq
    have hall : ∀ i : ι, b.coord i q = 0 := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    exact (b.forall_coord_eq_zero_iff).mp hall
  rcases hcoord_exists with ⟨i, hi⟩
  let φ : V →ₗ[K] K :=
    (b.coord i).comp W.mkQ
  refine ⟨φ, ?_, ?_⟩
  · intro z hz
    have hzq : W.mkQ z = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero (p := W) (x := z)).2 hz
    simp [φ, hzq]
  · simpa [φ, q] using hi

/-- For a Jennings-indexed basis satisfying the explicit `subOne` expansion, every coordinate of
`[q] - 1` is the corresponding formal expansion coefficient of the normal-form exponent vector of
`q`. -/
lemma OZReps.reprsub_oneeqsub_oneexpacoef
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (R : OZReps (p := p) Q m)
    (B : Module.Basis (Fin R.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (hexp :
      ∀ e : Fin R.r → Fin p,
        groupAlgebraSub p Q (R.wordEquiv e) =
          ∑ a : Fin R.r → Fin p,
            orderedJenningsCoeff (p := p) e a • B a)
    (q : Q)
    (a : Fin R.r → Fin p) :
    B.repr (groupAlgebraSub p Q q) a =
      orderedJenningsCoeff (p := p) (R.wordEquiv.symm q) a := by
  classical
  let e : Fin R.r → Fin p := R.wordEquiv.symm q
  have hq : R.wordEquiv e = q := by
    dsimp [e]
    simp
  rw [← hq, hexp e]
  simpa [e] using
    (repr_fintype_sum
      (B := B)
      (c := fun b : Fin R.r → Fin p =>
        orderedJenningsCoeff (p := p) e b)
      (i := a))

/-- If `q ∈ D_t`, then, under the explicit Jennings expansion, all coordinates of `[q] - 1`
of Jennings weight `< t` vanish. -/
lemma OZReps.reprsub_oneeq_zeromem
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m t : ℕ}
    (R : OZReps (p := p) Q m)
    (B : Module.Basis (Fin R.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (ht : t ≤ m)
    (hexp :
      ∀ e : Fin R.r → Fin p,
        groupAlgebraSub p Q (R.wordEquiv e) =
          ∑ a : Fin R.r → Fin p,
            orderedJenningsCoeff (p := p) e a • B a)
    {q : Q}
    {a : Fin R.r → Fin p}
    (hq : q ∈ zassenhausFiltration p Q t)
    (ha : expWeight (p := p) (r := R.r) R.weight a < t) :
    B.repr (groupAlgebraSub p Q q) a = 0 := by
  rw [R.reprsub_oneeqsub_oneexpacoef B hexp q a]
  exact
    R.sub_coeff_zero
      (t := t) (a := a) ht hq ha

/-- Under the explicit Jennings expansion, `q ∈ D_t` implies `[q] - 1` lies in the span of
basis monomials of Jennings weight at least `t`. -/
lemma OZReps.subone_membasishigh_weightspanmem
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m t : ℕ}
    (R : OZReps (p := p) Q m)
    (B : Module.Basis (Fin R.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (ht : t ≤ m)
    (hexp :
      ∀ e : Fin R.r → Fin p,
        groupAlgebraSub p Q (R.wordEquiv e) =
          ∑ a : Fin R.r → Fin p,
            orderedJenningsCoeff (p := p) e a • B a)
    {q : Q}
    (hq : q ∈ zassenhausFiltration p Q t) :
    groupAlgebraSub p Q q ∈
      basisHighSpan (p := p) (Q := Q) B
        (fun a : Fin R.r → Fin p =>
          expWeight (p := p) (r := R.r) R.weight a)
        t := by
  classical
  exact
    (basis_high_repr
      (p := p) (Q := Q)
      (B := B)
      (wt := fun a : Fin R.r → Fin p =>
        expWeight (p := p) (r := R.r) R.weight a)
      (s := t)
      (a := groupAlgebraSub p Q q)).2
      (by
        intro a ha
        exact R.reprsub_oneeq_zeromem B ht hexp hq ha)

/-- In particular, each chosen Zassenhaus representative has `[gen i] - 1` in the high-weight span
at its assigned weight. -/
lemma OZReps.gensub_onemembasis_highweightspan
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (R : OZReps (p := p) Q m)
    (B : Module.Basis (Fin R.r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q))
    (hexp :
      ∀ e : Fin R.r → Fin p,
        groupAlgebraSub p Q (R.wordEquiv e) =
          ∑ a : Fin R.r → Fin p,
            orderedJenningsCoeff (p := p) e a • B a)
    (i : Fin R.r) :
    groupAlgebraSub p Q (R.gen i) ∈
      basisHighSpan (p := p) (Q := Q) B
        (fun a : Fin R.r → Fin p =>
          expWeight (p := p) (r := R.r) R.weight a)
        (R.weight i) := by
  exact
    OZReps.subone_membasishigh_weightspanmem
      (p := p) (Q := Q) (m := m) (t := R.weight i)
      R B
      (le_of_lt (R.weight_lt i))
      hexp
      (R.gen_mem i)

/-- A nonzero exponent in `Fin p` is nonzero after coercion to `ZMod p`. -/
lemma zmod_nat_val
    {p : ℕ} [Fact p.Prime]
    {a : Fin p}
    (ha : a ≠ 0) :
    ((a.val : ℕ) : ZMod p) ≠ 0 := by
  intro hzero
  have hdiv : p ∣ a.val := by
    exact (ZMod.natCast_eq_zero_iff a.val p).mp hzero
  have hval0 : a.val = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdiv a.isLt
  exact ha (Fin.ext hval0)

end Towers
