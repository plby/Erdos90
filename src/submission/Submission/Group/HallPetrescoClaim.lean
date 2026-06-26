import Submission.Group.SignedBinomialBounds
import Mathlib.Order.Hom.PowersetCard
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

open scoped commutatorElement

namespace Submission
namespace HACoeff

open PPColl
open PPColl.RCColl.RPAggreg

/-- The labelled generators used in the proof of `docs/HallPetrescoClaim.tex`. -/
abbrev LabelledAtom (M N : ℕ) :=
  Fin M ⊕ Fin N

/-- Forget the label on one source generator, remembering only its Hall-pair side. -/
def collapseLabel
    {M N : ℕ} :
    LabelledAtom M N → HPAtom
  | .inl _ => .left
  | .inr _ => .right

/-- The labelled left block `x₁ x₂ ... x_M`. -/
def labelledLeft
    (M N : ℕ) :
    FreeGroup (LabelledAtom M N) :=
  (List.ofFn fun i : Fin M =>
    FreeGroup.of (Sum.inl i : LabelledAtom M N)).prod

/-- The labelled right block `y₁ y₂ ... y_N`. -/
def labelledRight
    (M N : ℕ) :
    FreeGroup (LabelledAtom M N) :=
  (List.ofFn fun j : Fin N =>
    FreeGroup.of (Sum.inr j : LabelledAtom M N)).prod

/-- Identify every labelled left atom with `X` and every labelled right atom with `Y`. -/
def collapseHom
    (M N : ℕ) :
    FreeGroup (LabelledAtom M N) →* UniversalGroup :=
  FreeGroup.map collapseLabel

/-- Collapse the labels in one formal commutator word. -/
def collapseWord
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    CWord HPAtom :=
  w.bind fun a => .atom (collapseLabel a)

/-- Evaluate a finite labelled commutator list in the labelled free group. -/
def labelledListEval
    {M N : ℕ}
    (L : List (CWord (LabelledAtom M N))) :
    FreeGroup (LabelledAtom M N) :=
  (L.map fun w => w.eval FreeGroup.of).prod

/-- Evaluate a finite labelled atom list in the labelled free group. -/
def labelledAtomList
    {M N : ℕ}
    (L : List (LabelledAtom M N)) :
    FreeGroup (LabelledAtom M N) :=
  (L.map FreeGroup.of).prod

/-- Evaluate the label-collapsed image of a finite labelled commutator list. -/
def collapsedListEval
    {M N : ℕ}
    (L : List (CWord (LabelledAtom M N))) :
    UniversalGroup :=
  (L.map fun w =>
    (collapseWord w).eval
      (HPAtom.eval universalLeft universalRight)).prod

/-- Collapsing the labelled left block gives `X^M`. -/
lemma collapse_labelled_left
    (M N : ℕ) :
    collapseHom M N (labelledLeft M N) =
      universalLeft ^ M := by
  rw [labelledLeft, map_list_prod, List.ofFn_eq_map, List.map_map]
  rw [show List.map (collapseHom M N ∘ fun i : Fin M =>
      FreeGroup.of (Sum.inl i : LabelledAtom M N)) (List.finRange M) =
        List.replicate M universalLeft by
    simpa using List.eq_replicate_of_mem (a := universalLeft)
      (l := List.map (collapseHom M N ∘ fun i : Fin M =>
        FreeGroup.of (Sum.inl i : LabelledAtom M N)) (List.finRange M)) (by
        intro z hz
        rcases List.mem_map.mp hz with ⟨i, _hi, rfl⟩
        simp [collapseHom, collapseLabel, universalLeft])]
  rw [List.prod_replicate]

/-- Collapsing the labelled right block gives `Y^N`. -/
lemma collapse_labelled_right
    (M N : ℕ) :
    collapseHom M N (labelledRight M N) =
      universalRight ^ N := by
  rw [labelledRight, map_list_prod, List.ofFn_eq_map, List.map_map]
  rw [show List.map (collapseHom M N ∘ fun j : Fin N =>
      FreeGroup.of (Sum.inr j : LabelledAtom M N)) (List.finRange N) =
        List.replicate N universalRight by
    simpa using List.eq_replicate_of_mem (a := universalRight)
      (l := List.map (collapseHom M N ∘ fun j : Fin N =>
        FreeGroup.of (Sum.inr j : LabelledAtom M N)) (List.finRange N)) (by
        intro z hz
        rcases List.mem_map.mp hz with ⟨j, _hj, rfl⟩
        simp [collapseHom, collapseLabel, universalRight])]
  rw [List.prod_replicate]

/-- Evaluation of one labelled formal commutator commutes with label collapse. -/
lemma collapseHom_eval
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    collapseHom M N (w.eval FreeGroup.of) =
      (collapseWord w).eval
        (HPAtom.eval universalLeft universalRight) := by
  rw [collapseWord, CWord.eval_bind, CWord.map_eval]
  congr 1
  funext a
  cases a <;>
    simp [collapseHom, collapseLabel, HPAtom.eval, universalLeft,
      universalRight]

/-- Evaluation of a labelled formal commutator list commutes with label collapse. -/
lemma collapse_labelled_eval
    {M N : ℕ}
    (L : List (CWord (LabelledAtom M N))) :
    collapseHom M N (labelledListEval L) =
      collapsedListEval L := by
  rw [labelledListEval, collapsedListEval, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro w _hw
  exact collapseHom_eval w

/-- The labelled source atoms in the left block. -/
def labelledLeftAtoms
    (M N : ℕ) :
    List (LabelledAtom M N) :=
  List.ofFn fun i : Fin M => (Sum.inl i : LabelledAtom M N)

/-- The labelled source atoms in the right block. -/
def labelledRightAtoms
    (M N : ℕ) :
    List (LabelledAtom M N) :=
  List.ofFn fun j : Fin N => (Sum.inr j : LabelledAtom M N)

lemma labelled_left_atoms
    (M N : ℕ) :
    labelledAtomList (labelledLeftAtoms M N) =
      labelledLeft M N := by
  simp [labelledAtomList, labelledLeftAtoms, labelledLeft, Function.comp_def]

lemma labelled_atom_atoms
    (M N : ℕ) :
    labelledAtomList (labelledRightAtoms M N) =
      labelledRight M N := by
  simp [labelledAtomList, labelledRightAtoms, labelledRight, Function.comp_def]

lemma collapse_label_atoms
    {M N : ℕ}
    {a : LabelledAtom M N}
    (ha : a ∈ labelledLeftAtoms M N) :
    collapseLabel a = .left := by
  rcases List.mem_ofFn.mp ha with ⟨i, rfl⟩
  rfl

lemma collapse_labelled_atoms
    {M N : ℕ}
    {a : LabelledAtom M N}
    (ha : a ∈ labelledRightAtoms M N) :
    collapseLabel a = .right := by
  rcases List.mem_ofFn.mp ha with ⟨j, rfl⟩
  rfl

lemma labelled_eval_append
    {M N : ℕ}
    (L K : List (CWord (LabelledAtom M N))) :
    labelledListEval (L ++ K) =
      labelledListEval L * labelledListEval K := by
  simp [labelledListEval, List.prod_append]

@[simp]
lemma labelled_eval_cons
    {M N : ℕ}
    (D : CWord (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    labelledListEval (D :: L) =
      D.eval FreeGroup.of * labelledListEval L :=
  rfl

/-- Expand conjugation by one atom as `[a, D] D`. -/
def conjugateAtomTrace
    {M N : ℕ}
    (a : LabelledAtom M N)
    (D : CWord (LabelledAtom M N)) :
    List (CWord (LabelledAtom M N)) :=
  [.commutator (.atom a) D, D]

/-- Expand conjugation by a finite atom word, one atom at a time. -/
def conjTrace
    {M N : ℕ} :
    List (LabelledAtom M N) →
      CWord (LabelledAtom M N) →
        List (CWord (LabelledAtom M N))
  | [], D => [D]
  | a :: A, D =>
      (conjTrace A D).flatMap (conjugateAtomTrace a)

/-- Expand conjugation of every factor in a formal commutator list. -/
def conjTraceList
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    List (CWord (LabelledAtom M N)) :=
  L.flatMap (conjTrace A)

lemma labelled_eval_flat
    {M N : ℕ}
    (f :
      CWord (LabelledAtom M N) →
        List (CWord (LabelledAtom M N))) :
    ∀ L : List (CWord (LabelledAtom M N)),
      labelledListEval (L.flatMap f) =
        (L.map fun D => labelledListEval (f D)).prod
  | [] => by
      simp [labelledListEval]
  | D :: L => by
      simp [labelled_eval_append, labelled_eval_flat f L]

lemma labelled_conjugate_trace
    {M N : ℕ}
    (a : LabelledAtom M N)
    (D : CWord (LabelledAtom M N)) :
    labelledListEval (conjugateAtomTrace a D) =
      FreeGroup.of a * D.eval FreeGroup.of * (FreeGroup.of a)⁻¹ := by
  simp [conjugateAtomTrace, labelledListEval, CWord.eval_commutator,
    commutatorElement_def]

lemma list_prod_conjugates
    {G : Type*} [Group G]
    (q : G) :
    ∀ L : List G,
      (L.map fun g => q * g * q⁻¹).prod =
        q * L.prod * q⁻¹
  | [] => by
      simp
  | g :: L => by
      simp [list_prod_conjugates q L]

lemma labelled_trace
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    labelledListEval (conjTrace A D) =
      labelledAtomList A * D.eval FreeGroup.of *
        (labelledAtomList A)⁻¹ := by
  induction A with
  | nil =>
      simp [conjTrace, labelledListEval, labelledAtomList]
  | cons a A ih =>
      rw [conjTrace, labelled_eval_flat]
      simp_rw [labelled_conjugate_trace]
      rw [show
          (List.map
              (fun E =>
                FreeGroup.of a * E.eval FreeGroup.of * (FreeGroup.of a)⁻¹)
              (conjTrace A D)).prod =
            FreeGroup.of a * labelledListEval (conjTrace A D) *
              (FreeGroup.of a)⁻¹ by
          simpa [labelledListEval, List.map_map, Function.comp_def] using
            (list_prod_conjugates (FreeGroup.of a)
              ((conjTrace A D).map fun E => E.eval FreeGroup.of))]
      rw [ih]
      simp [labelledAtomList]
      group

lemma labelled_list_eval
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    labelledListEval (conjTraceList A L) =
      labelledAtomList A * labelledListEval L *
        (labelledAtomList A)⁻¹ := by
  rw [conjTraceList, labelled_eval_flat]
  simp_rw [labelled_trace]
  rw [show
      (List.map
          (fun D =>
            labelledAtomList A * D.eval FreeGroup.of *
              (labelledAtomList A)⁻¹)
          L).prod =
        labelledAtomList A * labelledListEval L *
          (labelledAtomList A)⁻¹ by
      simpa [labelledListEval, List.map_map, Function.comp_def] using
        (list_prod_conjugates (labelledAtomList A)
          (L.map fun D => D.eval FreeGroup.of))]

lemma collapse_conjugate_atom
    {M N : ℕ}
    (a : LabelledAtom M N)
    {D : CWord (LabelledAtom M N)}
    (hD : (collapseWord D).PBPos) :
    (collapseWord (.commutator (.atom a) D)).PBPos := by
  cases a <;>
    simp [collapseWord, CWord.PBPos] at hD ⊢
  all_goals omega

lemma conjTrace_positive
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    {D : CWord (LabelledAtom M N)}
    (hD : (collapseWord D).PBPos) :
    ∀ E ∈ conjTrace A D,
      (collapseWord E).PBPos := by
  induction A with
  | nil =>
      intro E hE
      have hED : E = D := by
        simpa [conjTrace] using hE
      subst E
      exact hD
  | cons a A ih =>
      intro E hE
      rcases List.mem_flatMap.mp hE with ⟨F, hF, hEF⟩
      have hFpositive := ih F hF
      have hEF' :
          E = .commutator (.atom a) F ∨ E = F := by
        simpa [conjugateAtomTrace] using hEF
      rcases hEF' with rfl | rfl
      · exact collapse_conjugate_atom a hFpositive
      · exact hFpositive

lemma conj_list_positive
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    {L : List (CWord (LabelledAtom M N))}
    (hL : ∀ D ∈ L, (collapseWord D).PBPos) :
    ∀ E ∈ conjTraceList A L,
      (collapseWord E).PBPos := by
  intro E hE
  rcases List.mem_flatMap.mp hE with ⟨D, hD, hED⟩
  exact conjTrace_positive A (hL D hD) E hED

/-- Expand `[x, y₀ ... yₙ]` into labelled formal commutators. -/
def rightTrace
    {M N : ℕ}
    (x : LabelledAtom M N) :
    List (LabelledAtom M N) →
      List (CWord (LabelledAtom M N))
  | [] => []
  | y :: ys =>
      .commutator (.atom x) (.atom y) ::
        conjTraceList [y] (rightTrace x ys)

lemma labelled_list_right
    {M N : ℕ}
    (x : LabelledAtom M N) :
    ∀ ys : List (LabelledAtom M N),
      labelledListEval (rightTrace x ys) =
        ⁅FreeGroup.of x, labelledAtomList ys⁆
  | [] => by
      simp [rightTrace, labelledListEval, labelledAtomList]
  | y :: ys => by
      rw [rightTrace, labelled_eval_cons, CWord.eval_commutator,
        labelled_list_eval, labelled_list_right]
      change
        ⁅FreeGroup.of x, FreeGroup.of y⁆ *
              (FreeGroup.of y * ⁅FreeGroup.of x, labelledAtomList ys⁆ *
                (FreeGroup.of y)⁻¹) =
          ⁅FreeGroup.of x, FreeGroup.of y * labelledAtomList ys⁆
      rw [element_mul_right]
      group

lemma rightTrace_positive
    {M N : ℕ}
    {x : LabelledAtom M N}
    (hx : collapseLabel x = .left) :
    ∀ ys : List (LabelledAtom M N),
      (∀ y ∈ ys, collapseLabel y = .right) →
        ∀ D ∈ rightTrace x ys,
          (collapseWord D).PBPos
  | [], _hys => by
      simp [rightTrace]
  | y :: ys, hys => by
      intro D hD
      simp only [rightTrace, List.mem_cons] at hD
      rcases hD with rfl | hD
      · have hy : collapseLabel y = .right := hys y (by simp)
        simp [collapseWord, CWord.PBPos, hx, hy]
      · exact
          conj_list_positive [y]
            (rightTrace_positive hx ys fun z hz => hys z (by simp [hz]))
            D hD

/-- Expand `[x₀ ... xₘ, y₀ ... yₙ]` into labelled formal commutators. -/
def leftRightTrace
    {M N : ℕ} :
    List (LabelledAtom M N) →
      List (LabelledAtom M N) →
        List (CWord (LabelledAtom M N))
  | [], _ys => []
  | x :: xs, ys =>
      conjTraceList [x] (leftRightTrace xs ys) ++
        rightTrace x ys

lemma labelled_left_trace
    {M N : ℕ} :
    ∀ xs ys : List (LabelledAtom M N),
      labelledListEval (leftRightTrace xs ys) =
        ⁅labelledAtomList xs, labelledAtomList ys⁆
  | [], ys => by
      simp [leftRightTrace, labelledListEval, labelledAtomList]
  | x :: xs, ys => by
      rw [leftRightTrace, labelled_eval_append,
        labelled_list_eval, labelled_left_trace,
        labelled_list_right]
      change
        (FreeGroup.of x *
              ⁅labelledAtomList xs, labelledAtomList ys⁆ *
                (FreeGroup.of x)⁻¹) *
              ⁅FreeGroup.of x, labelledAtomList ys⁆ =
          ⁅FreeGroup.of x * labelledAtomList xs, labelledAtomList ys⁆
      rw [element_mul_left]

lemma left_right_positive
    {M N : ℕ} :
    ∀ xs ys : List (LabelledAtom M N),
      (∀ x ∈ xs, collapseLabel x = .left) →
        (∀ y ∈ ys, collapseLabel y = .right) →
          ∀ D ∈ leftRightTrace xs ys,
            (collapseWord D).PBPos
  | [], _ys, _hxs, _hys => by
      simp [leftRightTrace]
  | x :: xs, ys, hxs, hys => by
      intro D hD
      rw [leftRightTrace, List.mem_append] at hD
      have hx : collapseLabel x = .left := hxs x (by simp)
      rcases hD with hD | hD
      · exact
          conj_list_positive [x]
            (left_right_positive xs ys
              (fun z hz => hxs z (by simp [hz])) hys)
            D hD
      · exact rightTrace_positive hx ys hys D hD

/--
The exact labelled collection from Lemma 2 of `docs/HallPetrescoClaim.tex`.

Every emitted labelled commutator still uses at least one left and one right
source label after forgetting the individual labels.
-/
structure LabelledCollection
    (M N : ℕ) where
  factors :
    List (CWord (LabelledAtom M N))
  eval_eq :
    labelledListEval factors =
      ⁅labelledLeft M N, labelledRight M N⁆
  factors_positive :
    ∀ w ∈ factors,
      (collapseWord w).PBPos

/--
Lemma 2 from `docs/HallPetrescoClaim.tex`: expand the labelled commutator into
a finite exact product of labelled formal commutators.
-/
lemma nonempty_labelledCollection
    (M N : ℕ)
    (_hM : 0 < M)
    (_hN : 0 < N) :
    Nonempty (LabelledCollection M N) := by
  exact ⟨{
    factors := leftRightTrace (labelledLeftAtoms M N) (labelledRightAtoms M N)
    eval_eq := by
      simpa [labelled_left_atoms,
        labelled_atom_atoms] using
        (labelled_left_trace
          (labelledLeftAtoms M N) (labelledRightAtoms M N))
    factors_positive := by
      exact
        left_right_positive
          (labelledLeftAtoms M N) (labelledRightAtoms M N)
          (fun a ha => collapse_label_atoms ha)
          (fun a ha => collapse_labelled_atoms ha) }⟩

/-- Forgetting labels in any labelled collection recovers the universal block commutator. -/
lemma collapsed_eval_pow
    {M N : ℕ}
    (C : LabelledCollection M N) :
    collapsedListEval C.factors =
      ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  calc
    collapsedListEval C.factors =
        collapseHom M N (labelledListEval C.factors) :=
      (collapse_labelled_eval C.factors).symm
    _ = collapseHom M N ⁅labelledLeft M N, labelledRight M N⁆ := by
      rw [C.eval_eq]
    _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
      rw [map_commutatorElement, collapse_labelled_left,
        collapse_labelled_right]

/--
One collector term together with the raw-factor occurrences used to build it.

The support is More3's termination bookkeeping: a correction created while
interchanging two independent terms carries the union of their supports.
-/
structure DTerm
    (M N K : ℕ) where
  word :
    CWord (LabelledAtom M N)
  support :
    Finset (Fin K)

instance commutatorWordDecidable
    {α : Type*}
    [DecidableEq α] :
    DecidableEq (CWord α)
  | .atom a, .atom b =>
      if hab : a = b then
        isTrue (by cases hab; rfl)
      else
        isFalse (by
          intro h
          cases h
          exact hab rfl)
  | .atom _, .commutator _ _ =>
      isFalse (by intro h; cases h)
  | .commutator _ _, .atom _ =>
      isFalse (by intro h; cases h)
  | .commutator u v, .commutator u' v' =>
      match commutatorWordDecidable u u' with
      | isTrue hu =>
          match commutatorWordDecidable v v' with
          | isTrue hv =>
              isTrue (by cases hu; cases hv; rfl)
          | isFalse hv =>
              isFalse (by
                intro h
                cases h
                exact hv rfl)
      | isFalse hu =>
          isFalse (by
            intro h
            cases h
            exact hu rfl)

instance pairAtomDecidable :
    DecidableEq HPAtom
  | .left, .left => isTrue rfl
  | .left, .right => isFalse (by intro h; cases h)
  | .right, .left => isFalse (by intro h; cases h)
  | .right, .right => isTrue rfl

/-- Prefix code used for deterministic shape-first tie breaking. -/
def pairShapeCode :
    CWord HPAtom → List Nat
  | .atom .left => [0]
  | .atom .right => [1]
  | .commutator u v =>
      2 :: pairShapeCode u ++ 3 :: pairShapeCode v ++ [4]

/-- Prefix code for one labelled source atom. -/
def labelledAtomCode
    {M N : ℕ} :
    LabelledAtom M N → List Nat
  | .inl index => [0, index.val]
  | .inr index => [1, index.val]

/-- Prefix code used only for deterministic labelled-term tie breaking. -/
def labelledWordCode
    {M N : ℕ} :
    CWord (LabelledAtom M N) → List Nat
  | .atom atom => 0 :: labelledAtomCode atom
  | .commutator u v =>
      1 :: labelledWordCode u ++ 2 :: labelledWordCode v ++ [3]

namespace DTerm

/-- Evaluate the labelled commutator word carried by a decorated term. -/
def eval
    {M N K : ℕ}
    (T : DTerm M N K) :
    FreeGroup (LabelledAtom M N) :=
  T.word.eval FreeGroup.of

/-- Seed one decorated term from one occurrence in the raw trace. -/
def raw
    {M N K : ℕ}
    (word : CWord (LabelledAtom M N))
    (index : Fin K) :
    DTerm M N K where
  word := word
  support := {index}

/-- The correction emitted by the exact interchange `BA = [B,A]AB`. -/
def correction
    {M N K : ℕ}
    (B A : DTerm M N K) :
    DTerm M N K where
  word := .commutator B.word A.word
  support := B.support ∪ A.support

/-- Forget labels in the Hall shape carried by a decorated term. -/
def erasedShape
    {M N K : ℕ}
    (T : DTerm M N K) :
    CWord HPAtom :=
  collapseWord T.word

/-- Total Hall degree of the erased collector shape. -/
def erasedDegree
    {M N K : ℕ}
    (T : DTerm M N K) :
    ℕ :=
  T.erasedShape.weight (HPAtom.weight 1 1)

/-- Evaluate the erased Hall shape in the universal two-generator free group. -/
def collapsedEval
    {M N K : ℕ}
    (T : DTerm M N K) :
    UniversalGroup :=
  T.erasedShape.eval (HPAtom.eval universalLeft universalRight)

/-- Deterministic code for the erased Hall shape of one decorated term. -/
def erasedShapeCode
    {M N K : ℕ}
    (T : DTerm M N K) :
    List Nat :=
  pairShapeCode T.erasedShape

/-- Deterministic code for the labelled Hall word of one decorated term. -/
def labelledWordCode
    {M N K : ℕ}
    (T : DTerm M N K) :
    List Nat :=
  HACoeff.labelledWordCode T.word

/-- Deterministic code for the finite More3 support. -/
def supportCode
    {M N K : ℕ}
    (T : DTerm M N K) :
    List Nat :=
  T.support.sort.map Fin.val

/-- Lexicographic key for More3's deterministic high-degree collector order. -/
abbrev CollectorKey :=
  OrderDual ℕ × List Nat × OrderDual ℕ × List Nat × List Nat

/-- Reified More3 key: larger degree/support coordinates sort first. -/
def collectorKey
    {M N K : ℕ}
  (T : DTerm M N K) :
    CollectorKey :=
  (T.erasedDegree, T.erasedShapeCode, T.support.card, T.supportCode,
    T.labelledWordCode)

/-- Lexicographic comparison of More3 collector keys. -/
def collectorKeyBefore :
    CollectorKey → CollectorKey → Prop :=
  Prod.Lex (fun left right : OrderDual ℕ => left < right)
    (Prod.Lex (fun left right : List Nat => left < right)
      (Prod.Lex (fun left right : OrderDual ℕ => left < right)
        (Prod.Lex (fun left right : List Nat => left < right)
          (fun left right : List Nat => left < right))))

/-- More3's primary correction order: larger Hall degree comes earlier. -/
def higherDegreeBefore
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Prop :=
  U.erasedDegree < T.erasedDegree

instance higherBeforeDecidable
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Decidable (T.higherDegreeBefore U) := by
  unfold higherDegreeBefore
  infer_instance

/-- Shape-first part of More3's collector order. -/
def shapeBefore
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Prop :=
  T.higherDegreeBefore U ∨
    (T.erasedDegree = U.erasedDegree ∧
      T.erasedShapeCode < U.erasedShapeCode)

instance shapeBeforeDecidable
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Decidable (T.shapeBefore U) := by
  unfold shapeBefore
  infer_instance

/-- Secondary More3 key once the erased Hall shape key agrees. -/
def tieBefore
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Prop :=
  U.support.card < T.support.card ∨
    (T.support.card = U.support.card ∧
      (T.supportCode < U.supportCode ∨
        (T.supportCode = U.supportCode ∧
          T.labelledWordCode < U.labelledWordCode)))

instance tieBeforeDecidable
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Decidable (T.tieBefore U) := by
  unfold tieBefore
  infer_instance

/-- Full deterministic More3-style order key used by the collector. -/
def collectorBefore
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Prop :=
  collectorKeyBefore T.collectorKey U.collectorKey

instance collectorBeforeDecidable
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Decidable (T.collectorBefore U) := by
  unfold collectorBefore collectorKeyBefore
  infer_instance

lemma collectorBefore_trans
    {M N K : ℕ}
    {T U V : DTerm M N K}
    (hTU : T.collectorBefore U)
    (hUV : U.collectorBefore V) :
    T.collectorBefore V :=
  Prod.Lex.trans hTU hUV

lemma collector_before_self
    {M N K : ℕ}
    (T : DTerm M N K) :
    ¬ T.collectorBefore T := by
  unfold collectorBefore collectorKeyBefore
  exact Std.Irrefl.irrefl _

/-- Equal erased shapes receive the same primary shape-first key. -/
lemma erased_shape_code
    {M N K : ℕ}
    {T U : DTerm M N K}
    (hshape : T.erasedShape = U.erasedShape) :
    T.erasedShapeCode = U.erasedShapeCode := by
  rw [erasedShapeCode, erasedShapeCode, hshape]

/-- The shape-first key is asymmetric. -/
lemma shapeBefore_asymm
    {M N K : ℕ}
    {T U : DTerm M N K}
    (hTU : T.shapeBefore U) :
    ¬ U.shapeBefore T := by
  intro hUT
  simp only [shapeBefore, higherDegreeBefore] at hTU hUT
  rcases hTU with hdegree | ⟨hdegree, hcode⟩
  · rcases hUT with hdegree' | ⟨hdegree', _hcode'⟩ <;> omega
  · rcases hUT with hdegree' | ⟨_hdegree', hcode'⟩
    · omega
    · exact (List.lt_asymm hcode) hcode'

/-- Equal shape-first keys cannot be strictly shape ordered. -/
lemma not_before_key
    {M N K : ℕ}
    {T U : DTerm M N K}
    (hdegree : T.erasedDegree = U.erasedDegree)
    (hcode : T.erasedShapeCode = U.erasedShapeCode) :
    ¬ T.shapeBefore U := by
  intro hshape
  simp only [shapeBefore, higherDegreeBefore] at hshape
  rcases hshape with hdegree' | ⟨_hdegree', hcode'⟩
  · omega
  · rw [hcode] at hcode'
    exact (List.lt_irrefl _ hcode')

/-- The deterministic secondary key is asymmetric. -/
lemma tieBefore_asymm
    {M N K : ℕ}
    {T U : DTerm M N K}
    (hTU : T.tieBefore U) :
    ¬ U.tieBefore T := by
  intro hUT
  rcases hTU with hcard | ⟨hcard, hrest⟩
  · rcases hUT with hcard' | ⟨hcard', _hrest'⟩ <;> omega
  · rcases hUT with hcard' | ⟨_hcard', hrest'⟩
    · omega
    · rcases hrest with hsupport | ⟨hsupport, hword⟩
      · rcases hrest' with hsupport' | ⟨_hsupport', _hword'⟩
        · exact (List.lt_asymm hsupport) hsupport'
        · rw [_hsupport'] at hsupport
          exact List.lt_irrefl _ hsupport
      · rcases hrest' with hsupport' | ⟨_hsupport', hword'⟩
        · rw [hsupport] at hsupport'
          exact List.lt_irrefl _ hsupport'
        · exact (List.lt_asymm hword) hword'

/-- The full deterministic collector key is asymmetric. -/
lemma collectorBefore_asymm
    {M N K : ℕ}
    {T U : DTerm M N K}
    (hTU : T.collectorBefore U) :
    ¬ U.collectorBefore T := by
  intro hUT
  exact collector_before_self T (collectorBefore_trans hTU hUT)

lemma collectorBefore_trichotomy
    {M N K : ℕ}
    (T U : DTerm M N K) :
    T.collectorBefore U ∨
      T.collectorKey = U.collectorKey ∨
        U.collectorBefore T := by
  unfold collectorBefore collectorKeyBefore
  exact trichotomous _ _

/-- Non-strict collector order induced by the strict deterministic key. -/
def collectorLe
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Prop :=
  ¬ U.collectorBefore T

lemma collectorLe_refl
    {M N K : ℕ}
    (T : DTerm M N K) :
    T.collectorLe T :=
  collector_before_self T

lemma collectorLe_trans
    {M N K : ℕ}
    {T U V : DTerm M N K}
    (hTU : T.collectorLe U)
    (hUV : U.collectorLe V) :
    T.collectorLe V := by
  intro hVT
  rcases collectorBefore_trichotomy T U with hbefore | hkey | hafter
  · exact hUV (collectorBefore_trans hVT hbefore)
  · exact hUV (by
      unfold collectorBefore at hVT ⊢
      rw [← hkey]
      exact hVT)
  · exact hTU hafter

lemma collector_before
    {M N K : ℕ}
    {T U V : DTerm M N K}
    (hTU : T.collectorBefore U)
    (hUV : U.collectorLe V) :
    T.collectorBefore V := by
  rcases collectorBefore_trichotomy U V with hbefore | hkey | hafter
  · exact collectorBefore_trans hTU hbefore
  · unfold collectorBefore at hTU ⊢
    rw [← hkey]
    exact hTU
  · exact False.elim (hUV hafter)

lemma le_le_of
    {M N K : ℕ}
    {T U V : DTerm M N K}
    (hTU : T.collectorLe U)
    (hUV : U.collectorBefore V) :
    T.collectorLe V := by
  intro hVT
  exact hTU (collectorBefore_trans hUV hVT)

/-- More3's first termination coordinate: unused raw support slots. -/
def supportDefect
    {M N K : ℕ}
    (T : DTerm M N K) :
    ℕ :=
  K - T.support.card

@[simp]
lemma eval_raw
    {M N K : ℕ}
    (word : CWord (LabelledAtom M N))
    (index : Fin K) :
    (raw word index).eval = word.eval FreeGroup.of :=
  rfl

@[simp]
lemma support_raw
    {M N K : ℕ}
    (word : CWord (LabelledAtom M N))
    (index : Fin K) :
    (raw word index).support = {index} :=
  rfl

@[simp]
lemma support_correction
    {M N K : ℕ}
    (B A : DTerm M N K) :
    (correction B A).support = B.support ∪ A.support :=
  rfl

lemma support_raw_nonempty
    {M N K : ℕ}
    (word : CWord (LabelledAtom M N))
    (index : Fin K) :
    (raw word index).support.Nonempty := by
  simp

lemma support_nonempty_left
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hB : B.support.Nonempty) :
    (correction B A).support.Nonempty := by
  simp [hB]

lemma support_nonempty_right
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hA : A.support.Nonempty) :
    (correction B A).support.Nonempty := by
  simp [hA]

lemma support_correction_subset
    {M N K : ℕ}
    {B A : DTerm M N K}
    {S : Finset (Fin K)}
    (hB : B.support ⊆ S)
    (hA : A.support ⊆ S) :
    (correction B A).support ⊆ S := by
  rw [support_correction]
  exact Finset.union_subset hB hA

lemma support_subset_left
    {M N K : ℕ}
    (B A : DTerm M N K) :
    B.support ⊆ (correction B A).support := by
  rw [support_correction]
  exact Finset.subset_union_left

lemma support_subset_right
    {M N K : ℕ}
    (B A : DTerm M N K) :
    A.support ⊆ (correction B A).support := by
  rw [support_correction]
  exact Finset.subset_union_right

lemma card_correction_disjoint
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hdisjoint : Disjoint B.support A.support) :
    (correction B A).support.card =
      B.support.card + A.support.card := by
  rw [support_correction, Finset.card_union_of_disjoint hdisjoint]

lemma support_correction_disjoint
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hdisjoint : Disjoint B.support A.support)
    (hA : A.support.Nonempty) :
    B.support.card < (correction B A).support.card := by
  rw [card_correction_disjoint hdisjoint]
  exact Nat.lt_add_of_pos_right (Finset.card_pos.mpr hA)

lemma support_left_subset
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hnotSubset : ¬ A.support ⊆ B.support) :
    B.support.card < (correction B A).support.card := by
  rw [support_correction]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.subset_union_left, ?_⟩
  intro hEq
  exact hnotSubset (Finset.union_eq_left.mp hEq.symm)

lemma support_card_disjoint
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hdisjoint : Disjoint B.support A.support)
    (hB : B.support.Nonempty) :
    A.support.card < (correction B A).support.card := by
  rw [card_correction_disjoint hdisjoint]
  exact Nat.lt_add_of_pos_left (Finset.card_pos.mpr hB)

lemma support_card_subset
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hnotSubset : ¬ B.support ⊆ A.support) :
    A.support.card < (correction B A).support.card := by
  rw [support_correction]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.subset_union_right, ?_⟩
  intro hEq
  exact hnotSubset (Finset.union_eq_right.mp hEq.symm)

lemma support_left_disjoint
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hdisjoint : Disjoint B.support A.support)
    (hA : A.support.Nonempty) :
    (correction B A).supportDefect < B.supportDefect := by
  rw [supportDefect, supportDefect]
  have hcard :=
    support_correction_disjoint hdisjoint hA
  exact
    Nat.sub_lt_sub_left
      (lt_of_lt_of_le hcard (by
        simpa using Finset.card_le_univ (correction B A).support))
      hcard

lemma support_not_subset
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hnotSubset : ¬ A.support ⊆ B.support) :
    (correction B A).supportDefect < B.supportDefect := by
  rw [supportDefect, supportDefect]
  have hcard := support_left_subset hnotSubset
  exact
    Nat.sub_lt_sub_left
      (lt_of_lt_of_le hcard (by
        simpa using Finset.card_le_univ (correction B A).support))
      hcard

lemma support_defect_disjoint
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hdisjoint : Disjoint B.support A.support)
    (hB : B.support.Nonempty) :
    (correction B A).supportDefect < A.supportDefect := by
  rw [supportDefect, supportDefect]
  have hcard :=
    support_card_disjoint hdisjoint hB
  exact
    Nat.sub_lt_sub_left
      (lt_of_lt_of_le hcard (by
        simpa using Finset.card_le_univ (correction B A).support))
      hcard

lemma support_defect_subset
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hnotSubset : ¬ B.support ⊆ A.support) :
    (correction B A).supportDefect < A.supportDefect := by
  rw [supportDefect, supportDefect]
  have hcard := support_card_subset hnotSubset
  exact
    Nat.sub_lt_sub_left
      (lt_of_lt_of_le hcard (by
        simpa using Finset.card_le_univ (correction B A).support))
      hcard

@[simp]
lemma erasedShape_corr
    {M N K : ℕ}
    (B A : DTerm M N K) :
    (correction B A).erasedShape =
      .commutator B.erasedShape A.erasedShape := by
  rfl

@[simp]
lemma erasedDegree_correction
    {M N K : ℕ}
    (B A : DTerm M N K) :
    (correction B A).erasedDegree =
      B.erasedDegree + A.erasedDegree := by
  rfl

@[simp]
lemma eval_correction
    {M N K : ℕ}
    (B A : DTerm M N K) :
    (correction B A).eval = ⁅B.eval, A.eval⁆ := by
  simp [eval, correction, CWord.eval_commutator]

lemma collapseHom_eval
    {M N K : ℕ}
    (T : DTerm M N K) :
    collapseHom M N T.eval = T.collapsedEval := by
  exact HACoeff.collapseHom_eval T.word

/-- The local collector rewrite is exact in the labelled free group. -/
lemma eval_correction_mul
    {M N K : ℕ}
    (B A : DTerm M N K) :
    (correction B A).eval * A.eval * B.eval =
      B.eval * A.eval := by
  rw [eval_correction]
  simp [commutatorElement_def]

/-- Corrections preserve positivity after labels are erased. -/
lemma correction_positive
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hB : (collapseWord B.word).PBPos)
    (hA : (collapseWord A.word).PBPos) :
    (collapseWord (correction B A).word).PBPos := by
  simp only [correction, collapseWord, CWord.bind_commutator,
    CWord.PBPos,
    CWord.pair_left_commutator,
    CWord.pair_degree_commutator] at hB hA ⊢
  omega

/-- A positive erased Hall shape has positive total Hall degree. -/
lemma erasedDegree_pos
    {M N K : ℕ}
    {T : DTerm M N K}
    (hT : T.erasedShape.PBPos) :
    0 < T.erasedDegree := by
  rw [erasedDegree, CWord.pair_atom_degree]
  simpa using Nat.add_pos_left hT.left T.erasedShape.pairRightDegree

/-- A More3 correction has higher Hall degree than its left parent. -/
lemma higher_before_left
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hA : A.erasedShape.PBPos) :
    (correction B A).higherDegreeBefore B := by
  rw [higherDegreeBefore, erasedDegree_correction]
  exact Nat.lt_add_of_pos_right (erasedDegree_pos hA)

/-- A More3 correction has higher Hall degree than its right parent. -/
lemma higher_before_right
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hB : B.erasedShape.PBPos) :
    (correction B A).higherDegreeBefore A := by
  rw [higherDegreeBefore, erasedDegree_correction]
  exact Nat.lt_add_of_pos_left (erasedDegree_pos hB)

/-- Shape precedence is the primary component of the full collector order. -/
lemma collector_before_shape
    {M N K : ℕ}
    {T U : DTerm M N K}
    (hshape : T.shapeBefore U) :
    T.collectorBefore U := by
  unfold collectorBefore collectorKeyBefore collectorKey
  rcases hshape with hdegree | ⟨hdegree, hcode⟩
  · exact Prod.Lex.left _ _ hdegree
  · rw [← hdegree]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hcode)

/-- A More3 correction is collected before its left parent. -/
lemma collector_before_left
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hA : A.erasedShape.PBPos) :
    (correction B A).collectorBefore B :=
  collector_before_shape (Or.inl (higher_before_left hA))

/-- A More3 correction is collected before its right parent. -/
lemma collector_before_right
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hB : B.erasedShape.PBPos) :
    (correction B A).collectorBefore A :=
  collector_before_shape (Or.inl (higher_before_right hB))

end DTerm

/-- Evaluate a decorated collector list in its current noncommutative order. -/
def decoratedListEval
    {M N K : ℕ}
    (L : List (DTerm M N K)) :
    FreeGroup (LabelledAtom M N) :=
  (L.map DTerm.eval).prod

/-- Evaluate erased decorated terms in their current noncommutative order. -/
def decoratedCollapsedEval
    {M N K : ℕ}
    (L : List (DTerm M N K)) :
    UniversalGroup :=
  (L.map DTerm.collapsedEval).prod

@[simp]
lemma decorated_list_nil
    {M N K : ℕ} :
    decoratedListEval ([] : List (DTerm M N K)) = 1 :=
  rfl

@[simp]
lemma decorated_list_cons
    {M N K : ℕ}
    (T : DTerm M N K)
    (L : List (DTerm M N K)) :
    decoratedListEval (T :: L) =
      T.eval * decoratedListEval L :=
  rfl

lemma decorated_list_append
    {M N K : ℕ}
    (L R : List (DTerm M N K)) :
    decoratedListEval (L ++ R) =
      decoratedListEval L * decoratedListEval R := by
  simp [decoratedListEval, List.prod_append]

lemma collapse_decorated_eval
    {M N K : ℕ}
    (L : List (DTerm M N K)) :
    collapseHom M N (decoratedListEval L) =
      decoratedCollapsedEval L := by
  simp [decoratedListEval, decoratedCollapsedEval, map_list_prod,
    List.map_map, Function.comp_def, DTerm.collapseHom_eval]

/-- Replacing an adjacent obstructing pair by its correction preserves the suffix product. -/
lemma decorated_correction_cons
    {M N K : ℕ}
    (B A : DTerm M N K)
    (L : List (DTerm M N K)) :
    decoratedListEval (DTerm.correction B A :: A :: B :: L) =
      decoratedListEval (B :: A :: L) := by
  simp only [decorated_list_cons]
  calc
    (DTerm.correction B A).eval *
          (A.eval * (B.eval * decoratedListEval L)) =
        ((DTerm.correction B A).eval * A.eval * B.eval) *
          decoratedListEval L := by
      simp [mul_assoc]
    _ = (B.eval * A.eval) * decoratedListEval L := by
      rw [DTerm.eval_correction_mul]
    _ = B.eval * (A.eval * decoratedListEval L) := by
      simp [mul_assoc]

lemma decorated_append_cons
    {M N K : ℕ}
    (P : List (DTerm M N K))
    (B A : DTerm M N K)
    (L : List (DTerm M N K)) :
    decoratedListEval
        (P ++ DTerm.correction B A :: A :: B :: L) =
      decoratedListEval (P ++ B :: A :: L) := by
  rw [decorated_list_append, decorated_list_append,
    decorated_correction_cons]

/-- Number of More3 order obstructions to appending one decorated term. -/
def obstructionCount
    {M N K : ℕ}
    (L : List (DTerm M N K))
    (A : DTerm M N K) :
    ℕ :=
  L.countP fun B => decide (A.collectorBefore B)

@[simp]
lemma obstructionCount_nil
    {M N K : ℕ}
    (A : DTerm M N K) :
    obstructionCount [] A = 0 :=
  rfl

lemma obstruction_count_length
    {M N K : ℕ}
    (L : List (DTerm M N K))
    (A : DTerm M N K) :
    obstructionCount L A ≤ L.length := by
  exact List.countP_le_length

@[simp]
lemma obstructionCount_append
    {M N K : ℕ}
    (P L : List (DTerm M N K))
    (A : DTerm M N K) :
    obstructionCount (P ++ L) A =
      obstructionCount P A + obstructionCount L A := by
  simp [obstructionCount, List.countP_append]

lemma obstruction_last_before
    {M N K : ℕ}
    (P : List (DTerm M N K))
    (B A : DTerm M N K)
    (hAB : A.collectorBefore B) :
    obstructionCount (P ++ [B]) A =
      obstructionCount P A + 1 := by
  simp [obstructionCount, hAB]

lemma obstruction_append_before
    {M N K : ℕ}
    (P : List (DTerm M N K))
    (B A : DTerm M N K)
    (hAB : ¬ A.collectorBefore B) :
    obstructionCount (P ++ [B]) A =
      obstructionCount P A := by
  simp [obstructionCount, hAB]

/-- More3's lexicographic insertion measure, without an explicit countdown. -/
def insertionMeasure
    {M N K : ℕ}
    (L : List (DTerm M N K))
    (A : DTerm M N K) :
    ℕ × ℕ × ℕ :=
  (A.supportDefect, obstructionCount L A, L.length)

/-- Lexicographic relation used by More3's well-founded insertion recursion. -/
def insertionMeasureBefore :
    (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → Prop :=
  Prod.Lex (fun left right : ℕ => left < right)
    (Prod.Lex (fun left right : ℕ => left < right)
      (fun left right : ℕ => left < right))

lemma insertion_measure_wf :
    WellFounded insertionMeasureBefore := by
  unfold insertionMeasureBefore
  exact
    WellFounded.prod_lex Nat.lt_wfRel.wf
      (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

lemma insertion_measure_disjoint
    {M N K : ℕ}
    (P : List (DTerm M N K))
    {B A : DTerm M N K}
    (hdisjoint : Disjoint B.support A.support)
    (hB : B.support.Nonempty) :
    insertionMeasureBefore
      (insertionMeasure P (DTerm.correction B A))
      (insertionMeasure (P ++ [B]) A) := by
  apply Prod.Lex.left
  exact DTerm.support_defect_disjoint hdisjoint hB

/-- A list is collected when its More3 keys are nondecreasing from left to right. -/
def Collected
    {M N K : ℕ}
    (L : List (DTerm M N K)) :
    Prop :=
  L.Pairwise fun T U => T.collectorLe U

@[simp]
lemma collected_nil
    {M N K : ℕ} :
    Collected ([] : List (DTerm M N K)) := by
  simp [Collected]

lemma collected_append_singleton
    {M N K : ℕ}
    {P : List (DTerm M N K)}
    {A : DTerm M N K}
    (hP : Collected P)
    (hPA : ∀ T ∈ P, T.collectorLe A) :
    Collected (P ++ [A]) := by
  rw [Collected, List.pairwise_append]
  exact ⟨hP, by simp, by simpa using hPA⟩

/-- All current decorated factors retain positive erased Hall bidegree. -/
def PositiveList
    {M N K : ℕ}
    (L : List (DTerm M N K)) :
    Prop :=
  ∀ T ∈ L, T.erasedShape.PBPos

/-- Every current decorated factor still depends on at least one raw occurrence. -/
def SupportNonemptyList
    {M N K : ℕ}
    (L : List (DTerm M N K)) :
    Prop :=
  ∀ T ∈ L, T.support.Nonempty

/--
Every genuine obstruction to inserting `A` has disjoint raw support from
`A`, so the More3 correction strictly grows support.
-/
def CanInsert
    {M N K : ℕ}
    (L : List (DTerm M N K))
    (A : DTerm M N K) :
    Prop :=
  ∀ B ∈ L, A.collectorBefore B → Disjoint B.support A.support

@[simp]
lemma positiveList_nil
    {M N K : ℕ} :
    PositiveList ([] : List (DTerm M N K)) := by
  simp [PositiveList]

@[simp]
lemma support_nonempty_nil
    {M N K : ℕ} :
    SupportNonemptyList ([] : List (DTerm M N K)) := by
  simp [SupportNonemptyList]

@[simp]
lemma canInsert_nil
    {M N K : ℕ}
    (A : DTerm M N K) :
    CanInsert [] A := by
  simp [CanInsert]

lemma positive_append_singleton
    {M N K : ℕ}
    {P : List (DTerm M N K)}
    {A : DTerm M N K}
    (hP : PositiveList P)
    (hA : A.erasedShape.PBPos) :
    PositiveList (P ++ [A]) := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · exact hP T hT
  · rcases List.mem_singleton.mp hT with rfl
    exact hA

lemma support_nonempty_singleton
    {M N K : ℕ}
    {P : List (DTerm M N K)}
    {A : DTerm M N K}
    (hP : SupportNonemptyList P)
    (hA : A.support.Nonempty) :
    SupportNonemptyList (P ++ [A]) := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · exact hP T hT
  · rcases List.mem_singleton.mp hT with rfl
    exact hA

lemma positive_append_left
    {M N K : ℕ}
    {P L : List (DTerm M N K)}
    (hPL : PositiveList (P ++ L)) :
    PositiveList P := by
  intro T hT
  exact hPL T (List.mem_append_left L hT)

lemma support_nonempty_append
    {M N K : ℕ}
    {P L : List (DTerm M N K)}
    (hPL : SupportNonemptyList (P ++ L)) :
    SupportNonemptyList P := by
  intro T hT
  exact hPL T (List.mem_append_left L hT)

/--
One finite More3 insertion derivation.  The obstructing constructor is the
exact recursive clause from `HallPetrescoMore3.tex`; its proof tree replaces
an external countdown.
-/
inductive Inserts
    {M N K : ℕ} :
    List (DTerm M N K) →
      DTerm M N K →
        List (DTerm M N K) →
          Prop where
  | nil
      (A : DTerm M N K) :
      Inserts [] A [A]
  | append
      (P : List (DTerm M N K))
      (B A : DTerm M N K)
      (hBA : B.collectorLe A) :
      Inserts (P ++ [B]) A (P ++ [B, A])
  | obstruction
      (P : List (DTerm M N K))
      (B A : DTerm M N K)
      (hAB : A.collectorBefore B)
      (hdisjoint : Disjoint B.support A.support)
      {Q R : List (DTerm M N K)}
      (hcorrection : Inserts P (DTerm.correction B A) Q)
      (hinsert : Inserts Q A R) :
      Inserts (P ++ [B]) A (R ++ [B])

lemma decorated_append_singleton
    {M N K : ℕ}
    (P : List (DTerm M N K))
    (A : DTerm M N K) :
    decoratedListEval (P ++ [A]) =
      decoratedListEval P * A.eval := by
  simp [decoratedListEval, List.prod_append]

/-- Every finite More3 insertion derivation preserves exact labelled evaluation. -/
lemma decorated_list_inserts
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {A : DTerm M N K}
    (hinsert : Inserts L A R) :
    decoratedListEval R =
      decoratedListEval L * A.eval := by
  induction hinsert with
  | nil A =>
      simp
  | append P B A _hBA =>
      simp [decoratedListEval, List.prod_append, mul_assoc]
  | obstruction P B A _hAB _hdisjoint hcorrection hinsert ihcorrection ihinsert =>
      rw [decorated_append_singleton, ihinsert, ihcorrection,
        decorated_append_singleton]
      calc
        (decoratedListEval P * (DTerm.correction B A).eval) *
              A.eval * B.eval =
            decoratedListEval P *
              ((DTerm.correction B A).eval * A.eval * B.eval) := by
                group
        _ = decoratedListEval P * (B.eval * A.eval) := by
              rw [DTerm.eval_correction_mul]
        _ = (decoratedListEval P * B.eval) * A.eval := by
              group

lemma positiveList_inserts
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {A : DTerm M N K}
    (hinsert : Inserts L A R)
    (hL : PositiveList L)
    (hA : A.erasedShape.PBPos) :
    PositiveList R := by
  induction hinsert with
  | nil A =>
      intro T hT
      rcases List.mem_singleton.mp hT with rfl
      exact hA
  | append P B A _hBA =>
      simpa [List.append_assoc] using positive_append_singleton hL hA
  | obstruction P B A _hAB _hdisjoint hcorrection hinsert ihcorrection ihinsert =>
      have hP : PositiveList P := by
        intro T hT
        exact hL T (List.mem_append_left [B] hT)
      have hB : B.erasedShape.PBPos := hL B (by simp)
      have hcorrectionPositive :
          (DTerm.correction B A).erasedShape.PBPos :=
        DTerm.correction_positive hB hA
      have hQ := ihcorrection hP hcorrectionPositive
      have hR := ihinsert hQ hA
      exact positive_append_singleton hR hB

lemma support_nonempty_inserts
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {A : DTerm M N K}
    (hinsert : Inserts L A R)
    (hL : SupportNonemptyList L)
    (hA : A.support.Nonempty) :
    SupportNonemptyList R := by
  induction hinsert with
  | nil A =>
      intro T hT
      rcases List.mem_singleton.mp hT with rfl
      exact hA
  | append P B A _hBA =>
      simpa [List.append_assoc] using support_nonempty_singleton hL hA
  | obstruction P B A _hAB _hdisjoint hcorrection hinsert ihcorrection ihinsert =>
      have hP : SupportNonemptyList P := by
        intro T hT
        exact hL T (List.mem_append_left [B] hT)
      have hB : B.support.Nonempty := hL B (by simp)
      have hcorrectionNonempty :
          (DTerm.correction B A).support.Nonempty :=
        DTerm.support_nonempty_left hB
      have hQ := ihcorrection hP hcorrectionNonempty
      have hR := ihinsert hQ hA
      exact support_nonempty_singleton hR hB

/--
Terms freshly created while inserting `C` stay before any already-later
term `A`.  This is the second recursive-call obstruction lemma from More3.
-/
lemma collector_before_inserts
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {C A T : DTerm M N K}
    (hinsert : Inserts L C R)
    (hL : PositiveList L)
    (hC : C.erasedShape.PBPos)
    (hCA : C.collectorBefore A)
    (hT : T ∈ R)
    (hTnot : T ∉ L) :
    T.collectorBefore A := by
  induction hinsert generalizing A T with
  | nil C =>
      rcases List.mem_singleton.mp hT with rfl
      exact hCA
  | append P B C _hBC =>
      rcases List.mem_append.mp hT with hTP | hTBC
      · exact False.elim (hTnot (List.mem_append_left [B] hTP))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hTBC
        rcases hTBC with rfl | rfl
        · exact False.elim (hTnot (by simp))
        · exact hCA
  | @obstruction P B C _hCB _hdisjoint Q R hcorrection hinsert ihcorrection
      ihinsert =>
      have hP : PositiveList P :=
        positive_append_left hL
      have hB : B.erasedShape.PBPos := hL B (by simp)
      have hcorrectionPositive :
          (DTerm.correction B C).erasedShape.PBPos :=
        DTerm.correction_positive hB hC
      have hcorrectionBeforeC :
          (DTerm.correction B C).collectorBefore C :=
        DTerm.collector_before_right hB
      have hcorrectionBeforeA :
          (DTerm.correction B C).collectorBefore A :=
        DTerm.collectorBefore_trans hcorrectionBeforeC hCA
      have hQ : PositiveList Q :=
        positiveList_inserts hcorrection hP hcorrectionPositive
      rcases List.mem_append.mp hT with hTR | hTB
      · by_cases hTQ : T ∈ Q
        · have hTnotP : T ∉ P := by
            intro hTP
            exact hTnot (List.mem_append_left [B] hTP)
          exact
            ihcorrection hP hcorrectionPositive hcorrectionBeforeA hTQ hTnotP
        · exact ihinsert hQ hC hCA hTR hTQ
      · rcases List.mem_singleton.mp hTB with rfl
        exact False.elim (hTnot (by simp))

/--
When the inserted correction already precedes `A`, recursive insertion does
not change the list of obstructions to `A`.
-/
lemma count_inserts_before
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {C A : DTerm M N K}
    (hinsert : Inserts L C R)
    (hL : PositiveList L)
    (hC : C.erasedShape.PBPos)
    (hCA : C.collectorBefore A) :
    obstructionCount R A = obstructionCount L A := by
  induction hinsert generalizing A with
  | nil C =>
      have hAC : ¬ A.collectorBefore C :=
        DTerm.collectorBefore_asymm hCA
      simp [obstructionCount, hAC]
  | append P B C _hBC =>
      have hAC : ¬ A.collectorBefore C :=
        DTerm.collectorBefore_asymm hCA
      simpa [List.append_assoc] using
        obstruction_append_before (P ++ [B]) C A hAC
  | obstruction P B C _hCB _hdisjoint hcorrection hinsert ihcorrection ihinsert =>
      have hP : PositiveList P :=
        positive_append_left hL
      have hB : B.erasedShape.PBPos := hL B (by simp)
      have hcorrectionPositive :
          (DTerm.correction B C).erasedShape.PBPos :=
        DTerm.correction_positive hB hC
      have hcorrectionBeforeC :
          (DTerm.correction B C).collectorBefore C :=
        DTerm.collector_before_right hB
      have hcorrectionBeforeA :
          (DTerm.correction B C).collectorBefore A :=
        DTerm.collectorBefore_trans hcorrectionBeforeC hCA
      have hQ : PositiveList _ :=
        positiveList_inserts hcorrection hP hcorrectionPositive
      rw [obstructionCount_append, obstructionCount_append]
      rw [ihinsert hQ hC hCA, ihcorrection hP hcorrectionPositive hcorrectionBeforeA]

lemma measure_after_inserts
    {M N K : ℕ}
    (P : List (DTerm M N K))
    {B A : DTerm M N K}
    {Q : List (DTerm M N K)}
    (hAB : A.collectorBefore B)
    (hP : PositiveList P)
    (hB : B.erasedShape.PBPos)
    (hA : A.erasedShape.PBPos)
    (hcorrection : Inserts P (DTerm.correction B A) Q) :
    insertionMeasureBefore
      (insertionMeasure Q A)
      (insertionMeasure (P ++ [B]) A) := by
  have hcorrectionPositive :
      (DTerm.correction B A).erasedShape.PBPos :=
    DTerm.correction_positive hB hA
  have hcorrectionBeforeA :
      (DTerm.correction B A).collectorBefore A :=
    DTerm.collector_before_right hB
  unfold insertionMeasureBefore insertionMeasure
  apply Prod.Lex.right A.supportDefect
  apply Prod.Lex.left Q.length (P ++ [B]).length
  rw [count_inserts_before hcorrection hP hcorrectionPositive
      hcorrectionBeforeA,
    obstruction_last_before P B A hAB]
  omega

lemma collector_le_of
    {M N K : ℕ}
    {T U : DTerm M N K}
    (hTU : T.collectorBefore U) :
    T.collectorLe U :=
  DTerm.collectorBefore_asymm hTU

lemma collected_append_left
    {M N K : ℕ}
    {P L : List (DTerm M N K)}
    (hPL : Collected (P ++ L)) :
    Collected P := by
  rw [Collected, List.pairwise_append] at hPL
  exact hPL.1

lemma collector_last_collected
    {M N K : ℕ}
    {P : List (DTerm M N K)}
    {B : DTerm M N K}
    (hPB : Collected (P ++ [B])) :
    ∀ T ∈ P, T.collectorLe B := by
  rw [Collected, List.pairwise_append] at hPB
  intro T hT
  exact hPB.2.2 T hT B (by simp)

/-- Insertion preserves any common collected upper bound. -/
lemma collector_inserts
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {A U : DTerm M N K}
    (hinsert : Inserts L A R)
    (hL : PositiveList L)
    (hA : A.erasedShape.PBPos)
    (hLU : ∀ T ∈ L, T.collectorLe U)
    (hAU : A.collectorLe U) :
    ∀ T ∈ R, T.collectorLe U := by
  induction hinsert with
  | nil A =>
      intro T hT
      rcases List.mem_singleton.mp hT with rfl
      exact hAU
  | append P B A _hBA =>
      intro T hT
      rcases List.mem_append.mp hT with hTP | hTBA
      · exact hLU T (List.mem_append_left [B] hTP)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hTBA
        rcases hTBA with rfl | rfl
        · exact hLU T (by simp)
        · exact hAU
  | @obstruction P B A _hAB _hdisjoint Q R hcorrection hinsert ihcorrection
      ihinsert =>
      have hP : PositiveList P :=
        positive_append_left hL
      have hB : B.erasedShape.PBPos := hL B (by simp)
      have hcorrectionPositive :
          (DTerm.correction B A).erasedShape.PBPos :=
        DTerm.correction_positive hB hA
      have hcorrectionBeforeA :
          (DTerm.correction B A).collectorBefore A :=
        DTerm.collector_before_right hB
      have hcorrectionLeU :
          (DTerm.correction B A).collectorLe U :=
        collector_le_of
          (DTerm.collector_before
            hcorrectionBeforeA hAU)
      have hPU : ∀ T ∈ P, T.collectorLe U := by
        intro T hT
        exact hLU T (List.mem_append_left [B] hT)
      have hQU : ∀ T ∈ Q, T.collectorLe U :=
        ihcorrection hP hcorrectionPositive hPU hcorrectionLeU
      have hQ : PositiveList Q :=
        positiveList_inserts hcorrection hP hcorrectionPositive
      have hRU : ∀ T ∈ R, T.collectorLe U :=
        ihinsert hQ hA hQU hAU
      intro T hT
      rcases List.mem_append.mp hT with hTR | hTB
      · exact hRU T hTR
      · rcases List.mem_singleton.mp hTB with rfl
        exact hLU T (by simp)

/-- Every finite More3 insertion derivation returns a collected list. -/
lemma collected_inserts
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {A : DTerm M N K}
    (hinsert : Inserts L A R)
    (hL : Collected L)
    (hLpositive : PositiveList L)
    (hA : A.erasedShape.PBPos) :
    Collected R := by
  induction hinsert with
  | nil A =>
      simp [Collected]
  | append P B A hBA =>
      have hLleA : ∀ T ∈ P ++ [B], T.collectorLe A := by
        intro T hT
        rcases List.mem_append.mp hT with hTP | hTB
        · exact DTerm.collectorLe_trans
            (collector_last_collected hL T hTP) hBA
        · rcases List.mem_singleton.mp hTB with rfl
          exact hBA
      simpa [List.append_assoc] using collected_append_singleton hL hLleA
  | @obstruction P B A hAB _hdisjoint Q R hcorrection hinsert ihcorrection
      ihinsert =>
      have hP : Collected P :=
        collected_append_left hL
      have hPpositive : PositiveList P :=
        positive_append_left hLpositive
      have hB : B.erasedShape.PBPos := hLpositive B (by simp)
      have hcorrectionPositive :
          (DTerm.correction B A).erasedShape.PBPos :=
        DTerm.correction_positive hB hA
      have hQ : Collected Q :=
        ihcorrection hP hPpositive hcorrectionPositive
      have hQpositive : PositiveList Q :=
        positiveList_inserts hcorrection hPpositive hcorrectionPositive
      have hR : Collected R :=
        ihinsert hQ hQpositive hA
      have hPB : ∀ T ∈ P, T.collectorLe B :=
        collector_last_collected hL
      have hcorrectionLeB :
          (DTerm.correction B A).collectorLe B :=
        collector_le_of (DTerm.collector_before_left hA)
      have hQB : ∀ T ∈ Q, T.collectorLe B :=
        collector_inserts hcorrection hPpositive hcorrectionPositive
          hPB hcorrectionLeB
      have hABle : A.collectorLe B :=
        collector_le_of hAB
      have hRB : ∀ T ∈ R, T.collectorLe B :=
        collector_inserts hinsert hQpositive hA hQB hABle
      exact collected_append_singleton hR hRB

/-- One finite More3 collection derivation, built by inserting input terms. -/
inductive Collects
    {M N K : ℕ} :
    List (DTerm M N K) →
      List (DTerm M N K) →
        Prop where
  | nil :
      Collects [] []
  | snoc
      (P : List (DTerm M N K))
      (A : DTerm M N K)
      {C R : List (DTerm M N K)}
      (hcollect : Collects P C)
      (hinsert : Inserts C A R) :
      Collects (P ++ [A]) R

/-- Every finite More3 collection derivation preserves exact labelled evaluation. -/
lemma decorated_list_collects
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    (hcollect : Collects L R) :
    decoratedListEval R =
      decoratedListEval L := by
  induction hcollect with
  | nil =>
      rfl
  | snoc P A hcollect hinsert ihcollect =>
      rw [decorated_list_inserts hinsert, ihcollect,
        decorated_append_singleton]

lemma positiveList_collects
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    (hcollect : Collects L R)
    (hL : PositiveList L) :
    PositiveList R := by
  induction hcollect with
  | nil =>
      exact positiveList_nil
  | snoc P A hcollect hinsert ihcollect =>
      have hP : PositiveList P :=
        positive_append_left hL
      have hA : A.erasedShape.PBPos := hL A (by simp)
      exact positiveList_inserts hinsert (ihcollect hP) hA

lemma support_nonempty_collects
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    (hcollect : Collects L R)
    (hL : SupportNonemptyList L) :
    SupportNonemptyList R := by
  induction hcollect with
  | nil =>
      exact support_nonempty_nil
  | snoc P A hcollect hinsert ihcollect =>
      have hP : SupportNonemptyList P :=
        support_nonempty_append hL
      have hA : A.support.Nonempty := hL A (by simp)
      exact support_nonempty_inserts hinsert (ihcollect hP) hA

lemma collected_collects
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    (hcollect : Collects L R)
    (hL : PositiveList L) :
    Collected R := by
  induction hcollect with
  | nil =>
      exact collected_nil
  | snoc P A hcollect hinsert ihcollect =>
      have hP : PositiveList P :=
        positive_append_left hL
      have hA : A.erasedShape.PBPos := hL A (by simp)
      have hCpositive : PositiveList _ :=
        positiveList_collects hcollect hP
      exact collected_inserts hinsert (ihcollect hP) hCpositive hA

/--
Finite readiness certificate for one More3 insertion.  The later
well-founded construction only has to build this certificate from the support
invariant; exactness and collectedness then follow from `Inserts`.
-/
inductive InsertReady
    {M N K : ℕ} :
    List (DTerm M N K) →
      DTerm M N K →
        Prop where
  | nil
      (A : DTerm M N K) :
      InsertReady [] A
  | append
      (P : List (DTerm M N K))
      (B A : DTerm M N K)
      (hBA : B.collectorLe A) :
      InsertReady (P ++ [B]) A
  | obstruction
      (P : List (DTerm M N K))
      (B A : DTerm M N K)
      (hAB : A.collectorBefore B)
      (hdisjoint : Disjoint B.support A.support)
      (hcorrection : InsertReady P (DTerm.correction B A))
      (hinsert :
        ∀ Q : List (DTerm M N K),
          Inserts P (DTerm.correction B A) Q →
            InsertReady Q A) :
      InsertReady (P ++ [B]) A

lemma inserts_insert_ready
    {M N K : ℕ}
    {L : List (DTerm M N K)}
    {A : DTerm M N K}
    (hready : InsertReady L A) :
    ∃ R : List (DTerm M N K),
      Inserts L A R := by
  induction hready with
  | nil A =>
      exact ⟨[A], Inserts.nil A⟩
  | append P B A hBA =>
      exact ⟨P ++ [B, A], Inserts.append P B A hBA⟩
  | obstruction P B A hAB hdisjoint hcorrection hinsert ihcorrection ihinsert =>
      rcases ihcorrection with ⟨Q, hQ⟩
      rcases ihinsert Q hQ with ⟨R, hR⟩
      exact ⟨R ++ [B], Inserts.obstruction P B A hAB hdisjoint hQ hR⟩

/-- One insertion state for the More3 well-founded recursion. -/
abbrev InsertionState
    (M N K : ℕ) :=
  List (DTerm M N K) × DTerm M N K

def insertionStateMeasure
    {M N K : ℕ}
    (state : InsertionState M N K) :
    ℕ × ℕ × ℕ :=
  insertionMeasure state.1 state.2

def insertionStateBefore
    {M N K : ℕ} :
    InsertionState M N K → InsertionState M N K → Prop :=
  InvImage insertionMeasureBefore insertionStateMeasure

lemma insertion_state_wf
    {M N K : ℕ} :
    WellFounded (@insertionStateBefore M N K) := by
  exact InvImage.wf insertionStateMeasure insertion_measure_wf

/--
Build readiness from one genuine More3 well-founded recursive step.  The
remaining construction theorem should instantiate `hstep` from the support
invariant of the raw trace.
-/
lemma insert_well_founded
    {M N K : ℕ}
    (hstep :
      ∀ (L : List (DTerm M N K)) (A : DTerm M N K),
        (∀ (L' : List (DTerm M N K)) (A' : DTerm M N K),
          insertionMeasureBefore (insertionMeasure L' A') (insertionMeasure L A) →
            InsertReady L' A') →
          InsertReady L A) :
    ∀ (L : List (DTerm M N K)) (A : DTerm M N K),
      InsertReady L A := by
  intro L A
  refine insertion_state_wf.induction
    (C := fun state => InsertReady state.1 state.2) (L, A) ?_
  rintro ⟨L, A⟩ ih
  exact hstep L A (fun L' A' hmeasure =>
    ih (L', A') hmeasure)

/--
More3 insertion exists once its global support invariant has been proved:
every current obstruction has support disjoint from the term being inserted.
-/
lemma insert_ready_invariant
    {M N K : ℕ}
    (hpositive :
      ∀ T : DTerm M N K,
        T.erasedShape.PBPos)
    (hsupport :
      ∀ T : DTerm M N K,
        T.support.Nonempty)
    (hcan :
      ∀ (L : List (DTerm M N K)) (A : DTerm M N K),
        CanInsert L A) :
    ∀ (L : List (DTerm M N K)) (A : DTerm M N K),
      InsertReady L A := by
  apply insert_well_founded
  intro L A ih
  rcases List.eq_nil_or_concat' L with rfl | ⟨P, B, rfl⟩
  · exact InsertReady.nil A
  · by_cases hAB : A.collectorBefore B
    · have hdisjoint : Disjoint B.support A.support :=
        hcan (P ++ [B]) A B (by simp) hAB
      have hcorrection :
          InsertReady P (DTerm.correction B A) :=
        ih P (DTerm.correction B A)
          (insertion_measure_disjoint P hdisjoint (hsupport B))
      refine InsertReady.obstruction P B A hAB hdisjoint hcorrection ?_
      intro Q hQ
      exact ih Q A
        (measure_after_inserts P hAB
          (fun T _hT => hpositive T) (hpositive B) (hpositive A) hQ)
    · exact InsertReady.append P B A hAB

/-- Finite readiness certificate for collecting an input decorated list. -/
inductive CollectReady
    {M N K : ℕ} :
    List (DTerm M N K) →
      Prop where
  | nil :
      CollectReady []
  | snoc
      (P : List (DTerm M N K))
      (A : DTerm M N K)
      (hcollect : CollectReady P)
      (hinsert :
        ∀ C : List (DTerm M N K),
          Collects P C →
            InsertReady C A) :
      CollectReady (P ++ [A])

lemma collects_collect_ready
    {M N K : ℕ}
    {L : List (DTerm M N K)}
    (hready : CollectReady L) :
    ∃ R : List (DTerm M N K),
      Collects L R := by
  induction hready with
  | nil =>
      exact ⟨[], Collects.nil⟩
  | snoc P A hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨C, hC⟩
      rcases inserts_insert_ready (hinsert C hC) with ⟨R, hR⟩
      exact ⟨R, Collects.snoc P A hC hR⟩

lemma collect_ready_invariant
    {M N K : ℕ}
    (hpositive :
      ∀ T : DTerm M N K,
        T.erasedShape.PBPos)
    (hsupport :
      ∀ T : DTerm M N K,
        T.support.Nonempty)
    (hcan :
      ∀ (L : List (DTerm M N K)) (A : DTerm M N K),
        CanInsert L A) :
    ∀ L : List (DTerm M N K),
      CollectReady L := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
      exact CollectReady.nil
  | append_singleton P A hP =>
      exact CollectReady.snoc P A hP fun C _hC =>
        insert_ready_invariant hpositive hsupport hcan C A

/--
Reachable-state form of More3's support invariant.  This is the version the
raw trace construction must discharge: obstructions are disjoint whenever
the current state retains positivity and nonempty raw support.
-/
def ReachableCanInsert
    {M N K : ℕ} :
    Prop :=
  ∀ (L : List (DTerm M N K)) (A : DTerm M N K),
    Collected L →
      PositiveList L →
        SupportNonemptyList L →
          A.erasedShape.PBPos →
            A.support.Nonempty →
              CanInsert L A

lemma insert_ready_can
    {M N K : ℕ}
    (hcan : @ReachableCanInsert M N K) :
    ∀ (L : List (DTerm M N K)) (A : DTerm M N K),
      Collected L →
        PositiveList L →
          SupportNonemptyList L →
            A.erasedShape.PBPos →
              A.support.Nonempty →
                InsertReady L A := by
  intro L A
  refine insertion_state_wf.induction
    (C := fun state =>
      Collected state.1 →
        PositiveList state.1 →
          SupportNonemptyList state.1 →
            state.2.erasedShape.PBPos →
              state.2.support.Nonempty →
                InsertReady state.1 state.2)
    (L, A) ?_
  rintro ⟨L, A⟩ ih hLcollected hLpositive hLsupport hApositive hAsupport
  rcases List.eq_nil_or_concat' L with rfl | ⟨P, B, rfl⟩
  · exact InsertReady.nil A
  · by_cases hAB : A.collectorBefore B
    · have hdisjoint : Disjoint B.support A.support :=
        hcan (P ++ [B]) A hLcollected hLpositive hLsupport hApositive hAsupport
          B (by simp) hAB
      have hPcollected : Collected P :=
        collected_append_left hLcollected
      have hPpositive : PositiveList P :=
        positive_append_left hLpositive
      have hPsupport : SupportNonemptyList P :=
        support_nonempty_append hLsupport
      have hBpositive : B.erasedShape.PBPos :=
        hLpositive B (by simp)
      have hBsupport : B.support.Nonempty :=
        hLsupport B (by simp)
      have hcorrectionPositive :
          (DTerm.correction B A).erasedShape.PBPos :=
        DTerm.correction_positive hBpositive hApositive
      have hcorrectionSupport :
          (DTerm.correction B A).support.Nonempty :=
        DTerm.support_nonempty_left hBsupport
      have hcorrection :
          InsertReady P (DTerm.correction B A) :=
        ih (P, DTerm.correction B A)
          (insertion_measure_disjoint P hdisjoint hBsupport)
          hPcollected hPpositive hPsupport hcorrectionPositive hcorrectionSupport
      refine InsertReady.obstruction P B A hAB hdisjoint hcorrection ?_
      intro Q hQ
      have hQpositive : PositiveList Q :=
        positiveList_inserts hQ hPpositive hcorrectionPositive
      have hQsupport : SupportNonemptyList Q :=
        support_nonempty_inserts hQ hPsupport hcorrectionSupport
      have hQcollected : Collected Q :=
        collected_inserts hQ hPcollected hPpositive hcorrectionPositive
      exact ih (Q, A)
        (measure_after_inserts P hAB hPpositive
          hBpositive hApositive hQ)
        hQcollected hQpositive hQsupport hApositive hAsupport
    · exact InsertReady.append P B A hAB

lemma ready_can_insert
    {M N K : ℕ}
    (hcan : @ReachableCanInsert M N K) :
    ∀ L : List (DTerm M N K),
      PositiveList L →
        SupportNonemptyList L →
          CollectReady L := by
  intro L hLpositive hLsupport
  induction L using List.reverseRecOn with
  | nil =>
      exact CollectReady.nil
  | append_singleton P A ih =>
      have hPpositive : PositiveList P :=
        positive_append_left hLpositive
      have hPsupport : SupportNonemptyList P :=
        support_nonempty_append hLsupport
      have hApositive : A.erasedShape.PBPos :=
        hLpositive A (by simp)
      have hAsupport : A.support.Nonempty :=
        hLsupport A (by simp)
      exact CollectReady.snoc P A (ih hPpositive hPsupport) fun C hC =>
        insert_ready_can hcan C A
          (collected_collects hC hPpositive)
          (positiveList_collects hC hPpositive)
          (support_nonempty_collects hC hPsupport)
          hApositive hAsupport

/--
The actual finite history collector only interchanges independent histories.
This is the support condition More3 uses for its strict recursive decrease;
overlapping histories remain in their existing relative order.
-/
def DTerm.independentBefore
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Prop :=
  T.shapeBefore U ∧ Disjoint T.support U.support

instance DTerm.independentBeforeDecidable
    {M N K : ℕ}
    (T U : DTerm M N K) :
    Decidable (T.independentBefore U) := by
  unfold DTerm.independentBefore
  infer_instance

lemma disjoint_independent_before
    {M N K : ℕ}
    {T U : DTerm M N K}
    (hTU : T.independentBefore U) :
    Disjoint T.support U.support :=
  hTU.2

lemma independent_before_subset
    {M N K : ℕ}
    {T U : DTerm M N K}
    (hT : T.support.Nonempty)
    (hTU : T.support ⊆ U.support) :
    ¬ T.independentBefore U := by
  intro hbefore
  rcases hT with ⟨index, hindex⟩
  exact Finset.disjoint_left.mp hbefore.2 hindex (hTU hindex)

/-- Number of genuine independent obstructions to appending one history. -/
def independentObstructionCount
    {M N K : ℕ}
    (L : List (DTerm M N K))
    (A : DTerm M N K) :
    ℕ :=
  L.countP fun B => decide (A.independentBefore B)

@[simp]
lemma independent_obstruction_nil
    {M N K : ℕ}
    (A : DTerm M N K) :
    independentObstructionCount [] A = 0 :=
  rfl

@[simp]
lemma independent_obstruction_append
    {M N K : ℕ}
    (P L : List (DTerm M N K))
    (A : DTerm M N K) :
    independentObstructionCount (P ++ L) A =
      independentObstructionCount P A + independentObstructionCount L A := by
  simp [independentObstructionCount, List.countP_append]

lemma independent_obstruction_before
    {M N K : ℕ}
    (P : List (DTerm M N K))
    (B A : DTerm M N K)
    (hAB : A.independentBefore B) :
    independentObstructionCount (P ++ [B]) A =
      independentObstructionCount P A + 1 := by
  simp [independentObstructionCount, hAB]

/-- More3's lexicographic measure for the genuine independent-history collector. -/
def independentInsertionMeasure
    {M N K : ℕ}
    (L : List (DTerm M N K))
    (A : DTerm M N K) :
    ℕ × ℕ × ℕ :=
  (A.supportDefect, independentObstructionCount L A, L.length)

lemma independent_measure_before
    {M N K : ℕ}
    (P : List (DTerm M N K))
    {B A : DTerm M N K}
    (hAB : A.independentBefore B)
    (hB : B.support.Nonempty) :
    insertionMeasureBefore
      (independentInsertionMeasure P (DTerm.correction B A))
      (independentInsertionMeasure (P ++ [B]) A) := by
  apply Prod.Lex.left
  exact
    DTerm.support_defect_disjoint
      hAB.2.symm hB

/--
One finite independent-history insertion derivation.  Unlike the discarded
countdown helper, its obstruction constructor itself contains the strict
support-disjointness needed for recursive descent.
-/
inductive IInsert
    {M N K : ℕ} :
    List (DTerm M N K) →
      DTerm M N K →
        List (DTerm M N K) →
          Prop where
  | nil
      (A : DTerm M N K) :
      IInsert [] A [A]
  | append
      (P : List (DTerm M N K))
      (B A : DTerm M N K)
      (hAB : ¬ A.independentBefore B) :
      IInsert (P ++ [B]) A (P ++ [B, A])
  | obstruction
      (P : List (DTerm M N K))
      (B A : DTerm M N K)
      (hAB : A.independentBefore B)
      {Q R : List (DTerm M N K)}
      (hcorrection : IInsert P (DTerm.correction B A) Q)
      (hinsert : IInsert Q A R) :
      IInsert (P ++ [B]) A (R ++ [B])

lemma decorated_independent_inserts
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {A : DTerm M N K}
    (hinsert : IInsert L A R) :
    decoratedListEval R =
      decoratedListEval L * A.eval := by
  induction hinsert with
  | nil A =>
      simp
  | append P B A _hAB =>
      simp [decoratedListEval, List.prod_append, mul_assoc]
  | obstruction P B A _hAB hcorrection hinsert ihcorrection ihinsert =>
      rw [decorated_append_singleton, ihinsert, ihcorrection,
        decorated_append_singleton]
      calc
        (decoratedListEval P * (DTerm.correction B A).eval) *
              A.eval * B.eval =
            decoratedListEval P *
              ((DTerm.correction B A).eval * A.eval * B.eval) := by
                group
        _ = decoratedListEval P * (B.eval * A.eval) := by
              rw [DTerm.eval_correction_mul]
        _ = (decoratedListEval P * B.eval) * A.eval := by
              group

lemma positive_independent_inserts
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {A : DTerm M N K}
    (hinsert : IInsert L A R)
    (hL : PositiveList L)
    (hA : A.erasedShape.PBPos) :
    PositiveList R := by
  induction hinsert with
  | nil A =>
      intro T hT
      rcases List.mem_singleton.mp hT with rfl
      exact hA
  | append P B A _hAB =>
      simpa [List.append_assoc] using positive_append_singleton hL hA
  | obstruction P B A _hAB hcorrection hinsert ihcorrection ihinsert =>
      have hP : PositiveList P :=
        positive_append_left hL
      have hB : B.erasedShape.PBPos := hL B (by simp)
      have hcorrectionPositive :
          (DTerm.correction B A).erasedShape.PBPos :=
        DTerm.correction_positive hB hA
      have hQ := ihcorrection hP hcorrectionPositive
      have hR := ihinsert hQ hA
      exact positive_append_singleton hR hB

lemma support_independent_inserts
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {A : DTerm M N K}
    (hinsert : IInsert L A R)
    (hL : SupportNonemptyList L)
    (hA : A.support.Nonempty) :
    SupportNonemptyList R := by
  induction hinsert with
  | nil A =>
      intro T hT
      rcases List.mem_singleton.mp hT with rfl
      exact hA
  | append P B A _hAB =>
      simpa [List.append_assoc] using support_nonempty_singleton hL hA
  | obstruction P B A _hAB hcorrection hinsert ihcorrection ihinsert =>
      have hP : SupportNonemptyList P :=
        support_nonempty_append hL
      have hB : B.support.Nonempty := hL B (by simp)
      have hcorrectionNonempty :
          (DTerm.correction B A).support.Nonempty :=
        DTerm.support_nonempty_left hB
      have hQ := ihcorrection hP hcorrectionNonempty
      have hR := ihinsert hQ hA
      exact support_nonempty_singleton hR hB

lemma independent_inserts_not
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {C T : DTerm M N K}
    (hinsert : IInsert L C R)
    (hT : T ∈ R)
    (hTnot : T ∉ L) :
    C.support ⊆ T.support := by
  induction hinsert generalizing T with
  | nil C =>
      rcases List.mem_singleton.mp hT with rfl
      exact Finset.Subset.rfl
  | append P B C _hCB =>
      rcases List.mem_append.mp hT with hTP | hTBC
      · exact False.elim (hTnot (List.mem_append_left [B] hTP))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hTBC
        rcases hTBC with rfl | rfl
        · exact False.elim (hTnot (by simp))
        · exact Finset.Subset.rfl
  | @obstruction P B C _hCB Q R hcorrection hinsert ihcorrection ihinsert =>
      rcases List.mem_append.mp hT with hTR | hTB
      · by_cases hTQ : T ∈ Q
        · have hTnotP : T ∉ P := by
            intro hTP
            exact hTnot (List.mem_append_left [B] hTP)
          exact
            (DTerm.support_subset_right B C).trans
              (ihcorrection hTQ hTnotP)
        · exact ihinsert hTR hTQ
      · rcases List.mem_singleton.mp hTB with rfl
        exact False.elim (hTnot (by simp))

lemma independent_inserts_subset
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    {A C : DTerm M N K}
    (hinsert : IInsert L C R)
    (hA : A.support.Nonempty)
    (hAC : A.support ⊆ C.support) :
    independentObstructionCount R A =
      independentObstructionCount L A := by
  induction hinsert generalizing A with
  | nil C =>
      have hnotAC : ¬ A.independentBefore C :=
        independent_before_subset hA hAC
      simp [independentObstructionCount, hnotAC]
  | append P B C _hCB =>
      have hnotAC : ¬ A.independentBefore C :=
        independent_before_subset hA hAC
      have hcountC : independentObstructionCount [C] A = 0 := by
        simp [independentObstructionCount, hnotAC]
      calc
        independentObstructionCount (P ++ [B, C]) A =
            independentObstructionCount ((P ++ [B]) ++ [C]) A := by
              simp [List.append_assoc]
        _ = independentObstructionCount (P ++ [B]) A +
              independentObstructionCount [C] A := by
              rw [independent_obstruction_append]
        _ = independentObstructionCount (P ++ [B]) A := by
              rw [hcountC, Nat.add_zero]
  | obstruction P B C _hCB hcorrection hinsert ihcorrection ihinsert =>
      have hAD :
          A.support ⊆ (DTerm.correction B C).support :=
        hAC.trans (DTerm.support_subset_right B C)
      rw [independent_obstruction_append,
        independent_obstruction_append,
        ihinsert hA hAC, ihcorrection hA hAD]

lemma measure_after_before
    {M N K : ℕ}
    (P : List (DTerm M N K))
    {B A : DTerm M N K}
    {Q : List (DTerm M N K)}
    (hAB : A.independentBefore B)
    (hA : A.support.Nonempty)
    (hcorrection : IInsert P (DTerm.correction B A) Q) :
    insertionMeasureBefore
      (independentInsertionMeasure Q A)
      (independentInsertionMeasure (P ++ [B]) A) := by
  unfold independentInsertionMeasure insertionMeasureBefore
  apply Prod.Lex.right A.supportDefect
  apply Prod.Lex.left Q.length (P ++ [B]).length
  rw [independent_inserts_subset hcorrection
      hA (DTerm.support_subset_right B A),
    independent_obstruction_before P B A hAB]
  simpa only [Nat.succ_eq_add_one] using
    Nat.lt_succ_self (independentObstructionCount P A)

/-- Finite readiness certificate for one genuine independent-history insertion. -/
inductive IndependentInsertReady
    {M N K : ℕ} :
    List (DTerm M N K) →
      DTerm M N K →
        Prop where
  | nil
      (A : DTerm M N K) :
      IndependentInsertReady [] A
  | append
      (P : List (DTerm M N K))
      (B A : DTerm M N K)
      (hAB : ¬ A.independentBefore B) :
      IndependentInsertReady (P ++ [B]) A
  | obstruction
      (P : List (DTerm M N K))
      (B A : DTerm M N K)
      (hAB : A.independentBefore B)
      (hcorrection : IndependentInsertReady P (DTerm.correction B A))
      (hinsert :
        ∀ Q : List (DTerm M N K),
          IInsert P (DTerm.correction B A) Q →
            IndependentInsertReady Q A) :
      IndependentInsertReady (P ++ [B]) A

lemma independent_inserts_ready
    {M N K : ℕ}
    {L : List (DTerm M N K)}
    {A : DTerm M N K}
    (hready : IndependentInsertReady L A) :
    ∃ R : List (DTerm M N K),
      IInsert L A R := by
  induction hready with
  | nil A =>
      exact ⟨[A], IInsert.nil A⟩
  | append P B A hAB =>
      exact ⟨P ++ [B, A], IInsert.append P B A hAB⟩
  | obstruction P B A hAB hcorrection hinsert ihcorrection ihinsert =>
      rcases ihcorrection with ⟨Q, hQ⟩
      rcases ihinsert Q hQ with ⟨R, hR⟩
      exact ⟨R ++ [B], IInsert.obstruction P B A hAB hQ hR⟩

abbrev IndependentInsertionState
    (M N K : ℕ) :=
  List (DTerm M N K) × DTerm M N K

def independentStateMeasure
    {M N K : ℕ}
    (state : IndependentInsertionState M N K) :
    ℕ × ℕ × ℕ :=
  independentInsertionMeasure state.1 state.2

def independentInsertionBefore
    {M N K : ℕ} :
    IndependentInsertionState M N K →
      IndependentInsertionState M N K →
        Prop :=
  InvImage insertionMeasureBefore independentStateMeasure

lemma independent_before_wf
    {M N K : ℕ} :
    WellFounded (@independentInsertionBefore M N K) := by
  exact InvImage.wf independentStateMeasure insertion_measure_wf

lemma independentInsertReady
    {M N K : ℕ} :
    ∀ (L : List (DTerm M N K)) (A : DTerm M N K),
      PositiveList L →
        SupportNonemptyList L →
          A.erasedShape.PBPos →
            A.support.Nonempty →
              IndependentInsertReady L A := by
  intro L A
  refine independent_before_wf.induction
    (C := fun state =>
      PositiveList state.1 →
        SupportNonemptyList state.1 →
          state.2.erasedShape.PBPos →
            state.2.support.Nonempty →
              IndependentInsertReady state.1 state.2)
    (L, A) ?_
  rintro ⟨L, A⟩ ih hLpositive hLsupport hApositive hAsupport
  rcases List.eq_nil_or_concat' L with rfl | ⟨P, B, rfl⟩
  · exact IndependentInsertReady.nil A
  · by_cases hAB : A.independentBefore B
    · have hPpositive : PositiveList P :=
        positive_append_left hLpositive
      have hPsupport : SupportNonemptyList P :=
        support_nonempty_append hLsupport
      have hBpositive : B.erasedShape.PBPos :=
        hLpositive B (by simp)
      have hBsupport : B.support.Nonempty :=
        hLsupport B (by simp)
      have hcorrectionPositive :
          (DTerm.correction B A).erasedShape.PBPos :=
        DTerm.correction_positive hBpositive hApositive
      have hcorrectionSupport :
          (DTerm.correction B A).support.Nonempty :=
        DTerm.support_nonempty_left hBsupport
      have hcorrection :
          IndependentInsertReady P (DTerm.correction B A) :=
        ih (P, DTerm.correction B A)
          (independent_measure_before P hAB hBsupport)
          hPpositive hPsupport hcorrectionPositive hcorrectionSupport
      refine IndependentInsertReady.obstruction P B A hAB hcorrection ?_
      intro Q hQ
      exact ih (Q, A)
        (measure_after_before P hAB hAsupport hQ)
        (positive_independent_inserts hQ hPpositive hcorrectionPositive)
        (support_independent_inserts hQ hPsupport hcorrectionSupport)
        hApositive hAsupport
    · exact IndependentInsertReady.append P B A hAB

/-- One finite exact collection derivation using only genuine independent swaps. -/
inductive ICollec
    {M N K : ℕ} :
    List (DTerm M N K) →
      List (DTerm M N K) →
        Prop where
  | nil :
      ICollec [] []
  | snoc
      (P : List (DTerm M N K))
      (A : DTerm M N K)
      {C R : List (DTerm M N K)}
      (hcollect : ICollec P C)
      (hinsert : IInsert C A R) :
      ICollec (P ++ [A]) R

lemma decorated_independent_collects
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    (hcollect : ICollec L R) :
    decoratedListEval R =
      decoratedListEval L := by
  induction hcollect with
  | nil =>
      rfl
  | snoc P A hcollect hinsert ihcollect =>
      rw [decorated_independent_inserts hinsert, ihcollect,
        decorated_append_singleton]

lemma positive_independent_collects
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    (hcollect : ICollec L R)
    (hL : PositiveList L) :
    PositiveList R := by
  induction hcollect with
  | nil =>
      exact positiveList_nil
  | snoc P A hcollect hinsert ihcollect =>
      have hP : PositiveList P :=
        positive_append_left hL
      have hA : A.erasedShape.PBPos := hL A (by simp)
      exact positive_independent_inserts hinsert (ihcollect hP) hA

lemma support_independent_collects
    {M N K : ℕ}
    {L R : List (DTerm M N K)}
    (hcollect : ICollec L R)
    (hL : SupportNonemptyList L) :
    SupportNonemptyList R := by
  induction hcollect with
  | nil =>
      exact support_nonempty_nil
  | snoc P A hcollect hinsert ihcollect =>
      have hP : SupportNonemptyList P :=
        support_nonempty_append hL
      have hA : A.support.Nonempty := hL A (by simp)
      exact support_independent_inserts hinsert (ihcollect hP) hA

inductive IndependentCollectReady
    {M N K : ℕ} :
    List (DTerm M N K) →
      Prop where
  | nil :
      IndependentCollectReady []
  | snoc
      (P : List (DTerm M N K))
      (A : DTerm M N K)
      (hcollect : IndependentCollectReady P)
      (hinsert :
        ∀ C : List (DTerm M N K),
          ICollec P C →
            IndependentInsertReady C A) :
      IndependentCollectReady (P ++ [A])

lemma independent_collects_ready
    {M N K : ℕ}
    {L : List (DTerm M N K)}
    (hready : IndependentCollectReady L) :
    ∃ R : List (DTerm M N K),
      ICollec L R := by
  induction hready with
  | nil =>
      exact ⟨[], ICollec.nil⟩
  | snoc P A hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨C, hC⟩
      rcases independent_inserts_ready (hinsert C hC) with ⟨R, hR⟩
      exact ⟨R, ICollec.snoc P A hC hR⟩

lemma independentCollectReady
    {M N K : ℕ} :
    ∀ L : List (DTerm M N K),
      PositiveList L →
        SupportNonemptyList L →
          IndependentCollectReady L := by
  intro L hLpositive hLsupport
  induction L using List.reverseRecOn with
  | nil =>
      exact IndependentCollectReady.nil
  | append_singleton P A ih =>
      have hPpositive : PositiveList P :=
        positive_append_left hLpositive
      have hPsupport : SupportNonemptyList P :=
        support_nonempty_append hLsupport
      have hApositive : A.erasedShape.PBPos :=
        hLpositive A (by simp)
      have hAsupport : A.support.Nonempty :=
        hLsupport A (by simp)
      exact IndependentCollectReady.snoc P A (ih hPpositive hPsupport) fun C hC =>
        independentInsertReady C A
          (positive_independent_collects hC hPpositive)
          (support_independent_collects hC hPsupport)
          hApositive hAsupport

/-- Decorate the raw trace by its occurrence index. -/
def decorateRaw
    {M N : ℕ}
    (L : List (CWord (LabelledAtom M N))) :
    List (DTerm M N L.length) :=
  List.ofFn fun index => DTerm.raw (L.get index) index

lemma decorated_decorate_raw
    {M N : ℕ}
    (L : List (CWord (LabelledAtom M N))) :
    decoratedListEval (decorateRaw L) =
      labelledListEval L := by
  simp only [decoratedListEval, decorateRaw, List.map_ofFn,
    Function.comp_def, DTerm.eval_raw, labelledListEval]
  congr 1
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp [List.get_eq_getElem]

lemma decorateRaw_positive
    {M N : ℕ}
    {L : List (CWord (LabelledAtom M N))}
    (hL : ∀ word ∈ L, (collapseWord word).PBPos) :
    ∀ T ∈ decorateRaw L,
      (collapseWord T.word).PBPos := by
  intro T hT
  rcases List.mem_ofFn.mp hT with ⟨index, rfl⟩
  exact hL (L.get index) (List.get_mem L index)

/-- Exact collector state before any More3 insertion steps are performed. -/
structure DColl
    (M N K : ℕ) where
  factors :
    List (DTerm M N K)
  eval_eq :
    decoratedListEval factors =
      ⁅labelledLeft M N, labelledRight M N⁆
  factors_positive :
    ∀ T ∈ factors,
      T.erasedShape.PBPos
  factors_support_nonempty :
    ∀ T ∈ factors,
      T.support.Nonempty

/-- A decorated collection whose More3 output order is already collected. -/
structure CollectedDecoratedCollection
    (M N K : ℕ) extends DColl M N K where
  factors_collected :
    Collected factors

lemma DColl.collapsed_evaleq_commpow
    {M N K : ℕ}
    (C : DColl M N K) :
    decoratedCollapsedEval C.factors =
      ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  calc
    decoratedCollapsedEval C.factors =
        collapseHom M N (decoratedListEval C.factors) :=
      (collapse_decorated_eval C.factors).symm
    _ = collapseHom M N ⁅labelledLeft M N, labelledRight M N⁆ := by
      rw [C.eval_eq]
    _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
      rw [map_commutatorElement, collapse_labelled_left,
        collapse_labelled_right]

/-- The labelled raw trace, now equipped with singleton More3 supports. -/
def rawDecoratedCollection
    (M N : ℕ) :
    DColl M N
      (leftRightTrace (labelledLeftAtoms M N) (labelledRightAtoms M N)).length where
  factors :=
    decorateRaw (leftRightTrace (labelledLeftAtoms M N) (labelledRightAtoms M N))
  eval_eq := by
    rw [decorated_decorate_raw]
    simpa [labelled_left_atoms,
      labelled_atom_atoms] using
      (labelled_left_trace
        (labelledLeftAtoms M N) (labelledRightAtoms M N))
  factors_positive := by
    exact
      decorateRaw_positive
        (left_right_positive
          (labelledLeftAtoms M N) (labelledRightAtoms M N)
          (fun a ha => collapse_label_atoms ha)
          (fun a ha => collapse_labelled_atoms ha))
  factors_support_nonempty := by
    intro T hT
    rcases List.mem_ofFn.mp hT with ⟨index, rfl⟩
    exact DTerm.support_raw_nonempty _ _

lemma collected_decorated_ready
    {M N K : ℕ}
    (C : DColl M N K)
    (hready : CollectReady C.factors) :
    Nonempty (CollectedDecoratedCollection M N K) := by
  rcases collects_collect_ready hready with ⟨factors, hcollect⟩
  exact ⟨{
    factors := factors
    eval_eq := by
      rw [decorated_list_collects hcollect]
      exact C.eval_eq
    factors_positive := positiveList_collects hcollect C.factors_positive
    factors_support_nonempty :=
      support_nonempty_collects hcollect C.factors_support_nonempty
    factors_collected := collected_collects hcollect C.factors_positive }⟩

/--
Swap the two inputs of the top commutator.  On a genuine commutator word this
evaluates to the inverse, while leaving the subwords themselves unchanged.
-/
def rootSwapWord
    {α : Type*} :
    CWord α → CWord α
  | .atom a => .atom a
  | .commutator u v => .commutator v u

@[simp]
lemma root_swap_commutator
    {α G : Type*} [Group G]
    (f : α → G)
    (u v : CWord α) :
    (rootSwapWord (CWord.commutator u v)).eval f =
      ((CWord.commutator u v).eval f)⁻¹ := by
  simp [rootSwapWord, commutatorElement_def, mul_assoc]

lemma pair_bidegree_positive
    {w : CWord HPAtom}
    (hw : w.PBPos) :
    ∃ u v : CWord HPAtom,
      w = CWord.commutator u v := by
  cases w with
  | atom a =>
      cases a <;>
        simp [CWord.PBPos] at hw
  | commutator u v =>
      exact ⟨u, v, rfl⟩

lemma swap_bidegree_positive
    {G : Type*} [Group G]
    (f : HPAtom → G)
    {w : CWord HPAtom}
    (hw : w.PBPos) :
    (rootSwapWord w).eval f = (w.eval f)⁻¹ := by
  rcases pair_bidegree_positive hw with ⟨u, v, rfl⟩
  exact root_swap_commutator f u v

lemma root_swap_positive
    {w : CWord HPAtom}
    (hw : w.PBPos) :
    (rootSwapWord w).pairLeftDegree = w.pairLeftDegree := by
  rcases pair_bidegree_positive hw with ⟨u, v, rfl⟩
  simp [rootSwapWord, Nat.add_comm]

lemma pair_swap_positive
    {w : CWord HPAtom}
    (hw : w.PBPos) :
    (rootSwapWord w).pairRightDegree = w.pairRightDegree := by
  rcases pair_bidegree_positive hw with ⟨u, v, rfl⟩
  simp [rootSwapWord, Nat.add_comm]

lemma rootSwap_positive
    {w : CWord HPAtom}
    (hw : w.PBPos) :
    (rootSwapWord w).PBPos := by
  rw [CWord.PBPos,
    root_swap_positive hw,
    pair_swap_positive hw]
  exact hw

lemma collapse_root_swap
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    collapseWord (rootSwapWord w) =
      rootSwapWord (collapseWord w) := by
  cases w with
  | atom a =>
      rfl
  | commutator u v =>
      rfl

lemma weight_root_swap
    {α : Type*}
    (wt : α → ℕ)
    (w : CWord α) :
    (rootSwapWord w).weight wt = w.weight wt := by
  cases w with
  | atom a =>
      rfl
  | commutator u v =>
      simp [rootSwapWord, Nat.add_comm]

/-- Source labels occurring in one labelled formal commutator word. -/
def labelSupport
    {M N : ℕ} :
    CWord (LabelledAtom M N) →
      Finset (LabelledAtom M N)
  | .atom a => {a}
  | .commutator u v => labelSupport u ∪ labelSupport v

/-- Every source label occurs at most once in a labelled formal word. -/
def LabelLinear
    {M N : ℕ} :
    CWord (LabelledAtom M N) → Prop
  | .atom _ => True
  | .commutator u v =>
      LabelLinear u ∧ LabelLinear v ∧
        Disjoint (labelSupport u) (labelSupport v)

/-- Left source labels occurring in one labelled formal commutator word. -/
def leftLabelSupport
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    Finset (Fin M) :=
  (labelSupport w).toLeft

/-- Right source labels occurring in one labelled formal commutator word. -/
def rightLabelSupport
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    Finset (Fin N) :=
  (labelSupport w).toRight

/-- Relabel left and right source atoms separately inside one formal word. -/
def relabelWord
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    CWord (LabelledAtom M N) →
      CWord (LabelledAtom M' N')
  | .atom (.inl i) => .atom (.inl (left i))
  | .atom (.inr j) => .atom (.inr (right j))
  | .commutator u v => .commutator (relabelWord left right u) (relabelWord left right v)

/-- Relabel one left/right source atom without requiring injectivity. -/
def relabelLabel
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    LabelledAtom M N → LabelledAtom M' N'
  | .inl i => .inl (left i)
  | .inr j => .inr (right j)

/-- Relabel the selected word of one decorated history without changing its raw support. -/
def DTerm.relabel
    {M N M' N' K : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (T : DTerm M N K) :
    DTerm M' N' K where
  word := relabelWord left right T.word
  support := T.support

@[simp]
lemma DTerm.support_relabel
    {M N M' N' K : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (T : DTerm M N K) :
    (T.relabel left right).support = T.support :=
  rfl

@[simp]
lemma collapse_word_relabel
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ w : CWord (LabelledAtom M N),
      collapseWord (relabelWord left right w) = collapseWord w
  | .atom (.inl _) => rfl
  | .atom (.inr _) => rfl
  | .commutator u v => by
      change
        CWord.commutator (collapseWord (relabelWord left right u))
            (collapseWord (relabelWord left right v)) =
          CWord.commutator (collapseWord u) (collapseWord v)
      rw [collapse_word_relabel left right u,
        collapse_word_relabel left right v]

@[simp]
lemma DTerm.erasedShape_relabel
    {M N M' N' K : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (T : DTerm M N K) :
    (T.relabel left right).erasedShape = T.erasedShape := by
  exact collapse_word_relabel left right T.word

lemma DTerm.shape_before_relabeliff
    {M N M' N' K : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (T U : DTerm M N K) :
    (T.relabel left right).shapeBefore (U.relabel left right) ↔
      T.shapeBefore U := by
  simp [DTerm.shapeBefore, DTerm.higherDegreeBefore,
    DTerm.erasedDegree, DTerm.erasedShapeCode]

lemma DTerm.indep_before_relabeliff
    {M N M' N' K : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (T U : DTerm M N K) :
    (T.relabel left right).independentBefore (U.relabel left right) ↔
      T.independentBefore U := by
  simp [DTerm.independentBefore,
    DTerm.shape_before_relabeliff]

@[simp]
lemma DTerm.relabel_correction
    {M N M' N' K : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (B A : DTerm M N K) :
    (DTerm.correction B A).relabel left right =
      DTerm.correction (B.relabel left right) (A.relabel left right) := by
  rfl

lemma independentInserts_relabel
    {M N M' N' K : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    {L R : List (DTerm M N K)}
    {A : DTerm M N K}
    (hinsert : IInsert L A R) :
    IInsert
      (L.map (DTerm.relabel left right))
      (A.relabel left right)
      (R.map (DTerm.relabel left right)) := by
  induction hinsert with
  | nil A =>
      exact IInsert.nil (A.relabel left right)
  | append P B A hAB =>
      have hAB' :
          ¬ (A.relabel left right).independentBefore (B.relabel left right) :=
        fun h => hAB ((DTerm.indep_before_relabeliff left right A B).1 h)
      simpa [List.map_append] using
        (IInsert.append
          (P.map (DTerm.relabel left right))
          (B.relabel left right) (A.relabel left right) hAB')
  | obstruction P B A hAB hcorrection hinsert ihcorrection ihinsert =>
      simpa [List.map_append] using
        (IInsert.obstruction
          (P.map (DTerm.relabel left right))
          (B.relabel left right) (A.relabel left right)
          ((DTerm.indep_before_relabeliff left right A B).2 hAB)
          ihcorrection ihinsert)

lemma independentCollects_relabel
    {M N M' N' K : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    {L R : List (DTerm M N K)}
    (hcollect : ICollec L R) :
    ICollec
      (L.map (DTerm.relabel left right))
      (R.map (DTerm.relabel left right)) := by
  induction hcollect with
  | nil =>
      exact ICollec.nil
  | snoc P A hcollect hinsert ihcollect =>
      simpa [List.map_append] using
        (ICollec.snoc
          (P.map (DTerm.relabel left right))
          (A.relabel left right)
          ihcollect (independentInserts_relabel left right hinsert))

@[simp]
lemma relabel_root_swap
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ w : CWord (LabelledAtom M N),
      relabelWord left right (rootSwapWord w) =
        rootSwapWord (relabelWord left right w)
  | .atom (.inl _) => rfl
  | .atom (.inr _) => rfl
  | .commutator _ _ => rfl

lemma relabelWord_eval
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ w : CWord (LabelledAtom M N),
      (relabelWord left right w).eval FreeGroup.of =
        (FreeGroup.map fun
          | Sum.inl i => (Sum.inl (left i) : LabelledAtom M' N')
          | Sum.inr j => (Sum.inr (right j) : LabelledAtom M' N'))
          (w.eval FreeGroup.of)
  | .atom (.inl _) => by
      simp [relabelWord]
  | .atom (.inr _) => by
      simp [relabelWord]
  | .commutator u v => by
      rw [relabelWord, CWord.eval_commutator,
        relabelWord_eval left right u, relabelWord_eval left right v,
        CWord.eval_commutator, map_commutatorElement]

lemma label_support_image
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ w : CWord (LabelledAtom M N),
      labelSupport (relabelWord left right w) =
        (labelSupport w).image (relabelLabel left right)
  | .atom (.inl i) => by
      ext
      simp [labelSupport, relabelWord, relabelLabel]
  | .atom (.inr j) => by
      ext
      simp [labelSupport, relabelWord, relabelLabel]
  | .commutator u v => by
      simp [labelSupport, relabelWord, label_support_image left right u,
        label_support_image left right v, Finset.image_union]

lemma label_support_relabel
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ w : CWord (LabelledAtom M N),
      leftLabelSupport (relabelWord left right w) =
        (leftLabelSupport w).image left
  | .atom (.inl i) => by
      ext
      simp [leftLabelSupport, labelSupport, relabelWord, eq_comm]
  | .atom (.inr j) => by
      ext
      simp [leftLabelSupport, labelSupport, relabelWord]
  | .commutator u v => by
      simp only [leftLabelSupport, relabelWord, labelSupport,
        Finset.toLeft_union, Finset.image_union]
      change
        leftLabelSupport (relabelWord left right u) ∪
            leftLabelSupport (relabelWord left right v) =
          (leftLabelSupport u).image left ∪ (leftLabelSupport v).image left
      rw [label_support_relabel left right u,
        label_support_relabel left right v]

lemma label_relabel_image
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ w : CWord (LabelledAtom M N),
      rightLabelSupport (relabelWord left right w) =
        (rightLabelSupport w).image right
  | .atom (.inl i) => by
      ext
      simp [rightLabelSupport, labelSupport, relabelWord]
  | .atom (.inr j) => by
      ext
      simp [rightLabelSupport, labelSupport, relabelWord, eq_comm]
  | .commutator u v => by
      simp only [rightLabelSupport, relabelWord, labelSupport,
        Finset.toRight_union, Finset.image_union]
      change
        rightLabelSupport (relabelWord left right u) ∪
            rightLabelSupport (relabelWord left right v) =
          (rightLabelSupport u).image right ∪ (rightLabelSupport v).image right
      rw [label_relabel_image left right u,
        label_relabel_image left right v]

lemma relabel_label_inj
    {M N M' N' : ℕ}
    {w : CWord (LabelledAtom M N)}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (leftBack : Fin M' → Fin M)
    (rightBack : Fin N' → Fin N)
    (hleft :
      ∀ i ∈ leftLabelSupport w,
        leftBack (left i) = i)
    (hright :
      ∀ j ∈ rightLabelSupport w,
        rightBack (right j) = j) :
    Set.InjOn (relabelLabel left right) (labelSupport w : Set (LabelledAtom M N)) := by
  intro a ha b hb hab
  cases a with
  | inl i =>
      cases b with
      | inl i' =>
          simp only [relabelLabel, Sum.inl.injEq] at hab
          have hi : i ∈ leftLabelSupport w := by
            simpa [leftLabelSupport] using ha
          have hi' : i' ∈ leftLabelSupport w := by
            simpa [leftLabelSupport] using hb
          have : i = i' := by
            rw [← hleft i hi, ← hleft i' hi', hab]
          simp [this]
      | inr j =>
          simp [relabelLabel] at hab
  | inr j =>
      cases b with
      | inl i =>
          simp [relabelLabel] at hab
      | inr j' =>
          simp only [relabelLabel, Sum.inr.injEq] at hab
          have hj : j ∈ rightLabelSupport w := by
            simpa [rightLabelSupport] using ha
          have hj' : j' ∈ rightLabelSupport w := by
            simpa [rightLabelSupport] using hb
          have : j = j' := by
            rw [← hright j hj, ← hright j' hj', hab]
          simp [this]

lemma label_relabel_inj
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ {w : CWord (LabelledAtom M N)},
      LabelLinear w →
        Set.InjOn (relabelLabel left right) (labelSupport w : Set (LabelledAtom M N)) →
          LabelLinear (relabelWord left right w)
  | .atom (.inl _), _hw, _hinj => trivial
  | .atom (.inr _), _hw, _hinj => trivial
  | .commutator u v, hw, hinj => by
      rcases hw with ⟨hu, hv, hdisjoint⟩
      refine
        ⟨label_relabel_inj left right hu
            (hinj.mono (by intro z hz; simp [labelSupport, hz])),
          label_relabel_inj left right hv
            (hinj.mono (by intro z hz; simp [labelSupport, hz])),
          ?_⟩
      rw [label_support_image left right u,
        label_support_image left right v]
      rw [Finset.disjoint_left] at hdisjoint ⊢
      intro z hzu hzv
      rcases Finset.mem_image.mp hzu with ⟨u', hu', rfl⟩
      rcases Finset.mem_image.mp hzv with ⟨v', hv', huv⟩
      have huv' : u' = v' := by
        apply hinj
        · simp [labelSupport, hu']
        · simp [labelSupport, hv']
        · exact huv.symm
      subst v'
      exact hdisjoint hu' hv'

lemma relabel_inverse_support
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (leftBack : Fin M' → Fin M)
    (rightBack : Fin N' → Fin N) :
    ∀ w : CWord (LabelledAtom M N),
      (∀ i ∈ leftLabelSupport w, leftBack (left i) = i) →
        (∀ j ∈ rightLabelSupport w, rightBack (right j) = j) →
          relabelWord leftBack rightBack (relabelWord left right w) = w
  | .atom (.inl i), hleft, _hright => by
      simpa [relabelWord] using hleft i (by simp [leftLabelSupport, labelSupport])
  | .atom (.inr j), _hleft, hright => by
      simpa [relabelWord] using hright j (by simp [rightLabelSupport, labelSupport])
  | .commutator u v, hleft, hright => by
      change
        CWord.commutator
            (relabelWord leftBack rightBack (relabelWord left right u))
            (relabelWord leftBack rightBack (relabelWord left right v)) =
          CWord.commutator u v
      rw [relabel_inverse_support left right leftBack
          rightBack u
          (fun i hi => hleft i (by
            rw [leftLabelSupport, labelSupport, Finset.toLeft_union]
            exact Finset.mem_union_left _ hi))
          (fun j hj => hright j (by
            rw [rightLabelSupport, labelSupport, Finset.toRight_union]
            exact Finset.mem_union_left _ hj)),
        relabel_inverse_support left right leftBack
          rightBack v
          (fun i hi => hleft i (by
            rw [leftLabelSupport, labelSupport, Finset.toLeft_union]
            exact Finset.mem_union_right _ hi))
          (fun j hj => hright j (by
            rw [rightLabelSupport, labelSupport, Finset.toRight_union]
            exact Finset.mem_union_right _ hj))]

def relabelEmbedding
    {M N M' N' : ℕ}
    (left : Fin M ↪ Fin M')
    (right : Fin N ↪ Fin N') :
    LabelledAtom M N ↪ LabelledAtom M' N' :=
  Function.Embedding.sumMap left right

lemma label_relabel_word
    {M N M' N' : ℕ}
    (left : Fin M ↪ Fin M')
    (right : Fin N ↪ Fin N') :
    ∀ w : CWord (LabelledAtom M N),
      labelSupport (relabelWord left right w) =
        (labelSupport w).map (relabelEmbedding left right)
  | .atom (.inl i) => by
      ext
      simp [labelSupport, relabelWord, relabelEmbedding]
  | .atom (.inr j) => by
      ext
      simp [labelSupport, relabelWord, relabelEmbedding]
  | .commutator u v => by
      simp [labelSupport, relabelWord, label_relabel_word left right u,
        label_relabel_word left right v, Finset.map_union]

lemma left_label_relabel
    {M N M' N' : ℕ}
    (left : Fin M ↪ Fin M')
    (right : Fin N → Fin N') :
    ∀ w : CWord (LabelledAtom M N),
      leftLabelSupport (relabelWord left right w) =
        (leftLabelSupport w).map left
  | .atom (.inl i) => by
      ext
      simp [leftLabelSupport, labelSupport, relabelWord, eq_comm]
  | .atom (.inr j) => by
      ext
      simp [leftLabelSupport, labelSupport, relabelWord]
  | .commutator u v => by
      simp only [leftLabelSupport, relabelWord, labelSupport,
        Finset.toLeft_union, Finset.map_union]
      change
        leftLabelSupport (relabelWord left right u) ∪
            leftLabelSupport (relabelWord left right v) =
          (leftLabelSupport u).map left ∪ (leftLabelSupport v).map left
      rw [left_label_relabel left right u,
        left_label_relabel left right v]

lemma right_label_relabel
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N ↪ Fin N') :
    ∀ w : CWord (LabelledAtom M N),
      rightLabelSupport (relabelWord left right w) =
        (rightLabelSupport w).map right
  | .atom (.inl i) => by
      ext
      simp [rightLabelSupport, labelSupport, relabelWord]
  | .atom (.inr j) => by
      ext
      simp [rightLabelSupport, labelSupport, relabelWord, eq_comm]
  | .commutator u v => by
      simp only [rightLabelSupport, relabelWord, labelSupport,
        Finset.toRight_union, Finset.map_union]
      change
        rightLabelSupport (relabelWord left right u) ∪
            rightLabelSupport (relabelWord left right v) =
          (rightLabelSupport u).map right ∪ (rightLabelSupport v).map right
      rw [right_label_relabel left right u,
        right_label_relabel left right v]

lemma label_linear_relabel
    {M N M' N' : ℕ}
    (left : Fin M ↪ Fin M')
    (right : Fin N ↪ Fin N') :
    ∀ {w : CWord (LabelledAtom M N)},
      LabelLinear w →
        LabelLinear (relabelWord left right w)
  | .atom (.inl _), _ => trivial
  | .atom (.inr _), _ => trivial
  | .commutator u v, hw => by
      rcases hw with ⟨hu, hv, hdisjoint⟩
      refine ⟨label_linear_relabel left right hu,
        label_linear_relabel left right hv, ?_⟩
      rw [label_relabel_word left right u,
        label_relabel_word left right v]
      exact (Finset.disjoint_map (relabelEmbedding left right)).2 hdisjoint

/-- A source-label-linear erased Hall recipe with every placeholder used. -/
structure LRecipe where
  leftDegree :
    ℕ
  rightDegree :
    ℕ
  word :
    CWord (LabelledAtom leftDegree rightDegree)
  positive :
    (collapseWord word).PBPos
  linear :
    LabelLinear word
  left_support_full :
    leftLabelSupport word = Finset.univ
  right_support_full :
    rightLabelSupport word = Finset.univ

namespace LRecipe

/-- Erased Hall word carried by one linear recipe. -/
def erasedShape
    (R : LRecipe) :
    CWord HPAtom :=
  collapseWord R.word

/-- Instantiate one placeholder recipe in larger left and right label blocks. -/
def instantiate
    {M N : ℕ}
    (R : LRecipe)
    (left : Fin R.leftDegree → Fin M)
    (right : Fin R.rightDegree → Fin N) :
    CWord (LabelledAtom M N) :=
  relabelWord left right R.word

@[simp]
lemma collapseWord_instantiate
    {M N : ℕ}
    (R : LRecipe)
    (left : Fin R.leftDegree → Fin M)
    (right : Fin R.rightDegree → Fin N) :
    collapseWord (R.instantiate left right) = R.erasedShape := by
  simp [instantiate, erasedShape]

end LRecipe

@[simp]
lemma labelSupport_atom
    {M N : ℕ}
    (a : LabelledAtom M N) :
    labelSupport (.atom a) = {a} :=
  rfl

@[simp]
lemma labelSupport_commutator
    {M N : ℕ}
    (u v : CWord (LabelledAtom M N)) :
    labelSupport (.commutator u v) =
      labelSupport u ∪ labelSupport v :=
  rfl

lemma label_swap_word
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    labelSupport (rootSwapWord w) = labelSupport w := by
  cases w with
  | atom a =>
      rfl
  | commutator u v =>
      simp [rootSwapWord, labelSupport, Finset.union_comm]

lemma left_label_swap
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    leftLabelSupport (rootSwapWord w) = leftLabelSupport w := by
  simp [leftLabelSupport, label_swap_word]

lemma label_support_swap
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    rightLabelSupport (rootSwapWord w) = rightLabelSupport w := by
  simp [rightLabelSupport, label_swap_word]

lemma label_linear_swap
    {M N : ℕ}
    {w : CWord (LabelledAtom M N)}
    (hw : LabelLinear w) :
    LabelLinear (rootSwapWord w) := by
  cases w with
  | atom a =>
      trivial
  | commutator u v =>
      rcases hw with ⟨hu, hv, hdisjoint⟩
      exact ⟨hv, hu, by simpa [label_swap_word] using hdisjoint.symm⟩

lemma disjoint_left_label
    {M N : ℕ}
    {u v : CWord (LabelledAtom M N)}
    (hdisjoint : Disjoint (labelSupport u) (labelSupport v)) :
    Disjoint (leftLabelSupport u) (leftLabelSupport v) := by
  rw [Finset.disjoint_iff_inter_eq_empty, leftLabelSupport, leftLabelSupport,
    ← Finset.toLeft_inter, Finset.disjoint_iff_inter_eq_empty.mp hdisjoint]
  rfl

lemma disjoint_right_label
    {M N : ℕ}
    {u v : CWord (LabelledAtom M N)}
    (hdisjoint : Disjoint (labelSupport u) (labelSupport v)) :
    Disjoint (rightLabelSupport u) (rightLabelSupport v) := by
  rw [Finset.disjoint_iff_inter_eq_empty, rightLabelSupport, rightLabelSupport,
    ← Finset.toRight_inter, Finset.disjoint_iff_inter_eq_empty.mp hdisjoint]
  rfl

lemma label_pair_linear
    {M N : ℕ}
    {w : CWord (LabelledAtom M N)}
    (hw : LabelLinear w) :
    (leftLabelSupport w).card =
      (collapseWord w).pairLeftDegree := by
  induction w with
  | atom a =>
      cases a with
      | inl i =>
          change ({Sum.inl i} : Finset (LabelledAtom M N)).toLeft.card = 1
          rw [show ({Sum.inl i} : Finset (LabelledAtom M N)).toLeft = {i} by
            ext
            simp]
          simp
      | inr j =>
          change ({Sum.inr j} : Finset (LabelledAtom M N)).toLeft.card = 0
          rw [show ({Sum.inr j} : Finset (LabelledAtom M N)).toLeft = ∅ by
            ext
            simp]
          simp
  | commutator u v ihu ihv =>
      rcases hw with ⟨hu, hv, hdisjoint⟩
      rw [leftLabelSupport, labelSupport_commutator, Finset.toLeft_union]
      change
        (leftLabelSupport u ∪ leftLabelSupport v).card =
          (collapseWord (.commutator u v)).pairLeftDegree
      rw [Finset.card_union_of_disjoint
          (disjoint_left_label hdisjoint),
        ihu hu, ihv hv]
      rfl

lemma card_label_support
    {M N : ℕ}
    {w : CWord (LabelledAtom M N)}
    (hw : LabelLinear w) :
    (rightLabelSupport w).card =
      (collapseWord w).pairRightDegree := by
  induction w with
  | atom a =>
      cases a with
      | inl i =>
          change ({Sum.inl i} : Finset (LabelledAtom M N)).toRight.card = 0
          rw [show ({Sum.inl i} : Finset (LabelledAtom M N)).toRight = ∅ by
            ext
            simp]
          simp
      | inr j =>
          change ({Sum.inr j} : Finset (LabelledAtom M N)).toRight.card = 1
          rw [show ({Sum.inr j} : Finset (LabelledAtom M N)).toRight = {j} by
            ext
            simp]
          simp
  | commutator u v ihu ihv =>
      rcases hw with ⟨hu, hv, hdisjoint⟩
      rw [rightLabelSupport, labelSupport_commutator, Finset.toRight_union]
      change
        (rightLabelSupport u ∪ rightLabelSupport v).card =
          (collapseWord (.commutator u v)).pairRightDegree
      rw [Finset.card_union_of_disjoint
          (disjoint_right_label hdisjoint),
        ihu hu, ihv hv]
      rfl

lemma degree_label_linear
    {M N : ℕ}
    {w : CWord (LabelledAtom M N)}
    (hw : LabelLinear w) :
    (collapseWord w).pairLeftDegree ≤ M := by
  rw [← label_pair_linear hw]
  simpa using Finset.card_le_univ (leftLabelSupport w)

lemma pair_label_linear
    {M N : ℕ}
    {w : CWord (LabelledAtom M N)}
    (hw : LabelLinear w) :
    (collapseWord w).pairRightDegree ≤ N := by
  rw [← card_label_support hw]
  simpa using Finset.card_le_univ (rightLabelSupport w)

noncomputable def supportRank
    {M : ℕ}
    (support : Finset (Fin M))
    (hsupport : support.Nonempty) :
    Fin M → Fin support.card :=
  Function.extend Subtype.val (support.orderIsoOfFin rfl).symm
    fun _ => ⟨0, Finset.card_pos.mpr hsupport⟩

lemma emb_support_rank
    {M : ℕ}
    (support : Finset (Fin M))
    (hsupport : support.Nonempty)
    {i : Fin M}
    (hi : i ∈ support) :
    support.orderEmbOfFin rfl (supportRank support hsupport i) = i := by
  rw [supportRank, Function.extend_val_apply hi]
  change
    ↑(support.orderIsoOfFin rfl
        ((support.orderIsoOfFin rfl).symm ⟨i, hi⟩)) = i
  simp

lemma support_emb_fin
    {M : ℕ}
    (support : Finset (Fin M))
    (hsupport : support.Nonempty)
    (index : Fin support.card) :
    supportRank support hsupport (support.orderEmbOfFin rfl index) = index := by
  apply (support.orderEmbOfFin rfl).injective
  rw [emb_support_rank support hsupport
      (Finset.orderEmbOfFin_mem support rfl index)]

lemma image_support_univ
    {M : ℕ}
    (support : Finset (Fin M))
    (hsupport : support.Nonempty) :
    support.image (supportRank support hsupport) = Finset.univ := by
  ext index
  constructor
  · intro _hindex
    simp
  · intro _hindex
    let i : support := support.orderIsoOfFin rfl index
    refine Finset.mem_image.mpr ⟨i, i.property, ?_⟩
    rw [supportRank, Function.extend_val_apply i.property]
    change (support.orderIsoOfFin rfl).symm i = index
    exact (support.orderIsoOfFin rfl).symm_apply_apply index

lemma label_support_positive
    {M N : ℕ}
    {w : CWord (LabelledAtom M N)}
    (hlinear : LabelLinear w)
    (hpositive : (collapseWord w).PBPos) :
    (leftLabelSupport w).Nonempty := by
  apply Finset.card_pos.mp
  rw [label_pair_linear hlinear]
  exact hpositive.left

lemma label_nonempty_positive
    {M N : ℕ}
    {w : CWord (LabelledAtom M N)}
    (hlinear : LabelLinear w)
    (hpositive : (collapseWord w).PBPos) :
    (rightLabelSupport w).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_label_support hlinear]
  exact hpositive.right

lemma relabel_rank_inj
    {M N : ℕ}
    {w : CWord (LabelledAtom M N)}
    (hleft : (leftLabelSupport w).Nonempty)
    (hright : (rightLabelSupport w).Nonempty) :
    Set.InjOn
      (relabelLabel
        (supportRank (leftLabelSupport w) hleft)
        (supportRank (rightLabelSupport w) hright))
      (labelSupport w : Set (LabelledAtom M N)) := by
  apply relabel_label_inj
    (supportRank (leftLabelSupport w) hleft)
    (supportRank (rightLabelSupport w) hright)
    ((leftLabelSupport w).orderEmbOfFin rfl)
    ((rightLabelSupport w).orderEmbOfFin rfl)
  · intro i hi
    exact emb_support_rank (leftLabelSupport w) hleft hi
  · intro j hj
    exact emb_support_rank (rightLabelSupport w) hright hj

lemma fin_filter_sort
    {M : ℕ}
    (support : Finset (Fin M)) :
    (List.finRange M).filter (fun i => i ∈ support) = support.sort := by
  apply
    (((List.sortedLT_finRange M).pairwise.filter fun i => i ∈ support).sortedLT).eq_of_mem_iff
      support.sortedLT_sort
  intro i
  simp

lemma labelled_atoms_support
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    (labelledLeftAtoms M N).filter (fun a => a ∈ labelSupport w) =
      (leftLabelSupport w).sort.map fun i => (Sum.inl i : LabelledAtom M N) := by
  rw [labelledLeftAtoms, List.ofFn_eq_map, List.filter_map]
  simpa [List.ofFn_id,
    leftLabelSupport, Function.comp_def] using
    congrArg (List.map fun i : Fin M => (Sum.inl i : LabelledAtom M N))
      (fin_filter_sort (leftLabelSupport w))

lemma labelled_atoms_label
    {M N : ℕ}
    (w : CWord (LabelledAtom M N)) :
    (labelledRightAtoms M N).filter (fun a => a ∈ labelSupport w) =
      (rightLabelSupport w).sort.map fun j => (Sum.inr j : LabelledAtom M N) := by
  rw [labelledRightAtoms, List.ofFn_eq_map, List.filter_map]
  simpa [List.ofFn_id,
    rightLabelSupport, Function.comp_def] using
    congrArg (List.map fun j : Fin N => (Sum.inr j : LabelledAtom M N))
      (fin_filter_sort (rightLabelSupport w))

lemma relabel_label_labelled
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hleft : (leftLabelSupport w).Nonempty)
    (hright : (rightLabelSupport w).Nonempty) :
    ((labelledLeftAtoms M N).filter (fun a => a ∈ labelSupport w)).map
        (relabelLabel
          (supportRank (leftLabelSupport w) hleft)
          (supportRank (rightLabelSupport w) hright)) =
      labelledLeftAtoms (leftLabelSupport w).card (rightLabelSupport w).card := by
  rw [labelled_atoms_support]
  simp only [List.map_map, Function.comp_def, relabelLabel]
  rw [← Finset.listMap_orderEmbOfFin_finRange (leftLabelSupport w) rfl,
    List.map_map]
  simp [labelledLeftAtoms, List.ofFn_eq_map, Function.comp_def,
    support_emb_fin]

lemma relabel_label_atoms
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hleft : (leftLabelSupport w).Nonempty)
    (hright : (rightLabelSupport w).Nonempty) :
    ((labelledRightAtoms M N).filter (fun a => a ∈ labelSupport w)).map
        (relabelLabel
          (supportRank (leftLabelSupport w) hleft)
          (supportRank (rightLabelSupport w) hright)) =
      labelledRightAtoms (leftLabelSupport w).card (rightLabelSupport w).card := by
  rw [labelled_atoms_label]
  simp only [List.map_map, Function.comp_def, relabelLabel]
  rw [← Finset.listMap_orderEmbOfFin_finRange (rightLabelSupport w) rfl,
    List.map_map]
  simp [labelledRightAtoms, List.ofFn_eq_map, Function.comp_def,
    support_emb_fin]

namespace LRecipe

/-- Standardize one positive label-linear word to consecutive placeholder labels. -/
noncomputable def ofLabelLinear
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hpositive : (collapseWord w).PBPos)
    (hlinear : LabelLinear w) :
    LRecipe :=
  let leftSupport := leftLabelSupport w
  let rightSupport := rightLabelSupport w
  let hleft := label_support_positive hlinear hpositive
  let hright := label_nonempty_positive hlinear hpositive
  {
    leftDegree := leftSupport.card
    rightDegree := rightSupport.card
    word :=
      relabelWord (supportRank leftSupport hleft) (supportRank rightSupport hright) w
    positive := by
      simpa using hpositive
    linear := by
      exact
        label_relabel_inj
          (supportRank leftSupport hleft) (supportRank rightSupport hright)
          hlinear (relabel_rank_inj hleft hright)
    left_support_full := by
      rw [label_support_relabel]
      exact image_support_univ leftSupport hleft
    right_support_full := by
      rw [label_relabel_image]
      exact image_support_univ rightSupport hright
  }

end LRecipe

lemma choose_mul_submodule
    (M N r s : ℕ) :
    (Nat.choose M r : ℤ) * (Nat.choose N s : ℤ) ∈
      submodule M N r s := by
  have hright :
      (Nat.choose N s : ℤ) * 1 ∈ submodule M N 0 (s + 0) :=
    choose_submodule_right s
      (one_submodule_zero M N)
  have hleft :
      (Nat.choose M r : ℤ) * ((Nat.choose N s : ℤ) * 1) ∈
        submodule M N (r + 0) (s + 0) :=
    choose_submodule_left r hright
  simpa using hleft

/-- Repeating a full positive source block contributes coefficient one. -/
def fullPositiveBlocks
    (M q : ℕ) :
    List Block :=
  List.replicate q { sign := .positive, degree := M }

lemma degree_full_blocks
    (M q : ℕ) :
    degreeSum (fullPositiveBlocks M q) = q * M := by
  simp [fullPositiveBlocks, degreeSum, Nat.mul_comm]

lemma full_positive_blocks
    (M q : ℕ) :
    blockProduct M (fullPositiveBlocks M q) = 1 := by
  simp [fullPositiveBlocks, blockProduct, signedChoose]

/--
If the requested bidegree is built from whole positive source blocks on both
sides, coefficient one is already admissible.
-/
lemma submodule_dvd_degrees
    {M N r s : ℕ}
    (hMr : M ∣ r)
    (hNs : N ∣ s) :
    (1 : ℤ) ∈ submodule M N r s := by
  rcases hMr with ⟨q, rfl⟩
  rcases hNs with ⟨t, rfl⟩
  apply Submodule.subset_span
  refine ⟨fullPositiveBlocks M q, fullPositiveBlocks N t, ?_, ?_, ?_⟩
  · simpa [Nat.mul_comm] using degree_full_blocks M q
  · simpa [Nat.mul_comm] using degree_full_blocks N t
  · simp [full_positive_blocks]

/--
Package one signed Hall-Petresco recipe contribution as a certified bare
factor.  Positive `BRecipe.factor` below is the special case where every
source block has positive sign; the signed form is the one used by
inclusion-exclusion over overlapping history choices.
-/
def signedRecipeFactor
    (M N : ℕ)
    (word : CWord HPAtom)
    (coefficient : ℤ)
    (hpositive : word.PBPos)
    (left right : List Block)
    (hleft : degreeSum left = word.pairLeftDegree)
    (hright : degreeSum right = word.pairRightDegree)
    (hcoefficient :
      blockProduct M left * blockProduct N right = coefficient) :
    Factor M N where
  word := word
  coefficient := coefficient
  positive := hpositive
  coefficient_admissible := by
    apply Submodule.subset_span
    exact ⟨left, right, hleft, hright, hcoefficient⟩

lemma signed_recipe_eval
    {M N : ℕ}
    (word : CWord HPAtom)
    (coefficient : ℤ)
    (hpositive : word.PBPos)
    (left right : List Block)
    (hleft : degreeSum left = word.pairLeftDegree)
    (hright : degreeSum right = word.pairRightDegree)
    (hcoefficient :
      blockProduct M left * blockProduct N right = coefficient) :
    (signedRecipeFactor M N word coefficient hpositive left right hleft hright
        hcoefficient).eval universalLeft universalRight =
      word.eval (HPAtom.eval universalLeft universalRight) ^ coefficient :=
  rfl

/--
The first signed padding identity: selecting one source label and then
reusing it twice is the difference between the negative and positive
two-label block counts.  This is the local inclusion-exclusion step that
turns a diagonal history contribution into a total-degree-two admissible
coefficient.
-/
lemma choose_negative_positive
    (M : ℕ) :
    signedChoose .negative M 2 - signedChoose .positive M 2 =
      (M : ℤ) := by
  simp [signedChoose, Int.negOnePow_even 2 ⟨1, by simp⟩,
    Nat.choose_succ_succ' M 1]

/-- Reusing one selected left source label twice preserves provenance after
raising the left Hall degree by two. -/
lemma nat_submodule_two
    {M N r s : ℕ}
    {E : ℤ}
    (hE : E ∈ submodule M N r s) :
    (M : ℤ) * E ∈ submodule M N (2 + r) s := by
  have hnegative :=
    signed_submodule_left Sign.negative 2 hE
  have hpositive :=
    signed_submodule_left Sign.positive 2 hE
  have hsub := (submodule M N (2 + r) s).sub_mem hnegative hpositive
  simpa only [← sub_mul, choose_negative_positive] using hsub

/-- Reusing one selected right source label twice preserves provenance after
raising the right Hall degree by two. -/
lemma cast_submodule_two
    {M N r s : ℕ}
    {E : ℤ}
    (hE : E ∈ submodule M N r s) :
    (N : ℤ) * E ∈ submodule M N r (2 + s) := by
  have hnegative :=
    signed_choose_submodule Sign.negative 2 hE
  have hpositive :=
    signed_choose_submodule Sign.positive 2 hE
  have hsub := (submodule M N r (2 + s)).sub_mem hnegative hpositive
  simpa only [← sub_mul, choose_negative_positive] using hsub

/-- Evaluating the `k`th elementary symmetric polynomial on `M` copies of
one gives the ordinary binomial coefficient `choose M k`. -/
lemma aeval_esymm_choose
    (M k : ℕ) :
    MvPolynomial.aeval (fun _ : Fin M => (1 : ℤ))
        (MvPolynomial.esymm (Fin M) ℤ k) =
      (Nat.choose M k : ℤ) := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.esymm_map_val]
  simp [Finset.card_powersetCard]

/-- Evaluating every positive-degree power sum on `M` copies of one counts
the diagonal label choices: there are exactly `M` of them. -/
lemma aeval_psum_one
    (M k : ℕ) :
    MvPolynomial.aeval (fun _ : Fin M => (1 : ℤ))
        (MvPolynomial.psum (Fin M) ℤ k) =
      (M : ℤ) := by
  simp [MvPolynomial.psum]

/--
Newton's identity on `M` copies of one.  The right side is homogeneous of
total selected-label degree `k`, while the left side is the diagonal count
obtained by reusing one label `k` times.
-/
lemma newton_sum_choose
    (M k : ℕ)
    (hk : 0 < k) :
    (M : ℤ) =
      (-1 : ℤ) ^ (k + 1) * (k : ℤ) * (Nat.choose M k : ℤ) -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (-1 : ℤ) ^ a.1 * (Nat.choose M a.1 : ℤ) * (M : ℤ) := by
  have h := congrArg
      (MvPolynomial.aeval (fun _ : Fin M => (1 : ℤ)))
      (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin M) ℤ k hk)
  simpa only [map_sub, map_mul, map_pow, map_sum, map_neg, map_natCast,
    map_one, aeval_esymm_choose, aeval_psum_one] using h

/-- A single positive left source block gives a homogeneous degree-`k`
admissible coefficient. -/
lemma nat_choose_submodule
    (M N k : ℕ) :
    (Nat.choose M k : ℤ) ∈ submodule M N k 0 := by
  simpa using
    choose_submodule_left k (one_submodule_zero M N)

/-- A single positive right source block gives a homogeneous degree-`k`
admissible coefficient. -/
lemma cast_choose_submodule
    (M N k : ℕ) :
    (Nat.choose N k : ℤ) ∈ submodule M N 0 k := by
  simpa using
    choose_submodule_right k (one_submodule_zero M N)

/--
The diagonal left-label count remains admissible after recording any positive
total number of left Hall occurrences.  The induction is Newton's homogeneous
power-sum recurrence specialized at the all-ones alphabet.
-/
lemma nat_cast_submodule
    (M N : ℕ) :
    ∀ {k : ℕ}, 0 < k → (M : ℤ) ∈ submodule M N k 0 := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rw [newton_sum_choose M k hk]
      have hmain :
          (-1 : ℤ) ^ (k + 1) * (k : ℤ) * (Nat.choose M k : ℤ) ∈
            submodule M N k 0 := by
        simpa [smul_eq_mul, mul_assoc] using
          (submodule M N k 0).smul_mem
            ((-1 : ℤ) ^ (k + 1) * (k : ℤ))
            (nat_choose_submodule M N k)
      have hsum :
          (∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            (-1 : ℤ) ^ a.1 * (Nat.choose M a.1 : ℤ) * (M : ℤ)) ∈
            submodule M N k 0 := by
        apply Submodule.sum_mem
        intro a ha
        rw [Finset.mem_filter] at ha
        rcases ha with ⟨haanti, haIoo⟩
        have haeq : a.1 + a.2 = k := Finset.mem_antidiagonal.mp haanti
        change 0 < a.1 ∧ a.1 < k at haIoo
        rcases haIoo with ⟨_ha1pos, ha1lt⟩
        have ha2pos : 0 < a.2 := by omega
        have ha2lt : a.2 < k := by omega
        have hproduct :
            (Nat.choose M a.1 : ℤ) * (M : ℤ) ∈
              submodule M N (a.1 + a.2) (0 + 0) :=
          mul_mem_submodule
            (nat_choose_submodule M N a.1)
            (ih a.2 ha2lt ha2pos)
        have hproduct' :
            (Nat.choose M a.1 : ℤ) * (M : ℤ) ∈
              submodule M N k 0 := by
          simpa [haeq] using hproduct
        simpa [smul_eq_mul, mul_assoc] using
          (submodule M N k 0).smul_mem ((-1 : ℤ) ^ a.1) hproduct'
      exact (submodule M N k 0).sub_mem hmain hsum

/--
The diagonal right-label count remains admissible after recording any positive
total number of right Hall occurrences.
-/
lemma cast_submodule_degree
    (M N : ℕ) :
    ∀ {k : ℕ}, 0 < k → (N : ℤ) ∈ submodule M N 0 k := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rw [newton_sum_choose N k hk]
      have hmain :
          (-1 : ℤ) ^ (k + 1) * (k : ℤ) * (Nat.choose N k : ℤ) ∈
            submodule M N 0 k := by
        simpa [smul_eq_mul, mul_assoc] using
          (submodule M N 0 k).smul_mem
            ((-1 : ℤ) ^ (k + 1) * (k : ℤ))
            (cast_choose_submodule M N k)
      have hsum :
          (∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            (-1 : ℤ) ^ a.1 * (Nat.choose N a.1 : ℤ) * (N : ℤ)) ∈
            submodule M N 0 k := by
        apply Submodule.sum_mem
        intro a ha
        rw [Finset.mem_filter] at ha
        rcases ha with ⟨haanti, haIoo⟩
        have haeq : a.1 + a.2 = k := Finset.mem_antidiagonal.mp haanti
        change 0 < a.1 ∧ a.1 < k at haIoo
        rcases haIoo with ⟨_ha1pos, ha1lt⟩
        have ha2pos : 0 < a.2 := by omega
        have ha2lt : a.2 < k := by omega
        have hproduct :
            (Nat.choose N a.1 : ℤ) * (N : ℤ) ∈
              submodule M N (0 + 0) (a.1 + a.2) :=
          mul_mem_submodule
            (cast_choose_submodule M N a.1)
            (ih a.2 ha2lt ha2pos)
        have hproduct' :
            (Nat.choose N a.1 : ℤ) * (N : ℤ) ∈
              submodule M N 0 k := by
          simpa [haeq] using hproduct
        simpa [smul_eq_mul, mul_assoc] using
          (submodule M N 0 k).smul_mem ((-1 : ℤ) ^ a.1) hproduct'
      exact (submodule M N 0 k).sub_mem hmain hsum

/-- Reusing one left label through any positive number of new Hall leaves
preserves admissible provenance. -/
lemma cast_submodule_pos
    {M N r s k : ℕ}
    {E : ℤ}
    (hk : 0 < k)
    (hE : E ∈ submodule M N r s) :
    (M : ℤ) * E ∈ submodule M N (k + r) s := by
  simpa using
    mul_mem_submodule (nat_cast_submodule M N hk) hE

/-- Reusing one right label through any positive number of new Hall leaves
preserves admissible provenance. -/
lemma submodule_pos_degree
    {M N r s k : ℕ}
    {E : ℤ}
    (hk : 0 < k)
    (hE : E ∈ submodule M N r s) :
    (N : ℤ) * E ∈ submodule M N r (k + s) := by
  simpa using
    mul_mem_submodule (cast_submodule_degree M N hk) hE

/-- Product of the diagonal left-label counts for a list of equality-class
sizes.  Every class chooses one left label; its size records how many Hall
leaves reuse that label. -/
def diagonalLeftProduct
    (M : ℕ)
    (degrees : List ℕ) :
    ℤ :=
  (degrees.map fun _ => (M : ℤ)).prod

/-- Product of the diagonal right-label counts for a list of equality-class
sizes. -/
def diagonalRightProduct
    (N : ℕ)
    (degrees : List ℕ) :
    ℤ :=
  (degrees.map fun _ => (N : ℤ)).prod

/--
Independent diagonal left equality classes give a homogeneous admissible
coefficient whose total degree is the sum of the class sizes.
-/
lemma diagonal_left_submodule
    (M N : ℕ) :
    ∀ degrees : List ℕ,
      (∀ degree ∈ degrees, 0 < degree) →
        diagonalLeftProduct M degrees ∈
          submodule M N degrees.sum 0
  | [], _ => by
      simpa [diagonalLeftProduct] using one_submodule_zero M N
  | degree :: degrees, hpositive => by
      have hdegree : 0 < degree := hpositive degree (by simp)
      have htail :
          diagonalLeftProduct M degrees ∈
            submodule M N degrees.sum 0 :=
        diagonal_left_submodule M N degrees
          (fun entry hentry => hpositive entry (by simp [hentry]))
      have hproduct :=
        mul_mem_submodule
          (nat_cast_submodule M N hdegree)
          htail
      simpa [diagonalLeftProduct, List.sum_cons] using hproduct

/--
Independent diagonal right equality classes give a homogeneous admissible
coefficient whose total degree is the sum of the class sizes.
-/
lemma diagonal_right_submodule
    (M N : ℕ) :
    ∀ degrees : List ℕ,
      (∀ degree ∈ degrees, 0 < degree) →
        diagonalRightProduct N degrees ∈
          submodule M N 0 degrees.sum
  | [], _ => by
      simpa [diagonalRightProduct] using one_submodule_zero M N
  | degree :: degrees, hpositive => by
      have hdegree : 0 < degree := hpositive degree (by simp)
      have htail :
          diagonalRightProduct N degrees ∈
            submodule M N 0 degrees.sum :=
        diagonal_right_submodule M N degrees
          (fun entry hentry => hpositive entry (by simp [hentry]))
      have hproduct :=
        mul_mem_submodule
          (cast_submodule_degree M N hdegree)
          htail
      simpa [diagonalRightProduct, List.sum_cons] using hproduct

/--
Choosing independent diagonal equality classes on both Hall sides gives the
two-variable homogeneous coefficient used before distinctness exclusions are
applied.
-/
lemma diagonal_products_submodule
    (M N : ℕ)
    (leftDegrees rightDegrees : List ℕ)
    (hleft : ∀ degree ∈ leftDegrees, 0 < degree)
    (hright : ∀ degree ∈ rightDegrees, 0 < degree) :
    diagonalLeftProduct M leftDegrees *
        diagonalRightProduct N rightDegrees ∈
      submodule M N leftDegrees.sum rightDegrees.sum := by
  simpa using
    mul_mem_submodule
      (diagonal_left_submodule M N leftDegrees hleft)
      (diagonal_right_submodule M N rightDegrees hright)

namespace LRecipe

lemma erased_left_degree
    (R : LRecipe) :
    R.erasedShape.pairLeftDegree = R.leftDegree := by
  rw [erasedShape, ← label_pair_linear R.linear,
    R.left_support_full]
  simp

lemma erased_shape_degree
    (R : LRecipe) :
    R.erasedShape.pairRightDegree = R.rightDegree := by
  rw [erasedShape, ← card_label_support R.linear,
    R.right_support_full]
  simp

/-- Compress all order-preserving realizations of one linear recipe. -/
def factor
    (M N : ℕ)
    (R : LRecipe) :
    Factor M N where
  word := R.erasedShape
  coefficient :=
    (Nat.choose M R.leftDegree : ℤ) *
      (Nat.choose N R.rightDegree : ℤ)
  positive := R.positive
  coefficient_admissible := by
    rw [R.erased_left_degree, R.erased_shape_degree]
    exact choose_mul_submodule M N R.leftDegree R.rightDegree

lemma card_embedding_fin
    (M r : ℕ) :
    Fintype.card (Fin r ↪o Fin M) = Nat.choose M r := by
  rw [Fintype.card_congr (Set.powersetCard.ofFinEmbEquiv :
      (Fin r ↪o Fin M) ≃ Set.powersetCard (Fin M) r)]
  simpa using (Set.powersetCard.card (α := Fin M) (n := r))

lemma factor_coefficient_embeddings
    (M N : ℕ)
    (R : LRecipe) :
    (R.factor M N).coefficient =
      (Fintype.card (Fin R.leftDegree ↪o Fin M) : ℤ) *
        (Fintype.card (Fin R.rightDegree ↪o Fin N) : ℤ) := by
  simp [factor, card_embedding_fin]

/-- Order-preserving concrete labelled realizations of one recipe. -/
noncomputable def instantiations
    (M N : ℕ)
    (R : LRecipe) :
    List (CWord (LabelledAtom M N)) :=
  ((Finset.univ : Finset (Fin R.leftDegree ↪o Fin M)).toList).flatMap
    fun left =>
      ((Finset.univ : Finset (Fin R.rightDegree ↪o Fin N)).toList).map
        fun right => R.instantiate left right

lemma mem_instantiations_iff
    {M N : ℕ}
    (R : LRecipe)
    (w : CWord (LabelledAtom M N)) :
    w ∈ R.instantiations M N ↔
      ∃ left : Fin R.leftDegree ↪o Fin M,
        ∃ right : Fin R.rightDegree ↪o Fin N,
          w = R.instantiate left right := by
  simp [instantiations, eq_comm]

lemma instantiations_label_linear
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hpositive : (collapseWord w).PBPos)
    (hlinear : LabelLinear w) :
    w ∈ (LRecipe.ofLabelLinear w hpositive hlinear).instantiations M N := by
  let leftSupport := leftLabelSupport w
  let rightSupport := rightLabelSupport w
  let hleft := label_support_positive hlinear hpositive
  let hright := label_nonempty_positive hlinear hpositive
  rw [mem_instantiations_iff]
  refine
    ⟨leftSupport.orderEmbOfFin rfl, rightSupport.orderEmbOfFin rfl, ?_⟩
  change
    w =
      relabelWord (leftSupport.orderEmbOfFin rfl) (rightSupport.orderEmbOfFin rfl)
        (relabelWord (supportRank leftSupport hleft) (supportRank rightSupport hright) w)
  symm
  exact
    relabel_inverse_support
      (supportRank leftSupport hleft) (supportRank rightSupport hright)
      (leftSupport.orderEmbOfFin rfl) (rightSupport.orderEmbOfFin rfl) w
      (fun i hi => emb_support_rank leftSupport hleft hi)
      (fun j hj => emb_support_rank rightSupport hright hj)

lemma collapse_word_instantiations
    {M N : ℕ}
    (R : LRecipe)
    {w : CWord (LabelledAtom M N)}
    (hw : w ∈ R.instantiations M N) :
    collapseWord w = R.erasedShape := by
  rcases (R.mem_instantiations_iff w).mp hw with ⟨left, right, rfl⟩
  exact R.collapseWord_instantiate left right

lemma length_instantiations
    (M N : ℕ)
    (R : LRecipe) :
    (R.instantiations M N).length =
      Fintype.card (Fin R.leftDegree ↪o Fin M) *
        Fintype.card (Fin R.rightDegree ↪o Fin N) := by
  simp [instantiations, List.length_flatMap]

lemma collapsed_list_instantiations
    (M N : ℕ)
    (R : LRecipe) :
    collapsedListEval (R.instantiations M N) =
      R.erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        (Fintype.card (Fin R.leftDegree ↪o Fin M) *
          Fintype.card (Fin R.rightDegree ↪o Fin N)) := by
  rw [collapsedListEval]
  have hmap :
      List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          (R.instantiations M N) =
        List.replicate (R.instantiations M N).length
          (R.erasedShape.eval (HPAtom.eval universalLeft universalRight)) := by
    simpa using
      (List.eq_replicate_of_mem
        (a := R.erasedShape.eval (HPAtom.eval universalLeft universalRight))
        (l := List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          (R.instantiations M N))
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rw [R.collapse_word_instantiations hw]))
  rw [hmap, List.prod_replicate, R.length_instantiations]

lemma collapsed_instantiations_factor
    (M N : ℕ)
    (R : LRecipe) :
    collapsedListEval (R.instantiations M N) =
      (R.factor M N).eval universalLeft universalRight := by
  rw [R.collapsed_list_instantiations, Factor.eval]
  change
    R.erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        (Fintype.card (Fin R.leftDegree ↪o Fin M) *
          Fintype.card (Fin R.rightDegree ↪o Fin N)) =
      R.erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        (R.factor M N).coefficient
  rw [R.factor_coefficient_embeddings]
  rw [show
      (Fintype.card (Fin R.leftDegree ↪o Fin M) : ℤ) *
    (Fintype.card (Fin R.rightDegree ↪o Fin N) : ℤ) =
        ((Fintype.card (Fin R.leftDegree ↪o Fin M) *
          Fintype.card (Fin R.rightDegree ↪o Fin N) : ℕ) : ℤ) by norm_num,
    zpow_natCast]

lemma collapsed_eval_append
    {M N : ℕ}
    (L K : List (CWord (LabelledAtom M N))) :
    collapsedListEval (L ++ K) =
      collapsedListEval L * collapsedListEval K := by
  simp [collapsedListEval, List.prod_append]

/-- Concrete labelled realizations of a finite recipe list. -/
noncomputable def realizationList
    (M N : ℕ)
    (recipes : List LRecipe) :
    List (CWord (LabelledAtom M N)) :=
  recipes.flatMap fun R => R.instantiations M N

/-- Certified compressed factor list attached to a finite recipe list. -/
def factorList
    (M N : ℕ)
    (recipes : List LRecipe) :
    List (Factor M N) :=
  recipes.map fun R => R.factor M N

@[simp]
lemma realizationList_cons
    (M N : ℕ)
    (R : LRecipe)
    (recipes : List LRecipe) :
    realizationList M N (R :: recipes) =
      R.instantiations M N ++ realizationList M N recipes :=
  rfl

@[simp]
lemma factorList_cons
    (M N : ℕ)
    (R : LRecipe)
    (recipes : List LRecipe) :
    factorList M N (R :: recipes) =
      R.factor M N :: factorList M N recipes :=
  rfl

lemma collapsed_realization_factor
    (M N : ℕ) :
    ∀ recipes : List LRecipe,
      collapsedListEval (realizationList M N recipes) =
        listEval universalLeft universalRight (factorList M N recipes)
  | [] => by
      simp [realizationList, factorList, collapsedListEval, listEval]
  | R :: recipes => by
      rw [realizationList_cons, collapsed_eval_append,
        R.collapsed_instantiations_factor, factorList_cons,
        listEval_cons, collapsed_realization_factor M N recipes]

structure Expansion
    (M N : ℕ) where
  recipes :
    List LRecipe
  collapsed_eval_eq :
    collapsedListEval (realizationList M N recipes) =
      ⁅universalLeft ^ M, universalRight ^ N⁆

namespace Expansion

/-- Forget recipe realizations and retain their certified compressed factors. -/
def factors
    {M N : ℕ}
    (E : Expansion M N) :
    List (Factor M N) :=
  factorList M N E.recipes

lemma listEval_factors
    {M N : ℕ}
    (E : Expansion M N) :
    listEval universalLeft universalRight E.factors =
      ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  rw [factors, ← collapsed_realization_factor]
  exact E.collapsed_eval_eq

end Expansion

end LRecipe

/--
One family of abstract source labels selected independently from one input
block.  Different block labels may later instantiate to the same concrete
source label; that is exactly the multiplicative provenance needed for
collector corrections.
-/
abbrev BlockLabel
    (blocks : List ℕ) :=
  Σ index : Fin blocks.length, Fin (blocks.get index)

/-- Abstract left/right labels split into independent source blocks. -/
abbrev BlockRecipeAtom
    (leftBlocks rightBlocks : List ℕ) :=
  BlockLabel leftBlocks ⊕ BlockLabel rightBlocks

/-- Forget the independent block bookkeeping, remembering only Hall-pair side. -/
def collapseRecipeLabel
    {leftBlocks rightBlocks : List ℕ} :
    BlockRecipeAtom leftBlocks rightBlocks → HPAtom
  | .inl _ => .left
  | .inr _ => .right

/-- Collapse an independent-block recipe to its erased Hall-pair shape. -/
def collapseBlockRecipe
    {leftBlocks rightBlocks : List ℕ}
    (w : CWord (BlockRecipeAtom leftBlocks rightBlocks)) :
    CWord HPAtom :=
  w.bind fun a => .atom (collapseRecipeLabel a)

/-- Positive source blocks attached to a list of independent block degrees. -/
def positiveBlocks
    (degrees : List ℕ) :
    List Block :=
  degrees.map fun degree => { sign := .positive, degree := degree }

lemma sum_positive_blocks
    (degrees : List ℕ) :
    degreeSum (positiveBlocks degrees) = degrees.sum := by
  simp [positiveBlocks, degreeSum, Function.comp_def]

lemma block_product_blocks
    (M : ℕ)
    (degrees : List ℕ) :
    blockProduct M (positiveBlocks degrees) =
      (degrees.map fun degree => (Nat.choose M degree : ℤ)).prod := by
  simp [positiveBlocks, blockProduct, signedChoose, Function.comp_def]

/-- Source labels occurring in one formal commutator word over any alphabet. -/
def wordSupport
    {α : Type*}
    [DecidableEq α] :
    CWord α → Finset α
  | .atom a => {a}
  | .commutator u v => wordSupport u ∪ wordSupport v

/-- Every source label occurs at most once in a formal word over any alphabet. -/
def WordLinear
    {α : Type*}
    [DecidableEq α] :
    CWord α → Prop
  | .atom _ => True
  | .commutator u v =>
      WordLinear u ∧ WordLinear v ∧
        Disjoint (wordSupport u) (wordSupport v)

/-- Relabel a formal commutator word along one alphabet map. -/
def wordMap
    {α β : Type*}
    (f : α → β) :
    CWord α → CWord β
  | .atom a => .atom (f a)
  | .commutator u v => .commutator (wordMap f u) (wordMap f v)

lemma word_support
    {α β : Type*}
    [DecidableEq α]
    [DecidableEq β]
    (f : α ↪ β) :
    ∀ w : CWord α,
      wordSupport (wordMap f w) = (wordSupport w).map f
  | .atom a => by
      ext
      simp [wordSupport, wordMap]
  | .commutator u v => by
      simp [wordSupport, wordMap, word_support f u,
        word_support f v, Finset.map_union]

lemma word_linear
    {α β : Type*}
    [DecidableEq α]
    [DecidableEq β]
    (f : α ↪ β) :
    ∀ {w : CWord α},
      WordLinear w →
        WordLinear (wordMap f w)
  | .atom _, _ => trivial
  | .commutator u v, hw => by
      rcases hw with ⟨hu, hv, hdisjoint⟩
      refine ⟨word_linear f hu, word_linear f hv, ?_⟩
      rw [word_support f u, word_support f v]
      exact (Finset.disjoint_map f).2 hdisjoint

/-- Left independent-block labels occurring in one abstract recipe word. -/
def leftBlockLabel
    {leftBlocks rightBlocks : List ℕ}
    (w : CWord (BlockRecipeAtom leftBlocks rightBlocks)) :
    Finset (BlockLabel leftBlocks) :=
  (wordSupport w).toLeft

/-- Right independent-block labels occurring in one abstract recipe word. -/
def blockLabelSupport
    {leftBlocks rightBlocks : List ℕ}
    (w : CWord (BlockRecipeAtom leftBlocks rightBlocks)) :
    Finset (BlockLabel rightBlocks) :=
  (wordSupport w).toRight

lemma disjoint_block_label
    {leftBlocks rightBlocks : List ℕ}
    {u v : CWord (BlockRecipeAtom leftBlocks rightBlocks)}
    (hdisjoint : Disjoint (wordSupport u) (wordSupport v)) :
    Disjoint (leftBlockLabel u) (leftBlockLabel v) := by
  rw [Finset.disjoint_iff_inter_eq_empty, leftBlockLabel,
    leftBlockLabel, ← Finset.toLeft_inter,
    Finset.disjoint_iff_inter_eq_empty.mp hdisjoint]
  rfl

lemma disjoint_label_support
    {leftBlocks rightBlocks : List ℕ}
    {u v : CWord (BlockRecipeAtom leftBlocks rightBlocks)}
    (hdisjoint : Disjoint (wordSupport u) (wordSupport v)) :
    Disjoint (blockLabelSupport u) (blockLabelSupport v) := by
  rw [Finset.disjoint_iff_inter_eq_empty, blockLabelSupport,
    blockLabelSupport, ← Finset.toRight_inter,
    Finset.disjoint_iff_inter_eq_empty.mp hdisjoint]
  rfl

lemma card_label_linear
    {leftBlocks rightBlocks : List ℕ}
    {w : CWord (BlockRecipeAtom leftBlocks rightBlocks)}
    (hw : WordLinear w) :
    (leftBlockLabel w).card =
      (collapseBlockRecipe w).pairLeftDegree := by
  induction w with
  | atom a =>
      cases a with
      | inl index =>
          change ({Sum.inl index} : Finset
            (BlockRecipeAtom leftBlocks rightBlocks)).toLeft.card = 1
          rw [show ({Sum.inl index} : Finset
              (BlockRecipeAtom leftBlocks rightBlocks)).toLeft = {index} by
            ext
            simp]
          simp
      | inr index =>
          change ({Sum.inr index} : Finset
            (BlockRecipeAtom leftBlocks rightBlocks)).toLeft.card = 0
          rw [show ({Sum.inr index} : Finset
              (BlockRecipeAtom leftBlocks rightBlocks)).toLeft = ∅ by
            ext
            simp]
          simp
  | commutator u v ihu ihv =>
      rcases hw with ⟨hu, hv, hdisjoint⟩
      rw [leftBlockLabel, wordSupport, Finset.toLeft_union]
      change
        (leftBlockLabel u ∪ leftBlockLabel v).card =
          (collapseBlockRecipe (.commutator u v)).pairLeftDegree
      rw [Finset.card_union_of_disjoint
          (disjoint_block_label hdisjoint),
        ihu hu, ihv hv]
      rfl

lemma label_support_linear
    {leftBlocks rightBlocks : List ℕ}
    {w : CWord (BlockRecipeAtom leftBlocks rightBlocks)}
    (hw : WordLinear w) :
    (blockLabelSupport w).card =
      (collapseBlockRecipe w).pairRightDegree := by
  induction w with
  | atom a =>
      cases a with
      | inl index =>
          change ({Sum.inl index} : Finset
            (BlockRecipeAtom leftBlocks rightBlocks)).toRight.card = 0
          rw [show ({Sum.inl index} : Finset
              (BlockRecipeAtom leftBlocks rightBlocks)).toRight = ∅ by
            ext
            simp]
          simp
      | inr index =>
          change ({Sum.inr index} : Finset
            (BlockRecipeAtom leftBlocks rightBlocks)).toRight.card = 1
          rw [show ({Sum.inr index} : Finset
              (BlockRecipeAtom leftBlocks rightBlocks)).toRight = {index} by
            ext
            simp]
          simp
  | commutator u v ihu ihv =>
      rcases hw with ⟨hu, hv, hdisjoint⟩
      rw [blockLabelSupport, wordSupport, Finset.toRight_union]
      change
        (blockLabelSupport u ∪ blockLabelSupport v).card =
          (collapseBlockRecipe (.commutator u v)).pairRightDegree
      rw [Finset.card_union_of_disjoint
          (disjoint_label_support hdisjoint),
        ihu hu, ihv hv]
      rfl

/--
An erased Hall recipe whose abstract labels are split into independent
positive source blocks.  This strictly generalizes `LRecipe`: one block
on each side recovers the globally source-label-linear case, while correction
histories append independent blocks.
-/
structure BRecipe where
  leftBlocks :
    List ℕ
  rightBlocks :
    List ℕ
  word :
    CWord (BlockRecipeAtom leftBlocks rightBlocks)
  positive :
    (collapseBlockRecipe word).PBPos
  left_degree_eq :
    (collapseBlockRecipe word).pairLeftDegree = leftBlocks.sum
  right_degree_eq :
    (collapseBlockRecipe word).pairRightDegree = rightBlocks.sum

namespace BRecipe

/-- Erased Hall word carried by one independent-block recipe. -/
def erasedShape
    (R : BRecipe) :
    CWord HPAtom :=
  collapseBlockRecipe R.word

/-- Total left source degree selected by one independent-block recipe. -/
def leftDegree
    (R : BRecipe) :
    ℕ :=
  R.leftBlocks.sum

/-- Total right source degree selected by one independent-block recipe. -/
def rightDegree
    (R : BRecipe) :
    ℕ :=
  R.rightBlocks.sum

/-- Include labels from the left summand of an appended block list. -/
def labelLeftEmbedding
    (left right : List ℕ) :
    BlockLabel left ↪ BlockLabel (left ++ right) where
  toFun
    | ⟨block, index⟩ =>
        ⟨Fin.cast (by simp) (Fin.castAdd right.length block),
          by simpa using index⟩
  inj'
    | ⟨block, index⟩, ⟨block', index'⟩, h => by
        simpa using h

/-- Include labels from the right summand of an appended block list. -/
def blockLabelEmbedding
    (left right : List ℕ) :
    BlockLabel right ↪ BlockLabel (left ++ right) where
  toFun
    | ⟨block, index⟩ =>
        ⟨Fin.cast (by simp) (Fin.natAdd left.length block),
          by simpa using index⟩
  inj'
    | ⟨block, index⟩, ⟨block', index'⟩, h => by
        simpa using h

/-- Include all labels of the left recipe inside appended source blocks. -/
def atomLeftEmbedding
    (B A : BRecipe) :
    BlockRecipeAtom B.leftBlocks B.rightBlocks ↪
      BlockRecipeAtom (B.leftBlocks ++ A.leftBlocks)
        (B.rightBlocks ++ A.rightBlocks) :=
  Function.Embedding.sumMap
    (labelLeftEmbedding B.leftBlocks A.leftBlocks)
    (labelLeftEmbedding B.rightBlocks A.rightBlocks)

/-- Include all labels of the right recipe inside appended source blocks. -/
def appendAtomEmbedding
    (B A : BRecipe) :
    BlockRecipeAtom A.leftBlocks A.rightBlocks ↪
      BlockRecipeAtom (B.leftBlocks ++ A.leftBlocks)
        (B.rightBlocks ++ A.rightBlocks) :=
  Function.Embedding.sumMap
    (blockLabelEmbedding B.leftBlocks A.leftBlocks)
    (blockLabelEmbedding B.rightBlocks A.rightBlocks)

lemma collapse_label_embedding
    (B A : BRecipe)
    (atom : BlockRecipeAtom B.leftBlocks B.rightBlocks) :
    collapseRecipeLabel (B.atomLeftEmbedding A atom) =
      collapseRecipeLabel atom := by
  cases atom <;> rfl

lemma collapse_label_atom
    (B A : BRecipe)
    (atom : BlockRecipeAtom A.leftBlocks A.rightBlocks) :
    collapseRecipeLabel (B.appendAtomEmbedding A atom) =
      collapseRecipeLabel atom := by
  cases atom <;> rfl

lemma collapse_append_atom
    (B A : BRecipe) :
    ∀ w : CWord (BlockRecipeAtom B.leftBlocks B.rightBlocks),
      collapseBlockRecipe (wordMap (B.atomLeftEmbedding A) w) =
        collapseBlockRecipe w
  | .atom atom => by
      cases atom <;> rfl
  | .commutator u v => by
      change
        CWord.commutator
            (collapseBlockRecipe (wordMap (B.atomLeftEmbedding A) u))
            (collapseBlockRecipe (wordMap (B.atomLeftEmbedding A) v)) =
          CWord.commutator (collapseBlockRecipe u)
            (collapseBlockRecipe v)
      rw [collapse_append_atom B A u,
        collapse_append_atom B A v]

lemma collapse_block_atom
    (B A : BRecipe) :
    collapseBlockRecipe (wordMap (B.atomLeftEmbedding A) B.word) =
      B.erasedShape := by
  exact B.collapse_append_atom A B.word

lemma collapse_atom_embedding
    (B A : BRecipe) :
    ∀ w : CWord (BlockRecipeAtom A.leftBlocks A.rightBlocks),
      collapseBlockRecipe (wordMap (B.appendAtomEmbedding A) w) =
        collapseBlockRecipe w
  | .atom atom => by
      cases atom <;> rfl
  | .commutator u v => by
      change
        CWord.commutator
            (collapseBlockRecipe (wordMap (B.appendAtomEmbedding A) u))
            (collapseBlockRecipe (wordMap (B.appendAtomEmbedding A) v)) =
          CWord.commutator (collapseBlockRecipe u)
            (collapseBlockRecipe v)
      rw [collapse_atom_embedding B A u,
        collapse_atom_embedding B A v]

lemma collapse_append_embedding
    (B A : BRecipe) :
    collapseBlockRecipe (wordMap (B.appendAtomEmbedding A) A.word) =
      A.erasedShape := by
  exact B.collapse_atom_embedding A A.word

/-- The unique block label carrying one one-block source position. -/
def singletonLabelEmbedding
    (degree : ℕ) :
    Fin degree ↪ BlockLabel [degree] where
  toFun index := ⟨⟨0, by simp⟩, by simpa using index⟩
  inj' index index' h := by
    cases h
    rfl

/-- Regard one globally linear recipe as a one-block independent recipe. -/
def singletonAtomEmbedding
    (leftDegree rightDegree : ℕ) :
    LabelledAtom leftDegree rightDegree ↪
      BlockRecipeAtom [leftDegree] [rightDegree] :=
  Function.Embedding.sumMap
    (singletonLabelEmbedding leftDegree)
    (singletonLabelEmbedding rightDegree)

lemma collapse_label_singleton
    (leftDegree rightDegree : ℕ)
    (atom : LabelledAtom leftDegree rightDegree) :
    collapseRecipeLabel (singletonAtomEmbedding leftDegree rightDegree atom) =
      collapseLabel atom := by
  cases atom <;> rfl

lemma collapse_singleton_atom
    (leftDegree rightDegree : ℕ) :
    ∀ w : CWord (LabelledAtom leftDegree rightDegree),
      collapseBlockRecipe
          (wordMap (singletonAtomEmbedding leftDegree rightDegree) w) =
        collapseWord w
  | .atom atom => by
      cases atom <;> rfl
  | .commutator u v => by
      change
        CWord.commutator
            (collapseBlockRecipe
              (wordMap (singletonAtomEmbedding leftDegree rightDegree) u))
            (collapseBlockRecipe
              (wordMap (singletonAtomEmbedding leftDegree rightDegree) v)) =
          CWord.commutator (collapseWord u) (collapseWord v)
      rw [collapse_singleton_atom leftDegree rightDegree u,
        collapse_singleton_atom leftDegree rightDegree v]

/-- One-block inclusion of the previously certified globally linear recipes. -/
def ofLinear
    (R : LRecipe) :
    BRecipe where
  leftBlocks := [R.leftDegree]
  rightBlocks := [R.rightDegree]
  word := wordMap (singletonAtomEmbedding R.leftDegree R.rightDegree) R.word
  positive := by
    rw [collapse_singleton_atom]
    exact R.positive
  left_degree_eq := by
    rw [collapse_singleton_atom]
    change R.erasedShape.pairLeftDegree = [R.leftDegree].sum
    rw [LRecipe.erased_left_degree]
    simp
  right_degree_eq := by
    rw [collapse_singleton_atom]
    change R.erasedShape.pairRightDegree = [R.rightDegree].sum
    rw [LRecipe.erased_shape_degree]
    simp

lemma erased_shape_linear
    (R : LRecipe) :
    (ofLinear R).erasedShape = R.erasedShape := by
  rw [erasedShape, ofLinear,
    collapse_singleton_atom]
  rfl

/-- The independent-block correction recipe produced by interchanging two families. -/
def correction
    (B A : BRecipe) :
    BRecipe where
  leftBlocks := B.leftBlocks ++ A.leftBlocks
  rightBlocks := B.rightBlocks ++ A.rightBlocks
  word :=
    .commutator
      (wordMap (B.atomLeftEmbedding A) B.word)
      (wordMap (B.appendAtomEmbedding A) A.word)
  positive := by
    change
      (CWord.commutator
          (collapseBlockRecipe
            (wordMap (B.atomLeftEmbedding A) B.word))
          (collapseBlockRecipe
            (wordMap (B.appendAtomEmbedding A) A.word))).PBPos
    rw [
      B.collapse_block_atom A,
      B.collapse_append_embedding A]
    have hB : B.erasedShape.PBPos := B.positive
    have hA : A.erasedShape.PBPos := A.positive
    simp only [CWord.PBPos,
      CWord.pair_left_commutator,
      CWord.pair_degree_commutator] at hB hA ⊢
    omega
  left_degree_eq := by
    change
      (CWord.commutator
          (collapseBlockRecipe
            (wordMap (B.atomLeftEmbedding A) B.word))
          (collapseBlockRecipe
            (wordMap (B.appendAtomEmbedding A) A.word))).pairLeftDegree =
        (B.leftBlocks ++ A.leftBlocks).sum
    rw [
      B.collapse_block_atom A,
      B.collapse_append_embedding A,
      CWord.pair_left_commutator]
    simpa [erasedShape, List.sum_append] using
      congrArg₂ Nat.add B.left_degree_eq A.left_degree_eq
  right_degree_eq := by
    change
      (CWord.commutator
          (collapseBlockRecipe
            (wordMap (B.atomLeftEmbedding A) B.word))
          (collapseBlockRecipe
            (wordMap (B.appendAtomEmbedding A) A.word))).pairRightDegree =
        (B.rightBlocks ++ A.rightBlocks).sum
    rw [
      B.collapse_block_atom A,
      B.collapse_append_embedding A,
      CWord.pair_degree_commutator]
    simpa [erasedShape, List.sum_append] using
      congrArg₂ Nat.add B.right_degree_eq A.right_degree_eq

@[simp]
lemma erasedShape_corr
    (B A : BRecipe) :
    (B.correction A).erasedShape =
      .commutator B.erasedShape A.erasedShape := by
  change
    CWord.commutator
        (collapseBlockRecipe
          (wordMap (B.atomLeftEmbedding A) B.word))
        (collapseBlockRecipe
          (wordMap (B.appendAtomEmbedding A) A.word)) =
      CWord.commutator B.erasedShape A.erasedShape
  rw [
    B.collapse_block_atom A,
    B.collapse_append_embedding A]

lemma collapse_block_swap
    {leftBlocks rightBlocks : List ℕ}
    (w : CWord (BlockRecipeAtom leftBlocks rightBlocks)) :
    collapseBlockRecipe (rootSwapWord w) =
      rootSwapWord (collapseBlockRecipe w) := by
  cases w <;> rfl

/-- Swap the root commutator of one independent-block recipe. -/
def rootSwap
    (R : BRecipe) :
    BRecipe where
  leftBlocks := R.leftBlocks
  rightBlocks := R.rightBlocks
  word := rootSwapWord R.word
  positive := by
    rw [collapse_block_swap]
    exact rootSwap_positive R.positive
  left_degree_eq := by
    rw [collapse_block_swap,
      root_swap_positive R.positive]
    exact R.left_degree_eq
  right_degree_eq := by
    rw [collapse_block_swap,
      pair_swap_positive R.positive]
    exact R.right_degree_eq

@[simp]
lemma erased_shape_swap
    (R : BRecipe) :
    R.rootSwap.erasedShape = rootSwapWord R.erasedShape := by
  exact collapse_block_swap R.word

/-- The inverse-oriented correction recipe `[A^-1, B]`. -/
def inverseCorrection
    (B A : BRecipe) :
    BRecipe :=
  A.rootSwap.correction B

@[simp]
lemma erased_shape_correction
    (B A : BRecipe) :
    (B.inverseCorrection A).erasedShape =
      .commutator (rootSwapWord A.erasedShape) B.erasedShape := by
  simp [inverseCorrection]

lemma erased_left_degree
    (R : BRecipe) :
    R.erasedShape.pairLeftDegree = R.leftDegree := by
  exact R.left_degree_eq

lemma erased_shape_degree
    (R : BRecipe) :
    R.erasedShape.pairRightDegree = R.rightDegree := by
  exact R.right_degree_eq

/-- Compress one independent positive-block recipe into a certified factor. -/
def factor
    (M N : ℕ)
    (R : BRecipe) :
    Factor M N where
  word := R.erasedShape
  coefficient :=
    (R.leftBlocks.map fun degree => (Nat.choose M degree : ℤ)).prod *
      (R.rightBlocks.map fun degree => (Nat.choose N degree : ℤ)).prod
  positive := R.positive
  coefficient_admissible := by
    rw [R.erased_left_degree, R.erased_shape_degree]
    apply Submodule.subset_span
    refine ⟨positiveBlocks R.leftBlocks, positiveBlocks R.rightBlocks, ?_, ?_, ?_⟩
    · exact sum_positive_blocks R.leftBlocks
    · exact sum_positive_blocks R.rightBlocks
    · simp [block_product_blocks]

lemma factor_coefficient_correction
    (M N : ℕ)
    (B A : BRecipe) :
    ((B.correction A).factor M N).coefficient =
      (B.factor M N).coefficient * (A.factor M N).coefficient := by
  simp [factor, correction, List.map_append, List.prod_append]
  ring

lemma factor_coefficient_swap
    (M N : ℕ)
    (R : BRecipe) :
    (R.rootSwap.factor M N).coefficient = (R.factor M N).coefficient := by
  rfl

lemma factor_swap_inv
    (M N : ℕ)
    (R : BRecipe) :
    (R.rootSwap.factor M N).eval universalLeft universalRight =
      ((R.factor M N).eval universalLeft universalRight)⁻¹ := by
  simp only [Factor.eval, factor]
  have hroot :
      (rootSwapWord R.erasedShape).eval
          (HPAtom.eval universalLeft universalRight) =
        (R.erasedShape.eval (HPAtom.eval universalLeft universalRight))⁻¹ :=
    swap_bidegree_positive
      (HPAtom.eval universalLeft universalRight) R.positive
  rw [erased_shape_swap, hroot]
  simp [rootSwap]

lemma factor_linear_eval
    (M N : ℕ)
    (R : LRecipe) :
    ((ofLinear R).factor M N).eval universalLeft universalRight =
      (R.factor M N).eval universalLeft universalRight := by
  change
    (ofLinear R).erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        (((ofLinear R).leftBlocks.map fun degree => (Nat.choose M degree : ℤ)).prod *
          ((ofLinear R).rightBlocks.map fun degree => (Nat.choose N degree : ℤ)).prod) =
      R.erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        ((Nat.choose M R.leftDegree : ℤ) * (Nat.choose N R.rightDegree : ℤ))
  rw [erased_shape_linear]
  simp [ofLinear]

/-- Order-preserving realizations chosen independently for every source block. -/
abbrev OrderEmbeddings
    (blocks : List ℕ)
    (M : ℕ) :=
  ∀ index : Fin blocks.length, Fin (blocks.get index) ↪o Fin M

/-- Instantiate one independent abstract source-block label. -/
def instantiateLabel
    {M N : ℕ}
    {leftBlocks rightBlocks : List ℕ}
    (left : OrderEmbeddings leftBlocks M)
    (right : OrderEmbeddings rightBlocks N) :
    BlockRecipeAtom leftBlocks rightBlocks → LabelledAtom M N
  | .inl ⟨block, index⟩ => .inl (left block index)
  | .inr ⟨block, index⟩ => .inr (right block index)

/-- Instantiate one independent-block recipe in concrete left and right blocks. -/
def instantiate
    {M N : ℕ}
    (R : BRecipe)
    (left : OrderEmbeddings R.leftBlocks M)
    (right : OrderEmbeddings R.rightBlocks N) :
    CWord (LabelledAtom M N) :=
  R.word.bind fun a => .atom (instantiateLabel left right a)

lemma collapseWord_instantiate
    {M N : ℕ}
    (R : BRecipe)
    (left : OrderEmbeddings R.leftBlocks M)
    (right : OrderEmbeddings R.rightBlocks N) :
    collapseWord (R.instantiate left right) = R.erasedShape := by
  change
    collapseWord
        (R.word.bind fun a => .atom (instantiateLabel left right a)) =
      collapseBlockRecipe R.word
  induction R.word with
  | atom a =>
      cases a <;> rfl
  | commutator u v ihu ihv =>
      change
        CWord.commutator
            (collapseWord
              (u.bind fun a => .atom (instantiateLabel left right a)))
            (collapseWord
              (v.bind fun a => .atom (instantiateLabel left right a))) =
          CWord.commutator (collapseBlockRecipe u)
            (collapseBlockRecipe v)
      rw [ihu, ihv]

lemma card_orderEmbeddings
    (blocks : List ℕ)
    (M : ℕ) :
    Fintype.card (OrderEmbeddings blocks M) =
      (blocks.map fun degree => Nat.choose M degree).prod := by
  simp [OrderEmbeddings, LRecipe.card_embedding_fin]

lemma factor_coefficient_embeddings
    (M N : ℕ)
    (R : BRecipe) :
    (R.factor M N).coefficient =
      (Fintype.card (OrderEmbeddings R.leftBlocks M) : ℤ) *
        (Fintype.card (OrderEmbeddings R.rightBlocks N) : ℤ) := by
  change
    (R.leftBlocks.map fun degree => (Nat.choose M degree : ℤ)).prod *
        (R.rightBlocks.map fun degree => (Nat.choose N degree : ℤ)).prod =
      (Fintype.card (OrderEmbeddings R.leftBlocks M) : ℤ) *
        (Fintype.card (OrderEmbeddings R.rightBlocks N) : ℤ)
  rw [card_orderEmbeddings, card_orderEmbeddings]
  norm_num [Function.comp_def]

/-- Concrete labelled realizations of one independent-block recipe. -/
noncomputable def instantiations
    (M N : ℕ)
    (R : BRecipe) :
    List (CWord (LabelledAtom M N)) :=
  ((Finset.univ : Finset (OrderEmbeddings R.leftBlocks M)).toList).flatMap
    fun left =>
      ((Finset.univ : Finset (OrderEmbeddings R.rightBlocks N)).toList).map
        fun right => R.instantiate left right

lemma mem_instantiations_iff
    {M N : ℕ}
    (R : BRecipe)
    (w : CWord (LabelledAtom M N)) :
    w ∈ R.instantiations M N ↔
      ∃ left : OrderEmbeddings R.leftBlocks M,
        ∃ right : OrderEmbeddings R.rightBlocks N,
          w = R.instantiate left right := by
  simp [instantiations, eq_comm]

lemma collapse_word_instantiations
    {M N : ℕ}
    (R : BRecipe)
    {w : CWord (LabelledAtom M N)}
    (hw : w ∈ R.instantiations M N) :
    collapseWord w = R.erasedShape := by
  rcases (R.mem_instantiations_iff w).mp hw with ⟨left, right, rfl⟩
  exact R.collapseWord_instantiate left right

lemma length_instantiations
    (M N : ℕ)
    (R : BRecipe) :
    (R.instantiations M N).length =
      Fintype.card (OrderEmbeddings R.leftBlocks M) *
        Fintype.card (OrderEmbeddings R.rightBlocks N) := by
  simp [instantiations, List.length_flatMap]

lemma collapsed_list_instantiations
    (M N : ℕ)
    (R : BRecipe) :
    collapsedListEval (R.instantiations M N) =
      R.erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        (Fintype.card (OrderEmbeddings R.leftBlocks M) *
          Fintype.card (OrderEmbeddings R.rightBlocks N)) := by
  rw [collapsedListEval]
  have hmap :
      List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          (R.instantiations M N) =
        List.replicate (R.instantiations M N).length
          (R.erasedShape.eval (HPAtom.eval universalLeft universalRight)) := by
    simpa using
      (List.eq_replicate_of_mem
        (a := R.erasedShape.eval (HPAtom.eval universalLeft universalRight))
        (l := List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          (R.instantiations M N))
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rw [R.collapse_word_instantiations hw]))
  rw [hmap, List.prod_replicate, R.length_instantiations]

lemma collapsed_instantiations_factor
    (M N : ℕ)
    (R : BRecipe) :
    collapsedListEval (R.instantiations M N) =
      (R.factor M N).eval universalLeft universalRight := by
  rw [R.collapsed_list_instantiations, Factor.eval]
  change
    R.erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        (Fintype.card (OrderEmbeddings R.leftBlocks M) *
          Fintype.card (OrderEmbeddings R.rightBlocks N)) =
      R.erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        (R.factor M N).coefficient
  rw [R.factor_coefficient_embeddings]
  rw [show
      (Fintype.card (OrderEmbeddings R.leftBlocks M) : ℤ) *
      (Fintype.card (OrderEmbeddings R.rightBlocks N) : ℤ) =
        ((Fintype.card (OrderEmbeddings R.leftBlocks M) *
          Fintype.card (OrderEmbeddings R.rightBlocks N) : ℕ) : ℤ) by norm_num,
    zpow_natCast]

/-- Concrete labelled realizations of a finite independent-block recipe list. -/
noncomputable def realizationList
    (M N : ℕ)
    (recipes : List BRecipe) :
    List (CWord (LabelledAtom M N)) :=
  recipes.flatMap fun R => R.instantiations M N

/-- Certified compressed factor list attached to independent-block recipes. -/
def factorList
    (M N : ℕ)
    (recipes : List BRecipe) :
    List (Factor M N) :=
  recipes.map fun R => R.factor M N

@[simp]
lemma realizationList_cons
    (M N : ℕ)
    (R : BRecipe)
    (recipes : List BRecipe) :
    realizationList M N (R :: recipes) =
      R.instantiations M N ++ realizationList M N recipes :=
  rfl

@[simp]
lemma factorList_cons
    (M N : ℕ)
    (R : BRecipe)
    (recipes : List BRecipe) :
    factorList M N (R :: recipes) =
      R.factor M N :: factorList M N recipes :=
  rfl

lemma collapsed_eval_append
    {M N : ℕ}
    (L K : List (CWord (LabelledAtom M N))) :
    collapsedListEval (L ++ K) =
      collapsedListEval L * collapsedListEval K := by
  simp [collapsedListEval, List.prod_append]

lemma collapsed_realization_factor
    (M N : ℕ) :
    ∀ recipes : List BRecipe,
      collapsedListEval (realizationList M N recipes) =
        listEval universalLeft universalRight (factorList M N recipes)
  | [] => by
      simp [realizationList, factorList, collapsedListEval, listEval]
  | R :: recipes => by
      rw [realizationList_cons, collapsed_eval_append,
        R.collapsed_instantiations_factor, factorList_cons,
        listEval_cons, collapsed_realization_factor M N recipes]

structure Expansion
    (M N : ℕ) where
  recipes :
    List BRecipe
  collapsed_eval_eq :
    collapsedListEval (realizationList M N recipes) =
      ⁅universalLeft ^ M, universalRight ^ N⁆

namespace Expansion

/-- Forget recipe realizations and retain their certified compressed factors. -/
def factors
    {M N : ℕ}
    (E : Expansion M N) :
    List (Factor M N) :=
  factorList M N E.recipes

lemma listEval_factors
    {M N : ℕ}
    (E : Expansion M N) :
    listEval universalLeft universalRight E.factors =
      ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  rw [factors, ← collapsed_realization_factor]
  exact E.collapsed_eval_eq

end Expansion

end BRecipe

/--
A counted independent-block recipe together with the concrete labelled terms
currently represented by that recipe in one exact product.
-/
structure BFam
    (M N : ℕ) where
  recipe :
    BRecipe
  realizations :
    List (CWord (LabelledAtom M N))
  collapse_word :
    ∀ w ∈ realizations,
      collapseWord w = recipe.erasedShape
  length_eq :
    realizations.length =
      Fintype.card (BRecipe.OrderEmbeddings recipe.leftBlocks M) *
        Fintype.card (BRecipe.OrderEmbeddings recipe.rightBlocks N)

namespace BFam

/-- Use the canonical order-embedding realizations of one block recipe. -/
noncomputable def ofRecipe
    (M N : ℕ)
    (R : BRecipe) :
    BFam M N where
  recipe := R
  realizations := R.instantiations M N
  collapse_word := by
    intro w hw
    exact R.collapse_word_instantiations hw
  length_eq := R.length_instantiations M N

/-- Regard one globally linear recipe as a counted one-block family. -/
noncomputable def ofLinear
    (M N : ℕ)
    (R : LRecipe) :
    BFam M N where
  recipe := BRecipe.ofLinear R
  realizations := R.instantiations M N
  collapse_word := by
    intro w hw
    rw [BRecipe.erased_shape_linear]
    exact R.collapse_word_instantiations hw
  length_eq := by
    rw [R.length_instantiations]
    rw [LRecipe.card_embedding_fin M R.leftDegree,
      LRecipe.card_embedding_fin N R.rightDegree,
      BRecipe.card_orderEmbeddings, BRecipe.card_orderEmbeddings]
    simp [BRecipe.ofLinear]

/-- Certified factor compressed from one counted block family. -/
def factor
    {M N : ℕ}
    (F : BFam M N) :
    Factor M N :=
  F.recipe.factor M N

lemma collapsed_list_factor
    {M N : ℕ}
    (F : BFam M N) :
    collapsedListEval F.realizations =
      F.factor.eval universalLeft universalRight := by
  rw [collapsedListEval]
  have hmap :
      List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          F.realizations =
        List.replicate F.realizations.length
          (F.recipe.erasedShape.eval
            (HPAtom.eval universalLeft universalRight)) := by
    simpa using
      (List.eq_replicate_of_mem
        (a := F.recipe.erasedShape.eval
          (HPAtom.eval universalLeft universalRight))
        (l := List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          F.realizations)
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rw [F.collapse_word w hw]))
  rw [hmap, List.prod_replicate, F.length_eq, factor, Factor.eval]
  change
    F.recipe.erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        (Fintype.card (BRecipe.OrderEmbeddings F.recipe.leftBlocks M) *
          Fintype.card (BRecipe.OrderEmbeddings F.recipe.rightBlocks N)) =
      F.recipe.erasedShape.eval (HPAtom.eval universalLeft universalRight) ^
        (F.recipe.factor M N).coefficient
  rw [F.recipe.factor_coefficient_embeddings]
  rw [show
      (Fintype.card (BRecipe.OrderEmbeddings F.recipe.leftBlocks M) : ℤ) *
      (Fintype.card (BRecipe.OrderEmbeddings F.recipe.rightBlocks N) : ℤ) =
        ((Fintype.card (BRecipe.OrderEmbeddings F.recipe.leftBlocks M) *
          Fintype.card (BRecipe.OrderEmbeddings F.recipe.rightBlocks N) : ℕ) : ℤ) by
      norm_num,
    zpow_natCast]

/-- Correct two counted recipe families by forming every pairwise correction. -/
def correction
    {M N : ℕ}
    (B A : BFam M N) :
    BFam M N where
  recipe := B.recipe.correction A.recipe
  realizations :=
    B.realizations.flatMap fun b =>
      A.realizations.map fun a => .commutator b a
  collapse_word := by
    intro w hw
    rcases List.mem_flatMap.mp hw with ⟨b, hb, hw⟩
    rcases List.mem_map.mp hw with ⟨a, ha, rfl⟩
    rw [BRecipe.erasedShape_corr]
    change
      CWord.commutator (collapseWord b) (collapseWord a) =
        CWord.commutator B.recipe.erasedShape A.recipe.erasedShape
    rw [B.collapse_word b hb, A.collapse_word a ha]
  length_eq := by
    calc
      (B.realizations.flatMap fun b =>
          A.realizations.map fun a => CWord.commutator b a).length =
          B.realizations.length * A.realizations.length := by
        simp [List.length_flatMap]
      _ =
          (Fintype.card
              (BRecipe.OrderEmbeddings B.recipe.leftBlocks M) *
            Fintype.card
              (BRecipe.OrderEmbeddings B.recipe.rightBlocks N)) *
          (Fintype.card
              (BRecipe.OrderEmbeddings A.recipe.leftBlocks M) *
            Fintype.card
              (BRecipe.OrderEmbeddings A.recipe.rightBlocks N)) := by
        rw [B.length_eq, A.length_eq]
      _ =
          Fintype.card
              (BRecipe.OrderEmbeddings
                (B.recipe.correction A.recipe).leftBlocks M) *
            Fintype.card
              (BRecipe.OrderEmbeddings
                (B.recipe.correction A.recipe).rightBlocks N) := by
        simp only [BRecipe.correction]
        rw [BRecipe.card_orderEmbeddings B.recipe.leftBlocks M,
          BRecipe.card_orderEmbeddings B.recipe.rightBlocks N,
          BRecipe.card_orderEmbeddings A.recipe.leftBlocks M,
          BRecipe.card_orderEmbeddings A.recipe.rightBlocks N]
        calc
          _ =
              ((B.recipe.leftBlocks ++ A.recipe.leftBlocks).map
                  fun degree => Nat.choose M degree).prod *
                ((B.recipe.rightBlocks ++ A.recipe.rightBlocks).map
                  fun degree => Nat.choose N degree).prod := by
              simp [List.map_append, List.prod_append]
              ring
          _ =
              Fintype.card
                  (BRecipe.OrderEmbeddings
                    (B.recipe.leftBlocks ++ A.recipe.leftBlocks) M) *
                Fintype.card
                  (BRecipe.OrderEmbeddings
                    (B.recipe.rightBlocks ++ A.recipe.rightBlocks) N) := by
              rw [← BRecipe.card_orderEmbeddings
                (B.recipe.leftBlocks ++ A.recipe.leftBlocks) M,
                ← BRecipe.card_orderEmbeddings
                  (B.recipe.rightBlocks ++ A.recipe.rightBlocks) N]

@[simp]
lemma recipe_correction
    {M N : ℕ}
    (B A : BFam M N) :
    (B.correction A).recipe = B.recipe.correction A.recipe :=
  rfl

/-- Row-major slot of one entry in a `flatMap` of fixed-length mapped rows. -/
def List.flat_map_mapindex
    {α β γ : Type*}
    (xs : List α)
    (ys : List β)
  (f : α → β → γ)
  (x : Fin xs.length)
  (y : Fin ys.length) :
    Fin (xs.flatMap fun entry => ys.map (f entry)).length :=
  ⟨x.val * ys.length + y.val, by
    simpa [List.length_flatMap] using
      (calc
        x.val * ys.length + y.val <
            x.val * ys.length + ys.length :=
          Nat.add_lt_add_left y.isLt _
        _ = (x.val + 1) * ys.length := by
          simp [Nat.add_mul]
        _ ≤ xs.length * ys.length :=
          Nat.mul_le_mul_right ys.length (Nat.succ_le_iff.mpr x.isLt))⟩

lemma List.flatmap_mapindexeq_mkdivmod
    {α β γ : Type*}
    (xs : List α)
    (ys : List β)
    (f : α → β → γ)
    (x : Fin xs.length)
    (y : Fin ys.length) :
    List.flat_map_mapindex xs ys f x y =
      ⟨Fin.mkDivMod x y, by
        simpa [List.length_flatMap] using (Fin.mkDivMod x y).isLt⟩ := by
  ext
  simp [List.flat_map_mapindex, Fin.mkDivMod, Nat.mul_comm]

lemma List.getflat_mapmapflat_mapmapindex
    {α β γ : Type*}
    (xs : List α)
    (ys : List β)
    (f : α → β → γ)
    (x : Fin xs.length)
    (y : Fin ys.length) :
    (xs.flatMap fun entry => ys.map (f entry)).get
        (List.flat_map_mapindex xs ys f x y) =
      f (xs.get x) (ys.get y) := by
  induction xs with
  | nil =>
      exact Fin.elim0 x
  | cons entry xs ih =>
      cases x using Fin.cases with
      | zero =>
          simp [List.flat_map_mapindex]
      | succ x =>
          simp only [List.get_eq_getElem, List.flat_map_mapindex, List.flatMap_cons]
          rw [List.getElem_append_right (by simp [Nat.succ_mul]; omega)]
          convert ih x using 1
          congr 1
          simp [Nat.succ_mul]
          omega

/-- Realization slot of the pairwise correction of two concrete slots. -/
def correctionIndex
    {M N : ℕ}
    (B A : BFam M N)
    (b : Fin B.realizations.length)
    (a : Fin A.realizations.length) :
    Fin (B.correction A).realizations.length :=
  List.flat_map_mapindex B.realizations A.realizations
    CWord.commutator b a

lemma correction_get_index
    {M N : ℕ}
    (B A : BFam M N)
    (b : Fin B.realizations.length)
    (a : Fin A.realizations.length) :
    (B.correction A).realizations.get (B.correctionIndex A b a) =
      .commutator (B.realizations.get b) (A.realizations.get a) := by
  exact List.getflat_mapmapflat_mapmapindex B.realizations A.realizations
    CWord.commutator b a

/-- Root-swap every concrete realization while retaining the same count. -/
def rootSwap
    {M N : ℕ}
    (F : BFam M N) :
    BFam M N where
  recipe := F.recipe.rootSwap
  realizations := F.realizations.map rootSwapWord
  collapse_word := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨u, hu, rfl⟩
    rw [collapse_root_swap, F.collapse_word u hu]
    exact (BRecipe.erased_shape_swap F.recipe).symm
  length_eq := by
    simpa only [List.length_map, BRecipe.rootSwap] using F.length_eq

@[simp]
lemma recipe_rootSwap
    {M N : ℕ}
    (F : BFam M N) :
    F.rootSwap.recipe = F.recipe.rootSwap :=
  rfl

/-- Realization slot of the root-swap of one concrete slot. -/
def rootSwapIndex
    {M N : ℕ}
    (F : BFam M N)
    (index : Fin F.realizations.length) :
    Fin F.rootSwap.realizations.length :=
  ⟨index.val, by simp [BFam.rootSwap]⟩

lemma swap_get_index
    {M N : ℕ}
    (F : BFam M N)
    (index : Fin F.realizations.length) :
    F.rootSwap.realizations.get (F.rootSwapIndex index) =
      rootSwapWord (F.realizations.get index) := by
  simp [BFam.rootSwapIndex, BFam.rootSwap]

lemma factor_swap_inv
    {M N : ℕ}
    (F : BFam M N) :
    F.rootSwap.factor.eval universalLeft universalRight =
      (F.factor.eval universalLeft universalRight)⁻¹ := by
  exact F.recipe.factor_swap_inv M N

/-- Inverse-oriented family correction `[A^-1, B]`. -/
def inverseCorrection
    {M N : ℕ}
    (B A : BFam M N) :
    BFam M N :=
  A.rootSwap.correction B

/-- Concrete labelled realizations of a finite counted family list. -/
def realizationList
    {M N : ℕ}
    (families : List (BFam M N)) :
    List (CWord (LabelledAtom M N)) :=
  families.flatMap BFam.realizations

/-- Certified compressed factor list attached to counted families. -/
def factorList
    {M N : ℕ}
    (families : List (BFam M N)) :
    List (Factor M N) :=
  families.map BFam.factor

@[simp]
lemma realizationList_cons
    {M N : ℕ}
    (F : BFam M N)
    (families : List (BFam M N)) :
    realizationList (F :: families) =
      F.realizations ++ realizationList families :=
  rfl

@[simp]
lemma factorList_cons
    {M N : ℕ}
    (F : BFam M N)
    (families : List (BFam M N)) :
    factorList (F :: families) =
      F.factor :: factorList families :=
  rfl

lemma collapsed_realization_factor
    {M N : ℕ} :
    ∀ families : List (BFam M N),
      collapsedListEval (realizationList families) =
        listEval universalLeft universalRight (factorList families)
  | [] => by
      simp [realizationList, factorList, collapsedListEval, listEval]
  | F :: families => by
      rw [realizationList_cons, BRecipe.collapsed_eval_append,
        F.collapsed_list_factor, factorList_cons, listEval_cons,
        collapsed_realization_factor families]

structure Expansion
    (M N : ℕ) where
  families :
    List (BFam M N)
  collapsed_eval_eq :
    collapsedListEval (realizationList families) =
      ⁅universalLeft ^ M, universalRight ^ N⁆

namespace Expansion

/-- Forget counted family realizations and retain certified compressed factors. -/
def factors
    {M N : ℕ}
    (E : Expansion M N) :
    List (Factor M N) :=
  factorList E.families

lemma listEval_factors
    {M N : ℕ}
    (E : Expansion M N) :
    listEval universalLeft universalRight E.factors =
      ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  rw [factors, ← collapsed_realization_factor]
  exact E.collapsed_eval_eq

end Expansion

end BFam

/-- One decorated collector term paired with its counted recipe family. -/
structure DFTerm
    (M N K : ℕ) where
  decorated :
    DTerm M N K
  family :
    BFam M N
  word_mem :
    decorated.word ∈ family.realizations
  word_index :
    Fin family.realizations.length
  word_get :
    family.realizations.get word_index = decorated.word

namespace DFTerm

/-- Evaluate the decorated labelled term carried by one recipe-certified term. -/
def eval
    {M N K : ℕ}
    (T : DFTerm M N K) :
    FreeGroup (LabelledAtom M N) :=
  T.decorated.eval

/-- Forget labels in the Hall shape carried by one recipe-certified term. -/
def erasedShape
    {M N K : ℕ}
    (T : DFTerm M N K) :
    CWord HPAtom :=
  T.decorated.erasedShape

/-- Attach the counted one-block recipe family of one positive label-linear term. -/
noncomputable def ofLabelLinear
    {M N K : ℕ}
    (T : DTerm M N K)
    (hpositive : T.erasedShape.PBPos)
    (hlinear : LabelLinear T.word) :
    DFTerm M N K :=
  let family := BFam.ofLinear M N
    (LRecipe.ofLabelLinear T.word hpositive hlinear)
  let hword : T.word ∈ family.realizations :=
    LRecipe.instantiations_label_linear T.word hpositive hlinear
  {
    decorated := T
    family := family
    word_mem := hword
    word_index := (List.mem_iff_get.mp hword).choose
    word_get := (List.mem_iff_get.mp hword).choose_spec }

lemma erased_shape_family
    {M N K : ℕ}
    (T : DFTerm M N K) :
    T.erasedShape = T.family.recipe.erasedShape :=
  T.family.collapse_word T.decorated.word T.word_mem

lemma positive
    {M N K : ℕ}
    (T : DFTerm M N K) :
    T.erasedShape.PBPos := by
  rw [T.erased_shape_family]
  exact T.family.recipe.positive

def listEval
    {M N K : ℕ}
    (L : List (DFTerm M N K)) :
    FreeGroup (LabelledAtom M N) :=
  (L.map DFTerm.eval).prod

lemma list_eval_decorated
    {M N K : ℕ}
    (L : List (DFTerm M N K)) :
    DFTerm.listEval L =
      decoratedListEval (L.map DFTerm.decorated) := by
  rw [DFTerm.listEval, decoratedListEval, List.map_map]
  congr 1

/-- The exact correction term together with pairwise correction provenance. -/
noncomputable def correction
    {M N K : ℕ}
    (B A : DFTerm M N K) :
    DFTerm M N K :=
  let decorated := DTerm.correction B.decorated A.decorated
  let family := B.family.correction A.family
  let hword : decorated.word ∈ family.realizations := by
    apply List.mem_flatMap.mpr
    refine ⟨B.decorated.word, B.word_mem, ?_⟩
    exact List.mem_map.mpr ⟨A.decorated.word, A.word_mem, rfl⟩
  {
    decorated := decorated
    family := family
    word_mem := hword
    word_index := B.family.correctionIndex A.family B.word_index A.word_index
    word_get := by
      rw [BFam.correction_get_index, B.word_get, A.word_get]
      rfl }

@[simp]
lemma decorated_correction
    {M N K : ℕ}
    (B A : DFTerm M N K) :
    (B.correction A).decorated =
      DTerm.correction B.decorated A.decorated :=
  rfl

lemma eval_correction_mul
    {M N K : ℕ}
    (B A : DFTerm M N K) :
    (B.correction A).eval * A.eval * B.eval =
      B.eval * A.eval := by
  exact DTerm.eval_correction_mul B.decorated A.decorated

/-- Root-swap one recipe-certified labelled term. -/
noncomputable def rootSwap
    {M N K : ℕ}
    (T : DFTerm M N K) :
    DFTerm M N K :=
  let decorated : DTerm M N K := {
    word := rootSwapWord T.decorated.word
    support := T.decorated.support
  }
  let family := T.family.rootSwap
  let hword : decorated.word ∈ family.realizations :=
    List.mem_map.mpr ⟨T.decorated.word, T.word_mem, rfl⟩
  {
    decorated := decorated
    family := family
    word_mem := hword
    word_index := T.family.rootSwapIndex T.word_index
    word_get := by
      rw [BFam.swap_get_index, T.word_get] }

@[simp]
lemma decorated_root_swap
    {M N K : ℕ}
    (T : DFTerm M N K) :
    T.rootSwap.decorated.word = rootSwapWord T.decorated.word :=
  rfl

@[simp]
lemma decorated_swap_support
    {M N K : ℕ}
    (T : DFTerm M N K) :
    T.rootSwap.decorated.support = T.decorated.support :=
  rfl

/-- Inverse-oriented exact correction `[A^-1, B]` with counted provenance. -/
noncomputable def inverseCorrection
    {M N K : ℕ}
    (B A : DFTerm M N K) :
    DFTerm M N K :=
  A.rootSwap.correction B

/--
One finite More3 insertion derivation with counted family provenance.
The finite family collector follows More3's operational support condition:
only independent histories are interchanged.
-/
inductive Inserts
    {M N K : ℕ} :
    List (DFTerm M N K) →
      DFTerm M N K →
        List (DFTerm M N K) →
          Prop where
  | nil
      (A : DFTerm M N K) :
      Inserts [] A [A]
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : ¬ A.decorated.independentBefore B.decorated) :
      Inserts (P ++ [B]) A (P ++ [B, A])
  | obstruction
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.independentBefore B.decorated)
      {Q R : List (DFTerm M N K)}
      (hcorrection : Inserts P (B.correction A) Q)
      (hinsert : Inserts Q A R) :
      Inserts (P ++ [B]) A (R ++ [B])

lemma list_append_singleton
    {M N K : ℕ}
    (P : List (DFTerm M N K))
    (A : DFTerm M N K) :
    DFTerm.listEval (P ++ [A]) =
      DFTerm.listEval P * A.eval := by
  simp [DFTerm.listEval, List.prod_append]

lemma listEval_inserts
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : Inserts L A R) :
    DFTerm.listEval R =
      DFTerm.listEval L * A.eval := by
  induction hinsert with
  | nil A =>
      simp [DFTerm.listEval]
  | append P B A _hAB =>
      simp [DFTerm.listEval, List.prod_append, mul_assoc]
  | obstruction P B A _hAB hcorrection hinsert ihcorrection ihinsert =>
      rw [list_append_singleton, ihinsert, ihcorrection,
        list_append_singleton]
      calc
        (DFTerm.listEval P * (B.correction A).eval) *
              A.eval * B.eval =
            DFTerm.listEval P *
              ((B.correction A).eval * A.eval * B.eval) := by
                group
        _ = DFTerm.listEval P * (B.eval * A.eval) := by
              rw [DFTerm.eval_correction_mul]
        _ = (DFTerm.listEval P * B.eval) * A.eval := by
              group

/-- One finite More3 collection derivation with counted family provenance. -/
inductive Collects
    {M N K : ℕ} :
    List (DFTerm M N K) →
      List (DFTerm M N K) →
        Prop where
  | nil :
      Collects [] []
  | snoc
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      {C R : List (DFTerm M N K)}
      (hcollect : Collects P C)
      (hinsert : Inserts C A R) :
      Collects (P ++ [A]) R

lemma listEval_collects
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : Collects L R) :
    DFTerm.listEval R =
      DFTerm.listEval L := by
  induction hcollect with
  | nil =>
      rfl
  | snoc P A hcollect hinsert ihcollect =>
      rw [listEval_inserts hinsert, ihcollect, list_append_singleton]

lemma decorated_map_inserts
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : Inserts L A R) :
    HACoeff.IInsert
      (L.map DFTerm.decorated) A.decorated
      (R.map DFTerm.decorated) := by
  induction hinsert with
  | nil A =>
      exact HACoeff.IInsert.nil A.decorated
  | append P B A hAB =>
      simpa [List.map_append] using
        (HACoeff.IInsert.append
          (P.map DFTerm.decorated) B.decorated A.decorated hAB)
  | obstruction P B A hAB hcorrection hinsert ihcorrection ihinsert =>
      simpa [List.map_append, decorated_correction] using
        (HACoeff.IInsert.obstruction
          (P.map DFTerm.decorated) B.decorated A.decorated
          hAB ihcorrection ihinsert)

lemma decorated_map_collects
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : Collects L R) :
    HACoeff.ICollec
      (L.map DFTerm.decorated)
      (R.map DFTerm.decorated) := by
  induction hcollect with
  | nil =>
      exact HACoeff.ICollec.nil
  | snoc P A hcollect hinsert ihcollect =>
      simpa [List.map_append] using
        (HACoeff.ICollec.snoc
          (P.map DFTerm.decorated) A.decorated
          ihcollect (decorated_map_inserts hinsert))

/-- Finite family-provenance readiness certificate for one More3 insertion. -/
inductive InsertReady
    {M N K : ℕ} :
    List (DFTerm M N K) →
      DFTerm M N K →
        Prop where
  | nil
      (A : DFTerm M N K) :
      InsertReady [] A
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : ¬ A.decorated.independentBefore B.decorated) :
      InsertReady (P ++ [B]) A
  | obstruction
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.independentBefore B.decorated)
      (hcorrection : InsertReady P (B.correction A))
      (hinsert :
        ∀ Q : List (DFTerm M N K),
          Inserts P (B.correction A) Q →
            InsertReady Q A) :
      InsertReady (P ++ [B]) A

lemma inserts_insert_ready
    {M N K : ℕ}
    {L : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hready : InsertReady L A) :
    ∃ R : List (DFTerm M N K),
      Inserts L A R := by
  induction hready with
  | nil A =>
      exact ⟨[A], Inserts.nil A⟩
  | append P B A hBA =>
      exact ⟨P ++ [B, A], Inserts.append P B A hBA⟩
  | obstruction P B A hAB hcorrection hinsert ihcorrection ihinsert =>
      rcases ihcorrection with ⟨Q, hQ⟩
      rcases ihinsert Q hQ with ⟨R, hR⟩
      exact ⟨R ++ [B], Inserts.obstruction P B A hAB hQ hR⟩

/-- Finite family-provenance readiness certificate for a More3 collection. -/
inductive CollectReady
    {M N K : ℕ} :
    List (DFTerm M N K) →
      Prop where
  | nil :
      CollectReady []
  | snoc
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      (hcollect : CollectReady P)
      (hinsert :
        ∀ C : List (DFTerm M N K),
          Collects P C →
            InsertReady C A) :
      CollectReady (P ++ [A])

lemma collects_collect_ready
    {M N K : ℕ}
    {L : List (DFTerm M N K)}
    (hready : CollectReady L) :
    ∃ R : List (DFTerm M N K),
      Collects L R := by
  induction hready with
  | nil =>
      exact ⟨[], Collects.nil⟩
  | snoc P A hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨C, hC⟩
      rcases inserts_insert_ready (hinsert C hC) with ⟨R, hR⟩
      exact ⟨R, Collects.snoc P A hC hR⟩

/--
Family-provenance version of the genuine independent-history collector.
The selected labelled word still determines the exact noncommutative
rewrite, while the attached family records the full counted recipe produced
by the same history constructor.
-/
inductive IInsert
    {M N K : ℕ} :
    List (DFTerm M N K) →
      DFTerm M N K →
        List (DFTerm M N K) →
          Prop where
  | nil
      (A : DFTerm M N K) :
      IInsert [] A [A]
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : ¬ A.decorated.independentBefore B.decorated) :
      IInsert (P ++ [B]) A (P ++ [B, A])
  | obstruction
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.independentBefore B.decorated)
      {Q R : List (DFTerm M N K)}
      (hcorrection : IInsert P (B.correction A) Q)
      (hinsert : IInsert Q A R) :
      IInsert (P ++ [B]) A (R ++ [B])

lemma list_independent_inserts
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : IInsert L A R) :
    DFTerm.listEval R =
      DFTerm.listEval L * A.eval := by
  induction hinsert with
  | nil A =>
      simp [DFTerm.listEval]
  | append P B A _hAB =>
      simp [DFTerm.listEval, List.prod_append, mul_assoc]
  | obstruction P B A _hAB hcorrection hinsert ihcorrection ihinsert =>
      rw [list_append_singleton, ihinsert, ihcorrection,
        list_append_singleton]
      calc
        (DFTerm.listEval P * (B.correction A).eval) *
              A.eval * B.eval =
            DFTerm.listEval P *
              ((B.correction A).eval * A.eval * B.eval) := by
                group
        _ = DFTerm.listEval P * (B.eval * A.eval) := by
              rw [DFTerm.eval_correction_mul]
        _ = (DFTerm.listEval P * B.eval) * A.eval := by
              group

lemma decorated_inserts
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : IInsert L A R) :
    HACoeff.IInsert
      (L.map DFTerm.decorated) A.decorated
      (R.map DFTerm.decorated) := by
  induction hinsert with
  | nil A =>
      exact HACoeff.IInsert.nil A.decorated
  | append P B A hAB =>
      simpa [List.map_append] using
        (HACoeff.IInsert.append
          (P.map DFTerm.decorated) B.decorated A.decorated hAB)
  | obstruction P B A hAB hcorrection hinsert ihcorrection ihinsert =>
      simpa [List.map_append, decorated_correction] using
        (HACoeff.IInsert.obstruction
          (P.map DFTerm.decorated) B.decorated A.decorated
          hAB ihcorrection ihinsert)

/-- One finite exact family collection derivation using genuine swaps only. -/
inductive ICollec
    {M N K : ℕ} :
    List (DFTerm M N K) →
      List (DFTerm M N K) →
        Prop where
  | nil :
      ICollec [] []
  | snoc
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      {C R : List (DFTerm M N K)}
      (hcollect : ICollec P C)
      (hinsert : IInsert C A R) :
      ICollec (P ++ [A]) R

lemma list_independent_collects
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : ICollec L R) :
    DFTerm.listEval R =
      DFTerm.listEval L := by
  induction hcollect with
  | nil =>
      rfl
  | snoc P A hcollect hinsert ihcollect =>
      rw [list_independent_inserts hinsert, ihcollect, list_append_singleton]

lemma independent_collects
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : ICollec L R) :
    HACoeff.ICollec
      (L.map DFTerm.decorated)
      (R.map DFTerm.decorated) := by
  induction hcollect with
  | nil =>
      exact HACoeff.ICollec.nil
  | snoc P A hcollect hinsert ihcollect =>
      simpa [List.map_append] using
        (HACoeff.ICollec.snoc
          (P.map DFTerm.decorated) A.decorated
          ihcollect (decorated_inserts hinsert))

/-- Finite readiness certificate for one independent family insertion. -/
inductive IndependentInsertReady
    {M N K : ℕ} :
    List (DFTerm M N K) →
      DFTerm M N K →
        Prop where
  | nil
      (A : DFTerm M N K) :
      IndependentInsertReady [] A
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : ¬ A.decorated.independentBefore B.decorated) :
      IndependentInsertReady (P ++ [B]) A
  | obstruction
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.independentBefore B.decorated)
      (hcorrection : IndependentInsertReady P (B.correction A))
      (hinsert :
        ∀ Q : List (DFTerm M N K),
          IInsert P (B.correction A) Q →
            IndependentInsertReady Q A) :
      IndependentInsertReady (P ++ [B]) A

lemma independent_inserts_ready
    {M N K : ℕ}
    {L : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hready : IndependentInsertReady L A) :
    ∃ R : List (DFTerm M N K),
      IInsert L A R := by
  induction hready with
  | nil A =>
      exact ⟨[A], IInsert.nil A⟩
  | append P B A hAB =>
      exact ⟨P ++ [B, A], IInsert.append P B A hAB⟩
  | obstruction P B A hAB hcorrection hinsert ihcorrection ihinsert =>
      rcases ihcorrection with ⟨Q, hQ⟩
      rcases ihinsert Q hQ with ⟨R, hR⟩
      exact ⟨R ++ [B], IInsert.obstruction P B A hAB hQ hR⟩

abbrev IndependentInsertionState
    (M N K : ℕ) :=
  List (DFTerm M N K) × DFTerm M N K

def independentStateMeasure
    {M N K : ℕ}
    (state : IndependentInsertionState M N K) :
    ℕ × ℕ × ℕ :=
  HACoeff.independentInsertionMeasure
    (state.1.map DFTerm.decorated) state.2.decorated

def independentInsertionBefore
    {M N K : ℕ} :
    IndependentInsertionState M N K →
      IndependentInsertionState M N K →
        Prop :=
  InvImage insertionMeasureBefore independentStateMeasure

lemma independent_before_wf
    {M N K : ℕ} :
    WellFounded (@independentInsertionBefore M N K) := by
  exact InvImage.wf independentStateMeasure insertion_measure_wf

lemma independent_measure_before
    {M N K : ℕ}
    (P : List (DFTerm M N K))
    {B A : DFTerm M N K}
    (hAB : A.decorated.independentBefore B.decorated)
    (hB : B.decorated.support.Nonempty) :
    independentInsertionBefore
      (P, B.correction A)
      (P ++ [B], A) := by
  change
    insertionMeasureBefore
      (HACoeff.independentInsertionMeasure
        (P.map DFTerm.decorated) (B.correction A).decorated)
      (HACoeff.independentInsertionMeasure
        ((P ++ [B]).map DFTerm.decorated) A.decorated)
  simpa [List.map_append, decorated_correction] using
    (HACoeff.independent_measure_before
      (P.map DFTerm.decorated) hAB hB)

lemma measure_after_before
    {M N K : ℕ}
    (P : List (DFTerm M N K))
    {B A : DFTerm M N K}
    {Q : List (DFTerm M N K)}
    (hAB : A.decorated.independentBefore B.decorated)
    (hA : A.decorated.support.Nonempty)
    (hcorrection : IInsert P (B.correction A) Q) :
    independentInsertionBefore
      (Q, A)
      (P ++ [B], A) := by
  change
    insertionMeasureBefore
      (HACoeff.independentInsertionMeasure
        (Q.map DFTerm.decorated) A.decorated)
      (HACoeff.independentInsertionMeasure
        ((P ++ [B]).map DFTerm.decorated) A.decorated)
  simpa [List.map_append] using
    (HACoeff.measure_after_before
      (P.map DFTerm.decorated) hAB hA
      (decorated_inserts hcorrection))

lemma independentInsertReady
    {M N K : ℕ} :
    ∀ (L : List (DFTerm M N K)) (A : DFTerm M N K),
      SupportNonemptyList (L.map DFTerm.decorated) →
        A.decorated.support.Nonempty →
          IndependentInsertReady L A := by
  intro L A
  refine independent_before_wf.induction
    (C := fun state =>
      SupportNonemptyList (state.1.map DFTerm.decorated) →
        state.2.decorated.support.Nonempty →
          IndependentInsertReady state.1 state.2)
    (L, A) ?_
  rintro ⟨L, A⟩ ih hLsupport hAsupport
  rcases List.eq_nil_or_concat' L with rfl | ⟨P, B, rfl⟩
  · exact IndependentInsertReady.nil A
  · by_cases hAB : A.decorated.independentBefore B.decorated
    · have hPsupport :
          SupportNonemptyList (P.map DFTerm.decorated) := by
        apply support_nonempty_append
        simpa [List.map_append] using hLsupport
      have hBsupport : B.decorated.support.Nonempty :=
        hLsupport B.decorated (by simp)
      have hcorrectionSupport :
          (B.correction A).decorated.support.Nonempty := by
        rw [decorated_correction]
        exact DTerm.support_nonempty_left hBsupport
      have hcorrection : IndependentInsertReady P (B.correction A) :=
        ih (P, B.correction A)
          (independent_measure_before P hAB hBsupport)
          hPsupport hcorrectionSupport
      refine IndependentInsertReady.obstruction P B A hAB hcorrection ?_
      intro Q hQ
      exact ih (Q, A)
        (measure_after_before P hAB hAsupport hQ)
        (support_independent_inserts
          (decorated_inserts hQ) hPsupport hcorrectionSupport)
        hAsupport
    · exact IndependentInsertReady.append P B A hAB

/-- Finite readiness certificate for an independent family collection. -/
inductive IndependentCollectReady
    {M N K : ℕ} :
    List (DFTerm M N K) →
      Prop where
  | nil :
      IndependentCollectReady []
  | snoc
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      (hcollect : IndependentCollectReady P)
      (hinsert :
        ∀ C : List (DFTerm M N K),
          ICollec P C →
            IndependentInsertReady C A) :
      IndependentCollectReady (P ++ [A])

lemma independent_collects_ready
    {M N K : ℕ}
    {L : List (DFTerm M N K)}
    (hready : IndependentCollectReady L) :
    ∃ R : List (DFTerm M N K),
      ICollec L R := by
  induction hready with
  | nil =>
      exact ⟨[], ICollec.nil⟩
  | snoc P A hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨C, hC⟩
      rcases independent_inserts_ready (hinsert C hC) with ⟨R, hR⟩
      exact ⟨R, ICollec.snoc P A hC hR⟩

lemma independentCollectReady
    {M N K : ℕ} :
    ∀ L : List (DFTerm M N K),
      SupportNonemptyList (L.map DFTerm.decorated) →
        IndependentCollectReady L := by
  intro L hLsupport
  induction L using List.reverseRecOn with
  | nil =>
      exact IndependentCollectReady.nil
  | append_singleton P A ih =>
      have hPsupport :
          SupportNonemptyList (P.map DFTerm.decorated) := by
        apply support_nonempty_append
        simpa [List.map_append] using hLsupport
      have hAsupport : A.decorated.support.Nonempty :=
        hLsupport A.decorated (by simp)
      exact IndependentCollectReady.snoc P A (ih hPsupport) fun C hC =>
        independentInsertReady C A
          (support_independent_collects
            (independent_collects hC) hPsupport)
          hAsupport

lemma inserts_independent
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : IInsert L A R) :
    Inserts L A R := by
  induction hinsert with
  | nil A =>
      exact Inserts.nil A
  | append P B A hAB =>
      exact Inserts.append P B A hAB
  | obstruction P B A hAB hcorrection hinsert ihcorrection ihinsert =>
      exact Inserts.obstruction P B A hAB ihcorrection ihinsert

lemma independent_inserts
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : Inserts L A R) :
    IInsert L A R := by
  induction hinsert with
  | nil A =>
      exact IInsert.nil A
  | append P B A hAB =>
      exact IInsert.append P B A hAB
  | obstruction P B A hAB hcorrection hinsert ihcorrection ihinsert =>
      exact IInsert.obstruction P B A hAB ihcorrection ihinsert

lemma collects_independent
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : ICollec L R) :
    Collects L R := by
  induction hcollect with
  | nil =>
      exact Collects.nil
  | snoc P A hcollect hinsert ihcollect =>
      exact Collects.snoc P A ihcollect (inserts_independent hinsert)

lemma collects_of_collects
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : Collects L R) :
    ICollec L R := by
  induction hcollect with
  | nil =>
      exact ICollec.nil
  | snoc P A hcollect hinsert ihcollect =>
      exact
        ICollec.snoc P A ihcollect (independent_inserts hinsert)

lemma insert_ready_independent
    {M N K : ℕ}
    {L : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hready : IndependentInsertReady L A) :
    InsertReady L A := by
  induction hready with
  | nil A =>
      exact InsertReady.nil A
  | append P B A hAB =>
      exact InsertReady.append P B A hAB
  | obstruction P B A hAB hcorrection hinsert ihcorrection ihinsert =>
      exact InsertReady.obstruction P B A hAB ihcorrection fun Q hQ =>
        ihinsert Q (independent_inserts hQ)

lemma collect_ready_independent
    {M N K : ℕ}
    {L : List (DFTerm M N K)}
    (hready : IndependentCollectReady L) :
    CollectReady L := by
  induction hready with
  | nil =>
      exact CollectReady.nil
  | snoc P A hcollect hinsert ihcollect =>
      exact CollectReady.snoc P A ihcollect fun C hC =>
        insert_ready_independent
          (hinsert C (collects_of_collects hC))

end DFTerm

lemma commutator_collapse_positive
    {M N : ℕ}
    {w : CWord (LabelledAtom M N)}
    (hw : (collapseWord w).PBPos) :
    ∃ u v : CWord (LabelledAtom M N),
      w = CWord.commutator u v := by
  cases w with
  | atom a =>
      cases a <;>
        simp [collapseWord, collapseLabel,
          CWord.PBPos] at hw
  | commutator u v =>
      exact ⟨u, v, rfl⟩

lemma swap_collapse_positive
    {M N : ℕ}
    {G : Type*} [Group G]
    (f : LabelledAtom M N → G)
    {w : CWord (LabelledAtom M N)}
    (hw : (collapseWord w).PBPos) :
    (rootSwapWord w).eval f = (w.eval f)⁻¹ := by
  rcases commutator_collapse_positive hw with ⟨u, v, rfl⟩
  exact root_swap_commutator f u v

/--
Rewrite one conjugated positive-bidegree term so the old term stays before
the inverse-oriented correction.
-/
def inverseConjugateAtom
    {M N : ℕ}
    (a : LabelledAtom M N)
    (D : CWord (LabelledAtom M N)) :
    List (CWord (LabelledAtom M N)) :=
  [D, .commutator (rootSwapWord D) (.atom a)]

lemma relabel_conjugate_atom
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (a : LabelledAtom M N)
    (D : CWord (LabelledAtom M N)) :
    inverseConjugateAtom (relabelLabel left right a)
        (relabelWord left right D) =
      (inverseConjugateAtom a D).map (relabelWord left right) := by
  cases a <;>
    simp [inverseConjugateAtom, relabelWord, relabelLabel,
      relabel_root_swap]

lemma labelled_atom_trace
    {M N : ℕ}
    (a : LabelledAtom M N)
    (D : CWord (LabelledAtom M N))
    (hD : (collapseWord D).PBPos) :
    labelledListEval (inverseConjugateAtom a D) =
      FreeGroup.of a * D.eval FreeGroup.of * (FreeGroup.of a)⁻¹ := by
  simp [inverseConjugateAtom, labelledListEval,
    swap_collapse_positive FreeGroup.of hD,
    commutatorElement_def, mul_assoc]

lemma collapse_atom_positive
    {M N : ℕ}
    (a : LabelledAtom M N)
    {D : CWord (LabelledAtom M N)}
    (hD : (collapseWord D).PBPos) :
    ∀ E ∈ inverseConjugateAtom a D,
      (collapseWord E).PBPos := by
  intro E hE
  have hroot : (rootSwapWord (collapseWord D)).PBPos :=
    rootSwap_positive hD
  have hE' :
      E = D ∨
        E = .commutator (rootSwapWord D) (.atom a) := by
    simpa [inverseConjugateAtom] using hE
  rcases hE' with rfl | rfl
  · exact hD
  · cases a with
    | inl _ =>
        change
          0 < (collapseWord (rootSwapWord D)).pairLeftDegree + 1 ∧
            0 < (collapseWord (rootSwapWord D)).pairRightDegree + 0
        rw [collapse_root_swap]
        exact ⟨Nat.add_pos_left hroot.left _, by simpa using hroot.right⟩
    | inr _ =>
        change
          0 < (collapseWord (rootSwapWord D)).pairLeftDegree + 0 ∧
            0 < (collapseWord (rootSwapWord D)).pairRightDegree + 1
        rw [collapse_root_swap]
        exact ⟨by simpa using hroot.left, Nat.add_pos_left hroot.right _⟩

lemma label_atom_trace
    {M N : ℕ}
    (a : LabelledAtom M N)
    {D : CWord (LabelledAtom M N)}
    (hD : LabelLinear D)
    (ha : a ∉ labelSupport D) :
    ∀ E ∈ inverseConjugateAtom a D,
      LabelLinear E := by
  intro E hE
  have hE' :
      E = D ∨
        E = .commutator (rootSwapWord D) (.atom a) := by
    simpa [inverseConjugateAtom] using hE
  rcases hE' with rfl | rfl
  · exact hD
  · refine ⟨label_linear_swap hD, trivial, ?_⟩
    rw [labelSupport_atom, Finset.disjoint_singleton_right]
    simpa [label_swap_word] using ha

lemma label_subset_atom
    {M N : ℕ}
    (a : LabelledAtom M N)
    (D E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseConjugateAtom a D) :
    labelSupport E ⊆ insert a (labelSupport D) := by
  have hE' :
      E = D ∨
        E = .commutator (rootSwapWord D) (.atom a) := by
    simpa [inverseConjugateAtom] using hE
  rcases hE' with rfl | rfl
  · exact Finset.subset_insert _ _
  · rw [labelSupport_commutator, label_swap_word, labelSupport_atom]
    exact Finset.union_subset (Finset.subset_insert _ _)
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))

/-- Expand conjugation while keeping each old term before its correction. -/
def inverseConjTrace
    {M N : ℕ} :
    List (LabelledAtom M N) →
      CWord (LabelledAtom M N) →
        List (CWord (LabelledAtom M N))
  | [], D => [D]
  | a :: A, D =>
      (inverseConjTrace A D).flatMap (inverseConjugateAtom a)

lemma relabel_inverse_conj
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ A : List (LabelledAtom M N),
      ∀ D : CWord (LabelledAtom M N),
        inverseConjTrace (A.map (relabelLabel left right))
            (relabelWord left right D) =
          (inverseConjTrace A D).map (relabelWord left right)
  | [], D => by simp [inverseConjTrace]
  | a :: A, D => by
      rw [List.map_cons, inverseConjTrace, inverseConjTrace,
        relabel_inverse_conj]
      rw [List.flatMap_map, List.map_flatMap]
      simp [relabel_conjugate_atom]

/-- Expand inverse-oriented conjugation over a formal commutator list. -/
def inverseTraceList
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    List (CWord (LabelledAtom M N)) :=
  L.flatMap (inverseConjTrace A)

lemma relabel_inverse_list
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    inverseTraceList (A.map (relabelLabel left right))
        (L.map (relabelWord left right)) =
      (inverseTraceList A L).map (relabelWord left right) := by
  rw [inverseTraceList, inverseTraceList, List.flatMap_map,
    List.map_flatMap]
  simp [relabel_inverse_conj]

lemma sublist_flat_atom
    {M N : ℕ}
    (a : LabelledAtom M N) :
    ∀ L : List (CWord (LabelledAtom M N)),
      List.Sublist L (L.flatMap (inverseConjugateAtom a))
  | [] => by simp
  | D :: L => by
      change
        List.Sublist (D :: L)
          (D :: .commutator (rootSwapWord D) (.atom a) ::
            L.flatMap (inverseConjugateAtom a))
      exact
        List.Sublist.cons_cons D
          (List.Sublist.cons _ (sublist_flat_atom a L))

lemma inverse_trace_sublist
    {M N : ℕ}
    (D : CWord (LabelledAtom M N))
    {A B : List (LabelledAtom M N)}
    (h : List.Sublist A B) :
    List.Sublist (inverseConjTrace A D) (inverseConjTrace B D) := by
  induction h with
  | slnil =>
      simp [inverseConjTrace]
  | @cons _ _ a h ih =>
      simpa [inverseConjTrace] using
        ih.trans (sublist_flat_atom a _)
  | @cons_cons _ _ a h ih =>
      simpa [inverseConjTrace] using ih.flatMap (inverseConjugateAtom a)

lemma inverse_conj_sublist
    {M N : ℕ}
    {A B : List (LabelledAtom M N)}
    {L K : List (CWord (LabelledAtom M N))}
    (hA : List.Sublist A B)
    (hL : List.Sublist L K) :
    List.Sublist (inverseTraceList A L) (inverseTraceList B K) := by
  rw [inverseTraceList, inverseTraceList]
  exact
    (hL.flatMap (inverseConjTrace A)).trans
      (List.Sublist.flatMap_right K fun D _hD =>
        inverse_trace_sublist D hA)

lemma sublist_inverse_self
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    List.Sublist L (inverseTraceList A L) := by
  rw [inverseTraceList]
  simpa [inverseConjTrace] using
    List.Sublist.flatMap_right L fun D _hD =>
      inverse_trace_sublist D (List.nil_sublist A)

lemma filter_sublist_imp
    {α : Type*}
    (p q : α → Bool)
    (hpq : ∀ a, p a → q a) :
    ∀ L : List α,
      List.Sublist (L.filter p) (L.filter q)
  | [] => by simp
  | a :: L => by
      by_cases hpa : p a
      · have hqa : q a := hpq a hpa
        simpa [hpa, hqa] using
          (filter_sublist_imp p q hpq L).cons_cons a
      · by_cases hqa : q a
        · simpa [hpa, hqa] using
            (filter_sublist_imp p q hpq L).cons a
        · simpa [hpa, hqa] using
            filter_sublist_imp p q hpq L

lemma label_conjugate_atom
    {M N : ℕ}
    (a : LabelledAtom M N)
    (D E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseConjugateAtom a D) :
    labelSupport D ⊆ labelSupport E := by
  have hE' :
      E = D ∨
        E = .commutator (rootSwapWord D) (.atom a) := by
    simpa [inverseConjugateAtom] using hE
  rcases hE' with rfl | rfl
  · exact Finset.Subset.rfl
  · rw [labelSupport_commutator, label_swap_word]
    exact Finset.subset_union_left

lemma label_support_subset
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseConjTrace A D) :
    labelSupport D ⊆ labelSupport E := by
  induction A generalizing E with
  | nil =>
      have hED : E = D := by
        simpa [inverseConjTrace] using hE
      subst E
      exact Finset.Subset.rfl
  | cons a A ih =>
      rcases List.mem_flatMap.mp hE with ⟨F, hF, hEF⟩
      exact
        (ih F hF).trans
          (label_conjugate_atom a F E hEF)

lemma inverse_filter_label
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseConjTrace A D) :
    E ∈ inverseConjTrace (A.filter fun a => a ∈ labelSupport E) D := by
  induction A generalizing E with
  | nil =>
      simpa [inverseConjTrace] using hE
  | cons a A ih =>
      rcases List.mem_flatMap.mp hE with ⟨F, hF, hEF⟩
      have hFsupportE :=
        label_conjugate_atom a F E hEF
      have hfilter :
          List.Sublist
            (A.filter fun z => z ∈ labelSupport F)
            (A.filter fun z => z ∈ labelSupport E) :=
        filter_sublist_imp
          (fun z => z ∈ labelSupport F)
          (fun z => z ∈ labelSupport E)
          (fun z hz => by
            simpa using hFsupportE (by simpa using hz)) A
      have hF' :
          F ∈ inverseConjTrace (A.filter fun z => z ∈ labelSupport E) D :=
        (inverse_trace_sublist D hfilter).subset
          (ih F hF)
      by_cases haE : a ∈ labelSupport E
      · simpa [haE, inverseConjTrace] using
          (List.mem_flatMap.mpr ⟨F, hF', hEF⟩)
      · have hEF' :
            E = F ∨ E = .commutator (rootSwapWord F) (.atom a) := by
          simpa [inverseConjugateAtom] using hEF
        rcases hEF' with rfl | hcorrection
        · simpa [haE] using hF'
        · subst E
          exfalso
          exact haE (by simp [labelSupport_commutator, label_swap_word])

lemma label_subset_conj
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseConjTrace A D) :
    labelSupport E ⊆ A.toFinset ∪ labelSupport D := by
  induction A generalizing E with
  | nil =>
      have hED : E = D := by
        simpa [inverseConjTrace] using hE
      subst E
      simp
  | cons a A ih =>
      rcases List.mem_flatMap.mp hE with ⟨F, hF, hEF⟩
      have hEFsupport := label_subset_atom a F E hEF
      have hFsupport := ih F hF
      intro z hz
      have hz : z ∈ insert a (labelSupport F) := hEFsupport hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · simp
      · have hz' : z ∈ A.toFinset ∪ labelSupport D := hFsupport hz
        simpa [List.toFinset_cons, Finset.insert_union] using
          (Finset.mem_insert_of_mem hz')

lemma label_conj_trace
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    {D : CWord (LabelledAtom M N)}
    (hA : A.Nodup)
    (hAD : Disjoint A.toFinset (labelSupport D))
    (hD : LabelLinear D) :
    ∀ E ∈ inverseConjTrace A D,
      LabelLinear E := by
  induction A with
  | nil =>
      intro E hE
      have hED : E = D := by
        simpa [inverseConjTrace] using hE
      subst E
      exact hD
  | cons a A ih =>
      intro E hE
      rcases List.mem_flatMap.mp hE with ⟨F, hF, hEF⟩
      have haA_not : a ∉ A := (List.nodup_cons.mp hA).1
      have hA' : A.Nodup := (List.nodup_cons.mp hA).2
      have hADinsert : Disjoint (insert a A.toFinset) (labelSupport D) := by
        simpa [List.toFinset_cons] using hAD
      have hAD' : Disjoint A.toFinset (labelSupport D) :=
        Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hADinsert
      have hFlinear := ih hA' hAD' F hF
      have haF : a ∉ labelSupport F := by
        intro haF
        have ha :
            a ∈ A.toFinset ∪ labelSupport D :=
          label_subset_conj A D F hF haF
        rcases Finset.mem_union.mp ha with haA | haD
        · exact haA_not (List.mem_toFinset.mp haA)
        · exact Finset.disjoint_left.mp hADinsert (by simp) haD
      exact label_atom_trace a hFlinear haF E hEF

lemma inverse_trace_positive
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    {D : CWord (LabelledAtom M N)}
    (hD : (collapseWord D).PBPos) :
    ∀ E ∈ inverseConjTrace A D,
      (collapseWord E).PBPos := by
  induction A with
  | nil =>
      intro E hE
      have hED : E = D := by
        simpa [inverseConjTrace] using hE
      subst E
      exact hD
  | cons a A ih =>
      intro E hE
      rcases List.mem_flatMap.mp hE with ⟨F, hF, hEF⟩
      exact collapse_atom_positive a (ih F hF) E hEF

lemma inverse_list_positive
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    {L : List (CWord (LabelledAtom M N))}
    (hL : ∀ D ∈ L, (collapseWord D).PBPos) :
    ∀ E ∈ inverseTraceList A L,
      (collapseWord E).PBPos := by
  intro E hE
  rcases List.mem_flatMap.mp hE with ⟨D, hD, hED⟩
  exact inverse_trace_positive A (hL D hD) E hED

lemma labelled_list_inverse
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N))
    (hD : (collapseWord D).PBPos) :
    labelledListEval (inverseConjTrace A D) =
      labelledAtomList A * D.eval FreeGroup.of *
        (labelledAtomList A)⁻¹ := by
  induction A with
  | nil =>
      simp [inverseConjTrace, labelledListEval, labelledAtomList]
  | cons a A ih =>
      rw [inverseConjTrace, labelled_eval_flat]
      rw [show
          (List.map
              (fun E => labelledListEval (inverseConjugateAtom a E))
              (inverseConjTrace A D)).prod =
            (List.map
              (fun E =>
                FreeGroup.of a * E.eval FreeGroup.of * (FreeGroup.of a)⁻¹)
              (inverseConjTrace A D)).prod by
          congr 1
          apply List.map_congr_left
          intro E hE
          rw [labelled_atom_trace a E
            (inverse_trace_positive A hD E hE)]]
      rw [show
          (List.map
              (fun E =>
                FreeGroup.of a * E.eval FreeGroup.of * (FreeGroup.of a)⁻¹)
              (inverseConjTrace A D)).prod =
            FreeGroup.of a * labelledListEval (inverseConjTrace A D) *
              (FreeGroup.of a)⁻¹ by
          simpa [labelledListEval, List.map_map, Function.comp_def] using
            (list_prod_conjugates (FreeGroup.of a)
              ((inverseConjTrace A D).map fun E => E.eval FreeGroup.of))]
      rw [ih]
      simp [labelledAtomList]
      group

lemma labelled_list_trace
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N)))
    (hL : ∀ D ∈ L, (collapseWord D).PBPos) :
    labelledListEval (inverseTraceList A L) =
      labelledAtomList A * labelledListEval L *
        (labelledAtomList A)⁻¹ := by
  rw [inverseTraceList, labelled_eval_flat]
  rw [show
      (List.map (fun D => labelledListEval (inverseConjTrace A D)) L).prod =
        (List.map
          (fun D =>
            labelledAtomList A * D.eval FreeGroup.of *
              (labelledAtomList A)⁻¹)
          L).prod by
      congr 1
      apply List.map_congr_left
      intro D hD
      rw [labelled_list_inverse A D (hL D hD)]]
  rw [show
      (List.map
          (fun D =>
            labelledAtomList A * D.eval FreeGroup.of *
              (labelledAtomList A)⁻¹)
          L).prod =
        labelledAtomList A * labelledListEval L *
          (labelledAtomList A)⁻¹ by
      simpa [labelledListEval, List.map_map, Function.comp_def] using
        (list_prod_conjugates (labelledAtomList A)
          (L.map fun D => D.eval FreeGroup.of))]

/-- Expand `[x, y₀ ... yₙ]` using inverse-oriented conjugation traces. -/
def inverseRightTrace
    {M N : ℕ}
    (x : LabelledAtom M N) :
    List (LabelledAtom M N) →
      List (CWord (LabelledAtom M N))
  | [] => []
  | y :: ys =>
      .commutator (.atom x) (.atom y) ::
        inverseTraceList [y] (inverseRightTrace x ys)

lemma relabel_right_trace
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (x : LabelledAtom M N) :
    ∀ ys : List (LabelledAtom M N),
      inverseRightTrace (relabelLabel left right x)
          (ys.map (relabelLabel left right)) =
        (inverseRightTrace x ys).map (relabelWord left right)
  | [] => by simp [inverseRightTrace]
  | y :: ys => by
      rw [List.map_cons, inverseRightTrace, inverseRightTrace,
        relabel_right_trace, List.map_cons]
      congr 1
      · cases x <;> cases y <;> rfl
      · simpa using
          (relabel_inverse_list left right [y]
            (inverseRightTrace x ys))

lemma inverse_right_sublist
    {M N : ℕ}
    (x : LabelledAtom M N)
    {ys zs : List (LabelledAtom M N)}
    (h : List.Sublist ys zs) :
    List.Sublist (inverseRightTrace x ys) (inverseRightTrace x zs) := by
  induction h with
  | slnil =>
      simp [inverseRightTrace]
  | @cons _ _ y h ih =>
      simpa [inverseRightTrace] using
        ih.trans
          ((sublist_inverse_self [y] _).cons
            (.commutator (.atom x) (.atom y)))
  | @cons_cons _ _ y h ih =>
      simpa [inverseRightTrace] using
        List.Sublist.cons_cons (.commutator (.atom x) (.atom y))
          (inverse_conj_sublist (List.Sublist.refl [y]) ih)

lemma inverse_right_positive
    {M N : ℕ}
    {x : LabelledAtom M N}
    (hx : collapseLabel x = .left) :
    ∀ ys : List (LabelledAtom M N),
      (∀ y ∈ ys, collapseLabel y = .right) →
        ∀ D ∈ inverseRightTrace x ys,
          (collapseWord D).PBPos
  | [], _hys => by
      simp [inverseRightTrace]
  | y :: ys, hys => by
      intro D hD
      simp only [inverseRightTrace, List.mem_cons] at hD
      rcases hD with rfl | hD
      · have hy : collapseLabel y = .right := hys y (by simp)
        simp [collapseWord, CWord.PBPos, hx, hy]
      · exact
          inverse_list_positive [y]
            (inverse_right_positive hx ys fun z hz => hys z (by simp [hz]))
            D hD

lemma label_subset_inverse
    {M N : ℕ}
    (x : LabelledAtom M N) :
    ∀ ys : List (LabelledAtom M N),
      ∀ D ∈ inverseRightTrace x ys,
        labelSupport D ⊆ insert x ys.toFinset
  | [], D, hD => by
      simp [inverseRightTrace] at hD
  | y :: ys, D, hD => by
      simp only [inverseRightTrace, List.mem_cons] at hD
      rcases hD with rfl | hD
      · intro z hz
        simp only [labelSupport, Finset.mem_union, Finset.mem_singleton,
          List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at hz ⊢
        rcases hz with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · rcases List.mem_flatMap.mp hD with ⟨F, hF, hDF⟩
        have hDFsupport := label_subset_conj [y] F D hDF
        have hFsupport := label_subset_inverse x ys F hF
        intro z hz
        have hz' : z ∈ [y].toFinset ∪ labelSupport F := hDFsupport hz
        rcases Finset.mem_union.mp hz' with hy | hF
        · have : z = y := by simpa using hy
          subst z
          simp
        · have hz'' : z ∈ insert x ys.toFinset := hFsupport hF
          rcases Finset.mem_insert.mp hz'' with rfl | hzys
          · simp
          · simp [hzys]

lemma label_support_right
    {M N : ℕ}
    (x : LabelledAtom M N) :
    ∀ ys : List (LabelledAtom M N),
      ∀ D ∈ inverseRightTrace x ys,
        x ∈ labelSupport D
  | [], D, hD => by
      simp [inverseRightTrace] at hD
  | y :: ys, D, hD => by
      simp only [inverseRightTrace, List.mem_cons] at hD
      rcases hD with rfl | hD
      · simp [labelSupport]
      · rcases List.mem_flatMap.mp hD with ⟨F, hF, hDF⟩
        exact
          label_support_subset [y] F D hDF
            (label_support_right x ys F hF)

lemma inverse_label_support
    {M N : ℕ}
    (x : LabelledAtom M N) :
    ∀ ys : List (LabelledAtom M N),
      ∀ D ∈ inverseRightTrace x ys,
        D ∈ inverseRightTrace x (ys.filter fun y => y ∈ labelSupport D)
  | [], D, hD => by
      simp [inverseRightTrace] at hD
  | y :: ys, D, hD => by
      simp only [inverseRightTrace, List.mem_cons] at hD
      rcases hD with rfl | hD
      · simp [inverseRightTrace, labelSupport]
      · rcases List.mem_flatMap.mp hD with ⟨F, hF, hDF⟩
        have hFsupportD :=
          label_support_subset [y] F D hDF
        have hfilter :
            List.Sublist
              (ys.filter fun z => z ∈ labelSupport F)
              (ys.filter fun z => z ∈ labelSupport D) :=
          filter_sublist_imp
            (fun z => z ∈ labelSupport F)
            (fun z => z ∈ labelSupport D)
            (fun z hz => by
              simpa using hFsupportD (by simpa using hz)) ys
        have hF' :
            F ∈ inverseRightTrace x (ys.filter fun z => z ∈ labelSupport D) :=
          (inverse_right_sublist x hfilter).subset
            (inverse_label_support x ys F hF)
        by_cases hyD : y ∈ labelSupport D
        · have hfilter_cons :
              (y :: ys).filter (fun z => z ∈ labelSupport D) =
                y :: ys.filter (fun z => z ∈ labelSupport D) := by
            simp [hyD]
          rw [hfilter_cons, inverseRightTrace, List.mem_cons]
          exact Or.inr (List.mem_flatMap.mpr ⟨F, hF', hDF⟩)
        · have hDF' :
              D = F ∨ D = .commutator (rootSwapWord F) (.atom y) := by
            simpa [inverseConjTrace, inverseConjugateAtom] using hDF
          rcases hDF' with rfl | hcorrection
          · simpa [hyD] using hF'
          · subst D
            exfalso
            exact hyD (by simp [labelSupport_commutator, label_swap_word])

lemma ne_collapse_label
    {M N : ℕ}
    {x y : LabelledAtom M N}
    (hx : collapseLabel x = .left)
    (hy : collapseLabel y = .right) :
    x ≠ y := by
  intro hxy
  subst y
  rw [hx] at hy
  cases hy

lemma label_linear_inverse
    {M N : ℕ}
    {x : LabelledAtom M N}
    (hx : collapseLabel x = .left) :
    ∀ ys : List (LabelledAtom M N),
      ys.Nodup →
        (∀ y ∈ ys, collapseLabel y = .right) →
          ∀ D ∈ inverseRightTrace x ys,
            LabelLinear D
  | [], _hysNodup, _hys => by
      simp [inverseRightTrace]
  | y :: ys, hysNodup, hys => by
      intro D hD
      simp only [inverseRightTrace, List.mem_cons] at hD
      have hy : collapseLabel y = .right := hys y (by simp)
      have hxy : x ≠ y := ne_collapse_label hx hy
      rcases hD with rfl | hD
      · simp [LabelLinear, labelSupport, hxy]
      · rcases List.mem_flatMap.mp hD with ⟨F, hF, hDF⟩
        have hFlinear :=
          label_linear_inverse hx ys hysNodup.tail
            (fun z hz => hys z (by simp [hz])) F hF
        have hyF : y ∉ labelSupport F := by
          intro hyF
          have hySupport :
              y ∈ insert x ys.toFinset :=
            label_subset_inverse x ys F hF hyF
          have hy_not_mem : y ∉ ys := (List.nodup_cons.mp hysNodup).1
          rcases Finset.mem_insert.mp hySupport with hyx | hys
          · exact hxy hyx.symm
          · exact hy_not_mem (List.mem_toFinset.mp hys)
        exact label_atom_trace y hFlinear hyF D hDF

lemma labelled_inverse_right
    {M N : ℕ}
    (x : LabelledAtom M N)
    (hx : collapseLabel x = .left) :
    ∀ ys : List (LabelledAtom M N),
      (∀ y ∈ ys, collapseLabel y = .right) →
        labelledListEval (inverseRightTrace x ys) =
          ⁅FreeGroup.of x, labelledAtomList ys⁆
  | [], _hys => by
      simp [inverseRightTrace, labelledListEval, labelledAtomList]
  | y :: ys, hys => by
      rw [inverseRightTrace, labelled_eval_cons, CWord.eval_commutator,
        labelled_list_trace [y] (inverseRightTrace x ys)
          (inverse_right_positive hx ys fun z hz => hys z (by simp [hz])),
        labelled_inverse_right x hx ys fun z hz => hys z (by simp [hz])]
      change
        ⁅FreeGroup.of x, FreeGroup.of y⁆ *
              (FreeGroup.of y * ⁅FreeGroup.of x, labelledAtomList ys⁆ *
                (FreeGroup.of y)⁻¹) =
          ⁅FreeGroup.of x, FreeGroup.of y * labelledAtomList ys⁆
      rw [element_mul_right]
      group

/-- Expand `[x₀ ... xₘ, y₀ ... yₙ]` through the inverse-oriented trace. -/
def inverseLeftTrace
    {M N : ℕ} :
    List (LabelledAtom M N) →
      List (LabelledAtom M N) →
        List (CWord (LabelledAtom M N))
  | [], _ys => []
  | x :: xs, ys =>
      inverseTraceList [x] (inverseLeftTrace xs ys) ++
        inverseRightTrace x ys

lemma relabel_inverse_trace
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ xs ys : List (LabelledAtom M N),
      inverseLeftTrace
          (xs.map (relabelLabel left right))
          (ys.map (relabelLabel left right)) =
        (inverseLeftTrace xs ys).map (relabelWord left right)
  | [], ys => by simp [inverseLeftTrace]
  | x :: xs, ys => by
      rw [List.map_cons, inverseLeftTrace, inverseLeftTrace,
        relabel_inverse_trace, List.map_append]
      congr 1
      · simpa using
          (relabel_inverse_list left right [x]
            (inverseLeftTrace xs ys))
      · exact relabel_right_trace left right x ys

lemma sublist_append_self
    {α : Type*}
    (L R : List α) :
    List.Sublist L (L ++ R) := by
  simpa only [List.append_nil] using
    (List.Sublist.refl L).append (List.nil_sublist R)

lemma left_right_sublist
    {M N : ℕ}
    (xs : List (LabelledAtom M N))
    {ys zs : List (LabelledAtom M N)}
    (hys : List.Sublist ys zs) :
    List.Sublist (inverseLeftTrace xs ys) (inverseLeftTrace xs zs) := by
  induction xs with
  | nil =>
      simp [inverseLeftTrace]
  | cons x xs ih =>
      rw [inverseLeftTrace, inverseLeftTrace]
      exact
        List.Sublist.append
          (inverse_conj_sublist (List.Sublist.refl [x]) ih)
          (inverse_right_sublist x hys)

lemma right_trace_sublist
    {M N : ℕ}
    (ys : List (LabelledAtom M N))
    {xs zs : List (LabelledAtom M N)}
    (h : List.Sublist xs zs) :
    List.Sublist (inverseLeftTrace xs ys) (inverseLeftTrace zs ys) := by
  induction h with
  | slnil =>
      simp [inverseLeftTrace]
  | @cons _ _ x h ih =>
      simpa [inverseLeftTrace] using
        ih.trans
          ((sublist_inverse_self [x] _).trans
            (sublist_append_self _ _))
  | @cons_cons _ _ x h ih =>
      simpa [inverseLeftTrace] using
        List.Sublist.append
          (inverse_conj_sublist (List.Sublist.refl [x]) ih)
          (List.Sublist.refl (inverseRightTrace x ys))

lemma inverse_left_sublist
    {M N : ℕ}
    {xs zs ys ws : List (LabelledAtom M N)}
    (hxs : List.Sublist xs zs)
    (hys : List.Sublist ys ws) :
    List.Sublist (inverseLeftTrace xs ys) (inverseLeftTrace zs ws) :=
  (right_trace_sublist ys hxs).trans
    (left_right_sublist zs hys)

lemma fn_sublist_embedding
    {m n : ℕ}
    (f : Fin m ↪o Fin n) :
    List.Sublist (List.ofFn f) (List.ofFn fun i : Fin n => i) := by
  apply List.sublist_of_subperm_of_sortedLE
  · apply List.subperm_of_subset
    · exact List.nodup_ofFn_ofInjective f.injective
    · intro i hi
      simp
  · exact f.monotone.sortedLE_ofFn
  · exact monotone_id.sortedLE_ofFn

lemma relabel_labelled_sublist
    {M N M' N' : ℕ}
    (left : Fin M ↪o Fin M')
    (right : Fin N ↪o Fin N') :
    List.Sublist
      ((labelledLeftAtoms M N).map (relabelLabel left right))
      (labelledLeftAtoms M' N') := by
  simpa [labelledLeftAtoms, List.ofFn_eq_map, List.map_map,
    Function.comp_def, relabelLabel] using
    (fn_sublist_embedding left).map
      (fun i : Fin M' => (Sum.inl i : LabelledAtom M' N'))

lemma relabel_label_sublist
    {M N M' N' : ℕ}
    (left : Fin M ↪o Fin M')
    (right : Fin N ↪o Fin N') :
    List.Sublist
      ((labelledRightAtoms M N).map (relabelLabel left right))
      (labelledRightAtoms M' N') := by
  simpa [labelledRightAtoms, List.ofFn_eq_map, List.map_map,
    Function.comp_def, relabelLabel] using
    (fn_sublist_embedding right).map
      (fun j : Fin N' => (Sum.inr j : LabelledAtom M' N'))

lemma relabel_atoms_sublist
    {M N M' N' : ℕ}
    (left : Fin M ↪o Fin M')
    (right : Fin N ↪o Fin N') :
    List.Sublist
      ((inverseLeftTrace (labelledLeftAtoms M N) (labelledRightAtoms M N)).map
        (relabelWord left right))
      (inverseLeftTrace (labelledLeftAtoms M' N') (labelledRightAtoms M' N')) := by
  rw [← relabel_inverse_trace left right]
  exact
    inverse_left_sublist
      (relabel_labelled_sublist left right)
      (relabel_label_sublist left right)

lemma inverse_left_positive
    {M N : ℕ} :
    ∀ xs ys : List (LabelledAtom M N),
      (∀ x ∈ xs, collapseLabel x = .left) →
        (∀ y ∈ ys, collapseLabel y = .right) →
          ∀ D ∈ inverseLeftTrace xs ys,
            (collapseWord D).PBPos
  | [], _ys, _hxs, _hys => by
      simp [inverseLeftTrace]
  | x :: xs, ys, hxs, hys => by
      intro D hD
      rw [inverseLeftTrace, List.mem_append] at hD
      have hx : collapseLabel x = .left := hxs x (by simp)
      rcases hD with hD | hD
      · exact
          inverse_list_positive [x]
            (inverse_left_positive xs ys
              (fun z hz => hxs z (by simp [hz])) hys)
            D hD
      · exact inverse_right_positive hx ys hys D hD

lemma label_subset_trace
    {M N : ℕ} :
    ∀ xs ys : List (LabelledAtom M N),
      ∀ D ∈ inverseLeftTrace xs ys,
        labelSupport D ⊆ xs.toFinset ∪ ys.toFinset
  | [], _ys, D, hD => by
      simp [inverseLeftTrace] at hD
  | x :: xs, ys, D, hD => by
      rw [inverseLeftTrace, List.mem_append] at hD
      rcases hD with hD | hD
      · rcases List.mem_flatMap.mp hD with ⟨F, hF, hDF⟩
        have hDFsupport := label_subset_conj [x] F D hDF
        have hFsupport := label_subset_trace xs ys F hF
        intro z hz
        have hz' : z ∈ [x].toFinset ∪ labelSupport F := hDFsupport hz
        rcases Finset.mem_union.mp hz' with hx | hF
        · have : z = x := by simpa using hx
          subst z
          simp
        · have hz'' : z ∈ xs.toFinset ∪ ys.toFinset := hFsupport hF
          rcases Finset.mem_union.mp hz'' with hxs | hys
          · simp [hxs]
          · simp [hys]
      · have hDsupport := label_subset_inverse x ys D hD
        intro z hz
        have hz' : z ∈ insert x ys.toFinset := hDsupport hz
        rcases Finset.mem_insert.mp hz' with rfl | hys
        · simp
        · simp [hys]

lemma filter_label_support
    {M N : ℕ} :
    ∀ xs ys : List (LabelledAtom M N),
      ∀ D ∈ inverseLeftTrace xs ys,
        D ∈ inverseLeftTrace
          (xs.filter fun x => x ∈ labelSupport D)
          (ys.filter fun y => y ∈ labelSupport D)
  | [], _ys, D, hD => by
      simp [inverseLeftTrace] at hD
  | x :: xs, ys, D, hD => by
      rw [inverseLeftTrace, List.mem_append] at hD
      rcases hD with hD | hD
      · rcases List.mem_flatMap.mp hD with ⟨F, hF, hDF⟩
        have hFsupportD :=
          label_support_subset [x] F D hDF
        have hxsFilter :
            List.Sublist
              (xs.filter fun z => z ∈ labelSupport F)
              (xs.filter fun z => z ∈ labelSupport D) :=
          filter_sublist_imp
            (fun z => z ∈ labelSupport F)
            (fun z => z ∈ labelSupport D)
            (fun z hz => by
              simpa using hFsupportD (by simpa using hz)) xs
        have hysFilter :
            List.Sublist
              (ys.filter fun z => z ∈ labelSupport F)
              (ys.filter fun z => z ∈ labelSupport D) :=
          filter_sublist_imp
            (fun z => z ∈ labelSupport F)
            (fun z => z ∈ labelSupport D)
            (fun z hz => by
              simpa using hFsupportD (by simpa using hz)) ys
        have hF' :
            F ∈ inverseLeftTrace
              (xs.filter fun z => z ∈ labelSupport D)
              (ys.filter fun z => z ∈ labelSupport D) :=
          (inverse_left_sublist hxsFilter hysFilter).subset
            (filter_label_support xs ys F hF)
        by_cases hxD : x ∈ labelSupport D
        · have hfilter_cons :
              (x :: xs).filter (fun z => z ∈ labelSupport D) =
                x :: xs.filter (fun z => z ∈ labelSupport D) := by
            simp [hxD]
          rw [hfilter_cons, inverseLeftTrace, List.mem_append]
          exact Or.inl (List.mem_flatMap.mpr ⟨F, hF', hDF⟩)
        · have hDF' :
              D = F ∨ D = .commutator (rootSwapWord F) (.atom x) := by
            simpa [inverseConjTrace, inverseConjugateAtom] using hDF
          rcases hDF' with rfl | hcorrection
          · simpa [hxD] using hF'
          · subst D
            exfalso
            exact hxD (by simp [labelSupport_commutator, label_swap_word])
      · have hxD := label_support_right x ys D hD
        have hD' := inverse_label_support x ys D hD
        have hfilter_cons :
            (x :: xs).filter (fun z => z ∈ labelSupport D) =
              x :: xs.filter (fun z => z ∈ labelSupport D) := by
          simp [hxD]
        rw [hfilter_cons, inverseLeftTrace, List.mem_append]
        exact Or.inr hD'

lemma relabel_labelled_atoms
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hpositive : (collapseWord w).PBPos)
    (hlinear : LabelLinear w)
    (hw :
      w ∈ inverseLeftTrace (labelledLeftAtoms M N) (labelledRightAtoms M N)) :
    relabelWord
        (supportRank (leftLabelSupport w)
          (label_support_positive hlinear hpositive))
        (supportRank (rightLabelSupport w)
          (label_nonempty_positive hlinear hpositive))
        w ∈
      inverseLeftTrace
        (labelledLeftAtoms (leftLabelSupport w).card (rightLabelSupport w).card)
        (labelledRightAtoms (leftLabelSupport w).card (rightLabelSupport w).card) := by
  let hleft := label_support_positive hlinear hpositive
  let hright := label_nonempty_positive hlinear hpositive
  have hw' :=
    filter_label_support
      (labelledLeftAtoms M N) (labelledRightAtoms M N) w hw
  have hmap :
      relabelWord
          (supportRank (leftLabelSupport w) hleft)
          (supportRank (rightLabelSupport w) hright) w ∈
        (inverseLeftTrace
            ((labelledLeftAtoms M N).filter fun a => a ∈ labelSupport w)
            ((labelledRightAtoms M N).filter fun a => a ∈ labelSupport w)).map
          (relabelWord
            (supportRank (leftLabelSupport w) hleft)
            (supportRank (rightLabelSupport w) hright)) :=
    List.mem_map.mpr ⟨w, hw', rfl⟩
  rw [← relabel_inverse_trace
      (supportRank (leftLabelSupport w) hleft)
      (supportRank (rightLabelSupport w) hright)] at hmap
  rw [relabel_label_labelled w hleft hright,
    relabel_label_atoms w hleft hright] at hmap
  exact hmap

lemma LRecipe.labellinword_meminvleft_rigtralabato
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hpositive : (collapseWord w).PBPos)
    (hlinear : LabelLinear w)
    (hw :
      w ∈ inverseLeftTrace (labelledLeftAtoms M N) (labelledRightAtoms M N)) :
    (LRecipe.ofLabelLinear w hpositive hlinear).word ∈
      inverseLeftTrace
        (labelledLeftAtoms
          (LRecipe.ofLabelLinear w hpositive hlinear).leftDegree
          (LRecipe.ofLabelLinear w hpositive hlinear).rightDegree)
        (labelledRightAtoms
          (LRecipe.ofLabelLinear w hpositive hlinear).leftDegree
          (LRecipe.ofLabelLinear w hpositive hlinear).rightDegree) := by
  simpa only [LRecipe.ofLabelLinear] using
    relabel_labelled_atoms
      w hpositive hlinear hw

lemma LRecipe.instme_leftr_labea
    {M N : ℕ}
    (R : LRecipe)
    (hR :
      R.word ∈ inverseLeftTrace
        (labelledLeftAtoms R.leftDegree R.rightDegree)
        (labelledRightAtoms R.leftDegree R.rightDegree))
    (left : Fin R.leftDegree ↪o Fin M)
    (right : Fin R.rightDegree ↪o Fin N) :
    R.instantiate left right ∈
      inverseLeftTrace (labelledLeftAtoms M N) (labelledRightAtoms M N) := by
  apply (relabel_atoms_sublist left right).subset
  simpa [LRecipe.instantiate] using
    (List.mem_map.mpr ⟨R.word, hR, rfl⟩)

lemma label_linear_trace
    {M N : ℕ} :
    ∀ xs ys : List (LabelledAtom M N),
      xs.Nodup →
        ys.Nodup →
          (∀ x ∈ xs, collapseLabel x = .left) →
            (∀ y ∈ ys, collapseLabel y = .right) →
              ∀ D ∈ inverseLeftTrace xs ys,
                LabelLinear D
  | [], _ys, _hxsNodup, _hysNodup, _hxs, _hys => by
      simp [inverseLeftTrace]
  | x :: xs, ys, hxsNodup, hysNodup, hxs, hys => by
      intro D hD
      rw [inverseLeftTrace, List.mem_append] at hD
      have hx : collapseLabel x = .left := hxs x (by simp)
      have hx_not_mem : x ∉ xs := (List.nodup_cons.mp hxsNodup).1
      rcases hD with hD | hD
      · rcases List.mem_flatMap.mp hD with ⟨F, hF, hDF⟩
        have hFlinear :=
          label_linear_trace xs ys hxsNodup.tail hysNodup
            (fun z hz => hxs z (by simp [hz])) hys F hF
        have hxF : x ∉ labelSupport F := by
          intro hxF
          have hxSupport :
              x ∈ xs.toFinset ∪ ys.toFinset :=
            label_subset_trace xs ys F hF hxF
          rcases Finset.mem_union.mp hxSupport with hxsMem | hysMem
          · exact hx_not_mem (List.mem_toFinset.mp hxsMem)
          · have hy : collapseLabel x = .right :=
              hys x (List.mem_toFinset.mp hysMem)
            rw [hx] at hy
            cases hy
        have hxFdisjoint : Disjoint ({x} : Finset (LabelledAtom M N)) (labelSupport F) :=
          Finset.disjoint_singleton_left.mpr hxF
        exact
          label_conj_trace [x] (by simp) hxFdisjoint hFlinear D hDF
      · exact label_linear_inverse hx ys hysNodup hys D hD

lemma labelled_right_trace
    {M N : ℕ} :
    ∀ xs ys : List (LabelledAtom M N),
      (∀ x ∈ xs, collapseLabel x = .left) →
        (∀ y ∈ ys, collapseLabel y = .right) →
          labelledListEval (inverseLeftTrace xs ys) =
            ⁅labelledAtomList xs, labelledAtomList ys⁆
  | [], ys, _hxs, _hys => by
      simp [inverseLeftTrace, labelledListEval, labelledAtomList]
  | x :: xs, ys, hxs, hys => by
      have hx : collapseLabel x = .left := hxs x (by simp)
      rw [inverseLeftTrace, labelled_eval_append,
        labelled_list_trace [x] (inverseLeftTrace xs ys)
          (inverse_left_positive xs ys
            (fun z hz => hxs z (by simp [hz])) hys),
        labelled_right_trace xs ys
          (fun z hz => hxs z (by simp [hz])) hys,
        labelled_inverse_right x hx ys hys]
      change
        (FreeGroup.of x *
              ⁅labelledAtomList xs, labelledAtomList ys⁆ *
                (FreeGroup.of x)⁻¹) *
              ⁅FreeGroup.of x, labelledAtomList ys⁆ =
          ⁅FreeGroup.of x * labelledAtomList xs, labelledAtomList ys⁆
      rw [element_mul_left]

/--
The exact labelled source trace with inverse-oriented local conjugation
corrections.
-/
def inverseLabelledCollection
    (M N : ℕ) :
    LabelledCollection M N where
  factors := inverseLeftTrace (labelledLeftAtoms M N) (labelledRightAtoms M N)
  eval_eq := by
    simpa [labelled_left_atoms,
      labelled_atom_atoms] using
      (labelled_right_trace
        (labelledLeftAtoms M N) (labelledRightAtoms M N)
        (fun x hx => collapse_label_atoms hx)
        (fun y hy => collapse_labelled_atoms hy))
  factors_positive := by
    exact
      inverse_left_positive
        (labelledLeftAtoms M N) (labelledRightAtoms M N)
        (fun x hx => collapse_label_atoms hx)
        (fun y hy => collapse_labelled_atoms hy)

lemma inverse_labelled_linear
    (M N : ℕ) :
    ∀ D ∈ (inverseLabelledCollection M N).factors,
      LabelLinear D := by
  exact
    label_linear_trace
      (labelledLeftAtoms M N) (labelledRightAtoms M N)
      (by
        simp only [labelledLeftAtoms]
        exact List.nodup_ofFn_ofInjective fun _ _ h => Sum.inl.inj h)
      (by
        simp only [labelledRightAtoms]
        exact List.nodup_ofFn_ofInjective fun _ _ h => Sum.inr.inj h)
      (fun x hx => collapse_label_atoms hx)
      (fun y hy => collapse_labelled_atoms hy)

lemma LRecipe.meminv_labecollmem_instmemtrac
    {M N : ℕ}
    (R : LRecipe)
    (hR :
      R.word ∈ inverseLeftTrace
        (labelledLeftAtoms R.leftDegree R.rightDegree)
        (labelledRightAtoms R.leftDegree R.rightDegree))
    (w : CWord (LabelledAtom M N))
    (hw : w ∈ R.instantiations M N) :
    w ∈ (inverseLabelledCollection M N).factors := by
  rw [LRecipe.mem_instantiations_iff] at hw
  rcases hw with ⟨left, right, rfl⟩
  simpa [inverseLabelledCollection] using
    LRecipe.instme_leftr_labea
      R hR left right

lemma LRecipe.labellin_instantimem_invlabecoll
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hw : w ∈ (inverseLabelledCollection M N).factors) :
    ∀ D ∈
        (LRecipe.ofLabelLinear w
          ((inverseLabelledCollection M N).factors_positive w hw)
          (inverse_labelled_linear M N w hw)).instantiations M N,
      D ∈ (inverseLabelledCollection M N).factors := by
  intro D hD
  exact
    LRecipe.meminv_labecollmem_instmemtrac
      (LRecipe.ofLabelLinear w
        ((inverseLabelledCollection M N).factors_positive w hw)
        (inverse_labelled_linear M N w hw))
      (LRecipe.labellinword_meminvleft_rigtralabato
        w
        ((inverseLabelledCollection M N).factors_positive w hw)
        (inverse_labelled_linear M N w hw)
        hw)
      D hD

/-- The basic admissible coefficient attached to one linear erased recipe. -/
def linearChooseFactor
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hpositive : (collapseWord w).PBPos) :
    Factor M N where
  word := collapseWord w
  coefficient :=
    (Nat.choose M (collapseWord w).pairLeftDegree : ℤ) *
      (Nat.choose N (collapseWord w).pairRightDegree : ℤ)
  positive := hpositive
  coefficient_admissible :=
    choose_mul_submodule M N
      (collapseWord w).pairLeftDegree
      (collapseWord w).pairRightDegree

/-- Decorate the inverse-oriented raw trace by its occurrence index. -/
def inverseDecoratedCollection
    (M N : ℕ) :
    DColl M N
      (inverseLeftTrace (labelledLeftAtoms M N) (labelledRightAtoms M N)).length where
  factors :=
    decorateRaw (inverseLeftTrace (labelledLeftAtoms M N) (labelledRightAtoms M N))
  eval_eq := by
    rw [decorated_decorate_raw]
    simpa using (inverseLabelledCollection M N).eval_eq
  factors_positive := by
    exact decorateRaw_positive (inverseLabelledCollection M N).factors_positive
  factors_support_nonempty := by
    intro T hT
    rcases List.mem_ofFn.mp hT with ⟨index, rfl⟩
    exact DTerm.support_raw_nonempty _ _

/-- Counted one-block recipe witnesses for every inverse raw trace occurrence. -/
noncomputable def inverseDecoratedTerms
    (M N : ℕ) :
    List (DFTerm M N (inverseLabelledCollection M N).factors.length) :=
  List.ofFn fun index =>
    let word := (inverseLabelledCollection M N).factors.get index
    DFTerm.ofLabelLinear
      (DTerm.raw word index)
      ((inverseLabelledCollection M N).factors_positive word
        (List.get_mem _ index))
      (inverse_labelled_linear M N word
        (List.get_mem _ index))

lemma decorated_inverse_terms
    (M N : ℕ) :
    (inverseDecoratedTerms M N).map DFTerm.decorated =
      (inverseDecoratedCollection M N).factors := by
  simp [inverseDecoratedTerms, inverseDecoratedCollection, decorateRaw,
    DFTerm.ofLabelLinear, inverseLabelledCollection,
    Function.comp_def]

lemma list_decorated_terms
    (M N : ℕ) :
    DFTerm.listEval (inverseDecoratedTerms M N) =
      ⁅labelledLeft M N, labelledRight M N⁆ := by
  rw [DFTerm.list_eval_decorated,
    decorated_inverse_terms]
  exact (inverseDecoratedCollection M N).eval_eq

/-- Counted output of the inverse raw trace. -/
structure IndependentDecoratedTerms
    (M N : ℕ) where
  factors :
    List (DFTerm M N (inverseLabelledCollection M N).factors.length)
  eval_eq :
    DFTerm.listEval factors =
      ⁅labelledLeft M N, labelledRight M N⁆
  decorated_collects :
    ICollec
      ((inverseDecoratedTerms M N).map DFTerm.decorated)
      (factors.map DFTerm.decorated)

lemma nonempty_independent_decorated
    (M N : ℕ) :
    Nonempty
      (IndependentDecoratedTerms M N) := by
  have hinputSupport :
      SupportNonemptyList
        ((inverseDecoratedTerms M N).map DFTerm.decorated) := by
    rw [decorated_inverse_terms]
    exact (inverseDecoratedCollection M N).factors_support_nonempty
  rcases DFTerm.independent_collects_ready
      (DFTerm.independentCollectReady
        (inverseDecoratedTerms M N) hinputSupport) with
    ⟨factors, hcollect⟩
  exact ⟨{
    factors := factors
    eval_eq := by
      rw [DFTerm.list_independent_collects hcollect]
      exact list_decorated_terms M N
    decorated_collects :=
      DFTerm.independent_collects hcollect }⟩

/-- Counted-family More3 output together with its exact labelled product. -/
structure CDTerms
    (M N : ℕ) where
  factors :
    List (DFTerm M N (inverseLabelledCollection M N).factors.length)
  eval_eq :
    DFTerm.listEval factors =
      ⁅labelledLeft M N, labelledRight M N⁆
  family_collects :
    DFTerm.Collects (inverseDecoratedTerms M N) factors
  decorated_collects :
    ICollec
      ((inverseDecoratedTerms M N).map DFTerm.decorated)
      (factors.map DFTerm.decorated)

def decoratedFamilyList
    {M N K : ℕ}
    (L : List (DFTerm M N K)) :
    List (CWord (LabelledAtom M N)) :=
  L.map fun T => T.decorated.word

lemma labelled_decorated_family
    {M N K : ℕ}
    (L : List (DFTerm M N K)) :
    labelledListEval (decoratedFamilyList L) =
      DFTerm.listEval L := by
  rw [decoratedFamilyList, labelledListEval, DFTerm.listEval,
    List.map_map]
  rfl

/--
Final counted-family certificate needed for compression: the concrete
collected words are already an ordered concatenation of complete counted
families.
-/
structure CFExpa
    (M N K : ℕ) where
  terms :
    List (DFTerm M N K)
  families :
    List (BFam M N)
  realization_list_words :
    BFam.realizationList families =
      decoratedFamilyList terms
  eval_eq :
    DFTerm.listEval terms =
      ⁅labelledLeft M N, labelledRight M N⁆

namespace CFExpa

def blockExpansion
    {M N K : ℕ}
    (E : CFExpa M N K) :
    BFam.Expansion M N where
  families := E.families
  collapsed_eval_eq := by
    calc
      collapsedListEval (BFam.realizationList E.families) =
          collapseHom M N
            (labelledListEval (BFam.realizationList E.families)) :=
        (collapse_labelled_eval _).symm
      _ = collapseHom M N (DFTerm.listEval E.terms) := by
        rw [E.realization_list_words, labelled_decorated_family]
      _ = collapseHom M N ⁅labelledLeft M N, labelledRight M N⁆ := by
        rw [E.eval_eq]
      _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
        rw [map_commutatorElement, collapse_labelled_left,
          collapse_labelled_right]

lemma exists_canonicalFactors
    {M N K : ℕ}
    (E : CFExpa M N K) :
    ∃ factors : List (Factor M N),
      listEval universalLeft universalRight factors =
        ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  exact ⟨E.blockExpansion.factors,
    E.blockExpansion.listEval_factors⟩

end CFExpa

lemma nonempty_decorated_ready
    (M N : ℕ)
    (hready : DFTerm.CollectReady
      (inverseDecoratedTerms M N)) :
    Nonempty
      (CDTerms M N) := by
  rcases DFTerm.collects_collect_ready hready with
    ⟨factors, hcollect⟩
  exact ⟨{
    factors := factors
    eval_eq := by
      rw [DFTerm.listEval_collects hcollect]
      exact list_decorated_terms M N
    family_collects := hcollect
    decorated_collects := DFTerm.decorated_map_collects hcollect }⟩


end HACoeff
end Submission
