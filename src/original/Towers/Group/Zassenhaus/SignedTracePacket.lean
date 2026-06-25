import Towers.Group.Zassenhaus.ConjTraceEvaluation

/-!
# Exact signed Hall-Witt trace packet

The rearranged Hall-Witt identity expresses the inverse of `[[x, y], z]` as
two conjugated triple commutators with signed inputs.  This file records that
identity as a finite labelled inverse trace.

Each branch retains one signed triple head.  Every other occurrence belongs
to an explicit strict inverse-conjugation correction list and has formal
weight at least four.  Thus the packet separates the current Jacobi layer
from exact higher-weight conjugation corrections without invoking a
same-stratum semantic normalizer.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace WSTrace

open scoped commutatorElement

open HACoeff

/--
Six signed labels, grouped by Hall-pair side:
`x`, `x⁻¹`, `z`, `z⁻¹` on the left and `y`, `y⁻¹` on the right.
-/
abbrev Atom :=
  LabelledAtom 4 2

def xAtom : Atom := Sum.inl 0
def xInvAtom : Atom := Sum.inl 1
def zAtom : Atom := Sum.inl 2
def zInvAtom : Atom := Sum.inl 3
def yAtom : Atom := Sum.inr 0
def yInvAtom : Atom := Sum.inr 1

/-- Interpret the six formal labels as three ambient elements and inverses. -/
def signedEval
    {G : Type*}
    [Group G]
    (x y z : G) :
    Atom → G
  | .inl index =>
      Fin.cases x
        (fun index =>
          Fin.cases x⁻¹
            (fun index =>
              Fin.cases z (fun _ => z⁻¹) index)
            index)
        index
  | .inr index =>
      Fin.cases y (fun _ => y⁻¹) index

@[simp] lemma signedEval_x
    {G : Type*} [Group G] (x y z : G) :
    signedEval x y z xAtom = x :=
  rfl

@[simp] lemma eval_x_inv
    {G : Type*} [Group G] (x y z : G) :
    signedEval x y z xInvAtom = x⁻¹ :=
  rfl

@[simp] lemma signedEval_z
    {G : Type*} [Group G] (x y z : G) :
    signedEval x y z zAtom = z :=
  rfl

@[simp] lemma eval_z_inv
    {G : Type*} [Group G] (x y z : G) :
    signedEval x y z zInvAtom = z⁻¹ :=
  rfl

@[simp] lemma signedEval_y
    {G : Type*} [Group G] (x y z : G) :
    signedEval x y z yAtom = y :=
  rfl

@[simp] lemma eval_y_inv
    {G : Type*} [Group G] (x y z : G) :
    signedEval x y z yInvAtom = y⁻¹ :=
  rfl

/-- The original left-normed Jacobi triple `[[x, y], z]`. -/
def originalWord :
    CWord Atom :=
  .commutator
    (.commutator (.atom xAtom) (.atom yAtom))
    (.atom zAtom)

/-- First Hall-Witt signed head `[[z⁻¹, x⁻¹], y]`. -/
def firstSignedWord :
    CWord Atom :=
  .commutator
    (.commutator (.atom zInvAtom) (.atom xInvAtom))
    (.atom yAtom)

/-- Second Hall-Witt signed head `[[y⁻¹, z], x⁻¹]`. -/
def secondSignedWord :
    CWord Atom :=
  .commutator
    (.commutator (.atom yInvAtom) (.atom zAtom))
    (.atom xInvAtom)

@[simp]
lemma first_signed_positive :
    (collapseWord firstSignedWord).PBPos := by
  simp [firstSignedWord, zInvAtom, xInvAtom, yAtom, collapseWord, collapseLabel,
    CWord.PBPos]

@[simp]
lemma second_signed_positive :
    (collapseWord secondSignedWord).PBPos := by
  simp [secondSignedWord, yInvAtom, zAtom, xInvAtom, collapseWord, collapseLabel,
    CWord.PBPos]

/-- One doubly conjugated signed Hall-Witt branch. -/
def branchTrace
    (outer inner : Atom)
    (word : CWord Atom) :
    List (CWord Atom) :=
  inverseTraceList [outer] (inverseConjTrace [inner] word)

/--
The strict corrections in one doubly conjugated branch, after retaining its
signed triple head.
-/
def branchCorrectionTrace
    (outer inner : Atom)
    (word : CWord Atom) :
    List (CWord Atom) :=
  inverseConjCorrection [outer] word ++
    inverseTraceList [outer] (inverseConjCorrection [inner] word)

/-- A branch is its retained signed head followed by strict corrections. -/
lemma branch_cons_correction
    (outer inner : Atom)
    (word : CWord Atom) :
    branchTrace outer inner word =
      word :: branchCorrectionTrace outer inner word := by
  rw [branchTrace, branchCorrectionTrace, inverseTraceList,
    inverse_cons_correction]
  simp only [List.flatMap_cons]
  rw [inverse_cons_correction]
  rw [inverseTraceList]
  rfl

/-- Every branch correction lies at least one formal stratum above its head. -/
lemma succ_branch_trace
    (wt : Atom → ℕ)
    (hwt : ∀ atom, 0 < wt atom)
    (outer inner : Atom)
    (word correction : CWord Atom)
    (hcorrection : correction ∈
      branchCorrectionTrace outer inner word) :
    word.weight wt + 1 ≤ correction.weight wt := by
  rcases List.mem_append.mp hcorrection with houter | hinner
  · exact
      succ_conj_trace wt hwt [outer] word
        correction houter
  · rcases
        inverse_conj_list wt [outer]
          (inverseConjCorrection [inner] word) correction hinner with
      ⟨source, hsource, hsourceCorrection⟩
    exact
      (succ_conj_trace wt hwt [inner] word
        source hsource).trans hsourceCorrection

/-- Exact finite Hall-Witt trace, retaining its two signed triple heads. -/
def trace :
    List (CWord Atom) :=
  branchTrace xAtom zAtom firstSignedWord ++
    branchTrace xAtom yAtom secondSignedWord

/-- Strict higher-weight part of the exact finite Hall-Witt trace. -/
def correctionTrace :
    List (CWord Atom) :=
  branchCorrectionTrace xAtom zAtom firstSignedWord ++
    branchCorrectionTrace xAtom yAtom secondSignedWord

/-- The exact packet displays its two weight-three heads in operational order. -/
lemma first_corrections_second :
    trace =
      firstSignedWord ::
        branchCorrectionTrace xAtom zAtom firstSignedWord ++
          secondSignedWord ::
            branchCorrectionTrace xAtom yAtom secondSignedWord := by
  rw [trace, branch_cons_correction,
    branch_cons_correction]

@[simp]
lemma first_signed_word :
    firstSignedWord.weight (fun _ => 1) = 3 := by
  rfl

@[simp]
lemma second_signed_word :
    secondSignedWord.weight (fun _ => 1) = 3 := by
  rfl

/-- Every non-head Hall-Witt trace occurrence has formal weight at least four. -/
lemma four_correction_trace
    (correction : CWord Atom)
    (hcorrection : correction ∈ correctionTrace) :
    4 ≤ correction.weight (fun _ => 1) := by
  rcases List.mem_append.mp hcorrection with hfirst | hsecond
  · simpa only [first_signed_word] using
      (succ_branch_trace
        (fun _ => 1) (fun _ => by simp) xAtom zAtom firstSignedWord
          correction hfirst)
  · simpa only [second_signed_word] using
      (succ_branch_trace
        (fun _ => 1) (fun _ => by simp) xAtom yAtom secondSignedWord
          correction hsecond)

/-- Evaluation of one doubly conjugated branch under any substitution. -/
lemma labelled_branch_trace
    {G : Type*}
    [Group G]
    (f : Atom → G)
    (outer inner : Atom)
    (word : CWord Atom)
    (hword : (collapseWord word).PBPos) :
    labelledEval f (branchTrace outer inner word) =
      f outer * (f inner * word.eval f * (f inner)⁻¹) *
        (f outer)⁻¹ := by
  rw [branchTrace,
    labelled_inverse_conj f [outer]
      (inverseConjTrace [inner] word)
      (inverse_trace_positive [inner] hword),
    labelled_list_conj f [inner] word hword]
  simp [labelledAtomEval]

/--
The finite signed trace evaluates exactly to the inverse original triple
commutator.  This is the rearranged Hall-Witt identity with every conjugation
expanded as an inverse-oriented trace.
-/
lemma labelled_original_inv
    {G : Type*}
    [Group G]
    (x y z : G) :
    labelledEval (signedEval x y z) trace =
      (originalWord.eval (signedEval x y z))⁻¹ := by
  rw [trace, labelled_list_append,
    labelled_branch_trace (signedEval x y z) xAtom zAtom
      firstSignedWord first_signed_positive,
    labelled_branch_trace (signedEval x y z) xAtom yAtom
      secondSignedWord second_signed_positive]
  simp only [signedEval_x, signedEval_y, signedEval_z]
  simp [originalWord, firstSignedWord, secondSignedWord,
    CWord.eval_commutator, commutatorElement_def]
  group

end WSTrace
end TCTex
end Towers
