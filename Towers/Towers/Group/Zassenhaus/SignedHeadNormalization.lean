import Towers.Group.Zassenhaus.SignedTracePacket
import Towers.Group.Zassenhaus.CommutatorWordTrace

/-!
# Exact normalization of the two signed Hall-Witt heads

The exact Hall-Witt trace retains two signed triple heads:

* `[[z⁻¹, x⁻¹], y]`;
* `[[y⁻¹, z], x⁻¹]`.

Each signed inner bracket is an exact conjugate of a root-swapped ordinary
bracket.  The word-level product trace distributes the outer bracket across
that conjugation trace.  In each branch there is one weight-three
intermediate; every other occurrence has weight at least four.

The first intermediate is an exact conjugate of `[[x, z], y]⁻¹`.  The second
is an exact conjugate of `[[y, z], x]`.  Their normalization traces retain
those conventional Jacobi descendants and expose only strictly heavier
corrections.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace WHNorm

open scoped commutatorElement

open HACoeff
open CWTrace
open WSTrace

/-- Ordinary bracket `[x, z]`. -/
def xzWord :
    CWord Atom :=
  .commutator (.atom xAtom) (.atom zAtom)

/-- Ordinary bracket `[y, z]`. -/
def yzWord :
    CWord Atom :=
  .commutator (.atom yAtom) (.atom zAtom)

/-- Conventional first Jacobi descendant `[[x, z], y]`. -/
def firstConventionalWord :
    CWord Atom :=
  .commutator xzWord (.atom yAtom)

/-- Conventional second Jacobi descendant `[[y, z], x]`. -/
def secondConventionalWord :
    CWord Atom :=
  .commutator yzWord (.atom xAtom)

/-- Root-swapped first conventional descendant, evaluating to
`[[x, z], y]⁻¹`. -/
def firstConventionalInverse :
    CWord Atom :=
  rootSwapWord firstConventionalWord

/-- The first weight-three intermediate `[[z, x], y]`. -/
def firstIntermediateWord :
    CWord Atom :=
  .commutator (rootSwapWord xzWord) (.atom yAtom)

/-- The second weight-three intermediate `[[z, y], x⁻¹]`. -/
def secondIntermediateWord :
    CWord Atom :=
  .commutator (rootSwapWord yzWord) (.atom xInvAtom)

@[simp] lemma weight_xzWord :
    xzWord.weight (fun _ => 1) = 2 :=
  rfl

@[simp] lemma weight_yzWord :
    yzWord.weight (fun _ => 1) = 2 :=
  rfl

@[simp] lemma weight_first_conventional :
    firstConventionalWord.weight (fun _ => 1) = 3 :=
  rfl

@[simp] lemma weight_conventional_word :
    secondConventionalWord.weight (fun _ => 1) = 3 :=
  rfl

@[simp] lemma first_intermediate_word :
    firstIntermediateWord.weight (fun _ => 1) = 3 := by
  simp [firstIntermediateWord, weight_root_swap]

@[simp] lemma second_intermediate_word :
    secondIntermediateWord.weight (fun _ => 1) = 3 := by
  simp [secondIntermediateWord, weight_root_swap]

/-- Exact trace for the signed inner bracket `[z⁻¹, x⁻¹]`. -/
def firstInnerTrace :
    List (CWord Atom) :=
  conjTrace [zInvAtom, xInvAtom] (rootSwapWord xzWord)

/-- Exact trace for the signed inner bracket `[y⁻¹, z]`. -/
def secondInnerTrace :
    List (CWord Atom) :=
  conjTrace [yInvAtom] (rootSwapWord yzWord)

/-- The first inner trace is its strict correction prefix followed by
`[z, x]`. -/
lemma first_corrections_append :
    firstInnerTrace =
      conjCorrectionTrace [zInvAtom, xInvAtom] (rootSwapWord xzWord) ++
        [rootSwapWord xzWord] := by
  rw [firstInnerTrace, correction_append_singleton]

/-- The second inner trace is its strict correction prefix followed by
`[z, y]`. -/
lemma second_corrections_append :
    secondInnerTrace =
      conjCorrectionTrace [yInvAtom] (rootSwapWord yzWord) ++
        [rootSwapWord yzWord] := by
  rw [secondInnerTrace, correction_append_singleton]

/-- The first inner trace evaluates exactly to `[z⁻¹, x⁻¹]`. -/
lemma labelled_inner_trace
    {G : Type*}
    [Group G]
    (x y z : G) :
    labelledEval (signedEval x y z) firstInnerTrace =
      (CWord.commutator (.atom zInvAtom) (.atom xInvAtom)).eval
        (signedEval x y z) := by
  rw [firstInnerTrace,
    eval_conj_trace (signedEval x y z)
      [zInvAtom, xInvAtom] (rootSwapWord xzWord)]
  simp [labelledAtomEval, xzWord, rootSwapWord,
    CWord.eval_commutator, commutatorElement_def]
  group

/-- The second inner trace evaluates exactly to `[y⁻¹, z]`. -/
lemma labelled_second_inner
    {G : Type*}
    [Group G]
    (x y z : G) :
    labelledEval (signedEval x y z) secondInnerTrace =
      (CWord.commutator (.atom yInvAtom) (.atom zAtom)).eval
        (signedEval x y z) := by
  rw [secondInnerTrace,
    eval_conj_trace (signedEval x y z)
      [yInvAtom] (rootSwapWord yzWord)]
  simp [labelledAtomEval, yzWord, rootSwapWord,
    CWord.eval_commutator, commutatorElement_def]
  group

/-- Every first-inner occurrence has weight at least two. -/
lemma first_inner_trace
    (word : CWord Atom)
    (hword : word ∈ firstInnerTrace) :
    2 ≤ word.weight (fun _ => 1) := by
  rw [first_corrections_append] at hword
  simp only [List.mem_append, List.mem_singleton] at hword
  rcases hword with hword | rfl
  · have hweight :=
      succ_conj_correction
        (fun _ => 1) (fun _ => by simp) [zInvAtom, xInvAtom]
          (rootSwapWord xzWord) word hword
    simpa only [weight_root_swap, weight_xzWord] using
      (Nat.le_trans (by omega : 2 ≤ 2 + 1) hweight)
  · simp [weight_root_swap]

/-- Every second-inner occurrence has weight at least two. -/
lemma second_inner_trace
    (word : CWord Atom)
    (hword : word ∈ secondInnerTrace) :
    2 ≤ word.weight (fun _ => 1) := by
  rw [second_corrections_append] at hword
  simp only [List.mem_append, List.mem_singleton] at hword
  rcases hword with hword | rfl
  · have hweight :=
      succ_conj_correction
        (fun _ => 1) (fun _ => by simp) [yInvAtom]
          (rootSwapWord yzWord) word hword
    simpa only [weight_root_swap, weight_yzWord] using
      (Nat.le_trans (by omega : 2 ≤ 2 + 1) hweight)
  · simp [weight_root_swap]

/-- Exact word-level expansion of `[[z⁻¹, x⁻¹], y]`. -/
def firstHeadTrace :
    List (CWord Atom) :=
  leftWordTrace firstInnerTrace [.atom yAtom]

/-- Exact word-level expansion of `[[y⁻¹, z], x⁻¹]`. -/
def secondHeadTrace :
    List (CWord Atom) :=
  leftWordTrace secondInnerTrace [.atom xInvAtom]

/-- The first word-level trace evaluates exactly to the first Hall-Witt head. -/
lemma first_head_trace
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) firstHeadTrace =
      firstSignedWord.eval (signedEval x y z) := by
  rw [firstHeadTrace, left_right_trace]
  simp only [word_list_cons, word_list_nil, mul_one]
  change
    labelledEval (signedEval x y z) firstInnerTrace |> fun inner =>
      ⁅inner, y⁆ =
        firstSignedWord.eval (signedEval x y z)
  rw [labelled_inner_trace]
  rfl

/-- The second word-level trace evaluates exactly to the second Hall-Witt
head. -/
lemma second_signed_head
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) secondHeadTrace =
      secondSignedWord.eval (signedEval x y z) := by
  rw [secondHeadTrace, left_right_trace]
  simp only [word_list_cons, word_list_nil, mul_one]
  change
    labelledEval (signedEval x y z) secondInnerTrace |> fun inner =>
      ⁅inner, x⁻¹⁆ =
        secondSignedWord.eval (signedEval x y z)
  rw [labelled_second_inner]
  rfl

/-- Every first signed-head trace occurrence has weight at least three. -/
lemma three_head_trace
    (word : CWord Atom)
    (hword : word ∈ firstHeadTrace) :
    3 ≤ word.weight (fun _ => 1) := by
  exact
    add_left_trace (fun _ => 1) 2 1 firstInnerTrace
      [.atom yAtom] first_inner_trace
        (by
          intro right hright
          simp only [List.mem_singleton] at hright
          subst right
          rfl)
        word hword

/-- Every second signed-head trace occurrence has weight at least three. -/
lemma second_head_trace
    (word : CWord Atom)
    (hword : word ∈ secondHeadTrace) :
    3 ≤ word.weight (fun _ => 1) := by
  exact
    add_left_trace (fun _ => 1) 2 1 secondInnerTrace
      [.atom xInvAtom] second_inner_trace
        (by
          intro right hright
          simp only [List.mem_singleton] at hright
          subst right
          rfl)
        word hword

/-- The first word-level expansion contains its weight-three intermediate. -/
lemma first_intermediate_head :
    firstIntermediateWord ∈ firstHeadTrace := by
  rw [firstHeadTrace, first_corrections_append]
  exact
    principal_append_singleton
      (conjCorrectionTrace [zInvAtom, xInvAtom] (rootSwapWord xzWord))
        (rootSwapWord xzWord) (.atom yAtom)

/-- The second word-level expansion contains its weight-three intermediate. -/
lemma intermediate_head_trace :
    secondIntermediateWord ∈ secondHeadTrace := by
  rw [secondHeadTrace, second_corrections_append]
  exact
    principal_append_singleton
      (conjCorrectionTrace [yInvAtom] (rootSwapWord yzWord))
        (rootSwapWord yzWord) (.atom xInvAtom)

/-- Apart from the retained intermediate, every first-head occurrence has
weight at least four. -/
lemma intermediate_or_head
    (word : CWord Atom)
    (hword : word ∈ firstHeadTrace) :
    word = firstIntermediateWord ∨
      4 ≤ word.weight (fun _ => 1) := by
  rw [firstHeadTrace, first_corrections_append] at hword
  simpa only [firstIntermediateWord, first_intermediate_word] using
    (principal_or_singleton
      (fun _ => 1)
      (conjCorrectionTrace [zInvAtom, xInvAtom] (rootSwapWord xzWord))
      (rootSwapWord xzWord) (.atom yAtom) word
      (fun correction hcorrection =>
        succ_conj_correction
          (fun _ => 1) (fun _ => by simp) [zInvAtom, xInvAtom]
            (rootSwapWord xzWord) correction hcorrection)
      hword)

/-- Apart from the retained intermediate, every second-head occurrence has
weight at least four. -/
lemma second_intermediate_head
    (word : CWord Atom)
    (hword : word ∈ secondHeadTrace) :
    word = secondIntermediateWord ∨
      4 ≤ word.weight (fun _ => 1) := by
  rw [secondHeadTrace, second_corrections_append] at hword
  simpa only [secondIntermediateWord, second_intermediate_word] using
    (principal_or_singleton
      (fun _ => 1)
      (conjCorrectionTrace [yInvAtom] (rootSwapWord yzWord))
      (rootSwapWord yzWord) (.atom xInvAtom) word
      (fun correction hcorrection =>
        succ_conj_correction
          (fun _ => 1) (fun _ => by simp) [yInvAtom]
            (rootSwapWord yzWord) correction hcorrection)
      hword)

/-- Retained-head exact normalization of `[[z, x], y]` toward
`[[x, z], y]⁻¹`. -/
def firstPrincipalNormalization :
    List (CWord Atom) :=
  inverseConjugateTrace (rootSwapWord xzWord)
    firstConventionalInverse

/-- Strict first-principal correction, of weight five. -/
def firstPrincipalWord :
    CWord Atom :=
  .commutator (rootSwapWord firstConventionalInverse)
    (rootSwapWord xzWord)

lemma first_principal_normalization :
    firstPrincipalNormalization =
      [firstConventionalInverse, firstPrincipalWord] :=
  rfl

@[simp]
lemma weight_first_principal :
    firstPrincipalWord.weight (fun _ => 1) = 5 := by
  simp [firstPrincipalWord, firstConventionalInverse,
    weight_root_swap]

/-- The first principal normalization trace evaluates exactly to its
intermediate. -/
lemma principal_normalization_trace
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) firstPrincipalNormalization =
      firstIntermediateWord.eval (signedEval x y z) := by
  simp [firstPrincipalNormalization, inverseConjugateTrace,
    firstConventionalInverse, firstConventionalWord,
    firstIntermediateWord, xzWord, rootSwapWord, wordListEval,
    CWord.eval_commutator, commutatorElement_def]
  group

/-- Exact normalization of `[[z, y], x⁻¹]` toward `[[y, z], x]`. -/
def secondPrincipalNormalization :
    List (CWord Atom) :=
  wordConjTrace [rootSwapWord yzWord, .atom xInvAtom] secondConventionalWord

/-- Strict corrections before the conventional second Jacobi descendant. -/
def secondPrincipalTrace :
    List (CWord Atom) :=
  wordConjCorrection [rootSwapWord yzWord, .atom xInvAtom]
    secondConventionalWord

/-- The second principal normalization retains the conventional descendant
after a strict correction prefix. -/
lemma second_normalization_corrections :
    secondPrincipalNormalization =
      secondPrincipalTrace ++ [secondConventionalWord] := by
  rw [secondPrincipalNormalization, secondPrincipalTrace,
    conj_append_singleton]

/-- Every strict second-principal correction has weight at least four. -/
lemma four_second_principal
    (word : CWord Atom)
    (hword : word ∈ secondPrincipalTrace) :
    4 ≤ word.weight (fun _ => 1) := by
  simpa only [weight_conventional_word] using
    (succ_correction_trace
      (fun _ => 1) [rootSwapWord yzWord, .atom xInvAtom]
        secondConventionalWord word
        (by
          intro conjugator hconjugator
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hconjugator
          rcases hconjugator with rfl | rfl
          · simp [weight_root_swap]
          · simp)
        hword)

/-- The second principal normalization trace evaluates exactly to its
intermediate. -/
lemma second_principal_normalization
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) secondPrincipalNormalization =
      secondIntermediateWord.eval (signedEval x y z) := by
  rw [secondPrincipalNormalization, list_conj_trace]
  simp [secondConventionalWord, secondIntermediateWord, yzWord, rootSwapWord,
    wordListEval, CWord.eval_commutator, commutatorElement_def]
  group

end WHNorm
end TCTex
end Towers
