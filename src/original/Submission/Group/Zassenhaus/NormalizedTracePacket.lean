import Submission.Group.Zassenhaus.SignedHeadNormalization

/-!
# Exact Hall-Witt trace with conventional Jacobi heads

The signed Hall-Witt packet evaluates exactly to the inverse original triple.
Its two signed heads now have exact finite normalization traces.  Replacing
the retained intermediate occurrences in place produces a packet whose only
possible weight-three factors are the conventional Jacobi descendants
`[[x, z], y]⁻¹` and `[[y, z], x]`.

All other factors have formal weight at least four.  The packet preserves the
operational order of every correction occurrence, so a later collector can
recollect the strict tail without a same-stratum semantic callback.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace WNTrace

open HACoeff
open CWTrace
open WSTrace
open WHNorm

/-- First signed head with its unique intermediate replaced in place. -/
def firstNormalizedHead :
    List (CWord Atom) :=
  replaceWordTrace firstIntermediateWord firstPrincipalNormalization
    firstHeadTrace

/-- Second signed head with its unique intermediate replaced in place. -/
def secondNormalizedHead :
    List (CWord Atom) :=
  replaceWordTrace secondIntermediateWord secondPrincipalNormalization
    secondHeadTrace

@[simp]
lemma first_conventional_inverse :
    firstConventionalInverse.weight (fun _ => 1) = 3 := by
  simp [firstConventionalInverse, weight_root_swap]

/-- In-place normalization preserves the exact value of the first signed
head. -/
lemma normalized_head_trace
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) firstNormalizedHead =
      firstSignedWord.eval (signedEval x y z) := by
  rw [firstNormalizedHead,
    word_replace_trace (signedEval x y z) firstIntermediateWord
      firstPrincipalNormalization firstHeadTrace
      (principal_normalization_trace x y z),
    first_head_trace]

/-- In-place normalization preserves the exact value of the second signed
head. -/
lemma second_normalized_head
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) secondNormalizedHead =
      secondSignedWord.eval (signedEval x y z) := by
  rw [secondNormalizedHead,
    word_replace_trace (signedEval x y z) secondIntermediateWord
      secondPrincipalNormalization secondHeadTrace
      (second_principal_normalization x y z),
    second_signed_head]

/-- The normalized first signed-head packet has one possible weight-three
factor: `[[x, z], y]⁻¹`. -/
lemma conventional_or_head
    (word : CWord Atom)
    (hword : word ∈ firstNormalizedHead) :
    word = firstConventionalInverse ∨
      4 ≤ word.weight (fun _ => 1) := by
  rcases
      source_replace_trace firstIntermediateWord
        firstPrincipalNormalization firstHeadTrace word hword with
    ⟨source, hsource, hreplacement | hretained⟩
  · rcases hreplacement with ⟨rfl, hword⟩
    rw [first_principal_normalization] at hword
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hword
    rcases hword with heq | heq
    · exact Or.inl heq
    · subst word
      exact Or.inr (by simp)
  · rcases hretained with ⟨hne, heq⟩
    rcases
        intermediate_or_head
          source hsource with
      heq | hweight
    · exact False.elim (hne heq)
    · exact Or.inr (by simpa [heq] using hweight)

/-- The normalized second signed-head packet has one possible weight-three
factor: `[[y, z], x]`. -/
lemma second_conventional_head
    (word : CWord Atom)
    (hword : word ∈ secondNormalizedHead) :
    word = secondConventionalWord ∨
      4 ≤ word.weight (fun _ => 1) := by
  rcases
      source_replace_trace secondIntermediateWord
        secondPrincipalNormalization secondHeadTrace word hword with
    ⟨source, hsource, hreplacement | hretained⟩
  · rcases hreplacement with ⟨rfl, hword⟩
    rw [second_normalization_corrections] at hword
    rcases List.mem_append.mp hword with hcorrection | hretained
    · exact
        Or.inr
          (four_second_principal word
            hcorrection)
    · exact Or.inl (List.mem_singleton.mp hretained)
  · rcases hretained with ⟨hne, heq⟩
    rcases
        second_intermediate_head
          source hsource with
      heq | hweight
    · exact False.elim (hne heq)
    · exact Or.inr (by simpa [heq] using hweight)

/--
Exact Hall-Witt trace with both signed heads normalized to conventional Jacobi
descendants.  Branch strict tails remain in their original operational order.
-/
def trace :
    List (CWord Atom) :=
  firstNormalizedHead ++
    branchCorrectionTrace xAtom zAtom firstSignedWord ++
      secondNormalizedHead ++
        branchCorrectionTrace xAtom yAtom secondSignedWord

/-- The normalized packet still evaluates exactly to the inverse original
triple commutator. -/
lemma word_original_inv
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) trace =
      (originalWord.eval (signedEval x y z))⁻¹ := by
  calc
    wordListEval (signedEval x y z) trace =
        wordListEval (signedEval x y z)
          (firstSignedWord ::
            branchCorrectionTrace xAtom zAtom firstSignedWord ++
              secondSignedWord ::
                branchCorrectionTrace xAtom yAtom secondSignedWord) := by
      simp [trace, word_list_append,
        normalized_head_trace,
        second_normalized_head]
    _ = labelledEval (signedEval x y z)
        WSTrace.trace := by
      rw [first_corrections_second]
      rfl
    _ = (originalWord.eval (signedEval x y z))⁻¹ :=
      labelled_original_inv x y z

/--
Every normalized Hall-Witt factor is one of the two conventional
weight-three Jacobi heads or lies strictly above that layer.
-/
lemma conventional_or_second
    (word : CWord Atom)
    (hword : word ∈ trace) :
    word = firstConventionalInverse ∨
      word = secondConventionalWord ∨
        4 ≤ word.weight (fun _ => 1) := by
  simp only [trace, List.mem_append] at hword
  rcases hword with hrest | hsecondCorrection
  · rcases hrest with hrest | hsecond
    · rcases hrest with hfirst | hfirstCorrection
      · rcases
            conventional_or_head
              word hfirst with
          heq | hweight
        · exact Or.inl heq
        · exact Or.inr (Or.inr hweight)
      · exact
          Or.inr
            (Or.inr
              (four_correction_trace word (by
                rw [correctionTrace, List.mem_append]
                exact Or.inl hfirstCorrection)))
    · rcases
          second_conventional_head
            word hsecond with
        heq | hweight
      · exact Or.inr (Or.inl heq)
      · exact Or.inr (Or.inr hweight)
  · exact
      Or.inr
        (Or.inr
          (four_correction_trace word (by
            rw [correctionTrace, List.mem_append]
            exact Or.inr hsecondCorrection)))

end WNTrace
end TCTex
end Submission
