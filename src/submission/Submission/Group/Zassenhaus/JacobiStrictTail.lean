import Submission.Group.Zassenhaus.NormalizedTracePacket

/-!
# Exact strict tail for the unit Jacobi packet

Append the two forward Jacobi descendants to the normalized Hall-Witt trace.
The four remaining weight-three occurrences are

`B⁻¹, C, B, C⁻¹`,

where `B = [[x, z], y]` and `C = [[y, z], x]`.  Stable routing moves those
four occurrences to the right across the explicit higher trace, emitting
exact commutator corrections.  Their suffix is the single weight-six
commutator `[B⁻¹, C]`.

Consequently the unit Jacobi value packet has an exact finite representative
all of whose factors have weight at least four.  No associated-graded
simplification or same-stratum semantic normalizer appears in this packet.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace WSTail

open HACoeff
open CWTrace
open WSTrace
open WHNorm
open WNTrace

/-- Root-swapped second descendant, evaluating to `[[y, z], x]⁻¹`. -/
def secondConventionalInverse :
    CWord Atom :=
  rootSwapWord secondConventionalWord

@[simp]
lemma weight_second_conventional :
    secondConventionalInverse.weight (fun _ => 1) = 3 := by
  simp [secondConventionalInverse, weight_root_swap]

/-- Replace the original inverse triple in the forward Jacobi packet by its
exact normalized Hall-Witt trace. -/
def jacobiResidualTrace :
    List (CWord Atom) :=
  WNTrace.trace ++
    [firstConventionalWord, secondConventionalInverse]

/-- The expanded trace evaluates exactly to the unit Jacobi residual
`A⁻¹ B C⁻¹`. -/
lemma jacobi_residual_trace
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) jacobiResidualTrace =
      (originalWord.eval (signedEval x y z))⁻¹ *
        (firstConventionalWord.eval (signedEval x y z) *
          (secondConventionalWord.eval (signedEval x y z))⁻¹) := by
  rw [jacobiResidualTrace, word_list_append,
    word_original_inv]
  simp [secondConventionalInverse, secondConventionalWord, rootSwapWord,
    wordListEval, CWord.eval_commutator, commutatorElement_def]
  group

/-- Recognize the four current-layer words in the expanded unit packet. -/
def isCurrent
    (word : CWord Atom) :
    Bool :=
  decide
    (word = firstConventionalInverse ∨
      word = secondConventionalWord ∨
        word = firstConventionalWord ∨
          word = secondConventionalInverse)

@[simp] lemma current_conventional_word :
    isCurrent firstConventionalInverse = true := by
  simp [isCurrent]

@[simp] lemma current_second_word :
    isCurrent secondConventionalWord = true := by
  simp [isCurrent]

@[simp] lemma current_first_word :
    isCurrent firstConventionalWord = true := by
  simp [isCurrent]

@[simp] lemma current_conventional_inverse :
    isCurrent secondConventionalInverse = true := by
  simp [isCurrent]

/-- Every recognized current-layer word has weight three. -/
lemma weight_current_true
    (word : CWord Atom)
    (hword : isCurrent word = true) :
    word.weight (fun _ => 1) = 3 := by
  simp only [isCurrent, decide_eq_true_eq] at hword
  rcases hword with rfl | rfl | rfl | rfl <;> simp

/-- Any unselected expanded Jacobi-trace factor is already strictly above the
current layer. -/
lemma four_current_false
    (word : CWord Atom)
    (hword : word ∈ jacobiResidualTrace)
    (hcurrent : isCurrent word = false) :
    4 ≤ word.weight (fun _ => 1) := by
  rw [jacobiResidualTrace, List.mem_append] at hword
  rcases hword with htrace | htail
  · rcases
        conventional_or_second
          word htrace with
      rfl | rfl | hweight
    · simp at hcurrent
    · simp at hcurrent
    · exact hweight
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at htail
    rcases htail with rfl | rfl <;> simp at hcurrent

/-- Stable routing of all four current-layer occurrences to the right. -/
def routed :
    List (CWord Atom) × List (CWord Atom) :=
  stableRoute isCurrent jacobiResidualTrace

/-- The selected current suffix computes to `B⁻¹, C, B, C⁻¹`. -/
lemma routed_snd :
    routed.2 =
      [firstConventionalInverse, secondConventionalWord,
        firstConventionalWord, secondConventionalInverse] := by
  decide

/-- Every occurrence in the routed higher prefix has weight at least four. -/
lemma weight_routed_fst
    (word : CWord Atom)
    (hword : word ∈ routed.1) :
    4 ≤ word.weight (fun _ => 1) := by
  exact
    stable_route_fst (fun _ => 1) 4 isCurrent
      jacobiResidualTrace
        four_current_false word
          hword

/-- Weight-six collapse of the routed current suffix. -/
def currentCorrectionWord :
    CWord Atom :=
  .commutator firstConventionalInverse secondConventionalWord

@[simp]
lemma weight_current_word :
    currentCorrectionWord.weight (fun _ => 1) = 6 := by
  simp [currentCorrectionWord]

/-- The routed current suffix evaluates to its single weight-six commutator. -/
lemma word_routed_snd
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) routed.2 =
      currentCorrectionWord.eval (signedEval x y z) := by
  rw [routed_snd]
  simp [currentCorrectionWord, firstConventionalInverse,
    secondConventionalInverse, firstConventionalWord,
    secondConventionalWord, xzWord, yzWord, rootSwapWord, wordListEval,
    CWord.eval_commutator, commutatorElement_def]
  group

/-- Exact all-higher representative of the unit Jacobi packet. -/
def strictTrace :
    List (CWord Atom) :=
  routed.1 ++ [currentCorrectionWord]

/-- Replacing the routed current suffix by its weight-six commutator preserves
evaluation exactly. -/
lemma strict_jacobi_residual
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) strictTrace =
      wordListEval (signedEval x y z) jacobiResidualTrace := by
  calc
    wordListEval (signedEval x y z) strictTrace =
        wordListEval (signedEval x y z) (routed.1 ++ routed.2) := by
      rw [strictTrace, word_list_append, word_list_append,
        word_list_cons, word_list_nil, mul_one,
        word_routed_snd]
    _ = wordListEval (signedEval x y z) jacobiResidualTrace := by
      exact word_stable_route (signedEval x y z) isCurrent
        jacobiResidualTrace

/-- Exact strict-tail evaluation of the unit Jacobi packet. -/
lemma word_strict_trace
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) strictTrace =
      (originalWord.eval (signedEval x y z))⁻¹ *
        (firstConventionalWord.eval (signedEval x y z) *
          (secondConventionalWord.eval (signedEval x y z))⁻¹) := by
  rw [strict_jacobi_residual,
    jacobi_residual_trace]

/-- Every unit Jacobi strict-tail factor has formal weight at least four. -/
lemma four_weight_strict
    (word : CWord Atom)
    (hword : word ∈ strictTrace) :
    4 ≤ word.weight (fun _ => 1) := by
  rw [strictTrace, List.mem_append] at hword
  rcases hword with hword | hword
  · exact weight_routed_fst word hword
  · rcases List.mem_singleton.mp hword with rfl
    simp

end WSTail
end TCTex
end Submission
