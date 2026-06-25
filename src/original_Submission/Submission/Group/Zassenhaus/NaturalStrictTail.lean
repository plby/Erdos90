import Submission.Group.Zassenhaus.JacobiStrictTail

/-!
# Natural-power strict tails for the Jacobi packet

The unit strict-tail packet extends uniformly to every natural multiplicity.
Repeat the normalized Hall-Witt trace for `A⁻¹`, append `B^m` and `C⁻m`, then
perform two stable routing passes:

1. route `B⁻¹` and `B` occurrences to the right and cancel their suffix;
2. route `C` and `C⁻¹` occurrences to the right and cancel their suffix.

Every swap correction emitted by either pass lies in weight at least four.
The remaining finite trace therefore evaluates exactly to

`A⁻m B^m C⁻m`

and is supported strictly above the original weight-three Jacobi layer.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace NPTail

open HACoeff
open CWTrace
open WSTrace
open WHNorm
open WNTrace
open WSTail

/-- Repeat an ordered finite trace `multiplicity` times. -/
def repeatTrace
    {α : Type*} :
    ℕ → List (CWord α) → List (CWord α)
  | 0, _sourceWords => []
  | multiplicity + 1, sourceWords =>
      sourceWords ++ repeatTrace multiplicity sourceWords

/-- Evaluation of a repeated trace is the corresponding natural power. -/
lemma word_repeat_trace
    {α G : Type*}
    [Group G]
    (f : α → G)
    (trace : List (CWord α)) :
    ∀ multiplicity : ℕ,
      wordListEval f (repeatTrace multiplicity trace) =
        (wordListEval f trace) ^ multiplicity
  | 0 => by
      simp [repeatTrace]
  | multiplicity + 1 => by
      simp [repeatTrace, word_list_append,
        word_repeat_trace f trace multiplicity, pow_succ']

/-- Filtering commutes with finite trace repetition. -/
lemma filter_repeatTrace
    {α : Type*}
    (keep : CWord α → Bool)
    (trace : List (CWord α)) :
    ∀ multiplicity : ℕ,
      (repeatTrace multiplicity trace).filter keep =
        repeatTrace multiplicity (trace.filter keep)
  | 0 => by
      rfl
  | multiplicity + 1 => by
      simp [repeatTrace, List.filter_append,
        filter_repeatTrace keep trace multiplicity]

/-- Repeating a singleton trace is ordinary list replication. -/
lemma repeatTrace_singleton
    {α : Type*}
    (word : CWord α) :
    ∀ multiplicity : ℕ,
      repeatTrace multiplicity [word] =
        List.replicate multiplicity word
  | 0 => by
      rfl
  | multiplicity + 1 => by
      simp [repeatTrace, List.replicate_succ,
        repeatTrace_singleton word multiplicity]

/-- Every occurrence in a repeated trace comes from the repeated source. -/
lemma repeat_trace
    {α : Type*}
    {multiplicity : ℕ}
    {trace : List (CWord α)}
    {word : CWord α}
    (hword : word ∈ repeatTrace multiplicity trace) :
    word ∈ trace := by
  induction multiplicity with
  | zero =>
      simp [repeatTrace] at hword
  | succ multiplicity ih =>
      rw [repeatTrace, List.mem_append] at hword
      rcases hword with hword | hword
      · exact hword
      · exact ih hword

/-- The repeated normalized Hall-Witt traces followed by the two powered
forward descendants. -/
def naturalResidualTrace
    (multiplicity : ℕ) :
    List (CWord Atom) :=
  repeatTrace multiplicity WNTrace.trace ++
    List.replicate multiplicity firstConventionalWord ++
      List.replicate multiplicity secondConventionalInverse

/-- Root-swapping the first conventional descendant evaluates to inversion. -/
@[simp]
lemma conventional_inverse_word
    {G : Type*}
    [Group G]
    (f : Atom → G) :
    firstConventionalInverse.eval f =
      (firstConventionalWord.eval f)⁻¹ := by
  simp [firstConventionalInverse, firstConventionalWord, rootSwapWord,
    CWord.eval_commutator, commutatorElement_def]
  group

/-- Root-swapping the second conventional descendant evaluates to inversion. -/
@[simp]
lemma eval_second_conventional
    {G : Type*}
    [Group G]
    (f : Atom → G) :
    secondConventionalInverse.eval f =
      (secondConventionalWord.eval f)⁻¹ := by
  simp [secondConventionalInverse, secondConventionalWord, rootSwapWord,
    CWord.eval_commutator, commutatorElement_def]
  group

/-- The repeated source evaluates to `A⁻m B^m C⁻m`. -/
lemma natural_residual_trace
    {G : Type*}
    [Group G]
    (x y z : G)
    (multiplicity : ℕ) :
    wordListEval (signedEval x y z) (naturalResidualTrace multiplicity) =
      (originalWord.eval (signedEval x y z))⁻¹ ^ multiplicity *
        (firstConventionalWord.eval (signedEval x y z) ^ multiplicity *
          (secondConventionalWord.eval (signedEval x y z))⁻¹ ^
            multiplicity) := by
  rw [naturalResidualTrace, word_list_append, word_list_append,
    word_repeat_trace, word_original_inv]
  simp [wordListEval, secondConventionalInverse,
    secondConventionalWord, rootSwapWord, CWord.eval_commutator,
    commutatorElement_def]
  group

/-- Recognize the first current family `B⁻¹, B`. -/
def isFirstCurrent
    (word : CWord Atom) :
    Bool :=
  decide
    (word = firstConventionalInverse ∨
      word = firstConventionalWord)

/-- Recognize the second current family `C, C⁻¹`. -/
def isSecondCurrent
    (word : CWord Atom) :
    Bool :=
  decide
    (word = secondConventionalWord ∨
      word = secondConventionalInverse)

@[simp] lemma first_current_conventional :
    isFirstCurrent firstConventionalInverse = true := by
  decide

@[simp] lemma first_conventional_word :
    isFirstCurrent firstConventionalWord = true := by
  decide

@[simp] lemma second_conventional_word :
    isSecondCurrent secondConventionalWord = true := by
  decide

@[simp] lemma second_current_conventional :
    isSecondCurrent secondConventionalInverse = true := by
  decide

@[simp] lemma second_conventional_first :
    secondConventionalInverse ≠ firstConventionalInverse := by
  decide

@[simp] lemma second_conventional_ne :
    secondConventionalInverse ≠ firstConventionalWord := by
  decide

@[simp] lemma first_conventional_ne :
    firstConventionalWord ≠ secondConventionalWord := by
  decide

@[simp] lemma conventional_second_inverse :
    firstConventionalWord ≠ secondConventionalInverse := by
  decide

@[simp] lemma first_second_conventional :
    isFirstCurrent secondConventionalWord = false := by
  decide

@[simp] lemma current_second_conventional :
    isFirstCurrent secondConventionalInverse = false := by
  decide

@[simp] lemma current_first_conventional :
    isSecondCurrent firstConventionalInverse = false := by
  decide

@[simp] lemma second_first_conventional :
    isSecondCurrent firstConventionalWord = false := by
  decide

/-- Every first-family current word has weight three. -/
lemma first_current_true
    (word : CWord Atom)
    (hword : isFirstCurrent word = true) :
    word.weight (fun _ => 1) = 3 := by
  simp only [isFirstCurrent, decide_eq_true_eq] at hword
  rcases hword with rfl | rfl <;> simp

/-- Every second-family current word has weight three. -/
lemma second_current_true
    (word : CWord Atom)
    (hword : isSecondCurrent word = true) :
    word.weight (fun _ => 1) = 3 := by
  simp only [isSecondCurrent, decide_eq_true_eq] at hword
  rcases hword with rfl | rfl <;> simp

/-- Every natural residual source factor belongs to a current family or is
already strictly higher. -/
private lemma classifyNormalizedTrace
    (word : CWord Atom)
    (hword : word ∈ WNTrace.trace) :
    word = firstConventionalInverse ∨
      word = secondConventionalWord ∨
        4 ≤ word.weight (fun _ => 1) := by
  exact
    conventional_or_second
      word hword

lemma current_or_four
    (multiplicity : ℕ)
    (word : CWord Atom)
    (hword : word ∈ naturalResidualTrace multiplicity) :
    isFirstCurrent word = true ∨
      isSecondCurrent word = true ∨
        4 ≤ word.weight (fun _ => 1) := by
  simp only [naturalResidualTrace, List.mem_append] at hword
  rcases hword with hrest | hsecond
  · rcases hrest with htrace | hfirst
    · have htrace' := repeat_trace htrace
      rcases classifyNormalizedTrace word htrace' with
        rfl | rfl | hweight
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl (by simp))
      · exact Or.inr (Or.inr hweight)
    · have heq : word = firstConventionalWord :=
        (List.mem_replicate.mp hfirst).2
      subst word
      exact Or.inl (by simp)
  · have heq : word = secondConventionalInverse :=
      (List.mem_replicate.mp hsecond).2
    subst word
    exact Or.inr (Or.inl (by simp))

/-- First stable pass: move all `B`-family words to the right. -/
def firstRouted
    (multiplicity : ℕ) :
    List (CWord Atom) × List (CWord Atom) :=
  stableRoute isFirstCurrent (naturalResidualTrace multiplicity)

/-- The fixed normalized inverse-triple trace contains one selected `B⁻¹`. -/
lemma filter_trace_current :
    WNTrace.trace.filter isFirstCurrent =
      [firstConventionalInverse] := by
  decide

/-- Proposition-coerced form consumed by `stableRoute_snd`. -/
lemma filter_first_true :
    WNTrace.trace.filter
        (fun word => isFirstCurrent word = true) =
      [firstConventionalInverse] := by
  simpa using filter_trace_current

/-- The fixed normalized inverse-triple trace contains one selected `C`. -/
lemma filter_second_current :
    WNTrace.trace.filter isSecondCurrent =
      [secondConventionalWord] := by
  decide

/-- Proposition-coerced form consumed by the second stable suffix. -/
lemma filter_second_true :
    WNTrace.trace.filter
        (fun word => isSecondCurrent word = true) =
      [secondConventionalWord] := by
  simpa using filter_second_current

/-- The first routed suffix is `B⁻m B^m`. -/
lemma firstRouted_snd
    (multiplicity : ℕ) :
    (firstRouted multiplicity).2 =
      List.replicate multiplicity firstConventionalInverse ++
        List.replicate multiplicity firstConventionalWord := by
  rw [firstRouted, stableRoute_snd, naturalResidualTrace,
    List.filter_append, List.filter_append,
    filter_repeatTrace, filter_first_true,
    repeatTrace_singleton]
  simp [isFirstCurrent]

/-- The first routed suffix evaluates to one. -/
lemma first_routed_snd
    {G : Type*}
    [Group G]
    (x y z : G)
    (multiplicity : ℕ) :
    wordListEval (signedEval x y z) (firstRouted multiplicity).2 = 1 := by
  rw [firstRouted_snd, word_list_append]
  simp [wordListEval, conventional_inverse_word, inv_pow]

/-- After the first pass, every retained prefix word is either a `C`-family
word or already strictly higher. -/
lemma true_routed_fst
    (multiplicity : ℕ)
    (word : CWord Atom)
    (hword : word ∈ (firstRouted multiplicity).1) :
    isSecondCurrent word = true ∨
      4 ≤ word.weight (fun _ => 1) := by
  exact
    property_stable_fst
      (fun word => isSecondCurrent word = true ∨
        4 ≤ word.weight (fun _ => 1))
      isFirstCurrent (naturalResidualTrace multiplicity)
      (fun source hsource hsourceFirst => by
        rcases
            current_or_four
              multiplicity source hsource with
          hfirst | hsecond | hweight
        · rw [hfirst] at hsourceFirst
          contradiction
        · exact Or.inl hsecond
        · exact Or.inr hweight)
      (fun left right hleft hright => by
        right
        rw [CWord.weight_commutator]
        have hleftWeight := first_current_true left hleft
        rcases hright with hright | hright
        · have hrightWeight :=
            second_current_true right hright
          omega
        · omega)
      word hword

/-- The two current selectors are disjoint. -/
lemma second_false_true
    (word : CWord Atom)
    (hword : isFirstCurrent word = true) :
    isSecondCurrent word = false := by
  simp only [isFirstCurrent, decide_eq_true_eq] at hword
  rcases hword with rfl | rfl <;>
    decide

/-- A first-family swap correction cannot itself be a second-family word. -/
lemma current_false_true
    (left right : CWord Atom)
    (hleft : isFirstCurrent left = true) :
    isSecondCurrent (.commutator left right) = false := by
  simp only [isFirstCurrent, decide_eq_true_eq] at hleft
  rcases hleft with rfl | rfl <;>
    simp [isSecondCurrent, secondConventionalWord,
      secondConventionalInverse, firstConventionalWord,
      firstConventionalInverse, xzWord, yzWord, rootSwapWord]

/-- Second stable pass: move all `C`-family words to the right. -/
def secondRouted
    (multiplicity : ℕ) :
    List (CWord Atom) × List (CWord Atom) :=
  stableRoute isSecondCurrent (firstRouted multiplicity).1

/-- The second routed suffix is `C^m C⁻m`. -/
lemma secondRouted_snd
    (multiplicity : ℕ) :
    (secondRouted multiplicity).2 =
      List.replicate multiplicity secondConventionalWord ++
        List.replicate multiplicity secondConventionalInverse := by
  rw [secondRouted, stableRoute_snd, firstRouted,
    filter_stable_fst (fun word => isSecondCurrent word = true)
      isFirstCurrent
      (naturalResidualTrace multiplicity)
      (fun word hword => by
        simp [second_false_true word hword])
      (fun left right hleft => by
        simp [current_false_true
          left right hleft]),
    naturalResidualTrace, List.filter_append, List.filter_append,
    filter_repeatTrace, filter_second_true,
    repeatTrace_singleton]
  simp [isSecondCurrent]

/-- The second routed suffix evaluates to one. -/
lemma second_routed_snd
    {G : Type*}
    [Group G]
    (x y z : G)
    (multiplicity : ℕ) :
    wordListEval (signedEval x y z) (secondRouted multiplicity).2 = 1 := by
  rw [secondRouted_snd, word_list_append]
  simp [wordListEval, eval_second_conventional, inv_pow]

/-- Every factor remaining after the second pass has weight at least four. -/
lemma four_routed_fst
    (multiplicity : ℕ)
    (word : CWord Atom)
    (hword : word ∈ (secondRouted multiplicity).1) :
    4 ≤ word.weight (fun _ => 1) := by
  exact
    stable_route_fst (fun _ => 1) 4 isSecondCurrent
      (firstRouted multiplicity).1
      (fun source hsource hsourceSecond => by
        rcases
            true_routed_fst
              multiplicity source hsource with
          hsecond | hweight
        · rw [hsecond] at hsourceSecond
          contradiction
        · exact hweight)
      word hword

/-- Exact all-higher trace for the natural-power Jacobi packet. -/
def strictTrace
    (multiplicity : ℕ) :
    List (CWord Atom) :=
  (secondRouted multiplicity).1

/-- The first routing pass preserves evaluation after its cancelling suffix is
discarded. -/
lemma word_routed_fst
    {G : Type*}
    [Group G]
    (x y z : G)
    (multiplicity : ℕ) :
    wordListEval (signedEval x y z) (firstRouted multiplicity).1 =
      wordListEval (signedEval x y z)
        (naturalResidualTrace multiplicity) := by
  have hroute :=
    word_stable_route (signedEval x y z) isFirstCurrent
      (naturalResidualTrace multiplicity)
  change
    wordListEval (signedEval x y z)
          ((firstRouted multiplicity).1 ++ (firstRouted multiplicity).2) =
      wordListEval (signedEval x y z)
        (naturalResidualTrace multiplicity) at hroute
  rw [word_list_append, first_routed_snd, mul_one] at hroute
  exact hroute

/-- The second routing pass preserves evaluation after its cancelling suffix
is discarded. -/
lemma second_routed_fst
    {G : Type*}
    [Group G]
    (x y z : G)
    (multiplicity : ℕ) :
    wordListEval (signedEval x y z) (secondRouted multiplicity).1 =
      wordListEval (signedEval x y z) (firstRouted multiplicity).1 := by
  have hroute :=
    word_stable_route (signedEval x y z) isSecondCurrent
      (firstRouted multiplicity).1
  change
    wordListEval (signedEval x y z)
          ((secondRouted multiplicity).1 ++ (secondRouted multiplicity).2) =
      wordListEval (signedEval x y z) (firstRouted multiplicity).1 at hroute
  rw [word_list_append, second_routed_snd, mul_one] at hroute
  exact hroute

/-- Exact strict-tail evaluation for every natural Jacobi multiplicity. -/
lemma word_strict_trace
    {G : Type*}
    [Group G]
    (x y z : G)
    (multiplicity : ℕ) :
    wordListEval (signedEval x y z) (strictTrace multiplicity) =
      (originalWord.eval (signedEval x y z))⁻¹ ^ multiplicity *
        (firstConventionalWord.eval (signedEval x y z) ^ multiplicity *
          (secondConventionalWord.eval (signedEval x y z))⁻¹ ^
            multiplicity) := by
  rw [strictTrace, second_routed_fst,
    word_routed_fst, natural_residual_trace]

/-- Every natural-power strict-tail factor has weight at least four. -/
lemma four_weight_strict
    (multiplicity : ℕ)
    (word : CWord Atom)
    (hword : word ∈ strictTrace multiplicity) :
    4 ≤ word.weight (fun _ => 1) :=
  four_routed_fst multiplicity word hword

end NPTail
end TCTex
end Submission
