import Towers.Group.Zassenhaus.NaturalStrictTail

/-!
# Negative natural-power strict tails for the Jacobi packet

The normalized Hall-Witt trace evaluates to `A⁻¹`.  Reverse that trace and
root-swap every factor to obtain an exact trace for `A`.  Repeating the
inverted trace `multiplicity` times, appending `B⁻multiplicity` and
`C^multiplicity`, and routing the two current families yields a finite trace
for

`A^multiplicity B⁻multiplicity C^multiplicity`

supported entirely in weight at least four.

This is the negative-exponent companion to the natural-power strict tail.
The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace NNPower

open HACoeff
open CWTrace
open WSTrace
open WHNorm
open WNTrace
open WSTail
open NPTail

/-- Reverse a trace and replace every commutator word by its root-swapped
inverse. -/
def inverseTrace
    {α : Type*}
    (source : List (CWord α)) :
    List (CWord α) :=
  source.reverse.map rootSwapWord

/-- Reversing and root-swapping a list of genuine commutators evaluates to
the inverse product. -/
lemma word_inverse_trace
    {α G : Type*}
    [Group G]
    (f : α → G)
    (source : List (CWord α))
    (hsource :
      ∀ word ∈ source,
        ∃ left right, word = .commutator left right) :
    wordListEval f (inverseTrace source) =
      (wordListEval f source)⁻¹ := by
  induction source with
  | nil =>
      simp [inverseTrace]
  | cons word source ih =>
      have htail :
          ∀ tailWord ∈ source,
            ∃ left right, tailWord = .commutator left right := by
        intro tailWord htailWord
        exact hsource tailWord (by simp [htailWord])
      rw [show
          inverseTrace (word :: source) =
            inverseTrace source ++ [rootSwapWord word] by
          simp [inverseTrace],
        word_list_append, ih htail, word_list_cons,
        word_list_nil, mul_one]
      rcases hsource word (by simp) with ⟨left, right, rfl⟩
      rw [root_swap_commutator]
      simp only [word_list_cons]
      group

/-- Every inverse-trace occurrence comes from a source occurrence by one
root swap. -/
lemma source_inverse_trace
    {α : Type*}
    {source : List (CWord α)}
    {word : CWord α}
    (hword : word ∈ inverseTrace source) :
    ∃ sourceWord ∈ source, word = rootSwapWord sourceWord := by
  rw [inverseTrace] at hword
  rcases List.mem_map.mp hword with ⟨sourceWord, hsourceWord, rfl⟩
  exact ⟨sourceWord, by simpa using hsourceWord, rfl⟩

/-- Formal weight is unchanged by reverse-and-root-swap inversion. -/
lemma weight_inverse_trace
    {α : Type*}
    (wt : α → ℕ)
    {source : List (CWord α)}
    {word : CWord α}
    (hword : word ∈ inverseTrace source) :
    ∃ sourceWord ∈ source, word.weight wt = sourceWord.weight wt := by
  rcases source_inverse_trace hword with
    ⟨sourceWord, hsourceWord, rfl⟩
  exact ⟨sourceWord, hsourceWord, weight_root_swap wt sourceWord⟩

/-- Any word above atom weight is visibly a commutator word. -/
lemma commutator_one_weight
    {α : Type*}
    (word : CWord α)
    (hword : 1 < word.weight (fun _ => 1)) :
    ∃ left right, word = .commutator left right := by
  cases word with
  | atom atom =>
      simp at hword
  | commutator left right =>
      exact ⟨left, right, rfl⟩

/-- Every normalized Hall-Witt occurrence is a genuine commutator word. -/
lemma commutator_normalized_trace
    (word : CWord Atom)
    (hword : word ∈ WNTrace.trace) :
    ∃ left right, word = .commutator left right := by
  rcases
      conventional_or_second
        word hword with
    heq | heq | hweight
  · subst word
    exact commutator_one_weight firstConventionalInverse
      (by simp)
  · subst word
    exact commutator_one_weight secondConventionalWord (by simp)
  · exact commutator_one_weight word (by omega)

/-- Exact inverse of the normalized Hall-Witt trace. -/
def inverseNormalizedTrace :
    List (CWord Atom) :=
  inverseTrace WNTrace.trace

/-- The inverted normalized trace evaluates to the original Jacobi triple. -/
lemma word_normalized_trace
    {G : Type*}
    [Group G]
    (x y z : G) :
    wordListEval (signedEval x y z) inverseNormalizedTrace =
      originalWord.eval (signedEval x y z) := by
  rw [inverseNormalizedTrace,
    word_inverse_trace (signedEval x y z)
      WNTrace.trace
      commutator_normalized_trace,
    word_original_inv]
  simp

/--
The inverted normalized trace has only the two inverse-orientation current
heads `B` and `C⁻¹`; every other occurrence has weight at least four.
-/
lemma current_or_normalized
    (word : CWord Atom)
    (hword : word ∈ inverseNormalizedTrace) :
    word = firstConventionalWord ∨
      word = secondConventionalInverse ∨
        4 ≤ word.weight (fun _ => 1) := by
  rcases source_inverse_trace hword with
    ⟨sourceWord, hsourceWord, rfl⟩
  rcases
      conventional_or_second
        sourceWord hsourceWord with
    heq | heq | hweight
  · subst sourceWord
    exact Or.inl (by
      simp [firstConventionalInverse, firstConventionalWord,
        rootSwapWord])
  · subst sourceWord
    exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (by
      simpa only [weight_root_swap] using hweight))

/-- The inverted normalized traces followed by the two powered negative
descendants. -/
def naturalResidualTrace
    (multiplicity : ℕ) :
    List (CWord Atom) :=
  repeatTrace multiplicity inverseNormalizedTrace ++
    List.replicate multiplicity firstConventionalInverse ++
      List.replicate multiplicity secondConventionalWord

/-- The negative natural source evaluates to `A^m B⁻m C^m`. -/
lemma natural_residual_trace
    {G : Type*}
    [Group G]
    (x y z : G)
    (multiplicity : ℕ) :
    wordListEval (signedEval x y z) (naturalResidualTrace multiplicity) =
      originalWord.eval (signedEval x y z) ^ multiplicity *
        ((firstConventionalWord.eval (signedEval x y z))⁻¹ ^ multiplicity *
          secondConventionalWord.eval (signedEval x y z) ^ multiplicity) := by
  rw [naturalResidualTrace, word_list_append, word_list_append,
    word_repeat_trace, word_normalized_trace]
  simp [wordListEval, conventional_inverse_word]
  group

/-- Every negative natural residual source factor belongs to a current
family or is already strictly higher. -/
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
      rcases
          current_or_normalized
            word htrace' with
        rfl | rfl | hweight
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl (by simp))
      · exact Or.inr (Or.inr hweight)
    · have heq : word = firstConventionalInverse :=
        (List.mem_replicate.mp hfirst).2
      subst word
      exact Or.inl (by simp)
  · have heq : word = secondConventionalWord :=
      (List.mem_replicate.mp hsecond).2
    subst word
    exact Or.inr (Or.inl (by simp))

/-- First stable pass: move all `B`-family words to the right. -/
def firstRouted
    (multiplicity : ℕ) :
    List (CWord Atom) × List (CWord Atom) :=
  stableRoute isFirstCurrent (naturalResidualTrace multiplicity)

/-- The inverted normalized trace contains one selected `B`. -/
lemma filter_first_current :
    inverseNormalizedTrace.filter isFirstCurrent =
      [firstConventionalWord] := by
  decide

/-- Proposition-coerced form consumed by `stableRoute_snd`. -/
lemma normalized_current_true :
    inverseNormalizedTrace.filter (fun word => isFirstCurrent word = true) =
      [firstConventionalWord] := by
  simpa using filter_first_current

/-- The inverted normalized trace contains one selected `C⁻¹`. -/
lemma filter_normalized_current :
    inverseNormalizedTrace.filter isSecondCurrent =
      [secondConventionalInverse] := by
  decide

/-- Proposition-coerced form consumed by the second stable suffix. -/
lemma filter_current_true :
    inverseNormalizedTrace.filter (fun word => isSecondCurrent word = true) =
      [secondConventionalInverse] := by
  simpa using filter_normalized_current

@[simp] lemma second_conventional_inverse :
    secondConventionalWord ≠ firstConventionalInverse := by
  decide

@[simp] lemma conventional_ne_first :
    secondConventionalWord ≠ firstConventionalWord := by
  decide

@[simp] lemma conventional_ne_second :
    firstConventionalInverse ≠ secondConventionalWord := by
  decide

@[simp] lemma first_conventional_second :
    firstConventionalInverse ≠ secondConventionalInverse := by
  decide

/-- The first routed suffix is `B^m B⁻m`. -/
lemma firstRouted_snd
    (multiplicity : ℕ) :
    (firstRouted multiplicity).2 =
      List.replicate multiplicity firstConventionalWord ++
        List.replicate multiplicity firstConventionalInverse := by
  rw [firstRouted, stableRoute_snd, naturalResidualTrace,
    List.filter_append, List.filter_append, filter_repeatTrace,
    normalized_current_true,
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
  simp [wordListEval, conventional_inverse_word]

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

/-- Second stable pass: move all `C`-family words to the right. -/
def secondRouted
    (multiplicity : ℕ) :
    List (CWord Atom) × List (CWord Atom) :=
  stableRoute isSecondCurrent (firstRouted multiplicity).1

/-- The second routed suffix is `C⁻m C^m`. -/
lemma secondRouted_snd
    (multiplicity : ℕ) :
    (secondRouted multiplicity).2 =
      List.replicate multiplicity secondConventionalInverse ++
        List.replicate multiplicity secondConventionalWord := by
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
    filter_repeatTrace, filter_current_true,
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
  simp [wordListEval, eval_second_conventional]

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

/-- Exact all-higher trace for the negative natural-power Jacobi packet. -/
def strictTrace
    (multiplicity : ℕ) :
    List (CWord Atom) :=
  (secondRouted multiplicity).1

/-- The first routing pass preserves evaluation after its cancelling suffix
is discarded. -/
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

/-- Exact strict-tail evaluation for every negative natural multiplicity. -/
lemma word_strict_trace
    {G : Type*}
    [Group G]
    (x y z : G)
    (multiplicity : ℕ) :
    wordListEval (signedEval x y z) (strictTrace multiplicity) =
      originalWord.eval (signedEval x y z) ^ multiplicity *
        ((firstConventionalWord.eval (signedEval x y z))⁻¹ ^ multiplicity *
          secondConventionalWord.eval (signedEval x y z) ^ multiplicity) := by
  rw [strictTrace, second_routed_fst,
    word_routed_fst, natural_residual_trace]

/-- Every negative natural-power strict-tail factor has weight at least
four. -/
lemma four_weight_strict
    (multiplicity : ℕ)
    (word : CWord Atom)
    (hword : word ∈ strictTrace multiplicity) :
    4 ≤ word.weight (fun _ => 1) :=
  four_routed_fst multiplicity word hword

end NNPower
end TCTex
end Towers
