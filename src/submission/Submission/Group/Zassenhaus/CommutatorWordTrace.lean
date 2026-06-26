import Submission.Group.Zassenhaus.ConjTraceEvaluation

/-!
# Product traces for commutator words

The labelled Hall-Petresco traces distribute a bracket over products of
atoms.  Hall-Witt normalization also needs to distribute brackets over finite
products of commutator words that have already been expanded.

This file records the word-level analogue.  The traces evaluate exactly under
an arbitrary group-valued substitution, ordinary conjugation never decreases
formal weight, and every bracket emitted from bounded left and right sources
inherits the sum of their lower bounds.

The inverse-oriented one-step trace retains its old word before the strict
correction.  It is useful when a signed Hall-Witt head is rewritten toward its
conventional root-swapped descendant.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CWTrace

open scoped commutatorElement

open HACoeff

/-- Evaluate a finite commutator-word list under an arbitrary substitution. -/
def wordListEval
    {α G : Type*}
    [Group G]
    (f : α → G)
    (words : List (CWord α)) :
    G :=
  (words.map fun word => word.eval f).prod

@[simp]
lemma word_list_nil
    {α G : Type*}
    [Group G]
    (f : α → G) :
    wordListEval f [] = 1 :=
  rfl

@[simp]
lemma word_list_cons
    {α G : Type*}
    [Group G]
    (f : α → G)
    (word : CWord α)
    (words : List (CWord α)) :
    wordListEval f (word :: words) =
      word.eval f * wordListEval f words :=
  rfl

@[simp]
lemma word_list_append
    {α G : Type*}
    [Group G]
    (f : α → G)
    (left right : List (CWord α)) :
    wordListEval f (left ++ right) =
      wordListEval f left * wordListEval f right := by
  simp [wordListEval, List.prod_append]

lemma word_list_flat
    {α G : Type*}
    [Group G]
    (f : α → G)
    (expand : CWord α → List (CWord α)) :
    ∀ words : List (CWord α),
      wordListEval f (words.flatMap expand) =
        (words.map fun word => wordListEval f (expand word)).prod
  | [] => by
      rfl
  | word :: words => by
      simp [word_list_append, word_list_flat f expand words]

/-- Expand conjugation by one already-built commutator word. -/
def conjugateWordTrace
    {α : Type*}
    (conjugator target : CWord α) :
    List (CWord α) :=
  [.commutator conjugator target, target]

/-- A word-level conjugation step evaluates exactly. -/
lemma list_conjugate_trace
    {α G : Type*}
    [Group G]
    (f : α → G)
    (conjugator target : CWord α) :
    wordListEval f (conjugateWordTrace conjugator target) =
      conjugator.eval f * target.eval f * (conjugator.eval f)⁻¹ := by
  simp [conjugateWordTrace, wordListEval, CWord.eval_commutator,
    commutatorElement_def]

/-- A word-level conjugation step never decreases the target weight. -/
lemma weight_conjugate_trace
    {α : Type*}
    (wt : α → ℕ)
    (conjugator target emitted : CWord α)
    (hemitted : emitted ∈ conjugateWordTrace conjugator target) :
    target.weight wt ≤ emitted.weight wt := by
  have hemitted' :
      emitted = .commutator conjugator target ∨ emitted = target := by
    simpa [conjugateWordTrace] using hemitted
  rcases hemitted' with rfl | rfl
  · simp [CWord.weight_commutator]
  · exact Nat.le_refl _

/-- Expand conjugation of every factor in an already-built word list. -/
def conjugateTraceList
    {α : Type*}
    (conjugator : CWord α)
    (targets : List (CWord α)) :
    List (CWord α) :=
  targets.flatMap (conjugateWordTrace conjugator)

/-- Word-level conjugation distributes exactly over a finite product. -/
lemma word_conjugate_trace
    {α G : Type*}
    [Group G]
    (f : α → G)
    (conjugator : CWord α)
    (targets : List (CWord α)) :
    wordListEval f (conjugateTraceList conjugator targets) =
      conjugator.eval f * wordListEval f targets *
        (conjugator.eval f)⁻¹ := by
  rw [conjugateTraceList, word_list_flat]
  simp_rw [list_conjugate_trace]
  simpa [wordListEval, List.map_map, Function.comp_def] using
    (list_prod_conjugates (conjugator.eval f)
      (targets.map fun target => target.eval f))

/-- Every conjugated-list occurrence remembers a source of no larger weight. -/
lemma source_conjugate_list
    {α : Type*}
    (wt : α → ℕ)
    (conjugator : CWord α)
    (targets : List (CWord α))
    (emitted : CWord α)
    (hemitted : emitted ∈ conjugateTraceList conjugator targets) :
    ∃ target ∈ targets, target.weight wt ≤ emitted.weight wt := by
  rcases List.mem_flatMap.mp hemitted with ⟨target, htarget, hemitted⟩
  exact
    ⟨target, htarget,
      weight_conjugate_trace wt conjugator target emitted hemitted⟩

/-- Expand conjugation by a finite product of already-built words. -/
def wordConjTrace
    {α : Type*} :
    List (CWord α) →
      CWord α →
        List (CWord α)
  | [], target => [target]
  | conjugator :: conjugators, target =>
      (wordConjTrace conjugators target).flatMap
        (conjugateWordTrace conjugator)

/-- The strict correction prefix before the retained word. -/
def wordConjCorrection
    {α : Type*}
    (conjugators : List (CWord α))
    (target : CWord α) :
    List (CWord α) :=
  (wordConjTrace conjugators target).dropLast

/-- A word-sequence conjugation trace always ends with its original target. -/
lemma init_append_singleton
    {α : Type*} :
    ∀ (conjugators : List (CWord α))
      (target : CWord α),
      ∃ init, wordConjTrace conjugators target = init ++ [target]
  | [], target => ⟨[], rfl⟩
  | conjugator :: conjugators, target => by
      rcases
          init_append_singleton conjugators target with
        ⟨init, hinit⟩
      refine
        ⟨init.flatMap (conjugateWordTrace conjugator) ++
            [.commutator conjugator target], ?_⟩
      simp [wordConjTrace, hinit, conjugateWordTrace]

/-- Split a word-sequence trace into strict corrections and its retained head. -/
lemma conj_append_singleton
    {α : Type*}
    (conjugators : List (CWord α))
    (target : CWord α) :
    wordConjTrace conjugators target =
      wordConjCorrection conjugators target ++ [target] := by
  rcases
      init_append_singleton conjugators target with
    ⟨init, hinit⟩
  simp [wordConjCorrection, hinit]

@[simp]
lemma word_conj_nil
    {α : Type*}
    (target : CWord α) :
    wordConjCorrection [] target = [] :=
  rfl

/-- Adding one built conjugator expands older corrections and appends one new
immediate correction before the retained target. -/
lemma word_conj_cons
    {α : Type*}
    (conjugator : CWord α)
    (conjugators : List (CWord α))
    (target : CWord α) :
    wordConjCorrection (conjugator :: conjugators) target =
      (wordConjCorrection conjugators target).flatMap
          (conjugateWordTrace conjugator) ++
        [.commutator conjugator target] := by
  rw [wordConjCorrection, wordConjTrace,
    conj_append_singleton]
  simp [conjugateWordTrace]

/-- A word-sequence trace evaluates to conjugation by the source product. -/
lemma list_conj_trace
    {α G : Type*}
    [Group G]
    (f : α → G) :
    ∀ (conjugators : List (CWord α))
      (target : CWord α),
      wordListEval f (wordConjTrace conjugators target) =
        wordListEval f conjugators * target.eval f *
          (wordListEval f conjugators)⁻¹
  | [], target => by
      simp [wordConjTrace, wordListEval]
  | conjugator :: conjugators, target => by
      rw [wordConjTrace, word_list_flat]
      simp_rw [list_conjugate_trace]
      rw [show
          (List.map
              (fun word =>
                conjugator.eval f * word.eval f * (conjugator.eval f)⁻¹)
              (wordConjTrace conjugators target)).prod =
            conjugator.eval f *
                wordListEval f (wordConjTrace conjugators target) *
              (conjugator.eval f)⁻¹ by
          simpa [wordListEval, List.map_map, Function.comp_def] using
            (list_prod_conjugates (conjugator.eval f)
              ((wordConjTrace conjugators target).map fun word =>
                word.eval f))]
      rw [list_conj_trace]
      simp [wordListEval]
      group

/-- Every word-sequence correction is strictly heavier than the retained word
when each built conjugator has positive weight. -/
lemma conj_correction_trace
    {α : Type*}
    (wt : α → ℕ) :
    ∀ (conjugators : List (CWord α))
      (target emitted : CWord α),
      (∀ conjugator ∈ conjugators, 0 < conjugator.weight wt) →
        emitted ∈ wordConjCorrection conjugators target →
          target.weight wt < emitted.weight wt
  | [], target, emitted, _hconjugators, hemitted => by
      simp at hemitted
  | conjugator :: conjugators, target, emitted, hconjugators, hemitted => by
      rw [word_conj_cons] at hemitted
      simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at hemitted
      rcases hemitted with ⟨source, hsource, hsourceEmitted⟩ | rfl
      · exact
          lt_of_lt_of_le
            (conj_correction_trace wt conjugators target
              source (fun word hword => hconjugators word (by simp [hword]))
                hsource)
            (weight_conjugate_trace wt conjugator source emitted
              hsourceEmitted)
      · simp only [CWord.weight_commutator]
        exact Nat.lt_add_of_pos_left (hconjugators conjugator (by simp))

/-- The strict correction prefix gains at least one unit of weight. -/
lemma succ_correction_trace
    {α : Type*}
    (wt : α → ℕ)
    (conjugators : List (CWord α))
    (target emitted : CWord α)
    (hconjugators : ∀ conjugator ∈ conjugators, 0 < conjugator.weight wt)
    (hemitted : emitted ∈ wordConjCorrection conjugators target) :
    target.weight wt + 1 ≤ emitted.weight wt :=
  Nat.succ_le_of_lt
    (conj_correction_trace wt conjugators target emitted
      hconjugators hemitted)

/-- Evaluation of the strict prefix is the conjugation quotient. -/
lemma word_conj_trace
    {α G : Type*}
    [Group G]
    (f : α → G)
    (conjugators : List (CWord α))
    (target : CWord α) :
    wordListEval f (wordConjCorrection conjugators target) =
      (wordListEval f conjugators * target.eval f *
        (wordListEval f conjugators)⁻¹) *
          (target.eval f)⁻¹ := by
  have htrace := list_conj_trace f conjugators target
  rw [conj_append_singleton,
    word_list_append] at htrace
  simp only [word_list_cons, word_list_nil, mul_one] at htrace
  rw [← htrace]
  group

/--
Retain a positive commutator word before the strict correction introduced by
conjugation with another already-built word.
-/
def inverseConjugateTrace
    {α : Type*}
    (conjugator target : CWord α) :
    List (CWord α) :=
  [target, .commutator (rootSwapWord target) conjugator]

/-- The retained-head inverse-oriented trace evaluates as conjugation. -/
lemma inverse_conjugate_trace
    {α G : Type*}
    [Group G]
    (f : α → G)
    (conjugator target : CWord α)
    (hroot :
      (rootSwapWord target).eval f = (target.eval f)⁻¹) :
    wordListEval f (inverseConjugateTrace conjugator target) =
      conjugator.eval f * target.eval f * (conjugator.eval f)⁻¹ := by
  simp [inverseConjugateTrace, wordListEval,
    CWord.eval_commutator, hroot, commutatorElement_def, mul_assoc]

/-- The non-head inverse-oriented word has the sum of the two source weights. -/
lemma inverse_conjugate_correction
    {α : Type*}
    (wt : α → ℕ)
    (conjugator target : CWord α) :
    (CWord.commutator (rootSwapWord target) conjugator).weight wt =
      target.weight wt + conjugator.weight wt := by
  simp only [CWord.weight_commutator, weight_root_swap]

/-- Expand `[left, right₀ ... rightₙ]` over already-built words. -/
def rightWordTrace
    {α : Type*}
    (left : CWord α) :
    List (CWord α) → List (CWord α)
  | [] => []
  | right :: rights =>
      .commutator left right ::
        conjugateTraceList right (rightWordTrace left rights)

/-- The right product trace evaluates to the expected commutator. -/
lemma word_right_trace
    {α G : Type*}
    [Group G]
    (f : α → G)
    (left : CWord α) :
    ∀ rights : List (CWord α),
      wordListEval f (rightWordTrace left rights) =
        ⁅left.eval f, wordListEval f rights⁆
  | [] => by
      simp [rightWordTrace, wordListEval, commutatorElement_def]
  | right :: rights => by
      rw [rightWordTrace, word_list_cons,
        CWord.eval_commutator,
        word_conjugate_trace,
        word_right_trace]
      change
        ⁅left.eval f, right.eval f⁆ *
              (right.eval f * ⁅left.eval f, wordListEval f rights⁆ *
                (right.eval f)⁻¹) =
          ⁅left.eval f, right.eval f * wordListEval f rights⁆
      rw [element_mul_right]
      group

/-- Every right product-trace factor inherits the source weight sum. -/
lemma add_right_trace
    {α : Type*}
    (wt : α → ℕ)
    (lowerRight : ℕ)
    (left : CWord α)
    (rights : List (CWord α))
    (hrights : ∀ right ∈ rights, lowerRight ≤ right.weight wt)
    (emitted : CWord α)
    (hemitted : emitted ∈ rightWordTrace left rights) :
    left.weight wt + lowerRight ≤ emitted.weight wt := by
  induction rights generalizing emitted with
  | nil =>
      simp [rightWordTrace] at hemitted
  | cons right rights ih =>
      simp only [rightWordTrace, List.mem_cons] at hemitted
      rcases hemitted with rfl | hemitted
      · simpa only [CWord.weight_commutator] using
          Nat.add_le_add_left (hrights right (by simp)) (left.weight wt)
      · rcases
          source_conjugate_list wt right
            (rightWordTrace left rights) emitted hemitted with
          ⟨source, hsource, hsourceEmitted⟩
        exact
          (ih (fun target htarget => hrights target (by simp [htarget]))
            source hsource).trans hsourceEmitted

/-- Expand `[left₀ ... leftₘ, right₀ ... rightₙ]` over built words. -/
def leftWordTrace
    {α : Type*} :
    List (CWord α) →
      List (CWord α) →
        List (CWord α)
  | [], _rights => []
  | left :: lefts, rights =>
      conjugateTraceList left (leftWordTrace lefts rights) ++
        rightWordTrace left rights

/-- The two-sided product trace evaluates to the expected commutator. -/
lemma left_right_trace
    {α G : Type*}
    [Group G]
    (f : α → G) :
    ∀ lefts rights : List (CWord α),
      wordListEval f (leftWordTrace lefts rights) =
        ⁅wordListEval f lefts, wordListEval f rights⁆
  | [], rights => by
      simp [leftWordTrace, wordListEval, commutatorElement_def]
  | left :: lefts, rights => by
      rw [leftWordTrace, word_list_append,
        word_conjugate_trace,
        left_right_trace,
        word_right_trace]
      change
        (left.eval f *
              ⁅wordListEval f lefts, wordListEval f rights⁆ *
                (left.eval f)⁻¹) *
              ⁅left.eval f, wordListEval f rights⁆ =
          ⁅left.eval f * wordListEval f lefts, wordListEval f rights⁆
      rw [element_mul_left]

/-- Every two-sided product-trace factor inherits both source lower bounds. -/
lemma add_left_trace
    {α : Type*}
    (wt : α → ℕ)
    (lowerLeft lowerRight : ℕ) :
    ∀ (lefts rights : List (CWord α)),
      (∀ left ∈ lefts, lowerLeft ≤ left.weight wt) →
        (∀ right ∈ rights, lowerRight ≤ right.weight wt) →
          ∀ emitted ∈ leftWordTrace lefts rights,
            lowerLeft + lowerRight ≤ emitted.weight wt
  | [], rights, _hlefts, _hrights, emitted, hemitted => by
      simp [leftWordTrace] at hemitted
  | left :: lefts, rights, hlefts, hrights, emitted, hemitted => by
      rw [leftWordTrace, List.mem_append] at hemitted
      rcases hemitted with hemitted | hemitted
      · rcases
          source_conjugate_list wt left
            (leftWordTrace lefts rights) emitted hemitted with
          ⟨source, hsource, hsourceEmitted⟩
        exact
          (add_left_trace wt lowerLeft lowerRight
            lefts rights
              (fun target htarget => hlefts target (by simp [htarget]))
              hrights source hsource).trans hsourceEmitted
      · exact
          (Nat.add_le_add_right (hlefts left (by simp)) lowerRight).trans
            (add_right_trace wt lowerRight left rights
              hrights emitted hemitted)

/-- Bracketing a product ending in `retained` with one right word retains the
principal bracket as an explicit trace occurrence. -/
lemma principal_append_singleton
    {α : Type*}
    (earlier : List (CWord α))
    (retained right : CWord α) :
    .commutator retained right ∈
      leftWordTrace (earlier ++ [retained]) [right] := by
  induction earlier with
  | nil =>
      simp [leftWordTrace, rightWordTrace]
  | cons conjugator earlier ih =>
      rw [List.cons_append, leftWordTrace, List.mem_append]
      exact
        Or.inl
          (List.mem_flatMap.mpr
            ⟨.commutator retained right, ih,
              by simp [conjugateWordTrace]⟩)

/--
If every prefix word is strictly heavier than the retained last word, the
single-right product trace has only one possible factor in the principal
stratum.  Every other occurrence gains at least one unit of weight.
-/
lemma principal_or_singleton
    {α : Type*}
    (wt : α → ℕ)
    (earlier : List (CWord α))
    (retained right emitted : CWord α)
    (hearlier :
      ∀ word ∈ earlier, retained.weight wt + 1 ≤ word.weight wt)
    (hemitted :
      emitted ∈ leftWordTrace (earlier ++ [retained]) [right]) :
    emitted = .commutator retained right ∨
      (CWord.commutator retained right).weight wt + 1 ≤
        emitted.weight wt := by
  induction earlier generalizing emitted with
  | nil =>
      exact
        Or.inl
          (by
            simpa [leftWordTrace, rightWordTrace,
              conjugateTraceList] using hemitted)
  | cons conjugator earlier ih =>
      rw [List.cons_append, leftWordTrace, List.mem_append] at hemitted
      rcases hemitted with hemitted | hemitted
      · rcases List.mem_flatMap.mp hemitted with
          ⟨source, hsource, hsourceEmitted⟩
        rcases
            ih source (fun word hword => hearlier word (by simp [hword]))
              hsource with
          rfl | hsource
        · have hsourceEmitted' :
              emitted =
                  .commutator conjugator (.commutator retained right) ∨
                emitted = .commutator retained right := by
            simpa [conjugateWordTrace] using hsourceEmitted
          rcases hsourceEmitted' with rfl | rfl
          · right
            simp only [CWord.weight_commutator]
            have hconjugator := hearlier conjugator (by simp)
            omega
          · exact Or.inl rfl
        · exact
            Or.inr
              (hsource.trans
                (weight_conjugate_trace wt conjugator source
                  emitted hsourceEmitted))
      · have hemitted' :
            emitted = .commutator conjugator right := by
          simpa [rightWordTrace, conjugateTraceList] using hemitted
        subst emitted
        right
        simp only [CWord.weight_commutator]
        have hconjugator := hearlier conjugator (by simp)
        omega

/-- Replace every occurrence of one principal word by an ordered finite trace. -/
def replaceWordTrace
    {α : Type*}
    [DecidableEq α]
    (principal : CWord α)
    (replacement source : List (CWord α)) :
    List (CWord α) :=
  source.flatMap fun word =>
    if word = principal then replacement else [word]

/-- Ordered occurrence replacement preserves evaluation whenever the
replacement trace evaluates to its principal word. -/
lemma word_replace_trace
    {α G : Type*}
    [DecidableEq α]
    [Group G]
    (f : α → G)
    (principal : CWord α)
    (replacement source : List (CWord α))
    (hreplacement :
      wordListEval f replacement = principal.eval f) :
    wordListEval f (replaceWordTrace principal replacement source) =
      wordListEval f source := by
  induction source with
  | nil =>
      rfl
  | cons word source ih =>
      rw [replaceWordTrace, List.flatMap_cons, word_list_append,
        word_list_cons]
      have ih' :
          wordListEval f
              (source.flatMap fun word =>
                if word = principal then replacement else [word]) =
            wordListEval f source := by
        simpa only [replaceWordTrace] using ih
      rw [ih']
      by_cases hword : word = principal
      · subst word
        simp [hreplacement]
      · simp [hword]

/-- Every replaced occurrence either comes from the principal replacement
packet or is one unchanged source occurrence. -/
lemma source_replace_trace
    {α : Type*}
    [DecidableEq α]
    (principal : CWord α)
    (replacement source : List (CWord α))
    (emitted : CWord α)
    (hemitted : emitted ∈ replaceWordTrace principal replacement source) :
    ∃ word ∈ source,
      (word = principal ∧ emitted ∈ replacement) ∨
        (word ≠ principal ∧ emitted = word) := by
  rcases List.mem_flatMap.mp hemitted with ⟨word, hword, hemitted⟩
  refine ⟨word, hword, ?_⟩
  by_cases hprincipal : word = principal
  · exact Or.inl ⟨hprincipal, by simpa [hprincipal] using hemitted⟩
  · exact
      Or.inr
        ⟨hprincipal, by simpa [hprincipal] using hemitted⟩

/--
Move one selected current word rightward across a higher trace.  The emitted
correction before each crossed word records the exact noncommutative swap.
-/
def moveHigherTrace
    {α : Type*}
    (left : CWord α) :
    List (CWord α) → List (CWord α)
  | [] => []
  | right :: rights =>
      .commutator left right :: right :: moveHigherTrace left rights

/-- Moving one word across a higher trace preserves evaluation exactly. -/
lemma move_higher_mul
    {α G : Type*}
    [Group G]
    (f : α → G)
    (left : CWord α) :
    ∀ rights : List (CWord α),
      wordListEval f (moveHigherTrace left rights) * left.eval f =
        left.eval f * wordListEval f rights
  | [] => by
      simp [moveHigherTrace, wordListEval]
  | right :: rights => by
      change
        ⁅left.eval f, right.eval f⁆ *
              (right.eval f *
                wordListEval f (moveHigherTrace left rights)) *
            left.eval f =
          left.eval f * (right.eval f * wordListEval f rights)
      calc
        _ =
            ⁅left.eval f, right.eval f⁆ * right.eval f *
              (wordListEval f (moveHigherTrace left rights) *
                left.eval f) := by
          group
        _ =
            ⁅left.eval f, right.eval f⁆ * right.eval f *
              (left.eval f * wordListEval f rights) := by
          rw [move_higher_mul]
        _ = left.eval f * (right.eval f * wordListEval f rights) := by
          simp [commutatorElement_def]
          group

/-- Each moved-higher occurrence is either one crossed source word or its
explicit swap correction. -/
lemma move_higher_trace
    {α : Type*}
    (left : CWord α)
    (rights : List (CWord α))
    (emitted : CWord α)
    (hemitted : emitted ∈ moveHigherTrace left rights) :
    ∃ right ∈ rights,
      emitted = .commutator left right ∨ emitted = right := by
  induction rights with
  | nil =>
      simp [moveHigherTrace] at hemitted
  | cons right rights ih =>
      simp only [moveHigherTrace, List.mem_cons] at hemitted
      rcases hemitted with heq | heq | hemitted
      · exact ⟨right, by simp, Or.inl heq⟩
      · exact ⟨right, by simp, Or.inr heq⟩
      · rcases ih hemitted with ⟨source, hsource, heq⟩
        exact ⟨source, by simp [hsource], heq⟩

/-- Moving a word across a lower-bounded higher trace keeps every emitted
factor in that higher region. -/
lemma lower_move_higher
    {α : Type*}
    (wt : α → ℕ)
    (lowerWeight : ℕ)
    (left : CWord α)
    (rights : List (CWord α))
    (hrights : ∀ right ∈ rights, lowerWeight ≤ right.weight wt)
    (emitted : CWord α)
    (hemitted : emitted ∈ moveHigherTrace left rights) :
    lowerWeight ≤ emitted.weight wt := by
  rcases
      move_higher_trace left rights emitted hemitted with
    ⟨right, hright, heq | heq⟩
  · subst emitted
    simp only [CWord.weight_commutator]
    exact (hrights right hright).trans (Nat.le_add_left _ _)
  · subst emitted
    exact hrights right hright

/--
Stable routing of selected current words to the right.  The first component
is the higher trace, including exact swap corrections.  The second component
is the selected suffix in original relative order.
-/
def stableRoute
    {α : Type*}
    (isCurrent : CWord α → Bool) :
    List (CWord α) →
      List (CWord α) × List (CWord α)
  | [] => ([], [])
  | word :: words =>
      let routed := stableRoute isCurrent words
      if isCurrent word = true then
        (moveHigherTrace word routed.1, word :: routed.2)
      else
        (word :: routed.1, routed.2)

/-- The selected suffix of stable routing is the corresponding source filter. -/
lemma stableRoute_snd
    {α : Type*}
    (isCurrent : CWord α → Bool) :
    ∀ source : List (CWord α),
      (stableRoute isCurrent source).2 =
        source.filter fun word => isCurrent word = true
  | [] => by
      rfl
  | word :: words => by
      by_cases hcurrent : isCurrent word = true
      · simp [stableRoute, hcurrent, stableRoute_snd isCurrent words]
      · have hfalse : isCurrent word = false := by
          cases h : isCurrent word <;> simp_all
        simp [stableRoute, hcurrent, stableRoute_snd isCurrent words]

/-- Stable routing preserves the full ordered product exactly. -/
lemma word_stable_route
    {α G : Type*}
    [Group G]
    (f : α → G)
    (isCurrent : CWord α → Bool) :
    ∀ source : List (CWord α),
      wordListEval f
          ((stableRoute isCurrent source).1 ++
            (stableRoute isCurrent source).2) =
        wordListEval f source
  | [] => by
      rfl
  | word :: words => by
      by_cases hcurrent : isCurrent word = true
      · rw [stableRoute, if_pos hcurrent, word_list_append,
          word_list_cons]
        calc
          _ =
              (wordListEval f (moveHigherTrace word
                  (stableRoute isCurrent words).1) * word.eval f) *
                wordListEval f (stableRoute isCurrent words).2 := by
            group
          _ =
              (word.eval f *
                wordListEval f (stableRoute isCurrent words).1) *
                  wordListEval f (stableRoute isCurrent words).2 := by
            rw [move_higher_mul]
          _ =
              word.eval f *
                wordListEval f
                  ((stableRoute isCurrent words).1 ++
                    (stableRoute isCurrent words).2) := by
            rw [word_list_append]
            group
          _ = word.eval f * wordListEval f words := by
            rw [word_stable_route]
      · rw [stableRoute, if_neg hcurrent]
        simp only [word_list_append, word_list_cons]
        calc
          _ =
              word.eval f *
                (wordListEval f (stableRoute isCurrent words).1 *
                  wordListEval f (stableRoute isCurrent words).2) := by
            group
          _ =
              word.eval f *
                wordListEval f
                  ((stableRoute isCurrent words).1 ++
                    (stableRoute isCurrent words).2) := by
            rw [word_list_append]
          _ = word.eval f * wordListEval f words := by
            rw [word_stable_route]

/-- The higher output of stable routing remains lower-bounded whenever every
unselected source factor already satisfies that lower bound. -/
lemma stable_route_fst
    {α : Type*}
    (wt : α → ℕ)
    (lowerWeight : ℕ)
    (isCurrent : CWord α → Bool) :
    ∀ (source : List (CWord α)),
      (∀ word ∈ source, isCurrent word = false →
        lowerWeight ≤ word.weight wt) →
      ∀ emitted ∈ (stableRoute isCurrent source).1,
        lowerWeight ≤ emitted.weight wt
  | [], _hsource, emitted, hemitted => by
      simp [stableRoute] at hemitted
  | word :: words, hsource, emitted, hemitted => by
      by_cases hcurrent : isCurrent word = true
      · rw [stableRoute, if_pos hcurrent] at hemitted
        exact
          lower_move_higher wt lowerWeight word
            (stableRoute isCurrent words).1
            (fun right hright =>
              stable_route_fst wt lowerWeight isCurrent
                words
                (fun source hsourceMem hsourceCurrent =>
                  hsource source (by simp [hsourceMem]) hsourceCurrent)
                right hright)
            emitted hemitted
      · rw [stableRoute, if_neg hcurrent] at hemitted
        simp only [List.mem_cons] at hemitted
        rcases hemitted with heq | hemitted
        · rw [heq]
          apply hsource word (by simp)
          cases h : isCurrent word <;> simp_all
        · exact
            stable_route_fst wt lowerWeight isCurrent
              words
              (fun source hsourceMem hsourceCurrent =>
                hsource source (by simp [hsourceMem]) hsourceCurrent)
              emitted hemitted

/-- A property of crossed words and their explicit swap corrections is
preserved by moving one selected word rightward. -/
lemma property_move_higher
    {α : Type*}
    (P : CWord α → Prop)
    (left : CWord α)
    (rights : List (CWord α))
    (hrights : ∀ right ∈ rights, P right)
    (hcorrection : ∀ right, P right → P (.commutator left right))
    (emitted : CWord α)
    (hemitted : emitted ∈ moveHigherTrace left rights) :
    P emitted := by
  rcases
      move_higher_trace left rights emitted hemitted with
    ⟨right, hright, heq | heq⟩
  · rw [heq]
    exact hcorrection right (hrights right hright)
  · rw [heq]
    exact hrights right hright

/--
A property of unselected source words is preserved by the higher output of
stable routing when it is also preserved by every emitted swap correction.
-/
lemma property_stable_fst
    {α : Type*}
    (P : CWord α → Prop)
    (isCurrent : CWord α → Bool) :
    ∀ (source : List (CWord α)),
      (∀ word ∈ source, isCurrent word = false → P word) →
      (∀ left right, isCurrent left = true → P right →
        P (.commutator left right)) →
      ∀ emitted ∈ (stableRoute isCurrent source).1,
        P emitted
  | [], _hsource, _hcorrection, emitted, hemitted => by
      simp [stableRoute] at hemitted
  | word :: words, hsource, hcorrection, emitted, hemitted => by
      by_cases hcurrent : isCurrent word = true
      · rw [stableRoute, if_pos hcurrent] at hemitted
        exact
          property_move_higher P word
            (stableRoute isCurrent words).1
            (fun right hright =>
              property_stable_fst P isCurrent words
                (fun source hsourceMem hsourceCurrent =>
                  hsource source (by simp [hsourceMem]) hsourceCurrent)
                hcorrection right hright)
            (fun right hright => hcorrection word right hcurrent hright)
            emitted hemitted
      · rw [stableRoute, if_neg hcurrent] at hemitted
        simp only [List.mem_cons] at hemitted
        rcases hemitted with heq | hemitted
        · rw [heq]
          apply hsource word (by simp)
          cases h : isCurrent word <;> simp_all
        · exact
            property_stable_fst P isCurrent words
              (fun source hsourceMem hsourceCurrent =>
                hsource source (by simp [hsourceMem]) hsourceCurrent)
              hcorrection emitted hemitted

/-- Filtering after one rightward move retains exactly the filtered crossed
words when every emitted correction is rejected by the filter. -/
lemma filter_move_higher
    {α : Type*}
    (keep : CWord α → Bool)
    (left : CWord α) :
    ∀ rights : List (CWord α),
      (∀ right ∈ rights, keep (.commutator left right) = false) →
      (moveHigherTrace left rights).filter keep =
        rights.filter keep
  | [], _hcorrection => by
      rfl
  | right :: rights, hcorrection => by
      rw [moveHigherTrace]
      simp only [List.filter_cons, hcorrection right (by simp), Bool.false_eq_true,
        if_false]
      rw [filter_move_higher keep left rights
        (fun source hsource => hcorrection source (by simp [hsource]))]

/--
Filtering the higher output of stable routing by a disjoint selector is the
same as filtering the original source by that selector.
-/
lemma filter_stable_fst
    {α : Type*}
    (keep isCurrent : CWord α → Bool) :
    ∀ source : List (CWord α),
      (∀ word, isCurrent word = true → keep word = false) →
      (∀ left right, isCurrent left = true →
        keep (.commutator left right) = false) →
      (stableRoute isCurrent source).1.filter keep =
        source.filter keep
  | [], _hdisjoint, _hcorrection => by
      rfl
  | word :: words, hdisjoint, hcorrection => by
      by_cases hcurrent : isCurrent word = true
      · rw [stableRoute, if_pos hcurrent,
          filter_move_higher keep word
            (stableRoute isCurrent words).1
            (fun right _hright => hcorrection word right hcurrent),
          filter_stable_fst keep isCurrent words hdisjoint hcorrection]
        simp [hdisjoint word hcurrent]
      · rw [stableRoute, if_neg hcurrent]
        simp only [List.filter_cons]
        rw [filter_stable_fst keep isCurrent words hdisjoint hcorrection]

end CWTrace
end TCTex
end Submission
