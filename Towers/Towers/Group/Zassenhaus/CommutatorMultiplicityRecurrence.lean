import Towers.Group.Zassenhaus.CommutatorWordTrace

/-!
# Cutoff multiplicity recurrences for commutator-word routing

Stable rightward routing preserves an ordered noncommutative trace.  Its
multiplicity shadow is simpler: moving one selected word across a higher trace
retains the old higher occurrences and emits one left bracket for each of
them.

This file records that scalar recurrence before and after an arbitrary
filter.  It also isolates the strict correction operator and proves that its
iterates eventually vanish below every fixed positive-weight cutoff.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CWTrace

/-- The strict swap corrections emitted while one word moves rightward
across a higher trace. -/
def moveCorrectionTrace
    {α : Type*}
    (left : CWord α)
    (rights : List (CWord α)) :
    List (CWord α) :=
  rights.map fun right => .commutator left right

/-- The multiplicity shadow of a rightward move is the sum of the strict
correction multiplicity and the retained higher multiplicity. -/
lemma count_move_higher
    {α : Type*}
    [DecidableEq α]
    (left target : CWord α) :
    ∀ rights : List (CWord α),
      (moveHigherTrace left rights).count target =
        (moveCorrectionTrace left rights).count target +
          rights.count target
  | [] => by
      rfl
  | right :: rights => by
      simp only [moveHigherTrace, moveCorrectionTrace, List.map_cons,
        List.count_cons, count_move_higher left target rights]
      omega

/-- Filtering changes the count of one target only according to whether that
target itself passes the filter. -/
lemma count_filter_ite
    {α : Type*}
    [DecidableEq α]
    (keep : α → Bool)
    (target : α) :
    ∀ source : List α,
      (source.filter keep).count target =
        if keep target = true then source.count target else 0 := by
  intro source
  by_cases htarget : keep target = true
  · rw [if_pos htarget]
    exact List.count_filter htarget
  · rw [if_neg htarget]
    induction source with
    | nil =>
        rfl
    | cons entry source ih =>
        rw [List.filter_cons]
        split
        next hentry =>
          have hne : entry ≠ target := by
            intro heq
            subst entry
            contradiction
          rw [List.count_cons_of_ne hne, ih]
        next =>
          exact ih

/-- Counting one target is the length of its equality-filter fiber. -/
lemma length_filter_decide
    {α : Type*}
    [DecidableEq α]
    (target : α) :
    ∀ source : List α,
      (source.filter fun entry => decide (entry = target)).length =
        source.count target
  | [] => by
      rfl
  | entry :: source => by
      by_cases hentry : entry = target
      · subst entry
        simp [length_filter_decide target source]
      · simp [hentry, length_filter_decide target source]

/-- The strict-correction-plus-retained multiplicity recurrence survives an
arbitrary cutoff filter. -/
lemma count_filter_move
    {α : Type*}
    [DecidableEq α]
    (keep : CWord α → Bool)
    (left target : CWord α)
    (rights : List (CWord α)) :
    ((moveHigherTrace left rights).filter keep).count target =
      ((moveCorrectionTrace left rights).filter keep).count target +
        (rights.filter keep).count target := by
  by_cases htarget : keep target = true
  · simp [htarget, count_move_higher]
  · simp [count_filter_ite, htarget]

/-- One selected stable-routing step obeys the strict-correction-plus-retained
count recurrence. -/
lemma count_stable_current
    {α : Type*}
    [DecidableEq α]
    (isCurrent : CWord α → Bool)
    (word target : CWord α)
    (words : List (CWord α))
    (hcurrent : isCurrent word = true) :
    ((stableRoute isCurrent (word :: words)).1).count target =
      (moveCorrectionTrace word (stableRoute isCurrent words).1).count
          target +
        ((stableRoute isCurrent words).1).count target := by
  rw [stableRoute, if_pos hcurrent]
  exact count_move_higher word target _

/-- One unselected stable-routing step simply retains its source occurrence. -/
lemma route_fst_current
    {α : Type*}
    [DecidableEq α]
    (isCurrent : CWord α → Bool)
    (word target : CWord α)
    (words : List (CWord α))
    (hcurrent : isCurrent word ≠ true) :
    ((stableRoute isCurrent (word :: words)).1).count target =
      ([word].count target) +
        ((stableRoute isCurrent words).1).count target := by
  rw [stableRoute, if_neg hcurrent]
  simp only [List.count_cons, List.count_nil, Nat.zero_add]
  omega

/-- The filtered multiplicity shadow of one selected stable-routing step. -/
lemma filter_fst_current
    {α : Type*}
    [DecidableEq α]
    (keep isCurrent : CWord α → Bool)
    (word target : CWord α)
    (words : List (CWord α))
    (hcurrent : isCurrent word = true) :
    (((stableRoute isCurrent (word :: words)).1).filter keep).count target =
      ((moveCorrectionTrace word
          (stableRoute isCurrent words).1).filter keep).count target +
        (((stableRoute isCurrent words).1).filter keep).count target := by
  rw [stableRoute, if_pos hcurrent]
  exact count_filter_move keep word target _

/-- The filtered multiplicity shadow of one unselected stable-routing step. -/
lemma filter_stable_current
    {α : Type*}
    [DecidableEq α]
    (keep isCurrent : CWord α → Bool)
    (word target : CWord α)
    (words : List (CWord α))
    (hcurrent : isCurrent word ≠ true) :
    (((stableRoute isCurrent (word :: words)).1).filter keep).count target =
      ([word].filter keep).count target +
        (((stableRoute isCurrent words).1).filter keep).count target := by
  rw [stableRoute, if_neg hcurrent]
  by_cases htarget : keep target = true
  · simp [htarget, List.count_cons]
    omega
  · simp [count_filter_ite, htarget]

/-- Iterate the strict swap-correction operator for one fixed left word. -/
def iteratedMoveTrace
    {α : Type*}
    (left : CWord α) :
    ℕ → List (CWord α) → List (CWord α)
  | 0, rights => rights
  | steps + 1, rights =>
      moveCorrectionTrace left
        (iteratedMoveTrace left steps rights)

/-- Every strict correction raises a lower weight bound by the weight of the
left word. -/
lemma left_move_trace
    {α : Type*}
    (wt : α → ℕ)
    (lowerWeight : ℕ)
    (left : CWord α)
    (rights : List (CWord α))
    (hrights : ∀ right ∈ rights, lowerWeight ≤ right.weight wt)
    (emitted : CWord α)
    (hemitted : emitted ∈ moveCorrectionTrace left rights) :
    left.weight wt + lowerWeight ≤ emitted.weight wt := by
  rcases List.mem_map.mp hemitted with ⟨right, hright, rfl⟩
  simp only [CWord.weight_commutator]
  exact Nat.add_le_add_left (hrights right hright) _

/-- Iterating strict swap corrections raises a lower weight bound linearly in
the number of iterations. -/
lemma steps_iterated_move
    {α : Type*}
    (wt : α → ℕ)
    (lowerWeight : ℕ)
    (left : CWord α)
    (rights : List (CWord α))
    (hrights : ∀ right ∈ rights, lowerWeight ≤ right.weight wt) :
    ∀ (steps : ℕ)
      (emitted : CWord α),
      emitted ∈ iteratedMoveTrace left steps rights →
        steps * left.weight wt + lowerWeight ≤ emitted.weight wt
  | 0, emitted, hemitted => by
      simpa using hrights emitted hemitted
  | steps + 1, emitted, hemitted => by
      have hbound :=
        left_move_trace
          wt (steps * left.weight wt + lowerWeight) left
          (iteratedMoveTrace left steps rights)
          (fun right hright =>
            steps_iterated_move
              wt lowerWeight left rights hrights steps right hright)
          emitted hemitted
      simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hbound

/--
After enough strict swap-correction iterations, no occurrence survives below
a fixed cutoff.
-/
lemma filter_iterated_move
    {α : Type*}
    (wt : α → ℕ)
    (lowerWeight cutoff : ℕ)
    (left : CWord α)
    (rights : List (CWord α))
    (hrights : ∀ right ∈ rights, lowerWeight ≤ right.weight wt)
    (steps : ℕ)
    (hcutoff : cutoff ≤ steps * left.weight wt + lowerWeight) :
    (iteratedMoveTrace left steps rights).filter
        (fun word => decide (word.weight wt < cutoff)) =
      [] := by
  apply List.filter_eq_nil_iff.mpr
  intro word hword
  simp only [decide_eq_true_eq]
  intro hwordCutoff
  have hbound :=
    steps_iterated_move
      wt lowerWeight left rights hrights steps word hword
  omega

end CWTrace
end TCTex
end Towers
