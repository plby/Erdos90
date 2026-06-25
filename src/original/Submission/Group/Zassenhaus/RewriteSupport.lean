import Submission.Group.Zassenhaus.Truncation

/-!
# Lower-weight support for symbolic Hall power rewrites

Collection swaps retain their two input factors and emit only strictly heavier
corrections.  Consequently, any lower bound on the word weights in a symbolic
factor list is preserved by truncation and by every finite truncated rewrite
run.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace SPFactora

/-- Every factor in a list has word weight at least `lowerWeight`. -/
def WordWeightLeast
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (lowerWeight : ℕ)
    (L : List (SPFactora H inputWeight)) :
    Prop :=
  ∀ x ∈ L,
    lowerWeight ≤ x.word.weight PEAddres.weight

/-- Physical truncation preserves every lower bound on word weights. -/
lemma word_least_truncate
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L : List (SPFactora H inputWeight)}
    (hL : WordWeightLeast lowerWeight L) :
    WordWeightLeast lowerWeight (truncate n L) := by
  intro x hx
  exact hL x (List.mem_filter.mp hx).1

end SPFactora

/-- One truncated collection swap preserves every lower word-weight bound. -/
lemma TSStep.wordWeightLeast
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h : TSStep (n := n) H inputWeight L R)
    (hL : SPFactora.WordWeightLeast lowerWeight L) :
    SPFactora.WordWeightLeast lowerWeight R := by
  cases h with
  | obstruction P S B A C =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hxS
      · rcases List.mem_append.mp hx with hx | hxAB
        · rcases List.mem_append.mp hx with hxP | hxC
          · exact hL x (by simp [hxP])
          · exact (hL B (by simp)).trans
              (Nat.le_of_lt (C.word_weight_left x hxC))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxAB
          rcases hxAB with hxA | hxB
          · exact hL x (by simp [hxA])
          · exact hL x (by simp [hxB])
      · exact hL x (by simp [hxS])

/-- A finite truncated collection run preserves every lower word-weight bound. -/
lemma TSRwa.wordWeightLeast
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h : TSRwa (n := n) L R)
    (hL : SPFactora.WordWeightLeast lowerWeight L) :
    SPFactora.WordWeightLeast lowerWeight R := by
  induction h with
  | refl =>
      exact hL
  | tail hLR hstep ih =>
      exact hstep.wordWeightLeast ih

end TCTex
end Submission
