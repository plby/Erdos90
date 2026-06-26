import Towers.Group.Zassenhaus.RewriteSupport

/-!
# Membership monotonicity for symbolic Hall-power rewrites

The current truncated symbolic collector only swaps adjacent factors and emits
strictly heavier corrections.  It never erases an existing factor.  This small
invariant is useful when separating swap collection from the additional
coordinate compression needed by a full Hall collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- Every symbolic factor present before one swap remains present afterward. -/
lemma TSStep.mem_of_mem
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h : TSStep (n := n) H inputWeight L R)
    {factor : SPFactora H inputWeight}
    (hfactor : factor ∈ L) :
    factor ∈ R := by
  cases h with
  | obstruction P S B A C =>
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hfactor ⊢
      tauto

/-- Every symbolic factor present before a finite swap run remains present afterward. -/
lemma TSRwa.mem_of_mem
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h : TSRwa (n := n) L R)
    {factor : SPFactora H inputWeight}
    (hfactor : factor ∈ L) :
    factor ∈ R := by
  induction h with
  | refl =>
      exact hfactor
  | tail _ hstep ih =>
      exact hstep.mem_of_mem ih

end TCTex
end Towers
