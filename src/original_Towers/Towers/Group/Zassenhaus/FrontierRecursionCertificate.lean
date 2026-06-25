import Towers.Group.Zassenhaus.FrontierRecollection

/-!
# Recursion certificates for transient inner-reduction frontiers

Transient frontier words are not ordinary bounded symbolic factors yet, but
their physical Hall-word weights still support the global cutoff recursion.
This file packages that recursion surface explicitly:

* transient words carry their own cutoff defect;
* strict defect descent is well-founded;
* the active frontier worklist retains exactly the words below the cutoff;
* every retained worklist entry strictly descends from its ordinary parent;
* the worklist is empty at the next parent-stratum endpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TWExp

/-- Remaining room below the nilpotent cutoff for one transient Hall word. -/
def cutoffDefect
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (wordExpansion : TWExp H inputWeight) :
    ℕ :=
  n - wordExpansion.word.weight PEAddres.weight

/-- A transient child descends from a transient parent when its defect drops. -/
def Descends
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (child parent : TWExp H inputWeight) :
    Prop :=
  child.cutoffDefect n < parent.cutoffDefect n

/-- Transient-word descent is well-founded because it is measured in `ℕ`. -/
lemma descends_wellFounded
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    WellFounded (@Descends d inputWeight H n) := by
  unfold Descends
  exact InvImage.wf (cutoffDefect n) Nat.lt_wfRel.wf

/-- The induction principle for cutoff-specific transient-word recursion. -/
theorem descends_induction
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {motive : TWExp H inputWeight → Prop}
    (step :
      ∀ parent,
        (∀ child, Descends n child parent → motive child) →
          motive parent)
    (wordExpansion :
      TWExp H inputWeight) :
    motive wordExpansion :=
  descends_wellFounded.induction wordExpansion step

/-- A transient word has positive defect exactly while it remains active. -/
lemma cutoff_defect_pos
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion :
      TWExp H inputWeight) :
    0 < wordExpansion.cutoffDefect n ↔
      wordExpansion.word.weight PEAddres.weight < n := by
  simp [cutoffDefect]

/-- A transient word has zero defect exactly once it reaches the cutoff. -/
lemma cutoff_defect_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion :
      TWExp H inputWeight) :
    wordExpansion.cutoffDefect n = 0 ↔
      n ≤ wordExpansion.word.weight PEAddres.weight := by
  exact Nat.sub_eq_zero_iff_le

/-- A retained physical weight increase gives strict transient recursion descent. -/
lemma descends_word_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {child parent :
      TWExp H inputWeight}
    (hweight :
      parent.word.weight PEAddres.weight <
        child.word.weight PEAddres.weight)
    (hchildTruncated :
      child.word.weight PEAddres.weight < n) :
    Descends n child parent := by
  unfold Descends cutoffDefect
  omega

/--
A transient child descends from an ordinary parent factor when its transient
cutoff defect is strictly smaller than the factor defect.
-/
def DescendsFromFactor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (child : TWExp H inputWeight)
    (parent : SPFactora H inputWeight) :
    Prop :=
  child.cutoffDefect n < parent.cutoffDefect n

end TWExp

namespace PFSubsti.TAPkt

/--
The retained traversal worklist for an inner-reduction frontier.  Words at or
above the cutoff are omitted because they already evaluate trivially.
-/
def innerActiveExpansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (TWExp H inputWeight) :=
  (packet.innerOuterExpansions hinputWeight factor
      innerWord rightWord).filter fun wordExpansion =>
    wordExpansion.word.weight PEAddres.weight < n

/-- Membership in the active worklist is frontier membership plus truncation. -/
lemma inner_active_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (wordExpansion : TWExp H inputWeight) :
    wordExpansion ∈
        packet.innerActiveExpansions hinputWeight
          factor innerWord rightWord ↔
      wordExpansion ∈
          packet.innerOuterExpansions hinputWeight factor
            innerWord rightWord ∧
        wordExpansion.word.weight PEAddres.weight < n := by
  simp [innerActiveExpansions]

/-- Every retained frontier worklist entry strictly descends from its parent. -/
lemma descends_frontier_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    {wordExpansion : TWExp H inputWeight}
    (hwordExpansion :
      wordExpansion ∈
        packet.innerActiveExpansions hinputWeight
          factor innerWord rightWord) :
    wordExpansion.DescendsFromFactor n factor := by
  rw [packet.inner_active_expansions] at hwordExpansion
  have hfactorTruncated :
      factor.word.weight PEAddres.weight < n :=
    (packet.outer_frontier_expansions
      hinputWeight factor innerWord rightWord hword hwordExpansion.1).trans
        hwordExpansion.2
  simpa [TWExp.DescendsFromFactor,
    TWExp.cutoffDefect] using
      (packet.defect_inner_expansions
        hinputWeight factor innerWord rightWord hword hfactorTruncated
          hwordExpansion.1)

/-- At the next parent-stratum endpoint, no active frontier work remains. -/
lemma expansions_nil_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    packet.innerActiveExpansions hinputWeight factor
        innerWord rightWord =
      [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro wordExpansion hwordExpansion
  rw [packet.inner_active_expansions] at hwordExpansion
  have hweight :=
    packet.outer_frontier_expansions
      hinputWeight factor innerWord rightWord hword hwordExpansion.1
  exact (not_lt_of_ge (hcutoff.trans (Nat.succ_le_of_lt hweight)))
    hwordExpansion.2

end PFSubsti.TAPkt

end TCTex
end Towers
