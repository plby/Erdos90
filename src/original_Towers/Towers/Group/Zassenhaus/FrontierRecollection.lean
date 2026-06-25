import Towers.Group.Zassenhaus.RewriteSupport
import Towers.Group.Zassenhaus.FrontierWeightDescent

/-!
# Recollection interface for transient inner-reduction frontiers

An excess-left transient word cannot yet be attached to the ordinary symbolic
factor language, but its physical Hall-word weight is strictly larger than
the parent bracket.  This file isolates the recursive input needed to collect
such transient words and lifts it over the complete ordered frontier packet.

The resulting packet adapter only delegates active transient words of
strictly larger physical weight.  Words that have reached the nilpotent cutoff
recollect to the empty ordinary source immediately.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
An ordered transient source recollected into ordinary bounded symbolic
factors at a requested physical support bound.
-/
structure TTRecola
    {d inputWeight : ℕ}
    (n lowerWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (rawSource :
      List (TWExp H inputWeight)) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_weight_least :
    SPFactora.WordWeightLeast lowerWeight higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        TWExp.listValue (n := n) q rawSource

namespace TTRecola

/-- The empty transient source recollects to the empty ordinary source. -/
def empty
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    TTRecola
      n lowerWeight H ([] : List
        (TWExp H inputWeight)) where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro q
    rfl

/-- Concatenate independently recollected transient sources. -/
def append
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {leftSource rightSource :
      List (TWExp H inputWeight)}
    (left :
      TTRecola
        n lowerWeight H leftSource)
    (right :
      TTRecola
        n lowerWeight H rightSource) :
    TTRecola
      n lowerWeight H (leftSource ++ rightSource) where
  higherSource := left.higherSource ++ right.higherSource
  higher_source_truncated := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_source_truncated factor hfactor
    · exact right.higher_source_truncated factor hfactor
  higher_weight_least := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_weight_least factor hfactor
    · exact right.higher_weight_least factor hfactor
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append,
      left.list_higher_raw,
      right.list_higher_raw]
    simp [TWExp.listValue]

/-- Lower the requested physical support bound. -/
def weaken
    {d n inputWeight lowerWeight weakerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {rawSource :
      List (TWExp H inputWeight)}
    (recollection :
      TTRecola
        n lowerWeight H rawSource)
    (hweight : weakerWeight ≤ lowerWeight) :
    TTRecola
      n weakerWeight H rawSource where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least := fun factor hfactor =>
    hweight.trans
      (recollection.higher_weight_least factor hfactor)
  list_higher_raw :=
    recollection.list_higher_raw

/-- A transient singleton at or above the truncation cutoff recollects to the
empty ordinary source. -/
def singleton_n_weight
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (hweight :
      n ≤ wordExpansion.word.weight PEAddres.weight) :
    TTRecola
      n lowerWeight H [wordExpansion] where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro q
    simp [TWExp.listValue,
      wordExpansion.value_n_weight q hweight]

/-- Compose singleton transient recollections in their original order. -/
def of_singletons
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (rawSource :
      List (TWExp H inputWeight))
    (recollection :
      ∀ wordExpansion ∈ rawSource,
        TTRecola
          n lowerWeight H [wordExpansion]) :
    TTRecola
      n lowerWeight H rawSource := by
  induction rawSource with
  | nil =>
      exact empty
  | cons head tail ih =>
      simpa using
        (append
          (recollection head (by simp))
          (ih fun wordExpansion hwordExpansion =>
            recollection wordExpansion (by simp [hwordExpansion])))

end TTRecola

/--
Recursive collector for one active transient expansion.  The emitted ordinary
factors retain the physical support bound of the transient word.
-/
structure TTFtry
    (d n inputWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  sourceRecollection :
    ∀ wordExpansion :
        TWExp H inputWeight,
      wordExpansion.word.weight PEAddres.weight < n →
        TTRecola
          n (wordExpansion.word.weight PEAddres.weight)
            H [wordExpansion]

namespace
  TTFtry

/-- Delegate active transient words to the factory and erase words that have
already reached the truncation cutoff. -/
noncomputable def recollectionOrEmpty
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      TTFtry
        d n inputWeight H)
    (wordExpansion :
      TWExp H inputWeight) :
    TTRecola
      n (wordExpansion.word.weight PEAddres.weight)
        H [wordExpansion] := by
  by_cases hweight :
      wordExpansion.word.weight PEAddres.weight < n
  · exact factory.sourceRecollection wordExpansion hweight
  · exact
      TTRecola.singleton_n_weight
        wordExpansion (Nat.le_of_not_gt hweight)

end
  TTFtry

namespace PFSubsti.TAPkt

open
  TTFtry

/--
Collect an ordered excess-left frontier packet using only transient singleton
obligations at strictly larger physical Hall weights.
-/
noncomputable def
    recollection_inner_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      TTFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecola
      n (factor.word.weight PEAddres.weight + 1) H
        (packet.innerOuterExpansions hinputWeight factor
          innerWord rightWord) :=
  TTRecola.of_singletons _
    fun wordExpansion hwordExpansion =>
      (factory.recollectionOrEmpty wordExpansion).weaken
        (Nat.succ_le_of_lt
          (packet.outer_frontier_expansions
            hinputWeight factor innerWord rightWord hword hwordExpansion))

/-- At the next parent-stratum endpoint, the frontier packet recollects to the
empty ordinary source without invoking the recursive factory. -/
def
    recollection_expansions_terminal
    {d n inputWeight lowerWeight : ℕ}
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
    TTRecola
      n lowerWeight H
        (packet.innerOuterExpansions hinputWeight factor
          innerWord rightWord) where
  higherSource := []
  higher_source_truncated := by
    intro replacement hreplacement
    simp at hreplacement
  higher_weight_least := by
    intro replacement hreplacement
    simp at hreplacement
  list_higher_raw := by
    intro q
    simpa using
      (packet.frontier_expansions_n
        hinputWeight factor innerWord rightWord hword hcutoff q).symm

end PFSubsti.TAPkt

end TCTex
end Towers
