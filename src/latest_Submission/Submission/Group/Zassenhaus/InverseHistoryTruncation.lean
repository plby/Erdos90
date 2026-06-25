import Submission.Group.Zassenhaus.PacketScheduling
import Submission.Group.Zassenhaus.RecursiveObstructions

/-!
# Truncating inverse-oriented Hall-Petresco packet histories

The operational Hall collector records direct corrections and inverse-oriented
conjugation corrections as `PHistor` values.  At a fixed nilpotent
cutoff, only histories of weight below the cutoff need to be retained by
polynomial consumers.  Histories at or above the cutoff still occur in exact
free-group traces, but every realization in their packets evaluates trivially
in the corresponding quotient.

This file packages that cutoff boundary without imposing a binary obstruction
tree on the operational trace.  It is intentionally not imported by the
existing collection proof.
-/

namespace Submission
namespace TCTex
namespace PHTrunc

open HACoeff
open BRSpec
open BFTrunc
open BRScheda
open HOPacket
open ITSched

/-- Inverse-oriented correction lies strictly above its first parent. -/
lemma weighted_inverse_left
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BRecipe) :
    weightedWordWeight leftWeight rightWeight B <
      weightedWordWeight leftWeight rightWeight (B.inverseCorrection A) := by
  rw [weighted_inverse_correction]
  exact Nat.lt_add_of_pos_right
    (weighted_weight_pos hleftWeight hrightWeight A)

/-- Inverse-oriented correction lies strictly above its second parent. -/
lemma weighted_inverse_right
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BRecipe) :
    weightedWordWeight leftWeight rightWeight A <
      weightedWordWeight leftWeight rightWeight (B.inverseCorrection A) := by
  rw [weighted_inverse_correction, Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (weighted_weight_pos hleftWeight hrightWeight B)

/-- A retained inverse-oriented correction descends from its first parent. -/
lemma correction_descends_left
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BRecipe)
    (hcutoff :
      weightedWordWeight leftWeight rightWeight (B.inverseCorrection A) < n) :
    CorrectionDescends n leftWeight rightWeight (B.inverseCorrection A) B := by
  unfold CorrectionDescends cutoffDefect
  have hweight :=
    weighted_inverse_left
      hleftWeight hrightWeight B A
  omega

/-- A retained inverse-oriented correction descends from its second parent. -/
lemma correction_descends_right
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BRecipe)
    (hcutoff :
      weightedWordWeight leftWeight rightWeight (B.inverseCorrection A) < n) :
    CorrectionDescends n leftWeight rightWeight (B.inverseCorrection A) A := by
  unfold CorrectionDescends cutoffDefect
  have hweight :=
    weighted_inverse_right
      hleftWeight hrightWeight B A
  omega

/-- Every operational packet history has positive weighted Hall degree. -/
lemma packet_history_pos
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (history : PHistor M N) :
    0 < history.weight leftWeight rightWeight :=
  weighted_weight_pos hleftWeight hrightWeight history.family.recipe

/-- A conjugation packet also lies strictly above the parent moved across it. -/
lemma history_parent_conjugate
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parent : BFam M N)
    (emitted : PHistor M N) :
    weightedWordWeight leftWeight rightWeight parent.recipe <
      (PHistor.conjugate parent emitted).weight leftWeight rightWeight := by
  rw [PHistor.weight_conjugate]
  exact Nat.lt_add_of_pos_right
    (packet_history_pos hleftWeight hrightWeight emitted)

/-- A retained conjugation packet descends from the emitted packet it conjugates. -/
lemma history_descends_emitted
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parent : BFam M N)
    (emitted : PHistor M N)
    (hcutoff :
      (PHistor.conjugate parent emitted).weight leftWeight rightWeight < n) :
    CorrectionDescends n leftWeight rightWeight
      (PHistor.conjugate parent emitted).family.recipe emitted.family.recipe := by
  exact correction_descends_right
    hleftWeight hrightWeight parent.recipe emitted.family.recipe hcutoff

/-- A retained conjugation packet descends from the parent it crosses. -/
lemma history_descends_parent
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parent : BFam M N)
    (emitted : PHistor M N)
    (hcutoff :
      (PHistor.conjugate parent emitted).weight leftWeight rightWeight < n) :
    CorrectionDescends n leftWeight rightWeight
      (PHistor.conjugate parent emitted).family.recipe parent.recipe := by
  exact correction_descends_left
    hleftWeight hrightWeight parent.recipe emitted.family.recipe hcutoff

/-- Families represented by an operational packet-history endpoint. -/
def historyFamilies
    {M N : ℕ}
    (histories : List (PHistor M N)) :
    List (BFam M N) :=
  histories.map PHistor.family

/-- Recipes represented by an operational packet-history endpoint. -/
def historyRecipes
    {M N : ℕ}
    (histories : List (PHistor M N)) :
    List BRecipe :=
  (historyFamilies histories).map BFam.recipe

/-- Operational histories whose packet weights survive the cutoff. -/
def retainedHistories
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (PHistor M N)) :
    List (PHistor M N) :=
  histories.filter fun history =>
    decide (history.weight leftWeight rightWeight < n)

/-- Operational histories whose packet weights have reached the cutoff. -/
def residualHistories
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (PHistor M N)) :
    List (PHistor M N) :=
  histories.filter fun history =>
    decide (n ≤ history.weight leftWeight rightWeight)

/-- Below-cutoff family packets retained by polynomial consumers. -/
def retainedFamilies
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (PHistor M N)) :
    List (BFam M N) :=
  historyFamilies (retainedHistories n leftWeight rightWeight histories)

/-- Above-cutoff family packets retained only as exact residual words. -/
def residualFamilies
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (PHistor M N)) :
    List (BFam M N) :=
  historyFamilies (residualHistories n leftWeight rightWeight histories)

/-- The surviving raw-history recipes ready for polynomial specialization. -/
def retainedRecipes
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (PHistor M N)) :
    List BRecipe :=
  historyRecipes (retainedHistories n leftWeight rightWeight histories)

@[simp]
lemma mem_retainedHistories
    {M N n leftWeight rightWeight : ℕ}
    {history : PHistor M N}
    {histories : List (PHistor M N)} :
    history ∈ retainedHistories n leftWeight rightWeight histories ↔
      history ∈ histories ∧ history.weight leftWeight rightWeight < n := by
  simp [retainedHistories]

@[simp]
lemma mem_residualHistories
    {M N n leftWeight rightWeight : ℕ}
    {history : PHistor M N}
    {histories : List (PHistor M N)} :
    history ∈ residualHistories n leftWeight rightWeight histories ↔
      history ∈ histories ∧ n ≤ history.weight leftWeight rightWeight := by
  simp [residualHistories]

/-- Every retained family packet has weight strictly below the cutoff. -/
lemma weighted_cutoff_families
    {M N n leftWeight rightWeight : ℕ}
    {histories : List (PHistor M N)}
    {family : BFam M N}
    (hfamily :
      family ∈ retainedFamilies n leftWeight rightWeight histories) :
    weightedWordWeight leftWeight rightWeight family.recipe < n := by
  rcases List.mem_map.mp hfamily with ⟨history, hhistory, rfl⟩
  exact (mem_retainedHistories.mp hhistory).2

/-- Every residual family packet has weight at least the cutoff. -/
lemma cutoff_weighted_families
    {M N n leftWeight rightWeight : ℕ}
    {histories : List (PHistor M N)}
    {family : BFam M N}
    (hfamily :
      family ∈ residualFamilies n leftWeight rightWeight histories) :
    n ≤ weightedWordWeight leftWeight rightWeight family.recipe := by
  rcases List.mem_map.mp hfamily with ⟨history, hhistory, rfl⟩
  exact (mem_residualHistories.mp hhistory).2

/--
Every concrete realization of every residual history packet has reached the
cutoff after label collapse.
-/
lemma words_realization_families
    {M N n leftWeight rightWeight : ℕ}
    (histories : List (PHistor M N)) :
    WordsAboveCutoff n leftWeight rightWeight
      (BFam.realizationList
        (residualFamilies n leftWeight rightWeight histories)) := by
  intro word hword
  rcases List.mem_flatMap.mp hword with ⟨family, hfamily, hword⟩
  unfold CollapsedWeightLeast
  rw [family.collapse_word word hword]
  exact cutoff_weighted_families hfamily

/--
Residual family realizations evaluate trivially in every matching nilpotent
quotient.
-/
lemma collapsed_realization_families
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (histories : List (PHistor M N)) :
    collapsedList x y
        (BFam.realizationList
          (residualFamilies n leftWeight rightWeight histories)) =
      1 := by
  exact collapsed_words_above
    hleftWeight hrightWeight hx hy hbot _
      (words_realization_families histories)

/--
Removing above-cutoff packet histories from an endpoint preserves collapsed
evaluation in every matching nilpotent quotient.
-/
lemma collapsed_realization_history
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (histories : List (PHistor M N)) :
    collapsedList x y
        (BFam.realizationList (historyFamilies histories)) =
      collapsedList x y
        (BFam.realizationList
          (retainedFamilies n leftWeight rightWeight histories)) := by
  induction histories with
  | nil =>
      rfl
  | cons history histories ih =>
      by_cases hweight : history.weight leftWeight rightWeight < n
      · simpa [historyFamilies, retainedFamilies, retainedHistories, hweight,
          BFam.realizationList_cons, collapsed_list_append] using ih
      · have hcutoff :
            n ≤ weightedWordWeight leftWeight rightWeight history.family.recipe :=
          Nat.le_of_not_gt hweight
        have hvanish :
            collapsedList x y history.family.realizations = 1 :=
          BFTrunc.BFam.collapsedlist_evaleqone_nleweight
            hleftWeight hrightWeight hx hy hbot history.family hcutoff
        simpa [historyFamilies, retainedFamilies, retainedHistories, hweight,
          BFam.realizationList_cons, collapsed_list_append,
          hvanish] using ih

namespace CHSched

/-- Below-cutoff families retained from a packetized inverse-oriented trace. -/
def retainedFamilies
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (schedule : CHSched M N) :
    List (BFam M N) :=
  PHTrunc.retainedFamilies
    n leftWeight rightWeight schedule.histories

/--
The retained below-cutoff packet endpoint has the same value as the raw
inverse-oriented trace in every matching nilpotent quotient.
-/
lemma collapsed_families_source
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (schedule : CHSched M N)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    collapsedList x y
        (BFam.realizationList
          (retainedFamilies n leftWeight rightWeight schedule)) =
      collapsedList x y
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N)) := by
  exact
    (collapsed_realization_history
      hleftWeight hrightWeight hx hy hbot schedule.histories).symm.trans
        (schedule.collapsed_realization_source x y)

end CHSched

end PHTrunc
end TCTex
end Submission
