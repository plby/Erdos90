import Submission.Group.Zassenhaus.PacketClassification

/-!
# Weight descent on the transient inner-reduction frontier

The excess-left terms left behind by transient inner reduction are not
ordinary bounded symbolic factors yet, but they already carry the measure
needed by the global recursion.  Every such term has physical Hall-word
weight strictly above the original outer bracket.  Consequently its remaining
cutoff defect is strictly smaller, and every frontier packet vanishes once the
next parent stratum reaches the truncation cutoff.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff

namespace TWExp

/-- A transiently powered word lies in the lower-central layer predicted by
its physical Hall-word weight, independently of its arithmetic exponent
bound. -/
lemma value_central_series
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (wordExpansion : TWExp H inputWeight) :
    wordExpansion.value (n := n) q ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (wordExpansion.word.weight PEAddres.weight - 1) := by
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (wordExpansion.word.weight PEAddres.weight - 1)).zpow_mem
        (CWord.eval_lower_series
          PEAddres.freeLowerTruncation
          PEAddres.weight
          PEAddres.weight_pos
          PEAddres.free_truncation_series
          wordExpansion.word)
        (wordExpansion.exponent q)

/-- A transiently powered word at or above the truncation weight evaluates to
the identity. -/
lemma value_n_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (wordExpansion : TWExp H inputWeight)
    (hweight :
      n ≤ wordExpansion.word.weight PEAddres.weight) :
    wordExpansion.value (n := n) q = 1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hweight 1)
    (wordExpansion.value_central_series q)

/-- A finite transient packet whose physical words all reach the truncation
weight evaluates trivially. -/
lemma list_value_n
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (wordExpansions :
      List (TWExp H inputWeight))
    (hweight :
      ∀ wordExpansion ∈ wordExpansions,
        n ≤ wordExpansion.word.weight PEAddres.weight) :
    TWExp.listValue (n := n) q
        wordExpansions =
      1 := by
  induction wordExpansions with
  | nil =>
      rfl
  | cons wordExpansion wordExpansions ih =>
      change wordExpansion.value q *
          TWExp.listValue q wordExpansions =
        1
      rw [wordExpansion.value_n_weight q
        (hweight wordExpansion (by simp)),
        ih (fun next hnext => hweight next (by simp [hnext]))]
      exact one_mul 1

end TWExp

namespace PTSubsti

/-- An excess-left recipe uses its left parent at least twice. -/
lemma left_degree_right
    (R : BRecipe)
    (hfrontier : R.rightDegree < R.leftDegree) :
    1 < R.leftDegree := by
  have hrightPos := BRSpec.rightDegree_pos R
  omega

/--
Every excess-left transient output is physically strictly heavier than the
outer bracket from which it arose.
-/
lemma factor_inner_degree
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfrontier : R.rightDegree < R.leftDegree) :
    factor.word.weight PEAddres.weight <
      (innerReductionExpansion hinputWeight R factor innerWord
        rightWord).word.weight PEAddres.weight := by
  rw [inner_reduction_expansion, hword,
    CWord.weight_commutator]
  have hleftPos :=
    CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
      innerWord
  have hrightPos :=
    CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
      rightWord
  have hleftDegree := left_degree_right R hfrontier
  have hrightDegree :=
    BRSpec.rightDegree_pos R
  have hleftLt :
      innerWord.weight PEAddres.weight <
        R.leftDegree *
          innerWord.weight PEAddres.weight := by
    simpa using Nat.mul_lt_mul_of_pos_right hleftDegree hleftPos
  have hrightLe :
      rightWord.weight PEAddres.weight ≤
        R.rightDegree *
          rightWord.weight PEAddres.weight :=
    Nat.le_mul_of_pos_left _ hrightDegree
  exact add_lt_add_of_lt_of_le hleftLt hrightLe

/-- The physical frontier weight gains at least one full stratum. -/
lemma succ_inner_degree
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfrontier : R.rightDegree < R.leftDegree) :
    factor.word.weight PEAddres.weight + 1 ≤
      (innerReductionExpansion hinputWeight R factor innerWord
        rightWord).word.weight PEAddres.weight :=
  Nat.succ_le_of_lt
    (factor_inner_degree
      hinputWeight R factor innerWord rightWord hword hfrontier)

/-- While its parent is retained, an excess-left transient output strictly
decreases the cutoff-defect measure used by symbolic power recursion. -/
lemma defect_inner_degree
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfrontier : R.rightDegree < R.leftDegree)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    n -
          (innerReductionExpansion hinputWeight R factor innerWord
            rightWord).word.weight PEAddres.weight <
      SPFactora.cutoffDefect n factor := by
  rw [SPFactora.cutoffDefect]
  have hweight :=
    factor_inner_degree
      hinputWeight R factor innerWord rightWord hword hfrontier
  omega

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti

/-- The ordered transient expansions that remain after the balanced terms
have returned to the ordinary symbolic language. -/
def innerOuterExpansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (TWExp H inputWeight) :=
  packet.innerReductionRecipes.map fun R =>
    innerReductionExpansion hinputWeight R factor innerWord rightWord

/-- Every retained frontier expansion comes from an excess-left recipe in the
original Hall-Petresco packet. -/
lemma recipe_inner_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    {wordExpansion : TWExp H inputWeight}
    (hwordExpansion :
      wordExpansion ∈
        packet.innerOuterExpansions hinputWeight factor
          innerWord rightWord) :
    ∃ R ∈ packet.innerReductionRecipes,
      wordExpansion =
        innerReductionExpansion hinputWeight R factor innerWord
          rightWord := by
  rcases List.mem_map.mp hwordExpansion with ⟨R, hR, hwordExpansion⟩
  exact ⟨R, hR, hwordExpansion.symm⟩

/-- Every expansion in the frontier packet is physically strictly heavier
than its parent bracket. -/
lemma outer_frontier_expansions
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
        packet.innerOuterExpansions hinputWeight factor
          innerWord rightWord) :
    factor.word.weight PEAddres.weight <
      wordExpansion.word.weight PEAddres.weight := by
  rcases
      packet.recipe_inner_expansions
        hinputWeight factor innerWord rightWord hwordExpansion with
    ⟨R, hR, rfl⟩
  exact
    factor_inner_degree
      hinputWeight R factor innerWord rightWord hword
        ((packet.inner_reduction_recipes R).mp hR).2

/-- Each active frontier expansion strictly decreases the remaining cutoff
defect relative to its parent bracket. -/
lemma defect_inner_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    {wordExpansion : TWExp H inputWeight}
    (hwordExpansion :
      wordExpansion ∈
        packet.innerOuterExpansions hinputWeight factor
          innerWord rightWord) :
    n - wordExpansion.word.weight PEAddres.weight <
      SPFactora.cutoffDefect n factor := by
  have hweight :=
    packet.outer_frontier_expansions
      hinputWeight factor innerWord rightWord hword hwordExpansion
  rw [SPFactora.cutoffDefect]
  omega

/-- Once the next parent stratum reaches the cutoff, the complete transient
frontier packet evaluates trivially. -/
lemma frontier_expansions_n
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
      n ≤ factor.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (packet.innerOuterExpansions hinputWeight factor
          innerWord rightWord) =
      1 := by
  apply
    TWExp.list_value_n
  intro wordExpansion hwordExpansion
  exact hcutoff.trans
    (Nat.succ_le_of_lt
      (packet.outer_frontier_expansions
        hinputWeight factor innerWord rightWord hword hwordExpansion))

end PFSubsti.TAPkt

end TCTex
end Submission
