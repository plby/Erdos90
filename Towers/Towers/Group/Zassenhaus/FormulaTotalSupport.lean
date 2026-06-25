import Towers.Group.Zassenhaus.FormulaChooseSubstitution

/-!
# Total-weight support for substituted Hall-Petresco recipes

The ordinary supported correction factory records that every substituted
Hall-Petresco recipe word is strictly above each parent separately.  For
outer-bracket descent it is useful to retain the sharper lower bound: every
emitted correction has weight at least the sum of its two parent weights.

This file proves that bound without changing the existing factory interface.
It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HACoeff

namespace PFSubstia

/-- A substituted recipe word has at least the sum of its parent weights. -/
lemma add_weight_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    B.word.weight PEAddres.weight +
        A.word.weight PEAddres.weight ≤
      (wordExpansion hinputWeight R B A).word.weight
        PEAddres.weight := by
  rw [word_weight_expansion]
  exact Nat.add_le_add
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R))
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R))

/-- Every word in a substituted recipe list has total parent-weight support. -/
lemma add_weight_expansions
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (B A : SPFactora H inputWeight)
    {wordExpansion : SWExp H inputWeight}
    (hwordExpansion :
      wordExpansion ∈ wordExpansions hinputWeight recipes B A) :
    B.word.weight PEAddres.weight +
        A.word.weight PEAddres.weight ≤
      wordExpansion.word.weight PEAddres.weight := by
  rcases recipe_word_expansions hwordExpansion with
    ⟨R, _hR, rfl⟩
  exact add_weight_expansion hinputWeight R B A

/--
Every symbolic factor emitted by a substituted recipe list has total
parent-weight support.
-/
lemma add_factors_expansions
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (B A : SPFactora H inputWeight)
    {factor : SPFactora H inputWeight}
    (hfactor :
      factor ∈
        SWExp.listFactors
          (wordExpansions hinputWeight recipes B A)) :
    B.word.weight PEAddres.weight +
        A.word.weight PEAddres.weight ≤
      factor.word.weight PEAddres.weight := by
  rcases List.mem_flatMap.mp hfactor with
    ⟨wordExpansion, hwordExpansion, hfactor⟩
  rw [wordExpansion.of_mem_factors hfactor]
  exact
    add_weight_expansions
      hinputWeight recipes B A hwordExpansion

end PFSubstia

namespace PFSubsti.TAPkt

open PFSubstia

/--
Every retained factor in the truncated packet compiled from Hall-Petresco
recipes has total parent-weight support.
-/
lemma add_supported_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : SPFactora H inputWeight)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
    {factor : SPFactora H inputWeight}
    (hfactor :
      factor ∈
        (((packet.powerSupportedFactory
              hinputWeight lowerWeight).correctionPacketFactory)
          |>.packet B A hB hA).factors) :
    B.word.weight PEAddres.weight +
        A.word.weight PEAddres.weight ≤
      factor.word.weight PEAddres.weight := by
  apply add_factors_expansions
    hinputWeight packet.recipes B A
  exact (List.mem_filter.mp hfactor).1

end PFSubsti.TAPkt

end TCTex
end Towers
