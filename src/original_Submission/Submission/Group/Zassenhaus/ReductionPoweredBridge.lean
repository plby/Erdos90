import Submission.Group.Zassenhaus.FactorSourceReduction
import Submission.Group.Zassenhaus.FormulaChooseSubstitution
import Submission.Group.Zassenhaus.SourceRecollectionOperations

/-!
# Powered-commutator bridge packets for outer Hall reduction

Reducing the inner word of `[inner, right] ^ e` first exposes a comparison
with `[inner ^ e, right]`.  Existing Hall-Petresco packets already collect the
latter commutator once the parent recipe is reattached to `inner`.

This file supplies that recipe restriction, the temporary symbolic factors,
and the resulting correction packet.  It deliberately stops before asserting
that `[inner ^ e, right] = [inner, right] ^ e`: their quotient is the remaining
powered-commutator bridge residual.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace BBRecipe

/--
Reuse a bounded recipe at a smaller target once its intrinsic output weight
is known to fit.
-/
def restrict
    {inputWeight largerWeight smallerWeight : ℕ}
    (recipe : BBRecipe inputWeight largerWeight)
    (hweight : recipe.outputWeight ≤ smallerWeight) :
    BBRecipe inputWeight smallerWeight where
  toPBRecipe := recipe.toPBRecipe
  outputWeight_le := hweight

@[simp]
lemma eval_restrict
    {inputWeight largerWeight smallerWeight : ℕ}
    (recipe : BBRecipe inputWeight largerWeight)
    (hweight : recipe.outputWeight ≤ smallerWeight) :
    (recipe.restrict hweight).eval = recipe.eval :=
  rfl

end BBRecipe

namespace SPFactora

/--
Reattach the exponent recipe of a symbolic factor to another Hall word once
the recipe's intrinsic output weight is bounded by the new word weight.
-/
def rewordRecipeOutput
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (word : CWord (HEAddres H))
    (hrecipe :
      factor.recipe.outputWeight ≤
        word.weight PEAddres.weight) :
    SPFactora H inputWeight where
  word := word
  coefficient := factor.coefficient
  recipe := factor.recipe.restrict hrecipe

@[simp]
lemma reword_output_weight
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (word : CWord (HEAddres H))
    (hrecipe :
      factor.recipe.outputWeight ≤
        word.weight PEAddres.weight) :
    (factor.rewordRecipeOutput word hrecipe).word = word :=
  rfl

@[simp]
lemma exponent_reword_output
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (word : CWord (HEAddres H))
    (hrecipe :
      factor.recipe.outputWeight ≤
        word.weight PEAddres.weight)
    (q : ℕ) :
    (factor.rewordRecipeOutput word hrecipe).exponent q =
      factor.exponent q :=
  rfl

@[simp]
lemma reword_recipe_output
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (word : CWord (HEAddres H))
    (hrecipe :
      factor.recipe.outputWeight ≤
        word.weight PEAddres.weight)
    (q : ℕ) :
    (factor.rewordRecipeOutput word hrecipe).eval (n := n) q =
      word.eval PEAddres.freeLowerTruncation ^
        factor.exponent q :=
  rfl

/-- A unit-exponent symbolic occurrence of an arbitrary Hall word. -/
def wordUnit
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H)) :
    SPFactora H inputWeight where
  word := word
  coefficient := 1
  recipe :=
    BBRecipe.empty inputWeight
      (word.weight PEAddres.weight)

@[simp]
lemma word_wordUnit
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H)) :
    (wordUnit (inputWeight := inputWeight) word).word = word :=
  rfl

@[simp]
lemma exponent_wordUnit
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H))
    (q : ℕ) :
    (wordUnit (inputWeight := inputWeight) word).exponent q = 1 := by
  simp [wordUnit, exponent, BBRecipe.eval,
    BBRecipe.empty, PBRecipe.eval,
    PBRecipe.empty]

@[simp]
lemma eval_wordUnit
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H))
    (q : ℕ) :
    (wordUnit (inputWeight := inputWeight) word).eval (n := n) q =
      word.eval PEAddres.freeLowerTruncation := by
  simp [eval, wordValue]

end SPFactora

namespace IPBridge

/-- The inner word carrying the exponent recipe of the original outer factor. -/
def innerPowerFactor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (innerWord : CWord (HEAddres H))
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    SPFactora H inputWeight :=
  factor.rewordRecipeOutput innerWord hrecipe

/-- The fixed right word, represented with exponent one. -/
def rightUnitFactor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (rightWord : CWord (HEAddres H)) :
    SPFactora H inputWeight :=
  SPFactora.wordUnit rightWord

/--
Collect `[inner ^ e, right]` using the existing Hall-Petresco adjacent-swap
packet.  The lower support bound is zero because these are temporary factors.
-/
def correctionPacket
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    TCPkt n
      (innerPowerFactor factor innerWord hrecipe)
      (rightUnitFactor (inputWeight := inputWeight) rightWord) :=
  ((packet.powerSupportedFactory hinputWeight 0)
    |>.correctionPacketFactory).packet
      (innerPowerFactor factor innerWord hrecipe)
      (rightUnitFactor (inputWeight := inputWeight) rightWord)
      (Nat.zero_le _) (Nat.zero_le _)

/-- The temporary Hall-Petresco packet evaluates to `[inner ^ e, right]`. -/
lemma list_packet_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (correctionPacket packet hinputWeight factor innerWord rightWord
          hrecipe).factors =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [(correctionPacket packet hinputWeight factor innerWord rightWord
    hrecipe).listEval_eq]
  simp [innerPowerFactor, rightUnitFactor]

/--
The raw powered-commutator bridge residual: invert the collected
`[inner ^ e, right]` packet and append the original outer factor.
-/
def residualRawSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    List (SPFactora H inputWeight) :=
  SPFactora.inverseList
      (correctionPacket packet hinputWeight factor innerWord rightWord
        hrecipe).factors ++
    [factor]

/--
The bridge residual is exactly the quotient of `[inner ^ e, right]` from the
original outer factor.
-/
lemma list_raw_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe) =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆⁻¹ *
        factor.eval q := by
  simp [residualRawSource, SPFactora.list_eval_inverse,
    list_packet_factors]

/--
The error in pulling a left power out of an outer commutator lies one layer
above the ordinary outer-bracket weight.
-/
lemma eval_zpow_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (innerWord rightWord : CWord (HEAddres H))
    (exponent : ℤ) :
    ⁅innerWord.eval
          (PEAddres.freeLowerTruncation
            (n := n)) ^ exponent,
      rightWord.eval
        (PEAddres.freeLowerTruncation
          (n := n))⁆ *
        (⁅innerWord.eval
              (PEAddres.freeLowerTruncation
                (n := n)),
            rightWord.eval
              (PEAddres.freeLowerTruncation
                (n := n))⁆ ^ exponent)⁻¹ ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (innerWord.weight PEAddres.weight +
            rightWord.weight PEAddres.weight) := by
  let innerValue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    innerWord.eval
      (PEAddres.freeLowerTruncation (n := n))
  let rightValue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    rightWord.eval
      (PEAddres.freeLowerTruncation (n := n))
  let innerWeight := innerWord.weight PEAddres.weight
  let rightWeight := rightWord.weight PEAddres.weight
  have hinnerWeight : 0 < innerWeight := by
    exact CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
        innerWord
  have hrightWeight : 0 < rightWeight := by
    exact CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
        rightWord
  have hinner :
      innerValue ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (innerWeight - 1) := by
    simpa [innerValue, innerWeight] using
      (CWord.eval_lower_series
        (PEAddres.freeLowerTruncation (n := n))
        PEAddres.weight
        PEAddres.weight_pos
        PEAddres.free_truncation_series
        innerWord)
  have hright :
      rightValue ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (rightWeight - 1) := by
    simpa [rightValue, rightWeight] using
      (CWord.eval_lower_series
        (PEAddres.freeLowerTruncation (n := n))
        PEAddres.weight
        PEAddres.weight_pos
        PEAddres.free_truncation_series
        rightWord)
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (inv_zpow_series
      hinner hright exponent)

/--
Once the first nested commutator reaches the cutoff, the left power can be
pulled out of the outer commutator exactly.
-/
lemma element_zpow_cutoff
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (innerWord rightWord : CWord (HEAddres H))
    (hcutoff :
      n ≤
        2 * innerWord.weight PEAddres.weight +
          rightWord.weight PEAddres.weight)
    (exponent : ℤ) :
    ⁅innerWord.eval
          (PEAddres.freeLowerTruncation
            (n := n)) ^ exponent,
      rightWord.eval
        (PEAddres.freeLowerTruncation
          (n := n))⁆ =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)),
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆ ^ exponent := by
  let innerValue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    innerWord.eval
      (PEAddres.freeLowerTruncation (n := n))
  let rightValue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    rightWord.eval
      (PEAddres.freeLowerTruncation (n := n))
  let innerWeight := innerWord.weight PEAddres.weight
  let rightWeight := rightWord.weight PEAddres.weight
  have hinnerWeight : 0 < innerWeight := by
    exact CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
        innerWord
  have hrightWeight : 0 < rightWeight := by
    exact CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
        rightWord
  have hinner :
      innerValue ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (innerWeight - 1) := by
    simpa [innerValue, innerWeight] using
      (CWord.eval_lower_series
        (PEAddres.freeLowerTruncation (n := n))
        PEAddres.weight
        PEAddres.weight_pos
        PEAddres.free_truncation_series
        innerWord)
  have hright :
      rightValue ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (rightWeight - 1) := by
    simpa [rightValue, rightWeight] using
      (CWord.eval_lower_series
        (PEAddres.freeLowerTruncation (n := n))
        PEAddres.weight
        PEAddres.weight_pos
        PEAddres.free_truncation_series
        rightWord)
  have herror :
      ⁅innerValue ^ exponent, rightValue⁆ *
            (⁅innerValue, rightValue⁆ ^ exponent)⁻¹ ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (2 * (innerWeight - 1) + (rightWeight - 1) + 2) :=
    inv_zpow_series
      hinner hright exponent
  have herrorOne :
      ⁅innerValue ^ exponent, rightValue⁆ *
          (⁅innerValue, rightValue⁆ ^ exponent)⁻¹ = 1 := by
    apply eq_bot_iff.mp
      SPFactora.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by omega) herror
  exact mul_inv_eq_one.mp herrorOne

/-- At the first nested-commutator cutoff, the raw bridge residual is trivial. -/
lemma list_raw_cutoff
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤
        2 * innerWord.weight PEAddres.weight +
          rightWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe) =
      1 := by
  rw [list_raw_source,
    element_zpow_cutoff
      innerWord rightWord hcutoff]
  simp [SPFactora.eval, SPFactora.wordValue, hword]

/--
At the first nested-commutator cutoff, the bridge residual recollects to the
empty higher source at any requested support bound.
-/
def source_recollection_cutoff
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤
        2 * innerWord.weight PEAddres.weight +
          rightWord.weight PEAddres.weight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
      (residualRawSource packet hinputWeight factor innerWord rightWord
        hrecipe) where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_weight_least := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa using
      (list_raw_cutoff
        packet hinputWeight factor innerWord rightWord hword hrecipe hcutoff
          q).symm

end IPBridge

end TCTex
end Submission
