import Towers.Group.Zassenhaus.TransientPacketSubstitution

/-!
# Attaching balanced transient inner-reduction terms

Rewording an outer commutator exponent onto its inner word enlarges the
arithmetic bound relative to that word.  A Hall-Petresco block may still be
attached to the ordinary bounded symbolic language after its right-word depth
is taken into account.

This file identifies the exact elementary criterion: the substituted block is
attachable precisely when its left block degree is at most its right block
degree.  Terms with excess left degree are therefore the genuine
post-cancellation frontier.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HACoeff

namespace PTSubsti

/--
The transient arithmetic bound of an inner-reduction block fits its physical
Hall word exactly on the balanced side `leftDegree ≤ rightDegree`.
-/
lemma exponent_inner_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    (innerReductionExpansion hinputWeight R factor innerWord
        rightWord).exponentWeight ≤
          (innerReductionExpansion hinputWeight R factor innerWord
            rightWord).word.weight PEAddres.weight ↔
      R.leftDegree ≤ R.rightDegree := by
  rw [exponent_outer_expansion,
    inner_reduction_expansion, hword]
  change
    R.leftDegree *
          (innerWord.weight PEAddres.weight +
            rightWord.weight PEAddres.weight) ≤
        R.leftDegree *
            innerWord.weight PEAddres.weight +
          R.rightDegree *
            rightWord.weight PEAddres.weight ↔
      R.leftDegree ≤ R.rightDegree
  rw [Nat.mul_add, Nat.add_le_add_iff_left]
  exact Nat.mul_le_mul_right_iff
    (CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
      rightWord)

/--
Attach one balanced transient inner-reduction block to the ordinary symbolic
Hall word-expansion language.
-/
def attachedInnerExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : R.leftDegree ≤ R.rightDegree) :
    SWExp H inputWeight :=
  (innerReductionExpansion hinputWeight R factor innerWord rightWord)
    |>.toWordExpansion
      ((exponent_inner_expansion
        hinputWeight R factor innerWord rightWord hword).2 hbalanced)

@[simp]
lemma attached_inner_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : R.leftDegree ≤ R.rightDegree) :
    (attachedInnerExpansion hinputWeight R factor innerWord
      rightWord hword hbalanced).word =
        (innerReductionExpansion hinputWeight R factor innerWord
          rightWord).word :=
  rfl

@[simp]
lemma exponent_attached_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : R.leftDegree ≤ R.rightDegree) :
    (attachedInnerExpansion hinputWeight R factor innerWord
      rightWord hword hbalanced).exponent =
        fun q : ℕ =>
          BRSpec.coefficientValue R
            (factor.exponent q) 1 := by
  rw [attachedInnerExpansion,
    TWExp.exponent_word_expansion,
    exponent_reduction_expansion]

end PTSubsti

end TCTex
end Towers
