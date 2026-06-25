import Towers.Group.Zassenhaus.TransientPacketClassification

/-!
# Compatibility of transient packet classifiers

The original inner-reduction classifier is the first-stage specialization of
the arbitrary transient classifier: its left input is an ordinary factor
reworded onto the inner Hall word and its right input is the unit-powered
right Hall word.

This file identifies the two APIs termwise and packetwise.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HACoeff

namespace PTSubsti

/--
The specialized first-stage classifier agrees with arbitrary transient
classification after rewording the ordinary factor and adjoining the
unit-powered right word.
-/
lemma classified_inner_transient
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    classifiedOuterTerm hinputWeight R factor innerWord
        rightWord hword =
      classifiedTransientTerm hinputWeight R
        (TWExp.rewordFactor factor innerWord)
        (TWExp.wordUnit rightWord) := by
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · rw [classified_outer_degree
      hinputWeight R factor innerWord rightWord hword hbalanced]
    have hweight :
        (wordExpansion hinputWeight R
            (TWExp.rewordFactor factor
              innerWord)
            (TWExp.wordUnit
              rightWord)).exponentWeight ≤
          (wordExpansion hinputWeight R
              (TWExp.rewordFactor factor
                innerWord)
              (TWExp.wordUnit
                rightWord)).word.weight PEAddres.weight := by
      simpa only [innerReductionExpansion] using
        (exponent_inner_expansion
          hinputWeight R factor innerWord rightWord hword).2 hbalanced
    rw [classified_attached_exponent
      hinputWeight R
        (TWExp.rewordFactor factor innerWord)
        (TWExp.wordUnit rightWord) hweight]
    rfl
  · have hfrontier : R.rightDegree < R.leftDegree :=
      Nat.lt_of_not_ge hbalanced
    rw [classified_inner_degree
      hinputWeight R factor innerWord rightWord hword hfrontier]
    have hweight :
        ¬ (wordExpansion hinputWeight R
            (TWExp.rewordFactor factor
              innerWord)
            (TWExp.wordUnit
              rightWord)).exponentWeight ≤
          (wordExpansion hinputWeight R
              (TWExp.rewordFactor factor
                innerWord)
              (TWExp.wordUnit
                rightWord)).word.weight PEAddres.weight := by
      simpa only [innerReductionExpansion] using
        not_inner_degree
          hinputWeight R factor innerWord rightWord hword hfrontier
    rw [classified_transient_exponent
      hinputWeight R
        (TWExp.rewordFactor factor innerWord)
        (TWExp.wordUnit rightWord) hweight]
    rfl

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti

/--
The complete specialized inner-reduction packet is the arbitrary transient
packet at the reworded-factor and unit-right-word inputs.
-/
lemma inner_classified_transient
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    packet.innerOuterTerms hinputWeight factor innerWord
        rightWord hword =
      packet.transientClassifiedTerms hinputWeight
        (TWExp.rewordFactor factor innerWord)
        (TWExp.wordUnit rightWord) := by
  rw [innerOuterTerms, transientClassifiedTerms]
  apply List.map_congr_left
  intro R _
  exact
    classified_inner_transient
      hinputWeight R factor innerWord rightWord hword

end PFSubsti.TAPkt

end TCTex
end Towers
