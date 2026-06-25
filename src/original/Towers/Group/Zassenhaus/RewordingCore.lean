import Towers.Group.Zassenhaus.TransientPacketClassification

/-!
# Rewording transient symbolic Hall powers

Recursive powered bridges must carry an existing transient exponent from an
outer bracket onto an inner Hall word.  Ordinary symbolic factors cannot do
this unless their bounded recipe already fits the smaller word, but transient
carriers were introduced precisely to separate those two weights.

This file adds the exponent-preserving transient rewording operation and uses
it to form the classified temporary packet for `[inner ^ e, right]`.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace TWExp

/-- Change only the Hall word carrying a transient exponent. -/
def reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (word : CWord (HEAddres H)) :
    TWExp H inputWeight where
  word := word
  exponentWeight := wordExpansion.exponentWeight
  carrier := wordExpansion.carrier

@[simp]
lemma word_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (word : CWord (HEAddres H)) :
    (wordExpansion.reword word).word = word :=
  rfl

@[simp]
lemma exponentWeight_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (word : CWord (HEAddres H)) :
    (wordExpansion.reword word).exponentWeight =
      wordExpansion.exponentWeight :=
  rfl

@[simp]
lemma exponent_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (word : CWord (HEAddres H)) :
    (wordExpansion.reword word).exponent = wordExpansion.exponent :=
  rfl

@[simp]
lemma value_reword
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (word : CWord (HEAddres H))
    (q : ℕ) :
    (wordExpansion.reword word).value (n := n) q =
      word.eval PEAddres.freeLowerTruncation ^
        wordExpansion.exponent q :=
  rfl

@[simp]
lemma reword_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (leftWord rightWord : CWord (HEAddres H)) :
    (wordExpansion.reword leftWord).reword rightWord =
      wordExpansion.reword rightWord :=
  rfl

/--
The original ordinary-factor rewording is the specialization obtained by
rewording its transient view on the factor's own word.
-/
@[simp]
lemma reword_rewordFactor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (leftWord rightWord : CWord (HEAddres H)) :
    (rewordFactor factor leftWord).reword rightWord =
      rewordFactor factor rightWord :=
  rfl

end TWExp

namespace PFSubsti.TAPkt

/--
Classify the temporary packet for `[inner ^ e, right]` when `e` is already a
transient exponent carried by an arbitrary outer word.
-/
def transientInnerTerms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion : TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (SOTerm H inputWeight) :=
  packet.transientClassifiedTerms hinputWeight
    (wordExpansion.reword innerWord)
    (TWExp.wordUnit rightWord)

/--
The classified temporary packet evaluates to `[inner ^ e, right]`.
-/
lemma value_classified_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion : TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (q : ℕ) :
    SOTerm.listValue (n := n) q
        (packet.transientInnerTerms hinputWeight
          wordExpansion innerWord rightWord) =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          wordExpansion.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [transientInnerTerms,
    packet.value_transient_terms]
  simp [TWExp.value]
  rfl

end PFSubsti.TAPkt

end TCTex
end Towers
