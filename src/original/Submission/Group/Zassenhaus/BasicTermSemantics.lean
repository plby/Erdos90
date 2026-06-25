import Submission.Group.Zassenhaus.TransientResidual
import Submission.Group.Zassenhaus.CompletePetrescoRecipe

/-!
# Semantics of the basic transient rewording term

The principal `(1, 1)` Hall-Petresco recipe produced while recollecting
`[inner ^ e, right]` carries the same word and exponent as the original outer
carrier `[inner, right] ^ e`.  This file records that semantic cancellation
point independently of any ordering or tail-recollection strategy.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PTSubsti

open BRSpec

/-- The principal temporary output after rewording an outer exponent inward. -/
def rewordedBasicExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    TWExp H inputWeight :=
  wordExpansion hinputWeight hallPair (outerExpansion.reword innerWord)
    (TWExp.wordUnit rightWord)

/-- The principal temporary output has the expected outer bracket word. -/
@[simp]
lemma word_reworded_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (rewordedBasicExpansion hinputWeight outerExpansion innerWord
      rightWord).word = .commutator innerWord rightWord := by
  simp [rewordedBasicExpansion, boundWord,
    TWExp.wordUnit]

/-- The principal temporary output retains the outer arithmetic bound. -/
@[simp]
lemma exponent_reworded_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (rewordedBasicExpansion hinputWeight outerExpansion innerWord
      rightWord).exponentWeight = outerExpansion.exponentWeight := by
  simp [rewordedBasicExpansion, wordExpansion,
    TWExp.wordUnit]

/-- The principal temporary output retains the outer exponent polynomial. -/
@[simp]
lemma exponent_reworded_basic
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (rewordedBasicExpansion hinputWeight outerExpansion innerWord
      rightWord).exponent = outerExpansion.exponent := by
  funext q
  simp [rewordedBasicExpansion]

/-- When the parent carries the expected bracket, the principal words agree. -/
lemma reworded_expansion_outer
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    (rewordedBasicExpansion hinputWeight outerExpansion innerWord
      rightWord).word = outerExpansion.word := by
  rw [word_reworded_expansion, hword]

/-- The principal temporary output evaluates exactly to its outer parent. -/
lemma value_reworded_outer
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (q : ℕ) :
    (rewordedBasicExpansion hinputWeight outerExpansion innerWord
      rightWord).value (n := n) q = outerExpansion.value q := by
  simp only [TWExp.value,
    reworded_expansion_outer hinputWeight outerExpansion
      innerWord rightWord hword,
    exponent_reworded_basic]

/-- The inverse principal output evaluates to the inverse outer parent. -/
lemma value_reworded_inv
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (q : ℕ) :
    (rewordedBasicExpansion hinputWeight outerExpansion innerWord
      rightWord).neg.value (n := n) q =
        (outerExpansion.value q)⁻¹ := by
  rw [TWExp.value_neg,
    value_reworded_outer hinputWeight outerExpansion
      innerWord rightWord hword q]

end PTSubsti

end TCTex
end Submission
