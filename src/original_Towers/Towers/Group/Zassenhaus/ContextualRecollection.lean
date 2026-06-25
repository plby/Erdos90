import Towers.Group.Zassenhaus.ReductionPoweredBridge
import Towers.Group.Zassenhaus.SourceRecollectionOperations
import Towers.Group.Zassenhaus.ClassifiedPacketTerminal

/-!
# Contextual recollection of transient inner-reduction packets

An arbitrary transient singleton is stronger than the recursion actually
needs.  Inner reduction produces a complete ordered classified packet, and
its excess-left terms may have to cancel in that packet context before they
return to the ordinary symbolic language.

This file exposes that contextual recursive input directly.  Recursion is
required only while one full stratum remains below the cutoff.  At the next
parent-stratum endpoint, the terminal classified-packet adapter closes the
obligation without invoking the recursive field.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

/--
Recursive recollection input for complete ordered classified packets.  The
recursive case is requested only when the next parent stratum is still below
the nilpotent cutoff.
-/
structure
    ACFtry
    (d n inputWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  sourceRecollection :
    ∀
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (hinputWeight : 0 < inputWeight)
      (factor : SPFactora H inputWeight)
      (innerWord rightWord : CWord (HEAddres H))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight PEAddres.weight + 1 < n →
        TTRecol
          n (factor.word.weight PEAddres.weight) H
            (packet.innerOuterTerms hinputWeight factor
              innerWord rightWord hword)

namespace
  ACFtry

/--
Dispatch a complete classified packet either to the contextual recursive
field or to the factory-free terminal endpoint.
-/
noncomputable def recollectionOrTerminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecol
      n (factor.word.weight PEAddres.weight) H
        (packet.innerOuterTerms hinputWeight factor
          innerWord rightWord hword) := by
  by_cases hactive :
      factor.word.weight PEAddres.weight + 1 < n
  · exact
      factory.sourceRecollection packet hinputWeight factor innerWord
        rightWord hword hactive
  · exact
      packet.outer_classified_terminal
        hinputWeight factor innerWord rightWord hword (Nat.le_of_not_gt hactive)

/--
The older singleton transient factory is a sufficient compatibility input for
the contextual recursive field.
-/
noncomputable def ofTransientFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      TTFtry
        d n inputWeight H) :
    ACFtry
      d n inputWeight H where
  sourceRecollection packet hinputWeight factor innerWord rightWord hword _ :=
    packet.source_classified_terms factory
      hinputWeight factor innerWord rightWord hword

end
  ACFtry

open IPBridge

namespace PFSubsti.TAPkt

/--
Any ordinary recollection of the complete classified packet evaluates like
the concrete temporary correction packet.
-/
lemma classified_recollection_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (recollection :
      TTRecol
        n (factor.word.weight PEAddres.weight) H
          (packet.innerOuterTerms hinputWeight factor
            innerWord rightWord hword))
    (q : ℕ) :
    SPFactora.listEval (n := n) q recollection.higherSource =
      SPFactora.listEval q
        (correctionPacket packet hinputWeight factor innerWord rightWord
          hrecipe).factors := by
  rw [recollection.list_higher_raw,
    packet.inner_reduction_terms,
    list_packet_factors]

end PFSubsti.TAPkt

namespace TSRecol

/--
Expose any contextual classified-packet recollection through the ordinary
temporary correction-packet source API.
-/
noncomputable def classified_terms_recollection
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (recollection :
      TTRecol
        n (factor.word.weight PEAddres.weight) H
          (packet.innerOuterTerms hinputWeight factor
            innerWord rightWord hword)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight)
      H
      (correctionPacket packet hinputWeight factor innerWord rightWord
        hrecipe).factors where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := fun q =>
    packet.classified_recollection_factors
      hinputWeight factor innerWord rightWord hword hrecipe recollection q

/--
The contextual recursive field, with automatic terminal dispatch, recollects
the concrete temporary correction packet.
-/
noncomputable def active_classified_factory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight)
      H
      (correctionPacket packet hinputWeight factor innerWord rightWord
        hrecipe).factors :=
  classified_terms_recollection packet
    hinputWeight factor innerWord rightWord hword hrecipe
      (factory.recollectionOrTerminal packet hinputWeight factor
        innerWord rightWord hword)

end TSRecol

end TCTex
end Towers
