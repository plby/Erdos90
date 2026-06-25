import Towers.Group.Zassenhaus.ReductionPoweredBridge
import Towers.Group.Zassenhaus.SourceRecollectionOperations
import
  Towers.Group.Zassenhaus.ClassifiedPacketRecollection

/-!
# Concrete adapter for recollected transient inner-reduction packets

The order-preserving transient packet recollector emits an ordinary bounded
source for `[inner ^ e, right]`.  The existing concrete powered-bridge API
represents the same value by its temporary correction packet.  This file
connects the two representations and exposes the recollected transient packet
through the ordinary semantic source-recollection interface.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

open IPBridge

namespace PFSubsti.TAPkt

/--
The ordinary source emitted by classified transient recollection evaluates
like the concrete temporary correction packet.
-/
lemma
    recollected_classified_factors
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
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (packet.source_classified_terms
          factory hinputWeight factor innerWord rightWord hword).higherSource =
      SPFactora.listEval q
        (correctionPacket packet hinputWeight factor innerWord rightWord
          hrecipe).factors := by
  rw [
    packet.recollection_classified_terms,
    list_packet_factors]

end PFSubsti.TAPkt

namespace TSRecol

/--
Expose classified transient recollection as an ordinary recollection of the
concrete temporary correction packet.
-/
noncomputable def correction_transient_factory
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
        hrecipe).factors := by
  let recollection :=
    packet.source_classified_terms factory
      hinputWeight factor innerWord rightWord hword
  exact
    {
      higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_weight_least :=
        recollection.higher_weight_least
      list_higher_raw := fun q =>
        packet.recollected_classified_factors
          factory hinputWeight factor innerWord rightWord hword hrecipe q
    }

end TSRecol

end TCTex
end Towers
