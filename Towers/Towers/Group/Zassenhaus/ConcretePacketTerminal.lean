import Towers.Group.Zassenhaus.ClassifiedPacketTerminal
import
  Towers.Group.Zassenhaus.ConcreteClassifiedRecollection

/-!
# Concrete terminal adapter for classified transient packets

At the next parent-stratum endpoint, classified transient recollection no
longer needs a recursive factory.  This file exposes that terminal ordinary
source through the concrete temporary correction-packet API.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

open IPBridge

namespace PFSubsti.TAPkt

/-- The terminal classified source evaluates like the concrete temporary
correction packet. -/
lemma terminal_classified_higher
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
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (packet
          |>.outer_classified_terminal
            hinputWeight factor innerWord rightWord hword hcutoff).higherSource =
      SPFactora.listEval q
        (correctionPacket packet hinputWeight factor innerWord rightWord
          hrecipe).factors := by
  rw [
    classified_terms_terminal,
    list_packet_factors]

end PFSubsti.TAPkt

namespace TSRecol

/--
Expose terminal classified recollection as an ordinary recollection of the
concrete temporary correction packet.
-/
noncomputable def correction_transient_terminal
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
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight)
      H
      (correctionPacket packet hinputWeight factor innerWord rightWord
        hrecipe).factors := by
  let recollection :=
    packet
      |>.outer_classified_terminal
        hinputWeight factor innerWord rightWord hword hcutoff
  exact
    {
      higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_weight_least :=
        recollection.higher_weight_least
      list_higher_raw := fun q =>
        packet.terminal_classified_higher
          hinputWeight factor innerWord rightWord hword hrecipe hcutoff q
    }

end TSRecol

end TCTex
end Towers
