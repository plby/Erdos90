import Towers.Group.Zassenhaus.GeneratedPacketRouting
import Towers.Group.Zassenhaus.ContextualRecollection

/-!
# Active classified-packet factories from structural restarts

The contextual powered bridge consumes recollections of the first classified
packet emitted from an ordinary Hall factor.  Such a packet is the temporary
transient packet obtained by viewing the factor exponent on its own word.

This file specializes generated-packet structural restart routing to that
first packet and packages the result as the existing active classified-packet
factory interface.  The ordered basic split remains an explicit input: its
arbitrary-cutoff construction is a separate Hall-Petresco ordering task.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PFSubsti.TAPkt

/--
Recollect the first classified packet emitted by an ordinary Hall factor from
structural restart routing for its retained generated frontiers.
-/
noncomputable def
    recollection_smaller_restarts
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (frontierRecursiveResults :
      ∀ expansion,
        .frontier expansion ∈
            packet.innerOuterTerms hinputWeight factor
              innerWord rightWord hword →
          ∀ child,
            SOTerm.FrontierDefectMultiset
                n child [.frontier expansion] →
              TTRecol
                n (factor.word.weight PEAddres.weight) H child)
    (restart :
      ∀ expansion,
        .frontier expansion ∈
            packet.innerOuterTerms hinputWeight factor
              innerWord rightWord hword →
          TSRestar
            (n := n) H expansion) :
    TTRecol
      n (factor.word.weight PEAddres.weight) H
        (packet.innerOuterTerms hinputWeight factor
          innerWord rightWord hword) := by
  let outerExpansion :=
    TWExp.rewordFactor factor factor.word
  have hterms :=
    transient_inner_classified
      packet
        hinputWeight factor innerWord rightWord hword
  rw [← hterms]
  exact
    packet
      |>.classified_smaller_restarts
        split hinputWeight outerExpansion innerWord rightWord hword le_rfl
          (fun expansion hexpansion =>
            frontierRecursiveResults expansion (hterms ▸ hexpansion))
          (fun expansion hexpansion =>
            restart expansion (hterms ▸ hexpansion))

end PFSubsti.TAPkt

/--
All local data needed to compile structural-restart packet routing into the
active classified-packet factory consumed by contextual powered bridges.

The split field is intentionally visible.  It records the independent
arbitrary-cutoff Hall-Petresco ordering obligation rather than hiding it
inside transient recursion.
-/
structure
    CSRestar
    (d n inputWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  split :
    ∀ packet :
        PFSubsti.TAPkt.{u}
          d n,
      PFSubsti.TAPkt.OBSplit
        packet
  frontierRecursiveResults :
    ∀
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (hinputWeight : 0 < inputWeight)
      (factor : SPFactora H inputWeight)
      (innerWord rightWord : CWord (HEAddres H))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight PEAddres.weight + 1 < n →
        ∀ expansion,
          .frontier expansion ∈
              packet.innerOuterTerms hinputWeight factor
                innerWord rightWord hword →
            ∀ child,
              SOTerm.FrontierDefectMultiset
                  n child [.frontier expansion] →
                TTRecol
                  n (factor.word.weight PEAddres.weight) H child
  restart :
    ∀
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (hinputWeight : 0 < inputWeight)
      (factor : SPFactora H inputWeight)
      (innerWord rightWord : CWord (HEAddres H))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight PEAddres.weight + 1 < n →
        ∀ expansion,
          .frontier expansion ∈
              packet.innerOuterTerms hinputWeight factor
                innerWord rightWord hword →
            TSRestar
              (n := n) H expansion

namespace
  CSRestar

/--
Forget structural-restart routing into the active classified-packet factory
used by contextual powered bridge collection.
-/
noncomputable def toActiveFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (routing :
      CSRestar
        d n inputWeight H) :
    ACFtry
      d n inputWeight H where
  sourceRecollection packet hinputWeight factor innerWord rightWord hword
      hactive :=
    packet
      |>.recollection_smaller_restarts
        (routing.split packet) hinputWeight factor innerWord rightWord hword
          (routing.frontierRecursiveResults packet hinputWeight factor
            innerWord rightWord hword hactive)
          (routing.restart packet hinputWeight factor innerWord rightWord
            hword hactive)

end
  CSRestar

end TCTex
end Towers
