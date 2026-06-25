import Towers.Group.Zassenhaus.StructuralRestartRouting

/-!
# Structural restart routing for generated transient packets

The structural-restart frontier adapter closes one retained Hall-Petresco
frontier.  Complete temporary packets still have to preserve their original
recipe order: attached outputs return directly to ordinary symbolic factors,
while retained frontier outputs use that adapter in place.

This file packages the corresponding order-preserving fold.  Its recursive
inputs remain explicit for each retained frontier, so it does not collapse
the cutoff-defect callback and the strictly-smaller-root restart into one
fictional recursion order.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PFSubsti.TAPkt

open SOTerm
open TTRecol

/--
Recollect one temporary packet emitted while reducing an outer transient
commutator.  Attached terms close directly; retained frontiers are delegated
without changing their Hall-Petresco order.
-/
noncomputable def
    transient_frontier_recollections
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hlowerWeight :
      lowerWeight ≤
        outerExpansion.word.weight PEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.transientInnerTerms hinputWeight
              outerExpansion innerWord rightWord →
          TTRecol
            n lowerWeight H [.frontier expansion]) :
    TTRecol
      n lowerWeight H
        (packet.transientInnerTerms hinputWeight
          outerExpansion innerWord rightWord) :=
  of_singletons _ fun term hterm => by
    cases term with
    | attached expansion =>
        exact
          singleton_attached expansion <|
            hlowerWeight.trans <|
              packet
                |>.outer_classified_terms
                  hinputWeight outerExpansion innerWord rightWord hword
                    (.attached expansion) hterm
    | frontier expansion =>
        exact frontierRecollection expansion hterm

/--
Recollect one complete temporary packet from structural-restart routing for
each retained generated frontier.
-/
noncomputable def
    classified_smaller_restarts
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hlowerWeight :
      lowerWeight ≤
        outerExpansion.word.weight PEAddres.weight)
    (frontierRecursiveResults :
      ∀ expansion,
        .frontier expansion ∈
            packet.transientInnerTerms hinputWeight
              outerExpansion innerWord rightWord →
          ∀ child,
            SOTerm.FrontierDefectMultiset
                n child [.frontier expansion] →
              TTRecol
                n lowerWeight H child)
    (restart :
      ∀ expansion,
        .frontier expansion ∈
            packet.transientInnerTerms hinputWeight
              outerExpansion innerWord rightWord →
          TSRestar
            (n := n) H expansion) :
    TTRecol
      n lowerWeight H
        (packet.transientInnerTerms hinputWeight
          outerExpansion innerWord rightWord) :=
  packet
    |>.transient_frontier_recollections
      hinputWeight outerExpansion innerWord rightWord hword hlowerWeight
        fun expansion hexpansion =>
          let routing :=
            BRRoute.classified_inner_frontier
              packet hinputWeight outerExpansion innerWord rightWord expansion
                hexpansion
          routing.recollection_smaller_restart split
            (hlowerWeight.trans <|
              packet
                |>.outer_classified_terms
                  hinputWeight outerExpansion innerWord rightWord hword
                    (.frontier expansion) hexpansion)
            (frontierRecursiveResults expansion hexpansion)
            (restart expansion hexpansion)

end PFSubsti.TAPkt

end TCTex
end Towers

