import Submission.Group.Zassenhaus.GeneratedPacketRouting

/-!
# Structural restart routing for generic generated classified packets

The temporary-packet router handles packets emitted after rewording one
decomposable outer transient carrier.  Conjugation corrections use the more
general classified packet built from two arbitrary transient parents.

Every attached output of such a packet is physically above either parent,
and every retained frontier is a generated commutator.  This file packages
the corresponding order-preserving folds and structural-restart adapters
rooted at either chosen parent.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

open SOTerm
open TTRecol

/--
Recollect a generic classified packet from its retained frontiers while
using the left parent for the physical support bound.
-/
noncomputable def
    terms_frontier_recollections
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hlowerWeight :
      lowerWeight ≤ B.word.weight PEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.transientClassifiedTerms hinputWeight B A →
          TTRecol
            n lowerWeight H [.frontier expansion]) :
    TTRecol
      n lowerWeight H (packet.transientClassifiedTerms hinputWeight B A) :=
  of_singletons _ fun term hterm => by
    cases term with
    | attached expansion =>
        exact
          singleton_attached expansion <|
            hlowerWeight.trans <| Nat.le_of_lt <|
              packet.left_transient_terms
                hinputWeight B A (.attached expansion) hterm
    | frontier expansion =>
        exact frontierRecollection expansion hterm

/--
Recollect a generic classified packet from its retained frontiers while
using the right parent for the physical support bound.
-/
noncomputable def
    recollection_transient_recollections
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hlowerWeight :
      lowerWeight ≤ A.word.weight PEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.transientClassifiedTerms hinputWeight B A →
          TTRecol
            n lowerWeight H [.frontier expansion]) :
    TTRecol
      n lowerWeight H (packet.transientClassifiedTerms hinputWeight B A) :=
  of_singletons _ fun term hterm => by
    cases term with
    | attached expansion =>
        exact
          singleton_attached expansion <|
            hlowerWeight.trans <| Nat.le_of_lt <|
              packet.right_classified_terms
                hinputWeight B A (.attached expansion) hterm
    | frontier expansion =>
        exact frontierRecollection expansion hterm

/--
Recollect a generic classified packet from structural restarts for every
retained generated frontier, rooted at its left parent.
-/
noncomputable def
    terms_smaller_restarts
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hlowerWeight :
      lowerWeight ≤ B.word.weight PEAddres.weight)
    (frontierRecursiveResults :
      ∀ expansion,
        .frontier expansion ∈
            packet.transientClassifiedTerms hinputWeight B A →
          ∀ child,
            SOTerm.FrontierDefectMultiset
                n child [.frontier expansion] →
              TTRecol
                n lowerWeight H child)
    (restart :
      ∀ expansion,
        .frontier expansion ∈
            packet.transientClassifiedTerms hinputWeight B A →
          TSRestar
            (n := n) H expansion) :
    TTRecol
      n lowerWeight H (packet.transientClassifiedTerms hinputWeight B A) :=
  packet
    |>.terms_frontier_recollections
      hinputWeight B A hlowerWeight fun expansion hexpansion =>
        let routing :=
          BRRoute.transient_frontier
            packet hinputWeight B A expansion hexpansion
        routing.recollection_smaller_restart split
          (hlowerWeight.trans <| Nat.le_of_lt <|
            packet.left_transient_terms
              hinputWeight B A (.frontier expansion) hexpansion)
          (frontierRecursiveResults expansion hexpansion)
          (restart expansion hexpansion)

/--
Recollect a generic classified packet from structural restarts for every
retained generated frontier, rooted at its right parent.
-/
noncomputable def
    transient_smaller_restarts
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hlowerWeight :
      lowerWeight ≤ A.word.weight PEAddres.weight)
    (frontierRecursiveResults :
      ∀ expansion,
        .frontier expansion ∈
            packet.transientClassifiedTerms hinputWeight B A →
          ∀ child,
            SOTerm.FrontierDefectMultiset
                n child [.frontier expansion] →
              TTRecol
                n lowerWeight H child)
    (restart :
      ∀ expansion,
        .frontier expansion ∈
            packet.transientClassifiedTerms hinputWeight B A →
          TSRestar
            (n := n) H expansion) :
    TTRecol
      n lowerWeight H (packet.transientClassifiedTerms hinputWeight B A) :=
  packet
    |>.recollection_transient_recollections
      hinputWeight B A hlowerWeight fun expansion hexpansion =>
        let routing :=
          BRRoute.transient_frontier
            packet hinputWeight B A expansion hexpansion
        routing.recollection_smaller_restart split
          (hlowerWeight.trans <| Nat.le_of_lt <|
            packet.right_classified_terms
              hinputWeight B A (.frontier expansion) hexpansion)
          (frontierRecursiveResults expansion hexpansion)
          (restart expansion hexpansion)

end PFSubsti.TAPkt

end TCTex
end Submission
