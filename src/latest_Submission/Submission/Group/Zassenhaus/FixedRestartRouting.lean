import
  Submission.Group.Zassenhaus.GeneratedStructuralRouting
import Submission.Group.Zassenhaus.Ordered
import
Submission.Group.Zassenhaus.FixedPoweredFactory

/-!
# Fixed-packet generated structural restart routing

Generated-child structural restart routing only needs the ordered split of the
selected Hall-Petresco packet used by the powered collector.  This file
packages the recursive callbacks for that one packet, compiles them into the
fixed-packet active factory, and feeds the resulting powered pieces into the
Hall-ranked outer-residual scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open OFRoute

/--
Recursive callbacks for generated transient frontiers emitted from one fixed
Hall-Petresco packet.
-/
structure
    SRCallba
    (d n inputWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (packet :
      PFSubsti.TAPkt.{u}
        d n) where
  frontierRecursiveResults :
    ∀
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

/--
Generated structural restart data for one fixed Hall-Petresco packet.  The
ordered split is no longer quantified over unrelated packets.
-/
structure
    TRRoutea
    (d n inputWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    extends
      SRCallba
        d n inputWeight H packet where
  split :
    PFSubsti.TAPkt.OBSplit
      packet

namespace
  TRRoutea

/--
Construct the fixed-packet route from its principal recipe invariant and
duplicate-free finite recipe inventory.
-/
noncomputable def principalNodup
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (callbacks :
      SRCallba
        d n inputWeight H packet)
    (principal :
      PFSubsti.TAPkt.PBRecipea
        packet)
    (hnodup : packet.recipes.Nodup) :
    TRRoutea
      d n inputWeight H packet where
  toSRCallba :=
    callbacks
  split := principal.ordered_split_nodup hnodup

/--
Compile one-packet structural restart data through generated-child routing
into the fixed-packet active classified collector.
-/
noncomputable def fixedActiveFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (routing :
      TRRoutea
        d n inputWeight H packet) :
    CRFtry
      d n inputWeight H packet where
  sourceRecollection hinputWeight factor innerWord rightWord hword hactive :=
    packet
      |>.generated_smaller_restarts
        routing.split hinputWeight factor innerWord rightWord hword
          (routing.frontierRecursiveResults hinputWeight factor innerWord
            rightWord hword hactive)
          (routing.restart hinputWeight factor innerWord rightWord hword
            hactive)

end
  TRRoutea

/--
Scheduler-facing powered recollections built over one fixed packet and its
generated structural restart route.
-/
structure
    PRRouteb
    (d n inputWeight : ℕ)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight) where
  activeRouting :
    TRRoutea
      d n inputWeight (concreteBasicCommutators.{u} d) packet
  pieces :
    PPFtry
      d n inputWeight packet hinputWeight activeRouting.fixedActiveFactory

namespace
  PRRouteb

/-- Forget fixed-packet generated powered routing as an ordinary outer factory. -/
noncomputable def outerRecollectionFactory
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (routing :
      PRRouteb
        d n inputWeight packet hinputWeight) :
    IRFtry
      d n inputWeight :=
  routing.pieces.outerRecollectionFactory

/--
Combine one-packet generated powered routing with the correction schedule and
strictly-deeper normalizers used by Hall-ranked recursion.
-/
noncomputable def rankedFactoryRouting
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (routing :
      PRRouteb
        d n inputWeight packet hinputWeight)
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d)) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) :=
  factoryPoweredPieces
    schedule normalizerAbove routing.pieces

end
  PRRouteb

namespace
  RRSchedua

/--
Construct one concrete Hall-tree residual by ranked recursion from fixed-packet
generated structural restart routing and indexed local branch cases.
-/
noncomputable def
    structural_restart_cases
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (routing :
      PRRouteb
        d n inputWeight packet hinputWeight)
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        TruncatedBranchCase
          (n := n) factor rankDefect)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) :
    TSRecollb
      (n := n) factor :=
  recollect_factory_cases hn hH
    (routing.rankedFactoryRouting schedule normalizerAbove)
      cases factor rankDefect

end
  RRSchedua

end TCTex
end Submission
