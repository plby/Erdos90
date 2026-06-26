import Towers.Group.Zassenhaus.GeneratedOuterRouting
import Towers.Group.Zassenhaus.StructuralActiveFactory

/-!
# Generated-child structural restart routing

The structural-restart adapter for transient frontiers separates the
strictly-lighter inner root from the outer cutoff-defect recursion.  The
generated outer-residual adapter further restricts the outer recursion to the
singleton strict tails and conjugation packets actually emitted by an
ordered residual.

This file composes those two interfaces.  Frontier terms already at the
nilpotent cutoff close directly; active terms use generated-child outer
residual routing and restart temporary-packet recursion at the strictly
lighter reworded inner root.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  BRRoute

/--
Close one active decomposable transient frontier using only its generated
outer-residual children and a strictly-smaller-root restart handler.
-/
noncomputable def generated_smaller_restart
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    {outerExpansion :
      TWExp H inputWeight}
    (routing :
      BRRoute
        H packet hinputWeight outerExpansion)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hlowerWeight :
      lowerWeight ≤
        outerExpansion.word.weight PEAddres.weight)
    (houterTruncated :
      outerExpansion.word.weight PEAddres.weight < n)
    (outerRecursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecol
            n lowerWeight H child)
    (restart :
      TSRestar
        (n := n) H outerExpansion) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] := by
  let residualRouting :=
    TGRoute.of_recursiveResults
      split hinputWeight outerExpansion houterTruncated routing.innerWord
        routing.rightWord routing.word_eq outerRecursiveResults
  apply residualRouting.sourcerec_frontier routing.word_eq
  by_cases hinner :
      routing.innerWord.weight PEAddres.weight < n
  · exact
      packet.transient_result_reword
        hinputWeight outerExpansion routing.innerWord routing.rightWord hinner
          (restart.sourceRecollection
            (outerExpansion.reword routing.innerWord)
              routing.reword_inner_outer
                lowerWeight hlowerWeight)
  · exact
      (packet
        |>.reachably_terminal_inner
          hinputWeight outerExpansion routing.innerWord routing.rightWord
            routing.word_eq (by omega)
        |>.weaken hlowerWeight
        |>.sourceRecollection)

end
  BRRoute

namespace PFSubsti.TAPkt

open SOTerm
open TTRecol

/--
Recollect a temporary classified packet through generated-child structural
restart routing.  Frontier terms at the cutoff close immediately.
-/
noncomputable def
    recollect_smaller_restarts
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
            FrontierDefectMultiset n child [.frontier expansion] →
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
        fun expansion hexpansion => by
          have hexpansionWeight :
              lowerWeight ≤
                expansion.word.weight PEAddres.weight :=
            hlowerWeight.trans <|
              packet
                |>.outer_classified_terms
                  hinputWeight outerExpansion innerWord rightWord hword
                    (.frontier expansion) hexpansion
          by_cases hexpansionTruncated :
              expansion.word.weight PEAddres.weight < n
          · let routing :=
              BRRoute.classified_inner_frontier
                packet hinputWeight outerExpansion innerWord rightWord
                  expansion hexpansion
            exact
              routing.generated_smaller_restart split
                hexpansionWeight hexpansionTruncated
                  (frontierRecursiveResults expansion hexpansion)
                  (restart expansion hexpansion)
          · exact
              (STContex.singleton_frontier
                expansion hexpansionWeight
                  (Nat.le_of_not_gt hexpansionTruncated)).sourceRecollection

/--
Specialize generated-child structural restart routing to the first classified
packet emitted by an ordinary Hall factor.
-/
noncomputable def
    generated_smaller_restarts
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
            FrontierDefectMultiset n child [.frontier expansion] →
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
    packet
      |>.transient_inner_classified
        hinputWeight factor innerWord rightWord hword
  rw [← hterms]
  exact
    packet
      |>.recollect_smaller_restarts
        split hinputWeight outerExpansion innerWord rightWord hword le_rfl
          (fun expansion hexpansion =>
            frontierRecursiveResults expansion (hterms ▸ hexpansion))
          (fun expansion hexpansion =>
            restart expansion (hterms ▸ hexpansion))

end PFSubsti.TAPkt

namespace
  CSRestar

/--
Compile structural restart data through the generated-child outer-residual
route into the active classified-packet factory used by powered collection.
-/
noncomputable def generatedActiveFactory
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
      |>.generated_smaller_restarts
        (routing.split packet) hinputWeight factor innerWord rightWord hword
          (routing.frontierRecursiveResults packet hinputWeight factor
            innerWord rightWord hword hactive)
          (routing.restart packet hinputWeight factor innerWord rightWord
            hword hactive)

end
  CSRestar

end TCTex
end Towers
