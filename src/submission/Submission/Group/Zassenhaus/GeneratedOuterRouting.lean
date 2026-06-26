import
  Submission.Group.Zassenhaus.RestartOuterRouting
import Submission.Group.Zassenhaus.TransientConjugatedHigher

/-!
# Generated-child routing for transient outer residuals

The contextual callback interface is intentionally general: it can recollect
every mixed packet that descends in the frontier-defect multiset order.  A
local ordered residual uses a much smaller surface.  Its strict tails request
singleton transient recollections, and conjugating the recollected prefix
requests only the classified correction packets actually emitted by the
conjugation fold.

This file packages that generated-child surface directly.  It avoids asking
a structural scheduler to synthesize recollections for arbitrary mixed lists
whose attached terms are invisible to the frontier-defect measure.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt
namespace OBSplit

/-- Recollect the strict inverse suffix from its actual singleton children. -/
noncomputable def
    after_singleton_recollections
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (recollection :
      ∀ wordExpansion ∈
          split.strictAfterSource hinputWeight outerExpansion innerWord
            rightWord,
        TTRecola
          n lowerWeight H [wordExpansion]) :
    TTRecola
      n lowerWeight H
        (split.strictAfterSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.of_singletons _
    recollection

/-- Recollect the strict inverse prefix from its actual singleton children. -/
noncomputable def
    before_singleton_recollections
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (recollection :
      ∀ wordExpansion ∈
          split.strictBeforeSource hinputWeight outerExpansion
            innerWord rightWord,
        TTRecola
          n lowerWeight H [wordExpansion]) :
    TTRecola
      n lowerWeight H
        (split.strictBeforeSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.of_singletons _
    recollection

end OBSplit
end PFSubsti.TAPkt

/--
The generated recursive inputs used by one ordered outer residual.

The correction field ranges only over packets emitted while the transient
outer carrier is conjugating the already recollected strict prefix.
-/
structure TGRoute
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) where
  strictAfterRecollection :
    TTRecola
      n lowerWeight H
        (split.strictAfterSource hinputWeight outerExpansion innerWord
          rightWord)
  strictBeforeRecollection :
    TTRecola
      n lowerWeight H
        (split.strictBeforeSource hinputWeight outerExpansion innerWord
          rightWord)
  correctionPacketRecollection :
    ∀ factor ∈ strictBeforeRecollection.higherSource,
      TTRecol
        n lowerWeight H
          (packet.transientClassifiedTerms hinputWeight outerExpansion.neg
            (TWExp.rewordFactor factor
              factor.word))

namespace
  TGRoute

/--
Package singleton strict-tail recollections and the correction packets
emitted from their recollected prefix into the generated-child route.
-/
noncomputable def of_singletonRecollections
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (strictAfterRecollections :
      ∀ wordExpansion ∈
          split.strictAfterSource hinputWeight outerExpansion innerWord
            rightWord,
        TTRecola
          n lowerWeight H [wordExpansion])
    (strictBeforeRecollections :
      ∀ wordExpansion ∈
          split.strictBeforeSource hinputWeight outerExpansion
            innerWord rightWord,
        TTRecola
          n lowerWeight H [wordExpansion])
    (correctionPacketRecollection :
      ∀ factor ∈
          (split
            |>.before_singleton_recollections
              hinputWeight outerExpansion innerWord rightWord
                strictBeforeRecollections).higherSource,
        TTRecol
          n lowerWeight H
            (packet.transientClassifiedTerms hinputWeight outerExpansion.neg
              (TWExp.rewordFactor factor
                factor.word))) :
    TGRoute
      (lowerWeight := lowerWeight) H split hinputWeight outerExpansion
        innerWord rightWord where
  strictAfterRecollection :=
    split
      |>.after_singleton_recollections
        hinputWeight outerExpansion innerWord rightWord
          strictAfterRecollections
  strictBeforeRecollection :=
    split
      |>.before_singleton_recollections
        hinputWeight outerExpansion innerWord rightWord
          strictBeforeRecollections
  correctionPacketRecollection := correctionPacketRecollection

/--
Restrict the general contextual callback to the generated children actually
used by one ordered residual.
-/
noncomputable def of_recursiveResults
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (houterTruncated :
      outerExpansion.word.weight PEAddres.weight < n)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecol
            n lowerWeight H child) :
    TGRoute
      (lowerWeight := lowerWeight) H split hinputWeight outerExpansion
        innerWord rightWord where
  strictAfterRecollection :=
    split.after_recursive_results
      hinputWeight outerExpansion houterTruncated innerWord rightWord hword
        recursiveResults
  strictBeforeRecollection :=
    split.before_recursive_results
      hinputWeight outerExpansion houterTruncated innerWord rightWord hword
        recursiveResults
  correctionPacketRecollection := fun factor _ =>
    packet.transient_result_left hinputWeight
      outerExpansion.neg
      (TWExp.rewordFactor factor
        factor.word)
      (by simpa using houterTruncated) fun child hchild =>
        recursiveResults child (by
          simpa only [
            SOTerm.FrontierDefectMultiset,
            SOTerm.frontierMultisetCons,
            SOTerm.frontier_multiset_nil,
            TWExp.word_neg] using hchild)

/--
Compose the generated strict-tail and correction-packet inputs into a
recollection of the complete ordered residual.
-/
noncomputable def sourceRecollection
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {split :
      PFSubsti.TAPkt.OBSplit
        packet}
    {hinputWeight : 0 < inputWeight}
    {outerExpansion :
      TWExp H inputWeight}
    {innerWord rightWord : CWord (HEAddres H)}
    (routing :
      TGRoute
        (lowerWeight := lowerWeight) H split hinputWeight outerExpansion
          innerWord rightWord)
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    TTRecola
      n lowerWeight H
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) := by
  let conjugatedBefore :=
    packet.conjugatedSourceRecollection hinputWeight outerExpansion
      routing.strictBeforeRecollection.higherSource
        routing.strictBeforeRecollection.higher_source_truncated
          routing.strictBeforeRecollection.higher_weight_least
            routing.correctionPacketRecollection
  exact
    { higherSource :=
        routing.strictAfterRecollection.higherSource ++
          conjugatedBefore.higherSource
      higher_source_truncated := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact
            routing.strictAfterRecollection.higher_source_truncated factor
              hfactor
        · exact conjugatedBefore.higher_source_truncated factor hfactor
      higher_weight_least := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact
            routing.strictAfterRecollection.higher_weight_least
              factor hfactor
        · exact
            conjugatedBefore.higher_weight_least factor hfactor
      list_higher_raw := by
        intro q
        rw [SPFactora.listEval_append,
          routing.strictAfterRecollection.list_higher_raw,
          conjugatedBefore.transient_conjugated_raw,
          routing.strictBeforeRecollection.list_higher_raw,
          split.raw_strict_tails
            hinputWeight outerExpansion innerWord rightWord hword q]
        group }

/--
Compose an externally recollected temporary packet with the generated-child
outer-residual route, recovering the parent frontier singleton.
-/
noncomputable def sourcerec_frontier
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {split :
      PFSubsti.TAPkt.OBSplit
        packet}
    {hinputWeight : 0 < inputWeight}
    {outerExpansion :
      TWExp H inputWeight}
    {innerWord rightWord : CWord (HEAddres H)}
    (routing :
      TGRoute
        (lowerWeight := lowerWeight) H split hinputWeight outerExpansion
          innerWord rightWord)
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (packetRecollection :
      TTRecol
        n lowerWeight H
          (packet.transientInnerTerms hinputWeight
            outerExpansion innerWord rightWord)) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  packet.frontier_reworded_residual
    hinputWeight outerExpansion innerWord rightWord packetRecollection
      (routing.sourceRecollection hword)

end
  TGRoute

end TCTex
end Submission
