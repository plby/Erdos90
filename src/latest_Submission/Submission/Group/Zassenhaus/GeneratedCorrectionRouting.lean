import Submission.Group.Zassenhaus.GeneratedClassifiedRouting
import Submission.Group.Zassenhaus.GeneratedOuterRouting

/-!
# Generated correction routing for transient outer residuals

An ordered outer residual has two strict transient tails and a conjugation
fold over the recollected prefix.  Each correction packet emitted by that
fold is a generic classified transient packet rooted at the negated outer
carrier.

This file uses generic generated-packet structural restarts to construct the
correction-packet field of the restricted outer-residual routing record.  The
remaining inputs are exactly the strict-tail singleton recollections and the
generated frontier restarts that a scheduler must supply.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  TGRoute

/--
Construct restricted outer-residual routing from recollected strict tails
and structural restarts for each emitted correction-packet frontier.
-/
noncomputable def correction_smaller_restarts
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
    (hlowerWeight :
      lowerWeight ≤
        outerExpansion.word.weight PEAddres.weight)
    (strictAfterRecollection :
      TTRecola
        n lowerWeight H
          (split.strictAfterSource hinputWeight outerExpansion
            innerWord rightWord))
    (strictBeforeRecollection :
      TTRecola
        n lowerWeight H
          (split.strictBeforeSource hinputWeight outerExpansion
            innerWord rightWord))
    (frontierRecursiveResults :
      ∀ factor ∈ strictBeforeRecollection.higherSource,
        ∀ expansion,
          .frontier expansion ∈
              packet.transientClassifiedTerms hinputWeight outerExpansion.neg
                (TWExp.rewordFactor factor
                  factor.word) →
            ∀ child,
              SOTerm.FrontierDefectMultiset
                  n child [.frontier expansion] →
                TTRecol
                  n lowerWeight H child)
    (restart :
      ∀ factor ∈ strictBeforeRecollection.higherSource,
        ∀ expansion,
          .frontier expansion ∈
              packet.transientClassifiedTerms hinputWeight outerExpansion.neg
                (TWExp.rewordFactor factor
                  factor.word) →
            TSRestar
              (n := n) H expansion) :
    TGRoute
      (lowerWeight := lowerWeight) H split hinputWeight outerExpansion
        innerWord rightWord where
  strictAfterRecollection := strictAfterRecollection
  strictBeforeRecollection := strictBeforeRecollection
  correctionPacketRecollection := fun factor hfactor =>
    packet
      |>.terms_smaller_restarts
        split hinputWeight outerExpansion.neg
          (TWExp.rewordFactor factor
            factor.word)
          (by simpa only [TWExp.word_neg]
            using hlowerWeight)
          (frontierRecursiveResults factor hfactor)
          (restart factor hfactor)

/--
Construct restricted outer-residual routing directly from singleton
strict-tail recollections and generated correction-frontier restarts.
-/
noncomputable def
    recollections_smaller_restarts
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
    (hlowerWeight :
      lowerWeight ≤
        outerExpansion.word.weight PEAddres.weight)
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
    (frontierRecursiveResults :
      ∀ factor ∈
          (split
            |>.before_singleton_recollections
              hinputWeight outerExpansion innerWord rightWord
                strictBeforeRecollections).higherSource,
        ∀ expansion,
          .frontier expansion ∈
              packet.transientClassifiedTerms hinputWeight outerExpansion.neg
                (TWExp.rewordFactor factor
                  factor.word) →
            ∀ child,
              SOTerm.FrontierDefectMultiset
                  n child [.frontier expansion] →
                TTRecol
                  n lowerWeight H child)
    (restart :
      ∀ factor ∈
          (split
            |>.before_singleton_recollections
              hinputWeight outerExpansion innerWord rightWord
                strictBeforeRecollections).higherSource,
        ∀ expansion,
          .frontier expansion ∈
              packet.transientClassifiedTerms hinputWeight outerExpansion.neg
                (TWExp.rewordFactor factor
                  factor.word) →
            TSRestar
              (n := n) H expansion) :
    TGRoute
      (lowerWeight := lowerWeight) H split hinputWeight outerExpansion
        innerWord rightWord :=
  correction_smaller_restarts split hinputWeight outerExpansion
    innerWord rightWord hlowerWeight
      (split
        |>.after_singleton_recollections
          hinputWeight outerExpansion innerWord rightWord
            strictAfterRecollections)
      (split
        |>.before_singleton_recollections
          hinputWeight outerExpansion innerWord rightWord
            strictBeforeRecollections)
      frontierRecursiveResults restart

end
  TGRoute

end TCTex
end Submission
