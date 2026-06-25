import Towers.Group.Zassenhaus.TransientConjugatedHigher

/-!
# Ordered transient residual recollection by contextual conjugation

The strict-prefix part of an ordered transient residual is conjugated by its
possibly nonattachable transient parent.  Recollecting that conjugation
through generic transient packets removes the older matched ordinary-factor
hypothesis.

This file packages the completed recursive-step route.  It is intentionally
not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PFSubsti.TAPkt
namespace OBSplit

/--
Recollect an ordered transient residual by recursively collecting its strict
tails and conjugating the recollected prefix directly by the transient parent.
-/
noncomputable def
    recollect_matched_conjugator
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (step :
      TCReca
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    TTRecola
      n (outerExpansion.word.weight PEAddres.weight + 1) H
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) := by
  let afterRecollection :=
    split.recoll_after_inver step.toTransientFactory
      hinputWeight outerExpansion innerWord rightWord hword
  let beforeRecollection :=
    split.recoll_befor_inver step.toTransientFactory
      hinputWeight outerExpansion innerWord rightWord hword
  let conjugatedBefore :=
    packet.transient_conjugated_recollection hinputWeight
      step outerExpansion beforeRecollection.higherSource
        beforeRecollection.higher_source_truncated
          beforeRecollection.higher_weight_least
  exact
    { higherSource :=
        afterRecollection.higherSource ++ conjugatedBefore.higherSource
      higher_source_truncated := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact afterRecollection.higher_source_truncated factor hfactor
        · exact conjugatedBefore.higher_source_truncated factor hfactor
      higher_weight_least := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact
            afterRecollection.higher_weight_least factor hfactor
        · exact
            conjugatedBefore.higher_weight_least factor hfactor
      list_higher_raw := by
        intro q
        rw [SPFactora.listEval_append,
          afterRecollection.list_higher_raw,
          conjugatedBefore.transient_conjugated_raw,
          beforeRecollection.list_higher_raw,
          split.raw_strict_tails
            hinputWeight outerExpansion innerWord rightWord hword q]
        group }

/--
Compose contextual residual recollection with any recollection of the
classified reworded packet, obtaining the original arbitrary transient
frontier singleton without a matched ordinary conjugator.
-/
noncomputable def
    recollect_without_conjugator
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (step :
      TCReca
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight)
    (packetRecollection :
      TTRecol
        n lowerWeight H
          (packet.transientInnerTerms hinputWeight
            outerExpansion innerWord rightWord)) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  packet.frontier_reworded_residual
    hinputWeight outerExpansion innerWord rightWord packetRecollection
      ((split
        |>.recollect_matched_conjugator
          hinputWeight step outerExpansion innerWord rightWord hword).weaken
            (by omega))

/--
A complete contextual recursive step recollects an arbitrary commutator
frontier singleton with an ordered basic split, without attaching its
transient parent to one ordinary symbolic factor.
-/
noncomputable def
    without_matched_conjugator
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (step :
      TCReca
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  split
    |>.recollect_without_conjugator
      hinputWeight step outerExpansion innerWord rightWord hword houterWeight
        (step.sourceRecollection lowerWeight
          (packet.transientInnerTerms hinputWeight
            outerExpansion innerWord rightWord))

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers
