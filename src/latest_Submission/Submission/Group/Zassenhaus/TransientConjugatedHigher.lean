import Submission.Group.Zassenhaus.Ordered
import Submission.Group.Zassenhaus.Transient

/-!
# Conjugating ordinary higher tails by transient Hall-power carriers

An active transient carrier need not attach to one ordinary symbolic factor.
Nevertheless, it can conjugate an already recollected ordinary higher tail:
move across the tail one factor at a time and recollect each emitted
commutator through the generic classified transient-packet API.

The callback-facing constructor uses descent from the transient conjugator,
so it is suitable inside the contextual well-founded resolver.  The compiled
recursive-step constructor is convenient after that resolver has been tied
into a fixpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

/--
An upward semantic recollection of an ordinary symbolic source conjugated by
one possibly nonattachable transient Hall-power carrier.
-/
structure
    TruncatedTransientConjugated
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (conjugator : TWExp H inputWeight)
    (rawSource : List (SPFactora H inputWeight)) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_weight_least :
    SPFactora.WordWeightLeast lowerWeight higherSource
  transient_conjugated_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        (conjugator.value (n := n) q)⁻¹ *
          SPFactora.listEval q rawSource *
            conjugator.value q

namespace PFSubsti.TAPkt

/--
Conjugate an ordinary higher source by a transient carrier one factor at a
time.  Every emitted correction bracket is supplied as a recollected generic
transient packet.
-/
noncomputable def conjugatedSourceRecollection
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (conjugator :
      TWExp H inputWeight) :
    ∀
      (rawSource : List (SPFactora H inputWeight)),
      SPFactora.IsTruncated n rawSource →
      SPFactora.WordWeightLeast lowerWeight rawSource →
      (∀ factor ∈ rawSource,
        TTRecol
          n lowerWeight H
            (packet.transientClassifiedTerms hinputWeight
              conjugator.neg
              (TWExp.rewordFactor factor
                factor.word))) →
      TruncatedTransientConjugated
        (n := n) (lowerWeight := lowerWeight) H conjugator rawSource
  | [], _, _, _ =>
      { higherSource := []
        higher_source_truncated := by
          intro factor hfactor
          simp at hfactor
        higher_weight_least := by
          intro factor hfactor
          simp at hfactor
        transient_conjugated_raw := by
          intro q
          simp }
  | head :: tail, hsourceTruncated, hsourceSupported,
      correctionRecollection =>
      let correction := correctionRecollection head (by simp)
      let tailRecollection :=
        packet.conjugatedSourceRecollection hinputWeight conjugator
          tail
          (fun factor hfactor =>
            hsourceTruncated factor (by simp [hfactor]))
          (fun factor hfactor =>
            hsourceSupported factor (by simp [hfactor]))
          (fun factor hfactor =>
            correctionRecollection factor (by simp [hfactor]))
      { higherSource :=
          correction.higherSource ++
            (head :: tailRecollection.higherSource)
        higher_source_truncated := by
          intro factor hfactor
          simp only [List.mem_cons, List.mem_append] at hfactor
          rcases hfactor with hfactor | rfl | hfactor
          · exact correction.higher_source_truncated factor hfactor
          · exact hsourceTruncated factor (by simp)
          · exact tailRecollection.higher_source_truncated factor hfactor
        higher_weight_least := by
          intro factor hfactor
          simp only [List.mem_cons, List.mem_append] at hfactor
          rcases hfactor with hfactor | rfl | hfactor
          · exact correction.higher_weight_least factor hfactor
          · exact hsourceSupported factor (by simp)
          · exact
              tailRecollection.higher_weight_least factor
                hfactor
        transient_conjugated_raw := by
          intro q
          simp only [SPFactora.listEval_cons,
            SPFactora.listEval_append]
          rw [correction.list_higher_raw,
            packet.value_transient_terms,
            TWExp.value_neg,
            TWExp.value_reword_self,
            tailRecollection.transient_conjugated_raw]
          group }

/--
Inside the contextual resolver for an active transient singleton, every
correction packet needed to conjugate an ordinary higher tail is available
from the recursive callback: it strictly descends from the conjugator.
-/
noncomputable def
    transient_conjugated_results
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (conjugator :
      TWExp H inputWeight)
    (hconjugatorTruncated :
      conjugator.word.weight PEAddres.weight < n)
    (rawSource : List (SPFactora H inputWeight))
    (hsourceTruncated :
      SPFactora.IsTruncated n rawSource)
    (hsourceSupported :
      SPFactora.WordWeightLeast lowerWeight rawSource)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier conjugator] →
          TTRecol
            n lowerWeight H child) :
    TruncatedTransientConjugated
      (n := n) (lowerWeight := lowerWeight) H conjugator rawSource :=
  packet.conjugatedSourceRecollection hinputWeight conjugator
    rawSource hsourceTruncated hsourceSupported fun factor _ =>
      packet.transient_result_left hinputWeight
        conjugator.neg
        (TWExp.rewordFactor factor
          factor.word)
        (by simpa using hconjugatorTruncated) fun child hchild =>
          recursiveResults child (by
            simpa only [
              SOTerm.FrontierDefectMultiset,
              SOTerm.frontierMultisetCons,
              SOTerm.frontier_multiset_nil,
              TWExp.word_neg] using hchild)

/--
A complete support-polymorphic contextual recursive step can recollect the
correction packets directly, without requiring the transient conjugator to
attach to one ordinary factor.
-/
noncomputable def
    transient_conjugated_recollection
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (step :
      TCReca
        d n inputWeight H)
    (conjugator :
      TWExp H inputWeight)
    (rawSource : List (SPFactora H inputWeight))
    (hsourceTruncated :
      SPFactora.IsTruncated n rawSource)
    (hsourceSupported :
      SPFactora.WordWeightLeast lowerWeight rawSource) :
    TruncatedTransientConjugated
      (n := n) (lowerWeight := lowerWeight) H conjugator rawSource :=
  packet.conjugatedSourceRecollection hinputWeight conjugator
    rawSource hsourceTruncated hsourceSupported fun factor _ =>
      step.sourceRecollection lowerWeight
        (packet.transientClassifiedTerms hinputWeight
          conjugator.neg
          (TWExp.rewordFactor factor
            factor.word))

end PFSubsti.TAPkt

end TCTex
end Submission
