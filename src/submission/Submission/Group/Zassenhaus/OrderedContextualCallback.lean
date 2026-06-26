import
  Submission.Group.Zassenhaus.OrderedResidualConjugation
import
  Submission.Group.Zassenhaus.FrontierRecursionCertificate

/-!
# Callback-facing ordered transient residual recollection

Every strict carrier surrounding the principal inverse in an ordered
transient residual is physically heavier than the parent carrier.  Therefore
its singleton mixed packet is available from the well-founded contextual
callback rooted at the active parent frontier.

Combining those strict-tail callbacks with transient higher-tail conjugation
recollects the complete residual locally, without a matched ordinary
conjugator and without rerunning the compiled fixpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SOTerm

/--
A physically heavier transient singleton strictly descends from an active
transient singleton in the contextual frontier-defect multiset order.
-/
lemma
    frontier_multiset_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (child parent :
      TWExp H inputWeight)
    (hparentTruncated :
      parent.word.weight PEAddres.weight < n)
    (hweight :
      parent.word.weight PEAddres.weight <
        child.word.weight PEAddres.weight) :
    FrontierDefectMultiset n [.frontier child] [.frontier parent] := by
  refine ⟨∅,
    {n - child.word.weight PEAddres.weight},
    {n - parent.word.weight PEAddres.weight},
    by simp, by simp, by simp, ?_⟩
  intro defect hdefect
  simp only [Multiset.mem_singleton] at hdefect
  subst defect
  exact
    ⟨n - parent.word.weight PEAddres.weight, by simp, by omega⟩

end SOTerm

namespace PFSubsti.TAPkt
namespace OBSplit

open SOTerm

/--
Recollect the strict inverse suffix from the contextual callback rooted at
the active transient parent.
-/
noncomputable def
    after_recursive_results
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
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
    TTRecola
      n lowerWeight H
        (split.strictAfterSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.of_singletons _
    fun nextExpansion hnext =>
      TTRecola.singleton_frontier_recollection
        nextExpansion <|
          recursiveResults [.frontier nextExpansion] <|
            frontier_multiset_weight
              nextExpansion outerExpansion houterTruncated <|
                split.outer_after_source
                  hinputWeight outerExpansion innerWord rightWord hword
                    nextExpansion hnext

/--
Recollect the strict inverse prefix from the contextual callback rooted at
the active transient parent.
-/
noncomputable def
    before_recursive_results
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
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
    TTRecola
      n lowerWeight H
        (split.strictBeforeSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.of_singletons _
    fun nextExpansion hnext =>
      TTRecola.singleton_frontier_recollection
        nextExpansion <|
          recursiveResults [.frontier nextExpansion] <|
            frontier_multiset_weight
              nextExpansion outerExpansion houterTruncated <|
                split.outer_before_source
                  hinputWeight outerExpansion innerWord rightWord hword
                    nextExpansion hnext

/--
Recollect the complete ordered residual locally from recursive results rooted
at the active transient parent.
-/
noncomputable def
    recollection_recursive_results
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
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
    TTRecola
      n lowerWeight H
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) := by
  let afterRecollection :=
    split.after_recursive_results
      hinputWeight outerExpansion houterTruncated innerWord rightWord hword
        recursiveResults
  let beforeRecollection :=
    split.before_recursive_results
      hinputWeight outerExpansion houterTruncated innerWord rightWord hword
        recursiveResults
  let conjugatedBefore :=
    packet.transient_conjugated_results
      hinputWeight outerExpansion houterTruncated
        beforeRecollection.higherSource
          beforeRecollection.higher_source_truncated
            beforeRecollection.higher_weight_least
              recursiveResults
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
Compose local ordered-residual recollection with a recollection of the
temporary classified packet, recovering the parent singleton without a
matched ordinary conjugator.
-/
noncomputable def
    frontier_recursive_results
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
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
            n lowerWeight H child)
    (packetRecollection :
      TTRecol
        n lowerWeight H
          (packet.transientInnerTerms hinputWeight
            outerExpansion innerWord rightWord)) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  packet.frontier_reworded_residual
    hinputWeight outerExpansion innerWord rightWord packetRecollection
      (split
        |>.recollection_recursive_results
          hinputWeight outerExpansion houterTruncated innerWord rightWord hword
            recursiveResults)

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Submission
