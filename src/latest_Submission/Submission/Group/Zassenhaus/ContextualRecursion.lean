import
Submission.Group.Zassenhaus.ClassificationCompatibility
import Submission.Group.Zassenhaus.Transient
import Submission.Group.Zassenhaus.RewordingCore

/-!
# Contextual recursion for reworded transient powers

Rewording moves an existing transient exponent onto an inner Hall word before
forming the temporary packet for `[inner ^ e, right]`.  The resulting
classified packet descends from the singleton obligation on that reworded
inner carrier.  It does not assert descent from the original outer carrier,
whose physical word may be heavier.

This file exposes that exact recursion boundary and records that ordinary
factor inner reduction is its first-stage specialization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u v

namespace PFSubsti.TAPkt

/--
The classified temporary packet for a reworded transient exponent descends
from the singleton obligation on the reworded inner carrier.
-/
lemma
    transient_multiset_reword
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hinner :
      innerWord.weight PEAddres.weight < n) :
    SOTerm.FrontierDefectMultiset n
      (packet.transientInnerTerms hinputWeight
        wordExpansion innerWord rightWord)
      [.frontier (wordExpansion.reword innerWord)] :=
  packet.transient_multiset_singleton
    hinputWeight (wordExpansion.reword innerWord)
      (TWExp.wordUnit rightWord) hinner

/--
While resolving one reworded inner-carrier singleton, recursively obtain its
complete classified temporary packet.
-/
def transient_result_reword
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {Result :
      List (SOTerm H inputWeight) → Sort v}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hinner :
      innerWord.weight PEAddres.weight < n)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier (wordExpansion.reword innerWord)] →
          Result child) :
    Result
      (packet.transientInnerTerms hinputWeight
        wordExpansion innerWord rightWord) :=
  packet.transient_result_left hinputWeight
    (wordExpansion.reword innerWord)
      (TWExp.wordUnit rightWord) hinner
        recursiveResults

/--
Rewording the transient view of an ordinary factor recovers the original
first-stage classified inner-reduction packet.
-/
lemma
    transient_inner_classified
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    packet.transientInnerTerms hinputWeight
        (TWExp.rewordFactor factor
          factor.word)
        innerWord rightWord =
      packet.innerOuterTerms hinputWeight factor innerWord
        rightWord hword := by
  rw [packet.inner_classified_transient]
  simp only [transientInnerTerms,
    TWExp.reword_rewordFactor]

end PFSubsti.TAPkt

end TCTex
end Submission
