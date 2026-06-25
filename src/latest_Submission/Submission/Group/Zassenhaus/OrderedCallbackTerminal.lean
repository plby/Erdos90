import
  Submission.Group.Zassenhaus.OrderedContextualCallback
import Submission.Group.Zassenhaus.Ordered

/-!
# Terminal dispatch for callback-facing ordered transient residuals

The callback-facing residual collector is needed only below the next parent
stratum.  At the endpoint the ordered residual is already trivial, so the
dispatcher can return its empty recollection without requesting recursive
children.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt
namespace OBSplit

/--
Use contextual recursive results while the ordered residual remains active,
or erase the terminal residual without consuming the callback.
-/
noncomputable def
    or_recursive_results
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
  by_cases hactive :
      outerExpansion.word.weight PEAddres.weight + 1 < n
  · exact
      recollection_recursive_results split hinputWeight
        outerExpansion (by omega) innerWord rightWord hword recursiveResults
  · exact
      recollect_transient_terminal
        split hinputWeight outerExpansion innerWord rightWord hword (by omega)

/--
Compose an externally recollected temporary packet with active-or-terminal
callback-facing ordered residual recollection.
-/
noncomputable def
    results_or_terminal
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
        |>.or_recursive_results
          hinputWeight outerExpansion innerWord rightWord hword
            recursiveResults)

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Submission
