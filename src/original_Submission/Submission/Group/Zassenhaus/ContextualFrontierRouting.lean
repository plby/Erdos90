import Submission.Group.Zassenhaus.Contexts
import Submission.Group.Zassenhaus.OrderedCallbackTerminal

/-!
# Reachable contextual routing for one transient frontier

The callback-facing ordered residual collector closes the residual around a
transient commutator carrier.  The remaining local obligation is exactly the
temporary classified packet produced by rewording its inner word.

This file records that restricted local rule.  It also transports the closed
frontier singleton across reachable contextual rewrites, without asserting a
collector for arbitrary loose transient carriers.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
The exact remaining local input for recollecting one decomposable transient
frontier from a contextual recursive callback.
-/
structure
    FRRoute
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight) where
  innerWord : CWord (HEAddres H)
  rightWord : CWord (HEAddres H)
  word_eq : outerExpansion.word = .commutator innerWord rightWord
  temporaryPacketRecollection :
    (∀ child,
      SOTerm.FrontierDefectMultiset
          n child [.frontier outerExpansion] →
        TTRecol
          n lowerWeight H child) →
      TTRecol
        n lowerWeight H
          (packet.transientInnerTerms hinputWeight
            outerExpansion innerWord rightWord)

namespace
  FRRoute

/--
Close the parent transient singleton using the supplied temporary-packet rule
and the active-or-terminal ordered residual dispatcher.
-/
noncomputable def sourceRecollection
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    {outerExpansion :
      TWExp H inputWeight}
    (routing :
      FRRoute
        (lowerWeight := lowerWeight) H packet hinputWeight outerExpansion)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecol
            n lowerWeight H child) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  split
    |>.results_or_terminal
      hinputWeight outerExpansion routing.innerWord routing.rightWord
        routing.word_eq recursiveResults
          (routing.temporaryPacketRecollection recursiveResults)

/--
After closing the parent singleton, transport its recollection across any
reachable contextual rewrite chain.
-/
noncomputable def recollection_contextually_reachable
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    {outerExpansion :
      TWExp H inputWeight}
    (routing :
      FRRoute
        (lowerWeight := lowerWeight) H packet hinputWeight outerExpansion)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecol
            n lowerWeight H child)
    {target :
      List (SOTerm H inputWeight)}
    (reachable :
      SCReach
        (n := n) H [.frontier outerExpansion] target) :
    TTRecol
      n lowerWeight H target :=
  (routing.sourceRecollection split recursiveResults).of_contextuallyReachable
    reachable

end
  FRRoute

end TCTex
end Submission
