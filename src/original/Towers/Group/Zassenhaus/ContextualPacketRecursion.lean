import Towers.Group.Zassenhaus.ClassifiedPacketDescent

/-!
# Well-founded recursion on contextual transient packets

Transient inner reduction must recurse on complete ordered classified packets:
attached terms and frontier terms stay interleaved until contextual
recollection resolves them.  The frontier-defect multiset relation already
proves this recursion well founded.

This file packages the executable recursion skeleton.  A caller supplies one
resolver for an arbitrary mixed packet, with recursive results available for
strictly smaller packets.  The resulting fixpoint comes with its unfolding
equation and a helper for the concrete inner-reduction packet emitted from one
ordinary parent factor.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u v

/-- One resolver step for well-founded recursion on complete classified packets. -/
structure TRStep
    {d n inputWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (Result :
      List (SOTerm H inputWeight) → Sort v) where
  resolve :
    ∀ parent,
      (∀ child,
        SOTerm.FrontierDefectMultiset
            n child parent →
          Result child) →
        Result parent

namespace TRStep

/-- Run the resolver by well-founded frontier-defect multiset recursion. -/
noncomputable def recursiveResult
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {Result :
      List (SOTerm H inputWeight) → Sort v}
    (step :
      TRStep
        (n := n) H Result)
    (terms : List (SOTerm H inputWeight)) :
    Result terms :=
  (SOTerm.well_founded_multiset
      (n := n) (H := H) (inputWeight := inputWeight)).fix step.resolve terms

/-- Unfold one resolver call of contextual packet recursion. -/
theorem recursiveResult_eq
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {Result :
      List (SOTerm H inputWeight) → Sort v}
    (step :
      TRStep
        (n := n) H Result)
    (terms : List (SOTerm H inputWeight)) :
    step.recursiveResult terms =
      step.resolve terms fun child _ => step.recursiveResult child := by
  rw [recursiveResult, WellFounded.fix_eq]
  rfl

end TRStep

namespace PFSubsti.TAPkt

/--
While resolving the singleton transient view of an ordinary parent factor, the
recursive hypotheses already include the complete contextual inner-reduction
packet emitted by that parent.
-/
def inner_result_reword
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {Result :
      List (SOTerm H inputWeight) → Sort v}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child
              [.frontier
                (TWExp.rewordFactor factor
                  factor.word)] →
          Result child) :
    Result
      (packet.innerOuterTerms hinputWeight factor innerWord
        rightWord hword) :=
  recursiveResults _
    (packet.inner_multiset_reword
      hinputWeight factor innerWord rightWord hword hfactorTruncated)

end PFSubsti.TAPkt

end TCTex
end Towers
