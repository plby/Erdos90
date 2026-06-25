import Submission.Group.Zassenhaus.TerminalPacketRouting
import Submission.Group.Zassenhaus.ContextualRecursion

/-!
# Bifurcated routing for active transient frontiers

Recollecting a decomposable transient frontier has two distinct recursive
roots.  Its ordered residual tails are physically heavier than the original
outer carrier.  Its temporary classified packet instead descends from the
reworded inner carrier.  Neither root should be replaced by the other.

This file packages that bifurcation.  It also strengthens the terminal
temporary-packet endpoint to the original outer support bound, which is the
bound required when the packet is composed back into its parent frontier.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff

namespace PTSubsti

/--
Classifying one temporary reworded output preserves its physical support
bound from the original outer commutator.
-/
lemma outer_classified_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    outerExpansion.word.weight PEAddres.weight ≤
      (classifiedTransientTerm hinputWeight R
        (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord)).wordWeight := by
  by_cases hweight :
      (wordExpansion hinputWeight R (outerExpansion.reword innerWord)
          (TWExp.wordUnit rightWord)).exponentWeight ≤
        (wordExpansion hinputWeight R (outerExpansion.reword innerWord)
          (TWExp.wordUnit rightWord)).word.weight
            PEAddres.weight
  · rw [classified_attached_exponent
      hinputWeight R (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord) hweight]
    exact
      outer_expansion_reword hinputWeight R
        outerExpansion innerWord rightWord hword
  · rw [classified_transient_exponent
      hinputWeight R (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord) hweight]
    exact
      outer_expansion_reword hinputWeight R
        outerExpansion innerWord rightWord hword

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti
open SRTermin

/--
Every member of a temporary reworded classified packet retains the physical
support bound of the original outer commutator.
-/
lemma outer_classified_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (term : SOTerm H inputWeight)
    (hterm :
      term ∈
        packet.transientInnerTerms hinputWeight
          outerExpansion innerWord rightWord) :
    outerExpansion.word.weight PEAddres.weight ≤
      term.wordWeight := by
  rw [transientInnerTerms, transientClassifiedTerms]
    at hterm
  rcases List.mem_map.mp hterm with ⟨R, _, rfl⟩
  exact
    outer_classified_reword
      hinputWeight R outerExpansion innerWord rightWord hword

/--
An inner-terminal temporary packet is directly terminal at the stronger
original outer support bound.
-/
def
    terminal_context_inner
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ innerWord.weight PEAddres.weight + 1) :
    STContex
      (n := n)
      (lowerWeight :=
        outerExpansion.word.weight PEAddres.weight)
      H
        (packet.transientInnerTerms hinputWeight
          outerExpansion innerWord rightWord) where
  wordLeast := fun term hterm =>
    packet.outer_classified_terms
      hinputWeight outerExpansion innerWord rightWord hword term hterm
  frontierAtCutoff := fun wordExpansion hwordExpansion =>
    hcutoff.trans
      (Nat.succ_le_of_lt <| by
        apply
          packet.left_transient_frontier
            hinputWeight (outerExpansion.reword innerWord)
              (TWExp.wordUnit rightWord)
                wordExpansion
        simpa [transientInnerTerms] using
          hwordExpansion)

/-- Reachably terminal view of the stronger outer-support endpoint. -/
def
    reachably_terminal_inner
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ innerWord.weight PEAddres.weight + 1) :
    SRTermin
      (n := n)
      (lowerWeight :=
        outerExpansion.word.weight PEAddres.weight)
      H
        (packet.transientInnerTerms hinputWeight
          outerExpansion innerWord rightWord) :=
  SRTermin.of_terminal <|
    packet
      |>.terminal_context_inner
        hinputWeight outerExpansion innerWord rightWord hword hcutoff

end PFSubsti.TAPkt

namespace
  FRRoute

/--
Build frontier routing data at any weaker requested support bound when the
reworded inner carrier has reached its terminal endpoint.
-/
def inner_terminal_outer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hlowerWeight :
      lowerWeight ≤
        outerExpansion.word.weight PEAddres.weight)
    (hcutoff :
      n ≤ innerWord.weight PEAddres.weight + 1) :
    FRRoute
      (lowerWeight := lowerWeight) H packet hinputWeight outerExpansion where
  innerWord := innerWord
  rightWord := rightWord
  word_eq := hword
  temporaryPacketRecollection := fun _ =>
    (packet
      |>.reachably_terminal_inner
        hinputWeight outerExpansion innerWord rightWord hword hcutoff
      |>.weaken hlowerWeight
      |>.sourceRecollection)

end
  FRRoute

/--
Routing data for an arbitrary decomposable transient frontier.  The two
recursive callbacks used below intentionally have different roots.
-/
structure
    BRRoute
    {d n inputWeight : ℕ}
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

namespace
  BRRoute

/--
Recollect one decomposable transient outer frontier.  Residual tails use
recursive results rooted at the outer carrier.  While the inner carrier is
active, temporary terms use recursive results rooted at the reworded inner
carrier; at its endpoint they close directly.
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
      BRRoute
        H packet hinputWeight outerExpansion)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hlowerWeight :
      lowerWeight ≤
        outerExpansion.word.weight PEAddres.weight)
    (outerRecursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecol
            n lowerWeight H child)
    (innerRecursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier (outerExpansion.reword routing.innerWord)] →
          TTRecol
            n lowerWeight H child) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] := by
  by_cases hinner :
      routing.innerWord.weight PEAddres.weight < n
  · exact
      split
        |>.results_or_terminal
          hinputWeight outerExpansion routing.innerWord routing.rightWord
            routing.word_eq outerRecursiveResults
              (packet.transient_result_reword
                hinputWeight outerExpansion routing.innerWord
                  routing.rightWord hinner innerRecursiveResults)
  · exact
      (FRRoute.inner_terminal_outer
        packet hinputWeight outerExpansion routing.innerWord routing.rightWord
          routing.word_eq hlowerWeight (by omega))
        |>.sourceRecollection split outerRecursiveResults

end
  BRRoute

end TCTex
end Submission
