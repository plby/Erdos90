import Towers.Group.Zassenhaus.ContextualFrontierRouting
import Towers.Group.Zassenhaus.TerminalContexts

/-!
# Terminal packet routes for reachable transient contexts

Reachably terminal contexts provide a direct endpoint for classified packets
whose parent carrier is one stratum below the nilpotent cutoff.  Reworded
temporary packets use the same endpoint when their inner carrier is terminal.

This file packages those endpoint instances, support weakening, and the
corresponding constructor for contextual frontier routing data.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace STContex

/-- Lower the requested physical support bound of a terminal endpoint. -/
def weaken
    {d n inputWeight lowerWeight weakerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source :
      List (SOTerm H inputWeight)}
    (terminal :
      STContex
        (n := n) (lowerWeight := lowerWeight) H source)
    (hweight : weakerWeight ≤ lowerWeight) :
    STContex
      (n := n) (lowerWeight := weakerWeight) H source where
  wordLeast := fun term hterm =>
    hweight.trans (terminal.wordLeast term hterm)
  frontierAtCutoff := terminal.frontierAtCutoff

end STContex

namespace SRTermin

/-- Lower the requested physical support bound of a reachable endpoint. -/
def weaken
    {d n inputWeight lowerWeight weakerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source :
      List (SOTerm H inputWeight)}
    (normalizable :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H source)
    (hweight : weakerWeight ≤ lowerWeight) :
    SRTermin
      (n := n) (lowerWeight := weakerWeight) H source where
  target := normalizable.target
  reachable := normalizable.reachable
  terminal := normalizable.terminal.weaken hweight

end SRTermin

namespace PFSubsti.TAPkt

open PTSubsti
open SRTermin
open STContex

/--
A classified transient packet is a direct terminal endpoint when its left
parent is one stratum below the nilpotent cutoff.
-/
def context_transient_classified
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hcutoff :
      n ≤ B.word.weight PEAddres.weight + 1) :
    STContex
      (n := n)
      (lowerWeight := B.word.weight PEAddres.weight)
      H (packet.transientClassifiedTerms hinputWeight B A) where
  wordLeast := fun term hterm =>
    Nat.le_of_lt
      (packet.left_transient_terms
        hinputWeight B A term hterm)
  frontierAtCutoff := fun wordExpansion hwordExpansion =>
    hcutoff.trans
      (Nat.succ_le_of_lt
        (packet.left_transient_frontier
          hinputWeight B A wordExpansion hwordExpansion))

/--
A classified transient packet is a direct terminal endpoint when its right
parent is one stratum below the nilpotent cutoff.
-/
def terminal_context_right
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hcutoff :
      n ≤ A.word.weight PEAddres.weight + 1) :
    STContex
      (n := n)
      (lowerWeight := A.word.weight PEAddres.weight)
      H (packet.transientClassifiedTerms hinputWeight B A) where
  wordLeast := fun term hterm =>
    Nat.le_of_lt
      (packet.right_classified_terms
        hinputWeight B A term hterm)
  frontierAtCutoff := fun wordExpansion hwordExpansion =>
    hcutoff.trans
      (Nat.succ_le_of_lt
        (packet.right_classified_frontier
          hinputWeight B A wordExpansion hwordExpansion))

/-- Reachably terminal view of the left-terminal classified packet. -/
def reachably_classified_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hcutoff :
      n ≤ B.word.weight PEAddres.weight + 1) :
    SRTermin
      (n := n)
      (lowerWeight := B.word.weight PEAddres.weight)
      H (packet.transientClassifiedTerms hinputWeight B A) :=
  of_terminal <|
    packet.context_transient_classified
      hinputWeight B A hcutoff

/-- Reachably terminal view of the right-terminal classified packet. -/
def reachably_terminal_right
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hcutoff :
      n ≤ A.word.weight PEAddres.weight + 1) :
    SRTermin
      (n := n)
      (lowerWeight := A.word.weight PEAddres.weight)
      H (packet.transientClassifiedTerms hinputWeight B A) :=
  of_terminal <|
    packet.terminal_context_right
      hinputWeight B A hcutoff

/--
The temporary packet emitted by rewording an outer carrier is a direct
terminal endpoint when its inner Hall word is one stratum below cutoff.
-/
def terminal_context_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hcutoff :
      n ≤ innerWord.weight PEAddres.weight + 1) :
    STContex
      (n := n)
      (lowerWeight := innerWord.weight PEAddres.weight)
      H
        (packet.transientInnerTerms hinputWeight
          outerExpansion innerWord rightWord) := by
  exact
    packet.context_transient_classified
      hinputWeight (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord)
          (by simpa using hcutoff)

/-- Reachably terminal view of an inner-terminal temporary packet. -/
def reachably_terminal_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hcutoff :
      n ≤ innerWord.weight PEAddres.weight + 1) :
    SRTermin
      (n := n)
      (lowerWeight := innerWord.weight PEAddres.weight)
      H
        (packet.transientInnerTerms hinputWeight
          outerExpansion innerWord rightWord) :=
  of_terminal <|
    packet
      |>.terminal_context_terms
        hinputWeight outerExpansion innerWord rightWord hcutoff

end PFSubsti.TAPkt

namespace
  FRRoute

/--
Build frontier routing data without a recursive temporary-packet call when
the reworded inner carrier is already one stratum below cutoff.
-/
def of_inner_terminal
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
      lowerWeight ≤ innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤ innerWord.weight PEAddres.weight + 1) :
    FRRoute
      (lowerWeight := lowerWeight) H packet hinputWeight outerExpansion where
  innerWord := innerWord
  rightWord := rightWord
  word_eq := hword
  temporaryPacketRecollection := fun _ =>
    (packet
      |>.reachably_terminal_terms
        hinputWeight outerExpansion innerWord rightWord hcutoff
      |>.weaken hlowerWeight
      |>.sourceRecollection)

end
  FRRoute

end TCTex
end Towers
