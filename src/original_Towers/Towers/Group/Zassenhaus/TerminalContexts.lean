import Towers.Group.Zassenhaus.Transient
import Towers.Group.Zassenhaus.ContextualCongruence

/-!
# Reachably terminal transient contexts

A loose transient carrier need not have an ordinary symbolic representative
in isolation.  Contextual expansion can nevertheless expose a mixed source
whose remaining frontier terms have all reached the nilpotent cutoff.

This file packages that endpoint and its closure under reachable contextual
rewrites.  The resulting predicate is compositional under list concatenation
and supplies an ordinary recollection without normalizing loose frontiers by
fiat.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SCReach

/-- A reachable rewrite remains reachable after adding a fixed prefix. -/
lemma append_left
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (reachable :
      SCReach
        (n := n) H source target)
    (leftContext :
      List (SOTerm H inputWeight)) :
    SCReach
      (n := n) H
        (leftContext ++ source)
        (leftContext ++ target) := by
  simpa using reachable.context leftContext []

/-- A reachable rewrite remains reachable after adding a fixed suffix. -/
lemma append_right
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (reachable :
      SCReach
        (n := n) H source target)
    (rightContext :
      List (SOTerm H inputWeight)) :
    SCReach
      (n := n) H
        (source ++ rightContext)
        (target ++ rightContext) := by
  simpa using reachable.context [] rightContext

end SCReach

/--
A mixed transient context that can be recollected directly: every attached
term has enough physical support, and every retained frontier term has
reached the nilpotent cutoff.
-/
structure STContex
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (source :
      List (SOTerm H inputWeight)) :
    Prop where
  wordLeast :
    ∀ term ∈ source,
      lowerWeight ≤ SOTerm.wordWeight term
  frontierAtCutoff :
    ∀ wordExpansion,
      .frontier wordExpansion ∈ source →
        n ≤ wordExpansion.word.weight PEAddres.weight

namespace STContex

/-- The empty mixed source is terminal at every requested support bound. -/
def empty
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    STContex
      (n := n) (lowerWeight := lowerWeight) H
        ([] : List (SOTerm H inputWeight)) where
  wordLeast := by
    intro term hterm
    simp at hterm
  frontierAtCutoff := by
    intro wordExpansion hwordExpansion
    simp at hwordExpansion

/-- Concatenating terminal mixed sources preserves terminality. -/
def append
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {leftSource rightSource :
      List (SOTerm H inputWeight)}
    (left :
      STContex
        (n := n) (lowerWeight := lowerWeight) H leftSource)
    (right :
      STContex
        (n := n) (lowerWeight := lowerWeight) H rightSource) :
    STContex
      (n := n) (lowerWeight := lowerWeight) H (leftSource ++ rightSource) where
  wordLeast := by
    intro term hterm
    rcases List.mem_append.mp hterm with hterm | hterm
    · exact left.wordLeast term hterm
    · exact right.wordLeast term hterm
  frontierAtCutoff := by
    intro wordExpansion hwordExpansion
    rcases List.mem_append.mp hwordExpansion with hwordExpansion | hwordExpansion
    · exact left.frontierAtCutoff wordExpansion hwordExpansion
    · exact right.frontierAtCutoff wordExpansion hwordExpansion

/-- One attached term is terminal whenever it has the requested support. -/
def singleton_attached
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : SWExp H inputWeight)
    (hweight :
      lowerWeight ≤
        wordExpansion.word.weight PEAddres.weight) :
    STContex
      (n := n) (lowerWeight := lowerWeight) H [.attached wordExpansion] where
  wordLeast := by
    intro term hterm
    simp only [List.mem_singleton] at hterm
    subst term
    exact hweight
  frontierAtCutoff := by
    intro transientExpansion htransientExpansion
    simp at htransientExpansion

/--
One frontier term is terminal whenever it has the requested support and has
already reached the nilpotent cutoff.
-/
def singleton_frontier
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion :
      TWExp H inputWeight)
    (hweight :
      lowerWeight ≤
        wordExpansion.word.weight PEAddres.weight)
    (hcutoff :
      n ≤ wordExpansion.word.weight PEAddres.weight) :
    STContex
      (n := n) (lowerWeight := lowerWeight) H [.frontier wordExpansion] where
  wordLeast := by
    intro term hterm
    simp only [List.mem_singleton] at hterm
    subst term
    exact hweight
  frontierAtCutoff := by
    intro transientExpansion htransientExpansion
    simp only [List.mem_singleton] at htransientExpansion
    cases htransientExpansion
    exact hcutoff

/-- A terminal mixed source recollects directly to ordinary symbolic factors. -/
noncomputable def sourceRecollection
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source :
      List (SOTerm H inputWeight)}
    (terminal :
      STContex
        (n := n) (lowerWeight := lowerWeight) H source) :
    TTRecol
      n lowerWeight H source :=
  TTRecol.word_frontier_cutoff
    source terminal.wordLeast terminal.frontierAtCutoff

end STContex

/--
A mixed transient source is reachably terminal when contextual rewrites take
it to a directly recollectable terminal endpoint.
-/
structure SRTermin
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (source :
      List (SOTerm H inputWeight)) :
    Type (u + 1) where
  target :
    List (SOTerm H inputWeight)
  reachable :
    SCReach
      (n := n) H source target
  terminal :
    STContex
      (n := n) (lowerWeight := lowerWeight) H target

namespace SRTermin

/-- A directly terminal source is reachably terminal by reflexivity. -/
def of_terminal
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source :
      List (SOTerm H inputWeight)}
    (terminal :
      STContex
        (n := n) (lowerWeight := lowerWeight) H source) :
    SRTermin
      (n := n) (lowerWeight := lowerWeight) H source where
  target := source
  reachable := SCReach.refl source
  terminal := terminal

/-- Reachably terminality transports backward across contextual rewrites. -/
def of_contextuallyReachable
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (targetTerminal :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H target)
    (reachable :
      SCReach
        (n := n) H source target) :
    SRTermin
      (n := n) (lowerWeight := lowerWeight) H source where
  target := targetTerminal.target
  reachable := reachable.trans targetTerminal.reachable
  terminal := targetTerminal.terminal

/-- Reachably terminal mixed sources compose in their original order. -/
def append
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {leftSource rightSource :
      List (SOTerm H inputWeight)}
    (left :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H leftSource)
    (right :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H rightSource) :
    SRTermin
      (n := n) (lowerWeight := lowerWeight) H (leftSource ++ rightSource) where
  target := left.target ++ right.target
  reachable :=
    (left.reachable.append_right rightSource).trans
      (right.reachable.append_left left.target)
  terminal := left.terminal.append right.terminal

/--
Recollect a reachably terminal source by recollecting its endpoint and
transporting the result back across the contextual rewrite chain.
-/
noncomputable def sourceRecollection
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source :
      List (SOTerm H inputWeight)}
    (normalizable :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H source) :
    TTRecol
      n lowerWeight H source :=
  normalizable.terminal.sourceRecollection.of_contextuallyReachable
    normalizable.reachable.symm

end SRTermin

namespace PFSubsti.TAPkt

open SRTermin
open STContex

/--
A classified packet followed by its exact raw inverse is reachably terminal
at every requested support bound: contextual cancellation reduces it to the
empty endpoint.
-/
def reachably_terms_contextual
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight) :
    SRTermin
      (n := n) (lowerWeight := lowerWeight) H
        (packet.transientTermsContextual hinputWeight
          B A) :=
  of_contextuallyReachable (of_terminal empty) <| by
    exact
      (SCReach.nilClassifiedContext
        packet hinputWeight B A).symm

/--
The reworded contextual expansion is reachably terminal whenever the outer
frontier singleton is reachably terminal.
-/
def reachably_inner_contextual
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (outerTerminal :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H
          [.frontier outerExpansion]) :
    SRTermin
      (n := n) (lowerWeight := lowerWeight) H
        (packet.transientInnerContextual hinputWeight
          outerExpansion innerWord rightWord) :=
  of_contextuallyReachable outerTerminal <| by
    exact
      (SCReach.singletonFrontierContext
        packet hinputWeight outerExpansion innerWord rightWord).symm

/--
Conversely, a reachably terminal reworded contextual expansion closes its
original outer frontier singleton.
-/
def reachably_contextual_terms
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (contextualTerminal :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H
          (packet.transientInnerContextual hinputWeight
            outerExpansion innerWord rightWord)) :
    SRTermin
      (n := n) (lowerWeight := lowerWeight) H [.frontier outerExpansion] :=
  of_contextuallyReachable contextualTerminal <| by
    exact
      SCReach.singletonFrontierContext
        packet hinputWeight outerExpansion innerWord rightWord

end PFSubsti.TAPkt

end TCTex
end Towers
