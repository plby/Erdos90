import Towers.Group.Zassenhaus.TerminalContexts

/-!
# Contextual splicing for reachably terminal transient packets

Reachably terminal packets transport backward through contextual rewrites.
Recursive collectors also need the nested form of that rule: replace one
subpacket inside a fixed prefix and suffix, or insert a cancellation block
that contextually rewrites to the empty packet.

This file packages those closure operations without normalizing any loose
transient carrier in isolation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SRTermin

/--
Transport a reachably terminal endpoint backward through a contextual rewrite
nested inside a fixed prefix and suffix.
-/
def contextually_context
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (leftContext rightContext :
      List (SOTerm H inputWeight))
    (targetTerminal :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H
          (leftContext ++ target ++ rightContext))
    (reachable :
      SCReach
        (n := n) H source target) :
    SRTermin
      (n := n) (lowerWeight := lowerWeight) H
        (leftContext ++ source ++ rightContext) :=
  of_contextuallyReachable targetTerminal
    (reachable.context leftContext rightContext)

/--
Insert a mixed block into a reachably terminal context whenever that block
contextually rewrites to the empty packet.
-/
def insert_contextually_reachable
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {middle :
      List (SOTerm H inputWeight)}
    (leftContext rightContext :
      List (SOTerm H inputWeight))
    (contextTerminal :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H
          (leftContext ++ rightContext))
    (reachable :
      SCReach
        (n := n) H middle []) :
    SRTermin
      (n := n) (lowerWeight := lowerWeight) H
        (leftContext ++ middle ++ rightContext) := by
  apply contextually_context leftContext rightContext ?_ reachable
  simpa only [List.append_nil] using contextTerminal

/--
Recollect a source nested inside a larger context by transporting backward
from a reachably terminal replacement.
-/
noncomputable def contextually_reachable_context
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (leftContext rightContext :
      List (SOTerm H inputWeight))
    (targetTerminal :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H
          (leftContext ++ target ++ rightContext))
    (reachable :
      SCReach
        (n := n) H source target) :
    TTRecol
      n lowerWeight H (leftContext ++ source ++ rightContext) :=
  (contextually_context leftContext rightContext targetTerminal
      reachable).sourceRecollection

end SRTermin

namespace PFSubsti.TAPkt

/--
Insert one exact classified-packet inverse kernel into an arbitrary reachably
terminal context.
-/
def reachably_insert_classified
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (leftContext rightContext :
      List (SOTerm H inputWeight))
    (contextTerminal :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H
          (leftContext ++ rightContext)) :
    SRTermin
      (n := n) (lowerWeight := lowerWeight) H
        (leftContext ++
          packet.transientTermsContextual hinputWeight
            B A ++
          rightContext) :=
  SRTermin.insert_contextually_reachable
    leftContext rightContext contextTerminal <| by
      exact
        (packet.nilClassifiedContext
          hinputWeight B A).symm

/--
Recollect a context after inserting one exact classified-packet inverse
kernel.
-/
noncomputable def
    recollection_insert_contextual
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (leftContext rightContext :
      List (SOTerm H inputWeight))
    (contextTerminal :
      SRTermin
        (n := n) (lowerWeight := lowerWeight) H
          (leftContext ++ rightContext)) :
    TTRecol
      n lowerWeight H
        (leftContext ++
          packet.transientTermsContextual hinputWeight
            B A ++
          rightContext) :=
  (packet
    |>.reachably_insert_classified
      hinputWeight B A leftContext rightContext contextTerminal
    |>.sourceRecollection)

end PFSubsti.TAPkt

end TCTex
end Towers
