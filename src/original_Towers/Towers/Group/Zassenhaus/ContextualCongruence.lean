import Towers.Group.Zassenhaus.Contexts

/-!
# Congruence rules for reachable contextual transient packets

Reachable transient-packet rewrites are generated inside arbitrary list
contexts, but later collectors need to lift whole rewrite chains through a
larger surrounding packet.  This file packages that congruence rule and the
two elementary reachable expansions in a callback-friendly form.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SCReach

/-- Every mixed packet is contextually reachable from itself. -/
lemma refl
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (source :
      List (SOTerm H inputWeight)) :
    SCReach
      (n := n) H source source :=
  Relation.EqvGen.refl source

/-- Reverse a reachable contextual rewrite chain. -/
lemma symm
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (reachable :
      SCReach
        (n := n) H source target) :
    SCReach
      (n := n) H target source :=
  Relation.EqvGen.symm source target reachable

/-- Compose two reachable contextual rewrite chains. -/
lemma trans
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source middle target :
      List (SOTerm H inputWeight)}
    (left :
      SCReach
        (n := n) H source middle)
    (right :
      SCReach
        (n := n) H middle target) :
    SCReach
      (n := n) H source target :=
  Relation.EqvGen.trans source middle target left right

/-- Regard one elementary contextual expansion as a reachable rewrite. -/
lemma of_expansionStep
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (step :
      TCStep
        (n := n) H source target) :
    SCReach
      (n := n) H source target :=
  Relation.EqvGen.rel source target step

/--
Lift a complete reachable rewrite chain through an arbitrary surrounding
mixed-packet context.
-/
lemma context
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (reachable :
      SCReach
        (n := n) H source target)
    (leftContext rightContext :
      List (SOTerm H inputWeight)) :
    SCReach
      (n := n) H
        (leftContext ++ source ++ rightContext)
        (leftContext ++ target ++ rightContext) := by
  induction reachable with
  | rel source target step =>
      apply of_expansionStep
      cases step with
      | inverseKernel packet hinputWeight B A left right =>
          simpa only [List.append_assoc] using
            TCStep.inverseKernel
              packet hinputWeight B A (leftContext ++ left)
                (right ++ rightContext)
      | rewordedOuter packet hinputWeight outerExpansion innerWord rightWord
          left right =>
          simpa only [List.append_assoc] using
            TCStep.rewordedOuter
              packet hinputWeight outerExpansion innerWord rightWord
                (leftContext ++ left) (right ++ rightContext)
  | refl =>
      exact refl _
  | symm source target _ ih =>
      exact ih.symm
  | trans source middle target _ _ hsource htarget =>
      exact hsource.trans htarget

/-- Insert one exact classified-packet inverse kernel into a mixed context. -/
lemma inverseKernel
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (leftContext rightContext :
      List (SOTerm H inputWeight)) :
    SCReach
      (n := n) H
        (leftContext ++ rightContext)
        (leftContext ++
          packet.transientTermsContextual hinputWeight
            B A ++
          rightContext) :=
  of_expansionStep <|
    TCStep.inverseKernel
      packet hinputWeight B A leftContext rightContext

/-- Expand one transient outer frontier into its reworded contextual block. -/
lemma rewordedOuter
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SOTerm H inputWeight)) :
    SCReach
      (n := n) H
        (leftContext ++ [.frontier outerExpansion] ++ rightContext)
        (leftContext ++
          packet.transientInnerContextual hinputWeight
            outerExpansion innerWord rightWord ++
          rightContext) :=
  of_expansionStep <|
    TCStep.rewordedOuter
      packet hinputWeight outerExpansion innerWord rightWord leftContext
        rightContext

/-- The empty source reaches one exact classified-packet inverse kernel. -/
lemma nilClassifiedContext
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight) :
    SCReach
      (n := n) H []
        (packet.transientTermsContextual hinputWeight
          B A) := by
  simpa using inverseKernel packet hinputWeight B A [] []

/-- A singleton frontier reaches its reworded contextual expansion. -/
lemma singletonFrontierContext
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    SCReach
      (n := n) H [.frontier outerExpansion]
        (packet.transientInnerContextual hinputWeight
          outerExpansion innerWord rightWord) := by
  simpa using
    rewordedOuter packet hinputWeight outerExpansion innerWord rightWord [] []

end SCReach

open SCReach

local notation "reachableNilToClassifiedInverseContextualTerms" =>
  nilClassifiedContext

local notation "reachableSingletonFrontierToInnerReductionContextualTerms" =>
  singletonFrontierContext

namespace PFSubsti.TAPkt

/-- Packet-style alias for inserting one exact inverse cancellation kernel. -/
lemma nilClassifiedContext
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight) :
    SCReach
      (n := n) H []
        (packet.transientTermsContextual hinputWeight
          B A) :=
  reachableNilToClassifiedInverseContextualTerms
    packet hinputWeight B A

/-- Packet-style alias for expanding one transient outer frontier. -/
lemma singletonFrontierContext
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    SCReach
      (n := n) H [.frontier outerExpansion]
        (packet.transientInnerContextual hinputWeight
          outerExpansion innerWord rightWord) :=
  reachableSingletonFrontierToInnerReductionContextualTerms
    packet hinputWeight outerExpansion innerWord rightWord

end PFSubsti.TAPkt

namespace TTRecol

/--
Transport a recollection through a reachable rewrite chain nested inside a
larger mixed-packet context.
-/
def contextually_context
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (leftContext rightContext :
      List (SOTerm H inputWeight))
    (recollection :
      TTRecol
        n lowerWeight H (leftContext ++ source ++ rightContext))
    (reachable :
      SCReach
        (n := n) H source target) :
    TTRecol
      n lowerWeight H (leftContext ++ target ++ rightContext) :=
  recollection.of_contextuallyReachable
    (reachable.context leftContext rightContext)

end TTRecol

end TCTex
end Towers
