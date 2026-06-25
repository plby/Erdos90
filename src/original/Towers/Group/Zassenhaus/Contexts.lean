import Towers.Group.Zassenhaus.Transient

/-!
# Reachable contextual transient packets

Loose transient carriers should be manipulated in the mixed packet contexts
where their cancellation is visible, rather than normalized as isolated
ordinary factors.  This file records two semantic context moves:

* insert a classified transient packet together with its exact inverse;
* expand one transient outer frontier into its reworded contextual block.

Their equivalence closure is a small reachable-context vocabulary.  Every
reachable context has the same ordered value, so any ordinary recollection
transports across the complete relation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/-- One contextual transient-packet expansion inside an arbitrary list context. -/
inductive TCStep
    {d n inputWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    List (SOTerm H inputWeight) →
      List (SOTerm H inputWeight) →
        Prop
  | inverseKernel
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (hinputWeight : 0 < inputWeight)
      (B A : TWExp H inputWeight)
      (leftContext rightContext :
        List (SOTerm H inputWeight)) :
      TCStep H
        (leftContext ++ rightContext)
        (leftContext ++
          packet.transientTermsContextual hinputWeight
            B A ++
          rightContext)
  | rewordedOuter
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (hinputWeight : 0 < inputWeight)
      (outerExpansion :
        TWExp H inputWeight)
      (innerWord rightWord : CWord (HEAddres H))
      (leftContext rightContext :
        List (SOTerm H inputWeight)) :
      TCStep H
        (leftContext ++ [.frontier outerExpansion] ++ rightContext)
        (leftContext ++
          packet.transientInnerContextual hinputWeight
            outerExpansion innerWord rightWord ++
          rightContext)

namespace TCStep

/-- Every one-step contextual expansion preserves the ordered packet value. -/
lemma listValue_eq
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (step :
      TCStep
        (n := n) H source target)
    (q : ℕ) :
    SOTerm.listValue (n := n) q source =
      SOTerm.listValue q target := by
  cases step with
  | inverseKernel packet hinputWeight B A leftContext rightContext =>
      simp only [SOTerm.listValue_append]
      rw [packet.list_classified_contextual]
      group
  | rewordedOuter packet hinputWeight outerExpansion innerWord rightWord
      leftContext rightContext =>
      simp only [SOTerm.listValue_append,
        SOTerm.value_singleton_frontier]
      rw [packet.inner_contextual_terms]

end TCStep

/-- Equivalence closure of the elementary contextual transient expansions. -/
def SCReach
    {d n inputWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (source target :
      List (SOTerm H inputWeight)) :
    Prop :=
  Relation.EqvGen
    (TCStep (n := n) H)
      source target

namespace SCReach

/-- Contextually reachable mixed packets have the same ordered value. -/
lemma listValue_eq
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (reachable :
      SCReach
        (n := n) H source target)
    (q : ℕ) :
    SOTerm.listValue (n := n) q source =
      SOTerm.listValue q target := by
  induction reachable with
  | rel source target step =>
      exact step.listValue_eq q
  | refl =>
      rfl
  | symm source target _ ih =>
      exact ih.symm
  | trans source middle target _ _ hsource htarget =>
      exact hsource.trans htarget

end SCReach

namespace TTRecol

/-- Transport ordinary recollection across any reachable contextual rewrite. -/
def of_contextuallyReachable
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {source target :
      List (SOTerm H inputWeight)}
    (recollection :
      TTRecol
        n lowerWeight H source)
    (reachable :
      SCReach
        (n := n) H source target) :
    TTRecol
      n lowerWeight H target :=
  list_value recollection fun q => reachable.listValue_eq q

end TTRecol

end TCTex
end Towers
