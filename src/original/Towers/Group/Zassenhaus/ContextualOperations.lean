import
  Towers.Group.Zassenhaus.ClassifiedPacketRecollection

/-!
# Operations on contextual transient-packet recollections

Contextual transient recollection keeps attached and frontier terms in their
original packet order.  Recursive cancellation arguments still need a few
semantic operations: lower the requested support bound, transport a
recollection across equality of ordered packet values, and close a packet
whose ordered value is already trivial.

These operations do not reorder packet terms.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace TTRecol

/-- Lower the requested physical support bound. -/
def weaken
    {d n inputWeight lowerWeight weakerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {rawSource :
      List (SOTerm H inputWeight)}
    (recollection :
      TTRecol
        n lowerWeight H rawSource)
    (hweight : weakerWeight ≤ lowerWeight) :
    TTRecol
      n weakerWeight H rawSource where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least := fun factor hfactor =>
    hweight.trans
      (recollection.higher_weight_least factor hfactor)
  list_higher_raw :=
    recollection.list_higher_raw

/--
Transport a contextual recollection across semantic equality of complete
ordered mixed packets.
-/
def list_value
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {rawSource targetSource :
      List (SOTerm H inputWeight)}
    (recollection :
      TTRecol
        n lowerWeight H rawSource)
    (hvalue :
      ∀ q : ℕ,
        SOTerm.listValue (n := n) q
            rawSource =
          SOTerm.listValue q targetSource) :
    TTRecol
      n lowerWeight H targetSource where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := fun q =>
    (recollection.list_higher_raw q).trans (hvalue q)

/-- A complete ordered mixed packet with trivial value recollects to empty. -/
def empty_list_value
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (rawSource :
      List (SOTerm H inputWeight))
    (hvalue :
      ∀ q : ℕ,
        SOTerm.listValue (n := n) q
          rawSource = 1) :
    TTRecol
      n lowerWeight H rawSource where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro q
    simpa only [SPFactora.listEval_nil] using (hvalue q).symm

end TTRecol

end TCTex
end Towers
