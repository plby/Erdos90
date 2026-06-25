import Towers.Group.Zassenhaus.BracketPacketWorklist

/-!
# Inventory of powered outer-bracket packet worklists

The exact powered worklist for a bracket with a finite left product contains
three kinds of factors: retained left factors, their signed inverses, and
terminal correction-packet factors.  This file records that finite inventory
without imposing any concrete Hall-family specialization.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace PBWork

/-- Every worklist factor comes from a wrapper or one terminal packet. -/
theorem left_or_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right)
    {left : List (SPFactora H inputWeight)}
    {x : SPFactora H inputWeight}
    (hx : x ∈ factors right packet left) :
    (∃ source ∈ left, x = source) ∨
      (∃ source ∈ left, x = source.neg) ∨
        ∃ source ∈ left, x ∈ (packet source).factors := by
  induction left with
  | nil =>
      simp at hx
  | cons head tail ih =>
      simp only [factors_cons, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with ((hhead | hx) | hheadNeg) | hx
      · exact Or.inl ⟨head, List.mem_cons_self, hhead⟩
      · rcases ih hx with hsource | hsource | hsource
        · rcases hsource with ⟨source, hsource, hx⟩
          exact Or.inl ⟨source, List.mem_cons_of_mem head hsource, hx⟩
        · rcases hsource with ⟨source, hsource, hx⟩
          exact
            Or.inr
              (Or.inl ⟨source, List.mem_cons_of_mem head hsource, hx⟩)
        · rcases hsource with ⟨source, hsource, hx⟩
          exact
            Or.inr
              (Or.inr ⟨source, List.mem_cons_of_mem head hsource, hx⟩)
      · exact Or.inr (Or.inl ⟨head, List.mem_cons_self, hheadNeg⟩)
      · exact Or.inr (Or.inr ⟨head, List.mem_cons_self, hx⟩)

end PBWork
end TCTex
end Towers
