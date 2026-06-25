import Towers.Group.HallBasic.Weight

/-!
# Hall-tree Jacobi frontier with basic children

If both children of a bracket are basic and neither orientation is basic,
then the larger child is itself a commutator whose Hall admissibility
condition fails against the smaller child.  This is precisely the
left-normed shape repaired by a Jacobi rewrite.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/--
Two basic unequal children whose bracket is nonbasic in both orientations
determine an inadmissible left-normed Jacobi bracket in one orientation.
-/
theorem inadmissible_orientation_children
    (left right : HallTree α)
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (hne : left ≠ right)
    (hforward : ¬(commutator left right).IsBasic)
    (hreverse : ¬(commutator right left).IsBasic) :
    (∃ left₁ left₂ : HallTree α,
      left = commutator left₁ left₂ ∧
        right < left ∧
          ¬left₂ ≤ right) ∨
      ∃ right₁ right₂ : HallTree α,
        right = commutator right₁ right₂ ∧
          left < right ∧
            ¬right₂ ≤ left := by
  rcases lt_trichotomy left right with hleftRight | heq | hrightLeft
  · right
    cases right with
    | atom a =>
        exact
          (hreverse
            (basic_commutator_admissible
              hrightBasic hleftBasic hleftRight trivial)).elim
    | commutator right₁ right₂ =>
        refine ⟨right₁, right₂, rfl, hleftRight, ?_⟩
        intro hright₂Left
        exact
          hreverse
            (basic_commutator_admissible
              hrightBasic hleftBasic hleftRight hright₂Left)
  · exact (hne heq).elim
  · left
    cases left with
    | atom a =>
        exact
          (hforward
            (basic_commutator_admissible
              hleftBasic hrightBasic hrightLeft trivial)).elim
    | commutator left₁ left₂ =>
        refine ⟨left₁, left₂, rfl, hrightLeft, ?_⟩
        intro hleft₂Right
        exact
          hforward
            (basic_commutator_admissible
              hleftBasic hrightBasic hrightLeft hleft₂Right)

end HallTree
end Towers
