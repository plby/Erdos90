import Towers.Group.HallBasic.Weight

/-!
# The Hall-tree Jacobi frontier starts in weight three

For a bracket of two distinct Hall trees with total weight at most two, both
children are atoms.  Exactly one orientation is then basic.  Consequently the
first brackets that can require a Jacobi rewrite have total weight at least
three.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/--
Two distinct Hall trees of total bracket weight at most two cannot have both
bracket orientations non-basic.
-/
theorem false_swap_not
    (left right : HallTree α)
    (hweight : (commutator left right).weight ≤ 2)
    (hne : left ≠ right)
    (hforward : ¬(commutator left right).IsBasic)
    (hreverse : ¬(commutator right left).IsBasic) :
    False := by
  have hleftWeight : left.weight = 1 := by
    have hleftPos := left.weight_pos
    have hrightPos := right.weight_pos
    simp only [weight_commutator] at hweight
    omega
  have hrightWeight : right.weight = 1 := by
    have hleftPos := left.weight_pos
    have hrightPos := right.weight_pos
    simp only [weight_commutator] at hweight
    omega
  obtain ⟨leftAtom, rfl⟩ := atom_one hleftWeight
  obtain ⟨rightAtom, rfl⟩ := atom_one hrightWeight
  rcases lt_trichotomy (atom rightAtom) (atom leftAtom) with
    hrightLeft | heq | hleftRight
  · exact
      hforward
        (basic_commutator_admissible
          (isBasic_atom leftAtom) (isBasic_atom rightAtom)
            hrightLeft trivial)
  · exact hne heq.symm
  · exact
      hreverse
        (basic_commutator_admissible
          (isBasic_atom rightAtom) (isBasic_atom leftAtom)
            hleftRight trivial)

end HallTree
end Towers
