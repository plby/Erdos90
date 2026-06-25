import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Class Field Theory, Introduction: quadratic residues modulo a prime

For an odd prime `p`, Milne denotes by `H` the subgroup of squares in
`(Z / pZ)^×`.  This file records that `H` has index two, and hence that the
quotient has two elements.
-/

namespace Submission.CField.Examples

/-- The subgroup of nonzero quadratic residues modulo `p`. -/
def quadraticResidueSubgroup (p : ℕ) : Subgroup (ZMod p)ˣ :=
  (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range

theorem quadratic_residue_subgroup {p : ℕ} (u : (ZMod p)ˣ) :
    u ∈ quadraticResidueSubgroup p ↔ ∃ v : (ZMod p)ˣ, v ^ 2 = u := by
  simp [quadraticResidueSubgroup]

/-- For an odd prime, the nonzero squares have index two. -/
theorem quadratic_residue_index {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (quadraticResidueSubgroup p).index = 2 := by
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime Fact.out
  rw [quadraticResidueSubgroup, IsCyclic.index_powMonoidHom_range]
  rw [Nat.gcd_eq_right_iff_dvd, Nat.card_eq_fintype_card, ZMod.card_units]
  exact (Nat.Prime.even_sub_one Fact.out hp).two_dvd

/-- Equivalently, the quotient of `(Z / pZ)^×` by its subgroup of squares
has two elements. -/
theorem quadratic_residue_card {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    Nat.card ((ZMod p)ˣ ⧸ quadraticResidueSubgroup p) = 2 := by
  exact quadratic_residue_index hp

end Submission.CField.Examples
