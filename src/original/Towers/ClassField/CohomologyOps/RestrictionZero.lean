import Towers.ClassField.CohomologyOps.DegreeZero

/-!
# Milne, Class Field Theory, Proposition II.1.30 in degree zero

For a finite-index subgroup `H ≤ G`, the composite of restriction and corestriction on
degree-zero cohomology is multiplication by the index `(G : H)`.

The all-degree statement requires a cohomological corestriction construction, which is not yet
available in Mathlib.  This file proves the complete degree-zero case using the transversal norm
from `Example129`.
-/

namespace Towers.CField.COps

open scoped BigOperators

universe u

variable {k G : Type u} [CommRing k] [Group G]

section

variable (A : Rep k G) (H : Subgroup G)

/-- Restriction in degree zero sends a `G`-invariant vector to the same vector regarded as
`H`-invariant. -/
def restrictionZero :
    A.ρ.invariants →ₗ[k] Representation.invariants (A.ρ.comp H.subtype) :=
  { toFun := fun m ↦ ⟨m, fun h ↦ by simpa using m.2 (h : G)⟩
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

variable [H.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Proposition II.1.30, degree-zero form.** The composite of restriction and corestriction
sends an invariant vector `m` to `(G : H) • m`. -/
theorem corestriction_zero_restriction
    (S : H.LeftTransversal) (m : A.ρ.invariants) :
    corestrictionZero A H S (restrictionZero A H m) = H.index • m := by
  apply Subtype.ext
  change transversalNorm A H S (m : A) = H.index • (m : A)
  have hfix : ∀ q : G ⧸ H, A.ρ (S.2.leftQuotientEquiv q : G) (m : A) = m :=
    fun q ↦ m.2 _
  simp_rw [transversalNorm, hfix]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, ← H.index_eq_card]

/-- Linear-map version of Proposition II.1.30 in degree zero. -/
theorem corestriction_comp_restriction (S : H.LeftTransversal) :
    (corestrictionZero A H S).comp (restrictionZero A H) =
      H.index • LinearMap.id := by
  apply LinearMap.ext
  intro m
  exact corestriction_zero_restriction A H S m

end

end Towers.CField.COps
