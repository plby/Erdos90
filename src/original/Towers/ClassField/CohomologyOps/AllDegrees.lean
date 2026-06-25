import Towers.ClassField.CohomologyOps.Corestriction
import Towers.ClassField.CohomologyOps.GroupFiniteIso
import Towers.ClassField.CohomologyOps.BarRestriction

/-!
# Milne, Class Field Theory, Proposition II.1.30

This file develops the all-degree statement that corestriction after restriction is multiplication
by the subgroup index.
-/

namespace Towers.CField.COps

open CategoryTheory Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

section

variable (A : Rep k G) (H : Subgroup G) [H.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [H.FiniteIndex] in
lemma res_coind_unit (x : A) (g : G) :
    (((resCoindAdjunction k H.subtype).unit.app A).hom x :
      Representation.coindV H.subtype (A.ρ.comp H.subtype)).1 g = A.ρ g x := by
  rfl

omit [H.FiniteIndex] in
lemma res_counit_v (g : G) (x : A) :
    ((indResAdjunction k H.subtype).counit.app A).hom
        (Representation.IndV.mk H.subtype (A.ρ.comp H.subtype) g x) = A.ρ g⁻¹ x := by
  change ((indResHomEquiv H.subtype (res H.subtype A) A).symm (𝟙 _)).hom
      (Representation.IndV.mk H.subtype (A.ρ.comp H.subtype) g x) = A.ρ g⁻¹ x
  simp [indResHomEquiv]

/-- On coefficients, the restriction/coinduction unit followed by the finite-index trace is
multiplication by the subgroup index. -/
theorem res_coind_corestriction :
    (resCoindAdjunction k H.subtype).unit.app A ≫ corestrictionTrace A H =
      H.index • 𝟙 A := by
  letI := Classical.decRel (QuotientGroup.rightRel H)
  rw [corestrictionTrace, coindResAdjunction_counit_app]
  ext x
  change ((indResAdjunction k H.subtype).counit.app A).hom.toLinearMap
      ((indCoindIso (res H.subtype A)).inv.hom.toLinearMap
        (((resCoindAdjunction k H.subtype).unit.app A).hom.toLinearMap x)) = H.index • x
  rw [indCoindIso_inv_hom_toLinearMap]
  change ((indResAdjunction k H.subtype).counit.app A).hom
      (coindToInd (res H.subtype A)
        (((resCoindAdjunction k H.subtype).unit.app A).hom x)) = H.index • x
  rw [coindToInd_apply]
  change ((indResAdjunction k H.subtype).counit.app A).hom.toLinearMap _ = H.index • x
  change ((indResAdjunction k H.subtype).counit.app A).hom.toLinearMap
      (Finset.univ.sum fun q : Quotient (QuotientGroup.rightRel H) ↦ _) = H.index • x
  rw [map_sum]
  calc
    _ = ∑ _q : Quotient (QuotientGroup.rightRel H), x := by
      apply Fintype.sum_congr
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
          change ((indResAdjunction k H.subtype).counit.app A).hom
              (Representation.IndV.mk H.subtype (A.ρ.comp H.subtype) g
                ((((resCoindAdjunction k H.subtype).unit.app A).hom x :
                  Representation.coindV H.subtype (A.ρ.comp H.subtype)).1 g)) = x
          rw [res_counit_v, res_coind_unit]
          simp [← Module.End.mul_apply, ← map_mul]
    _ = H.index • x := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
        Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H),
        ← H.index_eq_card]

/-- Restriction expressed through the restriction/coinduction unit and Shapiro's isomorphism. -/
noncomputable def shapiroRestriction (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology (res H.subtype A) n :=
  groupCohomology.map (MonoidHom.id G)
      ((resCoindAdjunction k H.subtype).unit.app A) n ≫
    (groupCohomology.coindIso (res H.subtype A) n).hom

set_option backward.isDefEq.respectTransparency false in
/-- Shapiro restriction followed by corestriction is multiplication by the
subgroup index in every cohomological degree.  This is the transfer identity
needed in the Sylow argument of Theorem II.3.10; it does not require comparing
Shapiro restriction with the inhomogeneous-cochain restriction map. -/
theorem shapiro_restriction_corestriction (n : ℕ) :
    shapiroRestriction A H n ≫ corestriction A H n =
      H.index • 𝟙 (groupCohomology A n) := by
  dsimp only [shapiroRestriction, corestriction]
  slice_lhs 2 3 => rw [Iso.hom_inv_id]
  simp only [Category.id_comp]
  rw [← groupCohomology.map_id_comp]
  rw [res_coind_corestriction]
  change (groupCohomology.functor k G n).map (H.index • 𝟙 A) = _
  rw [Functor.map_nsmul]
  exact congrArg (H.index • ·) ((groupCohomology.functor k G n).map_id A)

/-!
The remaining step in Proposition II.1.30 is the equality

`restriction A H n = shapiroRestriction A H n`.

The explicit augmentation-compatible comparison map and its homotopy to Mathlib's chosen
projective-resolution lift are constructed in `BarRestriction.lean`.  Mathlib's
`groupCohomology.coindIso` is constructed in
`Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro` through projective
resolutions, whereas `groupCohomology.map H.subtype (𝟙 _) n` is constructed through
inhomogeneous cochains.  The remaining step is to transport the comparison homotopy through the
contravariant linear-Yoneda cochain complex and the `op`/`unop` layers of `isoExt`.  Once this
compatibility lemma is supplied, the all-degree formula follows from
`res_coind_corestriction`, functoriality, and additivity.
-/

end

end Towers.CField.COps
