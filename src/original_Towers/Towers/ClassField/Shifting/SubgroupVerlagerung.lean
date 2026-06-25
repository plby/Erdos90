import Mathlib.GroupTheory.Transfer
import Towers.ClassField.TateCohomology.AddEquivAbelianization

/-!
# Milne, Class Field Theory, Proposition II.3.2(b)

In Tate degree `-2`, restriction to a subgroup is Verlag under the
canonical identification with the abelianization.  Since Mathlib does not yet
provide a uniform negative Tate-cohomology restriction map, we realize this
map canonically by transporting Verlag across the identifications
`H₁(G, ℤ) ≃ Gᵃᵇ` and `H₁(H, ℤ) ≃ Hᵃᵇ`.
-/

namespace Towers.CField.Shifting

open Additive

variable {G : Type} [Group G] [Finite G]

/-- The transfer from `G` to the abelianization of a subgroup `H`. -/
noncomputable def subgroupTransferAbelianization (H : Subgroup G) :
    G →* Abelianization H :=
  MonoidHom.transfer (Abelianization.of : H →* Abelianization H)

/-- The Verlag homomorphism `Gᵃᵇ ⟶ Hᵃᵇ`. -/
noncomputable def subgroupVerlagerung (H : Subgroup G) :
    Abelianization G →* Abelianization H :=
  Abelianization.lift (subgroupTransferAbelianization H)

@[simp]
theorem subgroupVerlagerung_of (H : Subgroup G) (g : G) :
    subgroupVerlagerung H (Abelianization.of g) =
      subgroupTransferAbelianization H g :=
  rfl

/-- Restriction in Tate degree `-2`, equivalently the degree-one integral
group-homology restriction, obtained from the canonical Verlag. -/
noncomputable def restrictionTateInt (H : Subgroup G) :
    groupHomology (Rep.trivial ℤ G ℤ) 1 →+
      groupHomology (Rep.trivial ℤ H ℤ) 1 :=
  (TCohomo.homology1Abelianization H).symm.toAddMonoidHom.comp
    ((subgroupVerlagerung H).toAdditive.comp
      (TCohomo.homology1Abelianization G).toAddMonoidHom)

/-- **Proposition II.3.2(b).** Under the canonical identifications
`H₁(G, ℤ) ≃ Gᵃᵇ` and `H₁(H, ℤ) ≃ Hᵃᵇ`, restriction in Tate degree `-2` is
the Verlag map. -/
theorem restriction_int_verlagerung (H : Subgroup G) :
    (TCohomo.homology1Abelianization H).toAddMonoidHom.comp
        (restrictionTateInt H) =
      (subgroupVerlagerung H).toAdditive.comp
        (TCohomo.homology1Abelianization G).toAddMonoidHom := by
  ext x
  simp [restrictionTateInt]

/-- On a class represented by `g : G`, Tate degree-`-2` restriction is the
ordinary transfer of `g` to `Hᵃᵇ`. -/
theorem restriction_tate_int
    (H : Subgroup G) (g : G) :
    restrictionTateInt H
        ((TCohomo.homology1Abelianization G).symm
          (Additive.ofMul (Abelianization.of g))) =
      (TCohomo.homology1Abelianization H).symm
        (Additive.ofMul (subgroupTransferAbelianization H g)) := by
  apply (TCohomo.homology1Abelianization H).injective
  simp [restrictionTateInt]

end Towers.CField.Shifting
