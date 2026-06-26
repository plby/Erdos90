import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Towers.ClassField.TateCohomology.AddEquivAbelianization

/-!
# Milne, Class Field Theory, Proposition II.3.2(a)

In degree `-2`, Tate cohomology with integral coefficients is first group
homology.  Under the canonical identification `H₁(G, ℤ) ≃ Gᵃᵇ`, Milne's
corestriction map for a subgroup is the map on abelianizations induced by the
inclusion.
-/

namespace Towers.CField.Shifting

open Additive CategoryTheory Finsupp

variable {G : Type} [Group G]

/-- The degree-one homology corestriction associated to the inclusion of a
subgroup, specialized to integral trivial coefficients. -/
noncomputable def corestriction1Int (H : Subgroup G) :
    groupHomology (Rep.trivial ℤ H ℤ) 1 →+
      groupHomology (Rep.trivial ℤ G ℤ) 1 :=
  (groupHomology.map H.subtype (𝟙 (Rep.trivial ℤ H ℤ)) 1).hom.toAddMonoidHom

/-- **Proposition II.3.2(a).** Under the canonical identifications
`H₁(H, ℤ) ≃ Hᵃᵇ` and `H₁(G, ℤ) ≃ Gᵃᵇ`, homology corestriction along a
subgroup inclusion is the map on abelianizations induced by that inclusion. -/
theorem corestriction_int_abelianization (H : Subgroup G) :
    (TCohomo.homology1Abelianization G).toAddMonoidHom.comp
        (corestriction1Int H) =
      (Abelianization.map H.subtype).toAdditive.comp
        (TCohomo.homology1Abelianization H).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  obtain ⟨h, hh⟩ : ∃ h : H,
      TCohomo.homology1Abelianization H x =
        Additive.ofMul (Abelianization.of h) := by
    rcases TCohomo.homology1Abelianization H x with ⟨h⟩
    exact ⟨h, rfl⟩
  have hx : x =
      (TCohomo.homology1Abelianization H).symm
        (Additive.ofMul (Abelianization.of h)) := by
    apply (TCohomo.homology1Abelianization H).injective
    rw [hh, AddEquiv.apply_symm_apply]
  rw [hh]
  simp only [MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul,
    Abelianization.map_of]
  rw [hx]
  change
    TCohomo.homology1Abelianization G
        (corestriction1Int H
          ((TCohomo.homology1Abelianization H).symm
            (Additive.ofMul (Abelianization.of h)))) =
      Additive.ofMul (Abelianization.of (h : G))
  simp only [TCohomo.homology1Abelianization,
    corestriction1Int, AddEquiv.symm_trans_apply, AddEquiv.trans_apply]
  have hrid :
      (TensorProduct.rid ℤ (Additive (Abelianization H))).toAddEquiv.symm
          (Additive.ofMul (Abelianization.of h)) =
        (TensorProduct.rid ℤ (Additive (Abelianization H))).symm
          (Additive.ofMul (Abelianization.of h)) := rfl
  rw [hrid]
  simp only [TensorProduct.rid_symm_apply]
  have hgenerator :
      (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ H ℤ)).symm
          (Additive.ofMul (Abelianization.of h) ⊗ₜ[ℤ] (1 : ℤ)) =
        groupHomology.H1π (Rep.trivial ℤ H ℤ)
          ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ H ℤ)).inv
            (single h 1)) :=
    groupHomology.H1AddEquivOfIsTrivial_symm_tmul (Rep.trivial ℤ H ℤ) h 1
  rw [hgenerator]
  have hnatural :
      (groupHomology.map H.subtype (𝟙 (Rep.trivial ℤ H ℤ)) 1).hom.toAddMonoidHom
          (groupHomology.H1π (Rep.trivial ℤ H ℤ)
            ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ H ℤ)).inv
              (single h 1))) =
        groupHomology.H1π (Rep.trivial ℤ G ℤ)
          (groupHomology.mapCycles₁ H.subtype (𝟙 (Rep.trivial ℤ H ℤ))
            ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ H ℤ)).inv
              (single h 1))) := by
    have hnat := congrArg
      (fun q => q.hom
        ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ H ℤ)).inv
          (single h 1)))
      (groupHomology.H1π_comp_map (A := Rep.trivial ℤ H ℤ)
        (B := Rep.trivial ℤ G ℤ) H.subtype (𝟙 (Rep.trivial ℤ H ℤ)))
    change
      (groupHomology.map H.subtype (𝟙 (Rep.trivial ℤ H ℤ)) 1).hom
          (groupHomology.H1π (Rep.trivial ℤ H ℤ)
            ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ H ℤ)).inv
              (single h 1))) =
        groupHomology.H1π (Rep.trivial ℤ G ℤ)
          (groupHomology.mapCycles₁ H.subtype (𝟙 (Rep.trivial ℤ H ℤ))
            ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ H ℤ)).inv
              (single h 1))) at hnat
    exact hnat
  rw [hnatural]
  have hmap :
      groupHomology.mapCycles₁ H.subtype (𝟙 (Rep.trivial ℤ H ℤ))
          ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ H ℤ)).inv
            (single h 1)) =
        (groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv
          (single (h : G) 1) := by
    apply Subtype.ext
    change groupHomology.chainsMap₁ (A := Rep.trivial ℤ H ℤ)
        (B := Rep.trivial ℤ G ℤ) H.subtype (𝟙 (Rep.trivial ℤ H ℤ))
          (single h 1) = single (h : G) 1
    simp only [ModuleCat.ofHom_comp, Subgroup.coe_subtype, Rep.res_obj_ρ,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, lmapDomain_apply, mapDomain_single,
      mapRange.linearMap_apply, Representation.IntertwiningMap.coe_toLinearMap,
      mapRange_single]
    have hid :
        (𝟙 (Rep.trivial ℤ H ℤ) :
          Rep.trivial ℤ H ℤ ⟶ Rep.trivial ℤ H ℤ).hom (1 : ℤ) = 1 := rfl
    exact congrArg (single (h : G)) hid
  rw [hmap, groupHomology.H1AddEquivOfIsTrivial_single]
  have hrid' :
      (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv
          (Additive.ofMul (Abelianization.of (h : G)) ⊗ₜ[ℤ] (1 : ℤ)) =
        TensorProduct.rid ℤ (Additive (Abelianization G))
          (Additive.ofMul (Abelianization.of (h : G)) ⊗ₜ[ℤ] (1 : ℤ)) := rfl
  rw [hrid', TensorProduct.rid_tmul, one_smul]

end Towers.CField.Shifting
