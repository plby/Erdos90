import Submission.ClassField.LocalReciprocity.TowerMaps
import Submission.ClassField.LocalReciprocity.MaximalIntermediate

open scoped IsMulCommutative

/-!
# The Galois-closure group in norm limitation

In Milne's proof let `G = Gal(L/K)` and `H = Gal(L/E)`.  The cokernel of
`Hᵃᵇ → Gᵃᵇ` is the quotient of `G` by the inverse image of the image of
`H` in `Gᵃᵇ`.  Equivalently that subgroup is `H · G'`.  This file proves
that identification without assuming that `H` is normal.
-/

namespace Submission.CField.GClass

open Submission.CField.LRecip

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The inverse image in `G` of the image of `H` in the abelianization.
It is the smallest normal subgroup containing both `H` and the commutator. -/
def abelianClosureSubgroup (H : Subgroup G) : Subgroup G :=
  (H.map (Abelianization.of : G →* Abelianization G)).comap
    (Abelianization.of : G →* Abelianization G)

instance abelian_closure_normal (H : Subgroup G) :
    (abelianClosureSubgroup H).Normal := by
  change ((H.map (Abelianization.of : G →* Abelianization G)).comap
    (Abelianization.of : G →* Abelianization G)).Normal
  infer_instance

/-- The inverse-image description is the familiar product `H · G'`. -/
theorem abelian_sup_commutator (H : Subgroup G) :
    abelianClosureSubgroup H = H ⊔ commutator G := by
  simpa only [abelianClosureSubgroup, Abelianization.of, sup_comm] using
    (QuotientGroup.comap_map_mk' (commutator G) H)

theorem abelian_closure_subgroup (H : Subgroup G) :
    H ≤ abelianClosureSubgroup H := by
  rw [abelian_sup_commutator]
  exact le_sup_left

theorem commutator_abelian_closure (H : Subgroup G) :
    commutator G ≤ abelianClosureSubgroup H := by
  rw [abelian_sup_commutator]
  exact le_sup_right

/-- The range of `Hᵃᵇ → Gᵃᵇ` is precisely the image of `H` in `Gᵃᵇ`. -/
theorem abelianized_inclusion_range (H : Subgroup G) :
    (abelianizedSubgroupInclusion H).range =
      H.map (Abelianization.of : G →* Abelianization G) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
      (commutator H) x
    refine ⟨h.1, h.2, ?_⟩
    exact (Abelianization.map_of H.subtype h).symm
  · rintro y ⟨g, hg, rfl⟩
    refine ⟨Abelianization.of (⟨g, hg⟩ : H), ?_⟩
    simp [abelianizedSubgroupInclusion]

/-- Mapping `H · G'` to the abelianization kills `G'` and leaves exactly
the image of `H`. -/
theorem abelian_closure_abelianization (H : Subgroup G) :
    (abelianClosureSubgroup H).map
        (Abelianization.of : G →* Abelianization G) =
      H.map (Abelianization.of : G →* Abelianization G) := by
  rw [abelian_sup_commutator, Subgroup.map_sup]
  change H.map (QuotientGroup.mk' (commutator G)) ⊔
      (commutator G).map (QuotientGroup.mk' (commutator G)) =
    H.map (QuotientGroup.mk' (commutator G))
  rw [QuotientGroup.map_mk'_self, sup_bot_eq]

/-- The group-theoretic cokernel in the corestriction diagram is
`G / (H · G')`. -/
noncomputable def abelianizedCokerEquiv
    (H : Subgroup G) :
    (Abelianization G ⧸ (abelianizedSubgroupInclusion H).range) ≃*
      G ⧸ abelianClosureSubgroup H :=
  (QuotientGroup.quotientMulEquivOfEq
      ((abelianized_inclusion_range H).trans
        (abelian_closure_abelianization H).symm)).trans
    (QuotientGroup.quotientQuotientEquivQuotient
      (commutator G) (abelianClosureSubgroup H)
      (commutator_abelian_closure H))

theorem abelianized_inclusion_coker
    (H : Subgroup G) :
    Nat.card
        (Abelianization G ⧸ (abelianizedSubgroupInclusion H).range) =
      Nat.card (G ⧸ abelianClosureSubgroup H) :=
  Nat.card_congr (abelianizedCokerEquiv H).toEquiv

/-- The quotient corresponding to the maximal abelian subfield is
commutative. -/
theorem abelian_closure_commutative (H : Subgroup G) :
    Std.Commutative
      (· * · : (G ⧸ abelianClosureSubgroup H) →
        (G ⧸ abelianClosureSubgroup H) →
          (G ⧸ abelianClosureSubgroup H)) :=
  (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (commutator_abelian_closure H)).is_comm

section GaloisClosure

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- For `E = Lᴴ`, the maximal subfield of `E` abelian Galois over `K` is
the fixed field of the inverse image of the image of `H` in `Gᵃᵇ`. -/
def maximalSubfieldInside
    (H : Subgroup Gal(L/K)) : IntermediateField K L :=
  IntermediateField.fixedField (abelianClosureSubgroup H)

instance abelian_subfield_inside
    (H : Subgroup Gal(L/K)) :
    IsGalois K (maximalSubfieldInside K L H) :=
  IsGalois.of_fixedField_normal_subgroup (abelianClosureSubgroup H)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The canonical maximal abelian field lies inside `Lᴴ`. -/
theorem maximal_abelian_inside
    (H : Subgroup Gal(L/K)) :
    maximalSubfieldInside K L H ≤
      IntermediateField.fixedField H :=
  IntermediateField.fixedField_le (abelian_closure_subgroup H)

/-- Its Galois group is `G / (H · G')`. -/
noncomputable def maximal_subfield_inside
    (H : Subgroup Gal(L/K)) :
    Gal(L/K) ⧸ abelianClosureSubgroup H ≃*
      Gal(maximalSubfieldInside K L H/K) :=
  IsGalois.normalAutEquivQuotient (abelianClosureSubgroup H)

instance subfield_inside_commutative
    (H : Subgroup Gal(L/K)) :
    IsMulCommutative
      Gal(maximalSubfieldInside K L H/K) := by
  let e := maximal_subfield_inside K L H
  let hcomm := abelian_closure_commutative H
  refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
  apply e.symm.injective
  simpa only [map_mul] using hcomm.comm (e.symm sigma) (e.symm tau)

omit [IsGalois K L] in
/-- Every abelian Galois intermediate field contained in `Lᴴ` is contained
in the canonical field above. -/
theorem subfield_inside_fixed
    (H : Subgroup Gal(L/K))
    (F : IntermediateField K L)
    (hF : F ≤ IntermediateField.fixedField H)
    [IsGalois K F] [IsMulCommutative Gal(F/K)] :
    F ≤ maximalSubfieldInside K L H := by
  rw [maximalSubfieldInside,
    IntermediateField.le_iff_le]
  rw [abelian_sup_commutator]
  apply sup_le
  · have hfix := IntermediateField.fixingSubgroup_le hF
    rw [IntermediateField.fixingSubgroup_fixedField] at hfix
    exact hfix
  · letI : CommGroup Gal(F/K) := inferInstance
    let r : Gal(L/K) →* Gal(F/K) :=
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F
    have hcomm : commutator Gal(L/K) ≤ r.ker :=
      Abelianization.commutator_subset_ker r
    change commutator Gal(L/K) ≤ F.fixingSubgroup
    rw [← IntermediateField.restrictNormalHom_ker F]
    simpa only [r] using hcomm

/-- Thus the cokernel in Milne's diagram is the Galois group of the
canonical maximal abelian subfield of `Lᴴ`. -/
noncomputable def abelianizedInclusionCoker
    (H : Subgroup Gal(L/K)) :
    (Abelianization Gal(L/K) ⧸
        (abelianizedSubgroupInclusion H).range) ≃*
      Gal(maximalSubfieldInside K L H/K) :=
  (abelianizedCokerEquiv H).trans
    (maximal_subfield_inside K L H)

end GaloisClosure

end

end Submission.CField.GClass
