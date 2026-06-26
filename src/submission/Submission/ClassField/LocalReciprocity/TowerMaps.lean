import Submission.ClassField.LocalFields.NormSubgroups
import Submission.ClassField.Shifting.SubgroupCorestrictionInt
import Submission.ClassField.Shifting.SubgroupVerlagerung
import Submission.ClassField.ArtinReciprocity.Verlagerung

/-!
# The vertical maps in Milne III.3.2

This file packages the four vertical maps occurring in the two local Artin
tower squares.  It also records the elementary inverse-square argument that
turns naturality of the forward fundamental-class maps into naturality of
their inverse Artin maps.
-/

namespace Submission.CField.LRecip

noncomputable section

open Submission.CField.LFTheory

section Units

variable (K E : Type*) [CommRing K] [CommRing E] [Algebra K E]

/-- The map on unit groups induced by an inclusion of fields. -/
def unitInclusion : Kˣ →* Eˣ :=
  Units.map (algebraMap K E)

@[simp]
theorem unitInclusion_apply (x : Kˣ) :
    ((unitInclusion K E x : Eˣ) : E) = algebraMap K E (x : K) :=
  rfl

end Units

section NormQuotient

variable (K E L : Type*)
  [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
  [FiniteDimensional K E] [FiniteDimensional E L]

omit [FiniteDimensional K E] [FiniteDimensional E L] in
/-- Norm transitivity says that the norm `Eˣ → Kˣ` carries norms from
`L/E` to norms from `L/K`. -/
theorem units_maps_subgroup :
    normSubgroup E L ≤ (normSubgroup K L).comap (normOnUnits K E) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  apply Units.ext
  exact (Algebra.norm_norm (R := K) (S := E) (A := L) (a := (x : L))).symm

/-- The map on norm quotients induced by the field norm in a finite tower. -/
def towerNormHom :
    (Eˣ ⧸ normSubgroup E L) →* (Kˣ ⧸ normSubgroup K L) :=
  QuotientGroup.map (normSubgroup E L) (normSubgroup K L)
    (normOnUnits K E) (units_maps_subgroup K E L)

omit [FiniteDimensional K E] [FiniteDimensional E L] in
@[simp]
theorem tower_hom_mk (x : Eˣ) :
    towerNormHom K E L (QuotientGroup.mk' (normSubgroup E L) x) =
      QuotientGroup.mk' (normSubgroup K L) (normOnUnits K E x) :=
  rfl

end NormQuotient

section GroupMaps

variable {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]

/-- The downward group arrow in the norm square: inclusion followed by
abelianization. -/
def abelianizedSubgroupInclusion : Abelianization H →* Abelianization G :=
  Abelianization.map H.subtype

/-- The upward group arrow in the inclusion square: Verlag. -/
def subgroupVerlagerung : Abelianization G →* Abelianization H :=
  ARecip.verlagerung H

end GroupMaps

section TateIdentification

variable {G : Type} [Group G] [Finite G] (H : Subgroup G)

omit [Finite G] in
/-- Proposition II.3.2(a) identifies the downward group arrow in III.3.2
with corestriction in Tate degree `-2`. -/
theorem abelianized_inclusion_corestriction :
    (TCohomo.homology1Abelianization G).toAddMonoidHom.comp
        (Shifting.corestriction1Int H) =
      (abelianizedSubgroupInclusion H).toAdditive.comp
        (TCohomo.homology1Abelianization H).toAddMonoidHom := by
  simpa [abelianizedSubgroupInclusion] using
    Shifting.corestriction_int_abelianization H

/-- Proposition II.3.2(b) identifies the upward group arrow in III.3.2
with restriction in Tate degree `-2`. -/
theorem subgroup_verlagerung_restriction :
    (TCohomo.homology1Abelianization H).toAddMonoidHom.comp
        (Shifting.restrictionTateInt H) =
      (subgroupVerlagerung H).toAdditive.comp
        (TCohomo.homology1Abelianization G).toAddMonoidHom := by
  simpa [subgroupVerlagerung,
    Shifting.subgroupVerlagerung,
    Shifting.subgroupTransferAbelianization,
    ARecip.verlagerung,
    ARecip.transferToAbelianization] using
      Shifting.restriction_int_verlagerung H

end TateIdentification

section InverseSquare

variable {A B G H : Type*}
  [CommGroup A] [CommGroup B] [CommGroup G] [CommGroup H]

/-- An elementary inverse-square argument.  This is the formal step used in
both diagrams of III.3.2 after cup-product naturality has supplied the
corresponding square for the forward fundamental-class equivalences. -/
theorem inverse_square_forward
    (upper : H ≃* A) (lower : G ≃* B)
    (groupMap : H →* G) (coefficientMap : A →* B)
    (hforward : coefficientMap.comp upper.toMonoidHom =
      lower.toMonoidHom.comp groupMap) :
    groupMap.comp upper.symm.toMonoidHom =
      lower.symm.toMonoidHom.comp coefficientMap := by
  ext x
  apply lower.injective
  simp only [MonoidHom.comp_apply]
  have hx := DFunLike.congr_fun hforward (upper.symm x)
  simpa using hx.symm

end InverseSquare

end

end Submission.CField.LRecip
