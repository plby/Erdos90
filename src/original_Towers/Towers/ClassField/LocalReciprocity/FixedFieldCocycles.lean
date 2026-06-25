import Towers.ClassField.LocalReciprocity.FundamentalClass
import Towers.ClassField.LocalReciprocity.NormResidueFormula

/-!
# Fixed-field cocycles in Lemma III.3.2

Formula (31) says that, after identifying a subgroup with the Galois group
over its fixed field, the restricted ambient fundamental cocycle and the
intrinsic fixed-field fundamental cocycle are cohomologous.  This file makes
that representative-level consequence explicit.
-/

namespace Towers.CField.LRecip

open Towers.CField.LFTheory
open Towers.CField.LClass
open Towers.CField.CProduca
open Towers.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance fixedCocycleValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance fixedCocycleValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

private abbrev F (H : Subgroup Gal(L/K)) :=
  IntermediateField.fixedField H

private abbrev eH (H : Subgroup Gal(L/K)) :
    H ≃* Gal(L/F K L H) :=
  IntermediateField.subgroupEquivAlgEquiv H

local instance fixedCocycleSubgroupFintype
    (H : Subgroup Gal(L/K)) : Fintype H :=
  Fintype.ofFinite H

/-- Restriction of the ambient chosen cocycle to `H`. -/
noncomputable def restrictedFundamentalCocycle
    (H : Subgroup Gal(L/K)) :
    NMCocycl₂ (G := H) (M := Lˣ) :=
  NMCocycl₂.restrict H.subtype (by intro h x; rfl)
    (localFundamentalCocycle K L)

/-- The intrinsic cocycle over the fixed field, reindexed back to `H`. -/
noncomputable def fixedFundamentalCocycle
    (H : Subgroup Gal(L/K)) :
    NMCocycl₂ (G := H) (M := Lˣ) := by
  let E := F K L H
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  exact MHTrans.cocycleMap (eH K L H).symm
    (MulEquiv.refl Lˣ) (by intro g x; rfl)
      (localFundamentalCocycle E L)

set_option maxHeartbeats 3000000 in
-- Comparing the two transported fixed-field cocycles requires extended cohomology normalization.
set_option synthInstance.maxHeartbeats 500000 in
/-- Under local-invariant base change, the two chosen cocycles over `H`
represent the same multiplicative `H²` class. -/
theorem restricted_cocycle_cohomologous
    (H : Subgroup Gal(L/K))
    (hbase : SpectralChangeFormula K (F K L H)) :
    MHTwo.IsCohomologous
      (restrictedFundamentalCocycle K L H)
      (fixedFundamentalCocycle K L H) := by
  let E := F K L H
  let e := eH K L H
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  rw [← MHTwo.mk_eq_iff]
  apply (MHTrans.h2Equiv e
    (MulEquiv.refl Lˣ) (by intro g x; rfl)).injective
  rw [MHTrans.h_2_mk,
    MHTrans.h_2_mk]
  have hleft :
      MHTrans.cocycleMap e (MulEquiv.refl Lˣ)
          (by intro g x; rfl)
          (restrictedFundamentalCocycle K L H) =
        NMCocycl₂.restrict (galoisTowerInclusion K E L)
          (by intro g x; rfl) (localFundamentalCocycle K L) := by
    apply NMCocycl₂.ext
    rintro ⟨g, h⟩
    rfl
  have hright :
      MHTrans.cocycleMap e (MulEquiv.refl Lˣ)
          (by intro g x; rfl)
          (fixedFundamentalCocycle K L H) =
        localFundamentalCocycle E L := by
    apply NMCocycl₂.ext
    rintro ⟨g, h⟩
    rfl
  rw [hleft, hright]
  change galoisHRestriction K E L
      (MHTwo.mk (localFundamentalCocycle K L)) =
    MHTwo.mk (localFundamentalCocycle E L)
  rw [mk_fundamental_cocycle,
    mk_fundamental_cocycle]
  exact multiplicative_fundamental_change
    K E L hbase

/-- Identify the fixed-field norm quotient with subgroup invariants modulo
the subgroup norm. -/
noncomputable def fixedSubgroupInvariants
    (H : Subgroup Gal(L/K)) :
    ((F K L H)ˣ ⧸ normSubgroup (F K L H) L) ≃*
      FMAct.invariantsModNorm H Lˣ := by
  let E := F K L H
  let e := eH K L H
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  exact (galoisInvariantsMod E L).symm.trans
    (FATrans.invariantsModGroup e.symm
      (by intro g x; rfl))

set_option maxHeartbeats 3000000 in
-- Expanding the cyclic product after invariant transport requires extended normalization.
set_option synthInstance.maxHeartbeats 500000 in
/-- The fixed-field forward map, transported to subgroup invariants, is the
cyclic product of the transported fixed-field fundamental cocycle. -/
theorem fixed_cyclic_product
    (H : Subgroup Gal(L/K)) (h : H) :
    fixedSubgroupInvariants K L H
        (fixedResidueEquiv K L H (Abelianization.of h)) =
      QuotientGroup.mk' (FMAct.norm H Lˣ).range
        (NMCocycl₂.cyclicProductInvariant
          (fixedFundamentalCocycle K L H) h) := by
  let E := F K L H
  let e := eH K L H
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  change FATrans.invariantsModGroup e.symm
      (by intro g x; rfl)
      ((galoisInvariantsMod E L).symm
        (localNormResidue E L
          (Abelianization.of (e h)))) = _
  rw [local_cyclic_product E L (e h),
    local_cyclic_invariant]
  rw [FATrans.invariants_mod_mk]
  apply congrArg (QuotientGroup.mk' (FMAct.norm H Lˣ).range)
  apply Subtype.ext
  change NMCocycl₂.cyclicProduct
      (localFundamentalCocycle E L) (e h) =
    NMCocycl₂.cyclicProduct
      (fixedFundamentalCocycle K L H) h
  rw [NMCocycl₂.cyclicProduct,
    NMCocycl₂.cyclicProduct]
  exact Fintype.prod_equiv e.symm.toEquiv _ _ (fun g ↦ rfl)

/-- Map the ambient norm quotient to subgroup invariants by first passing to
Galois invariants and then forgetting from `Gal(L/K)` to `H`. -/
noncomputable def ambientSubgroupInvariants
    (H : Subgroup Gal(L/K)) :
    (Kˣ ⧸ normSubgroup K L) →*
      FMAct.invariantsModNorm H Lˣ :=
  (NMCocycl₂.invariantsModRestriction H).comp
    (galoisInvariantsMod K L).symm.toMonoidHom

set_option maxHeartbeats 2000000 in
-- Normalizing both routes through subgroup invariants needs a larger elaboration budget.
set_option synthInstance.maxHeartbeats 500000 in
omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- The two routes from a base-field unit to subgroup invariants agree. -/
theorem fixed_unit_inclusion
    (H : Subgroup Gal(L/K)) (a : Kˣ) :
    fixedSubgroupInvariants K L H
        (QuotientGroup.mk' (normSubgroup (F K L H) L)
          (unitInclusion K (F K L H) a)) =
      ambientSubgroupInvariants K L H
        (QuotientGroup.mk' (normSubgroup K L) a) := by
  let E := F K L H
  let e := eH K L H
  let xK : FMAct.invariants Gal(L/K) Lˣ :=
    ⟨Units.map (algebraMap K L) a, by
      intro σ
      apply Units.ext
      exact σ.commutes a⟩
  let xE : FMAct.invariants Gal(L/E) Lˣ :=
    ⟨Units.map (algebraMap E L) (unitInclusion K E a), by
      intro σ
      apply Units.ext
      exact σ.commutes (unitInclusion K E a)⟩
  have hK :
      (galoisInvariantsMod K L).symm
          (QuotientGroup.mk' (normSubgroup K L) a) =
        QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range xK := by
    apply (galoisInvariantsMod K L).injective
    rw [(galoisInvariantsMod K L).apply_symm_apply]
    exact (galois_invariants_algebra K L a).symm
  have hE :
      (galoisInvariantsMod E L).symm
          (QuotientGroup.mk' (normSubgroup E L) (unitInclusion K E a)) =
        QuotientGroup.mk' (FMAct.norm Gal(L/E) Lˣ).range xE := by
    apply (galoisInvariantsMod E L).injective
    rw [(galoisInvariantsMod E L).apply_symm_apply]
    exact (galois_invariants_algebra E L
      (unitInclusion K E a)).symm
  change FATrans.invariantsModGroup e.symm
      (by intro g x; rfl)
      ((galoisInvariantsMod E L).symm
        (QuotientGroup.mk' (normSubgroup E L) (unitInclusion K E a))) =
    NMCocycl₂.invariantsModRestriction H
      ((galoisInvariantsMod K L).symm
        (QuotientGroup.mk' (normSubgroup K L) a))
  rw [hK, hE,
    FATrans.invariants_mod_mk,
    NMCocycl₂.invariants_restriction_mk]
  apply congrArg (QuotientGroup.mk' (FMAct.norm H Lˣ).range)
  apply Subtype.ext
  apply Units.ext
  exact IsScalarTower.algebraMap_apply K E L a

end

end Towers.CField.LRecip
