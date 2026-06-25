import Submission.ClassField.LocalReciprocity.FixedFieldCocycles
import Submission.ClassField.LocalReciprocity.FixedFieldNorm

/-!
# The norm/corestriction square in Lemma III.3.2

The field norm from a subgroup fixed field is a left-coset product.  Combined
with the cocycle left-coset identity, this proves the degree-minus-two
corestriction square.  As in the restriction square, the sole arithmetic
normalization input is formula (31).
-/

namespace Submission.CField.LRecip

open Submission.CField.LFTheory
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance normSquareNormValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance normSquareNormValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private abbrev F (H : Subgroup Gal(L/K)) :=
  IntermediateField.fixedField H

private abbrev eH (H : Subgroup Gal(L/K)) :
    H ≃* Gal(L/F K L H) :=
  IntermediateField.subgroupEquivAlgEquiv H

local instance normSubgroupFintype
    (H : Subgroup Gal(L/K)) : Fintype H :=
  Fintype.ofFinite H

/-- Corestriction on invariant norm quotients, defined through the field
norm.  The following theorem computes it as the left-transversal norm. -/
noncomputable def fixedInvariantsCorestriction
    (H : Subgroup Gal(L/K)) :
    FMAct.invariantsModNorm H Lˣ →*
      FMAct.invariantsModNorm Gal(L/K) Lˣ :=
  (galoisInvariantsMod K L).symm.toMonoidHom.comp
    ((towerNormHom K (F K L H) L).comp
      (fixedSubgroupInvariants K L H).symm.toMonoidHom)

set_option maxHeartbeats 5000000 in
-- Corestriction on the transported invariant cocycle expands a large dependent product.
set_option synthInstance.maxHeartbeats 500000 in
/-- On the restricted ambient cocycle product, invariant corestriction is
the ambient cocycle product. -/
theorem fixed_invariants_corestriction
    (H : Subgroup Gal(L/K)) (h : H) :
    fixedInvariantsCorestriction K L H
        (QuotientGroup.mk' (FMAct.norm H Lˣ).range
          (NMCocycl₂.cyclicProductInvariant
            (restrictedFundamentalCocycle K L H) h)) =
      QuotientGroup.mk'
        (FMAct.norm Gal(L/K) Lˣ).range
        (NMCocycl₂.cyclicProductInvariant
          (localFundamentalCocycle K L) (h : Gal(L/K))) := by
  let G := Gal(L/K)
  let E := F K L H
  let e := eH K L H
  let c := localFundamentalCocycle K L
  let cH := restrictedFundamentalCocycle K L H
  let xH := NMCocycl₂.cyclicProductInvariant cH h
  let p : Lˣ := xH.1
  have hpFixed (t : H) : (t : G) • p = p := xH.2 t
  let yVal : E := ⟨(p : L), by
    rw [IntermediateField.mem_fixedField_iff]
    intro t ht
    have ht' := hpFixed ⟨t, ht⟩
    exact congrArg Units.val ht'⟩
  have hy0 : (yVal : E) ≠ 0 := by
    intro hy
    exact p.ne_zero (congrArg Subtype.val hy)
  let y : Eˣ := Units.mk0 yVal hy0
  let xE : FMAct.invariants Gal(L/E) Lˣ :=
    ⟨Units.map (algebraMap E L) y, by
      intro σ
      apply Units.ext
      exact σ.commutes y⟩
  have hxy : Units.map (algebraMap E L) y = p := by
    apply Units.ext
    rfl
  have hEpre :
      (fixedSubgroupInvariants K L H).symm
          (QuotientGroup.mk' (FMAct.norm H Lˣ).range xH) =
        QuotientGroup.mk' (normSubgroup E L) y := by
    apply (fixedSubgroupInvariants K L H).injective
    rw [MulEquiv.apply_symm_apply
      (fixedSubgroupInvariants K L H)]
    symm
    change FATrans.invariantsModGroup e.symm
        (by intro g x; rfl)
        ((galoisInvariantsMod E L).symm
          (QuotientGroup.mk' (normSubgroup E L) y)) =
      QuotientGroup.mk' (FMAct.norm H Lˣ).range xH
    have hEinv :
        (galoisInvariantsMod E L).symm
            (QuotientGroup.mk' (normSubgroup E L) y) =
          QuotientGroup.mk'
            (FMAct.norm Gal(L/E) Lˣ).range xE := by
      apply (galoisInvariantsMod E L).injective
      rw [(galoisInvariantsMod E L).apply_symm_apply]
      exact (galois_invariants_algebra
        E L y).symm
    rw [hEinv,
      FATrans.invariants_mod_mk]
    apply congrArg (QuotientGroup.mk' (FMAct.norm H Lˣ).range)
    apply Subtype.ext
    exact hxy
  let ny : Kˣ := normOnUnits K E y
  let xG : FMAct.invariants G Lˣ :=
    ⟨Units.map (algebraMap K L) ny, by
      intro σ
      apply Units.ext
      exact σ.commutes ny⟩
  have hKinv :
      (galoisInvariantsMod K L).symm
          (QuotientGroup.mk' (normSubgroup K L) ny) =
        QuotientGroup.mk' (FMAct.norm G Lˣ).range xG := by
    apply (galoisInvariantsMod K L).injective
    rw [(galoisInvariantsMod K L).apply_symm_apply]
    exact (galois_invariants_algebra
      K L ny).symm
  change (galoisInvariantsMod K L).symm
      (towerNormHom K E L
        ((fixedSubgroupInvariants K L H).symm
          (QuotientGroup.mk' (FMAct.norm H Lˣ).range xH))) = _
  rw [hEpre, tower_hom_mk, hKinv]
  apply congrArg (QuotientGroup.mk' (FMAct.norm G Lˣ).range)
  apply Subtype.ext
  apply Units.ext
  change algebraMap K L (Algebra.norm K (y : E)) =
    NMCocycl₂.cyclicProduct c (h : G)
  rw [algebra_fixed_prod K L H y]
  let S : H.LeftTransversal :=
    ⟨Set.range (fun q : G ⧸ H ↦ q.out),
      Subgroup.isComplement_range_left Quotient.out_eq'⟩
  have hc := NMCocycl₂.cyclic_transversal_norm
    c H S h
  rw [hc]
  rw [show ((∏ q : G ⧸ H,
      (S.2.leftQuotientEquiv q : G) •
        ∏ t : H, c (t, h) : Lˣ) : L) =
      ∏ q : G ⧸ H,
        (((S.2.leftQuotientEquiv q : G) •
          ∏ t : H, c (t, h) : Lˣ) : L) by
    exact map_prod (Units.coeHom L) _ _]
  apply Finset.prod_congr rfl
  intro q _
  rw [Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq']
  change q.out ((y : E) : L) = q.out
    ((NMCocycl₂.cyclicProduct cH h : Lˣ) : L)
  change q.out (p : L) = q.out
    ((NMCocycl₂.cyclicProduct cH h : Lˣ) : L)
  rfl

set_option maxHeartbeats 5000000 in
-- The cocycle-level norm square requires extended normalization of both product formulas.
set_option synthInstance.maxHeartbeats 500000 in
/-- Forward form of the left-hand square from formula (31), expressed at the
level of the chosen normalized cocycles. -/
theorem forward_square_cohomologous
    (H : Subgroup Gal(L/K))
    (hcoh : MHTwo.IsCohomologous
      (restrictedFundamentalCocycle K L H)
      (fixedFundamentalCocycle K L H)) :
    ForwardNormSquare K L H := by
  apply MonoidHom.ext
  intro gbar
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (commutator H) gbar
  change Abelianization.of h = gbar at hh
  subst gbar
  apply (galoisInvariantsMod K L).symm.injective
  simp only [MonoidHom.comp_apply]
  change (galoisInvariantsMod K L).symm
      (towerNormHom K (F K L H) L
        (fixedResidueEquiv K L H (Abelianization.of h))) =
    (galoisInvariantsMod K L).symm
      (localNormResidue K L
        (abelianizedSubgroupInclusion H (Abelianization.of h)))
  rw [← MulEquiv.symm_apply_apply
    (fixedSubgroupInvariants K L H)
    (fixedResidueEquiv K L H (Abelianization.of h))]
  change fixedInvariantsCorestriction K L H
      (fixedSubgroupInvariants K L H
        (fixedResidueEquiv K L H (Abelianization.of h))) =
    (galoisInvariantsMod K L).symm
      (localNormResidue K L
        (abelianizedSubgroupInclusion H (Abelianization.of h)))
  rw [fixed_cyclic_product K L H h]
  let cH := restrictedFundamentalCocycle K L H
  let dH := fixedFundamentalCocycle K L H
  rw [← NMCocycl₂.cyclic_invariant_cohomologous
    hcoh h]
  rw [fixed_invariants_corestriction K L H h]
  change QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
      (NMCocycl₂.cyclicProductInvariant
        (localFundamentalCocycle K L) (h : Gal(L/K))) =
    (galoisInvariantsMod K L).symm
      (localNormResidue K L (Abelianization.of (h : Gal(L/K))))
  rw [local_cyclic_product K L (h : Gal(L/K)),
    local_cyclic_invariant]

set_option maxHeartbeats 5000000 in
-- Rewriting the norm square with fixed-field base change requires extended normalization.
set_option synthInstance.maxHeartbeats 500000 in
/-- Forward form of the left-hand square, conditional only on local-invariant
base change over the subgroup fixed field. -/
theorem forward_square_change
    (H : Subgroup Gal(L/K))
    (hbase : SpectralChangeFormula K (F K L H)) :
    ForwardNormSquare K L H :=
  forward_square_cohomologous K L H
    (restricted_cocycle_cohomologous K L H hbase)

set_option maxHeartbeats 5000000 in
-- Packaging the norm diagram re-elaborates the transported corestriction calculation.
set_option synthInstance.maxHeartbeats 500000 in
/-- The left-hand diagram of Lemma III.3.2 under local-invariant base change
over the subgroup fixed field. -/
theorem square_base_change
    (H : Subgroup Gal(L/K))
    (hbase : SpectralChangeFormula K (F K L H)) :
    NormSquare K L H :=
  norm_square_forward K L H
    (forward_square_change K L H hbase)

end

end Submission.CField.LRecip
