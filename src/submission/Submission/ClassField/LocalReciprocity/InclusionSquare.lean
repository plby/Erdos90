import Submission.ClassField.LocalReciprocity.FixedFieldCocycles

/-!
# The inclusion/Verlag square in Lemma III.3.2

The proof is the explicit degree-minus-two restriction calculation.  Its
only arithmetic input is formula (31), supplied here by local-invariant base
change over the subgroup fixed field.
-/

namespace Submission.CField.LRecip

open Submission.CField.LFTheory
open Submission.CField.Shifting
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance inclusionValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance inclusionValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private abbrev F (H : Subgroup Gal(L/K)) :=
  IntermediateField.fixedField H

local instance inclusionSubgroupFintype
    (H : Subgroup Gal(L/K)) : Fintype H :=
  Fintype.ofFinite H

set_option maxHeartbeats 5000000 in
-- The cocycle-level inclusion square expands several transported cohomology maps.
set_option synthInstance.maxHeartbeats 500000 in
/-- Forward form of the right-hand square from formula (31), expressed at
the level of the chosen normalized cocycles. -/
theorem forward_inclusion_cohomologous
    (H : Subgroup Gal(L/K))
    (hcoh : MHTwo.IsCohomologous
      (restrictedFundamentalCocycle K L H)
      (fixedFundamentalCocycle K L H)) :
    ForwardInclusionSquare K L H := by
  intro gbar a hga
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    (commutator Gal(L/K)) gbar
  change Abelianization.of g = gbar at hg
  subst gbar
  apply (fixedSubgroupInvariants K L H).injective
  rw [fixed_unit_inclusion K L H a]
  rw [← hga]
  let c := localFundamentalCocycle K L
  let cH := restrictedFundamentalCocycle K L H
  let dH := fixedFundamentalCocycle K L H
  have hver : subgroupVerlagerung H (Abelianization.of g) =
      ∏ q : Quotient (QuotientGroup.rightRel H),
        Abelianization.of (Rep.rightCosetCorrection H (q.out * g)) := by
    exact transfer_prod_coset H g
  rw [hver, map_prod]
  rw [map_prod]
  simp_rw [fixed_cyclic_product K L H]
  calc
    ∏ q : Quotient (QuotientGroup.rightRel H),
        QuotientGroup.mk' (FMAct.norm H Lˣ).range
          (NMCocycl₂.cyclicProductInvariant dH
            (Rep.rightCosetCorrection H (q.out * g))) =
        ∏ q : Quotient (QuotientGroup.rightRel H),
          QuotientGroup.mk' (FMAct.norm H Lˣ).range
            (NMCocycl₂.cyclicProductInvariant cH
              (Rep.rightCosetCorrection H (q.out * g))) := by
      apply Finset.prod_congr rfl
      intro q _
      exact (NMCocycl₂.cyclic_invariant_cohomologous hcoh
          (Rep.rightCosetCorrection H (q.out * g))).symm
    _ = QuotientGroup.mk' (FMAct.norm H Lˣ).range
        (NMCocycl₂.transferCyclicInvariant c H g) := by
      rw [NMCocycl₂.transferCyclicInvariant]
      exact (map_prod (QuotientGroup.mk' (FMAct.norm H Lˣ).range)
        (fun q : Quotient (QuotientGroup.rightRel H) ↦
          NMCocycl₂.cyclicProductInvariant cH
            (Rep.rightCosetCorrection H (q.out * g))) Finset.univ).symm
    _ = NMCocycl₂.invariantsModRestriction H
        (QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
          (NMCocycl₂.cyclicProductInvariant c g)) := by
      exact (NMCocycl₂.invariants_restriction_cyclic
        c H g).symm
    _ = ambientSubgroupInvariants K L H
        (localNormResidue K L (Abelianization.of g)) := by
      rw [ambientSubgroupInvariants,
        MonoidHom.comp_apply]
      change NMCocycl₂.invariantsModRestriction H
          (QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
            (NMCocycl₂.cyclicProductInvariant c g)) =
        NMCocycl₂.invariantsModRestriction H
          ((galoisInvariantsMod K L).symm
            (localNormResidue K L (Abelianization.of g)))
      rw [local_cyclic_product K L g,
        local_cyclic_invariant]

set_option maxHeartbeats 5000000 in
-- Rewriting the inclusion square with the fixed-field base-change witness is normalization-heavy.
set_option synthInstance.maxHeartbeats 500000 in
/-- Forward form of the right-hand square, conditional only on the spectral
local-invariant base-change formula over the fixed field. -/
theorem forward_inclusion_change
    (H : Subgroup Gal(L/K))
    (hbase : SpectralChangeFormula K (F K L H)) :
    ForwardInclusionSquare K L H :=
  forward_inclusion_cohomologous K L H
    (restricted_cocycle_cohomologous K L H hbase)

set_option maxHeartbeats 5000000 in
-- Packaging the inclusion diagram requires re-elaborating both transported cocycle routes.
set_option synthInstance.maxHeartbeats 500000 in
/-- The right-hand diagram of Lemma III.3.2 under local-invariant base
change over the subgroup fixed field. -/
theorem inclusion_square_change
    (H : Subgroup Gal(L/K))
    (hbase : SpectralChangeFormula K (F K L H)) :
    InclusionSquare K L H :=
  inclusion_square_forward K L H
    (forward_inclusion_change K L H hbase)

end

end Submission.CField.LRecip
