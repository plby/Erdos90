import Towers.ClassField.LocalReciprocity.InclusionSquare
import Towers.ClassField.LocalReciprocity.NormSquare

/-!
# Milne, Class Field Theory, Lemma III.3.2

Both Artin tower diagrams follow from formula (31), expressed by spectral
local-invariant base change over the subgroup fixed field.  The two proofs
are unconditional after that single arithmetic compatibility: the norm
square is the left-coset cocycle identity and the inclusion square is the
right-coset/Verlag identity.
-/

namespace Towers.CField.LRecip

open Towers.CField.LClass
open Towers.CField.CProduca
open Towers.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance valuativeRel' : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance valuationCompatible' :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

private abbrev F (H : Subgroup Gal(L/K)) :=
  IntermediateField.fixedField H

/-- The conjunction of the two diagrams in Lemma III.3.2. -/
def LocalTowerCompatibility : Prop :=
  ∀ H : Subgroup Gal(L/K),
    NormSquare K L H ∧ InclusionSquare K L H

/-- Formula (31), in the precise representative-level form used by Lemma
III.3.2: restriction of the ambient fundamental cocycle to every subgroup is
cohomologous to the intrinsic fundamental cocycle over its fixed field. -/
def FundamentalClassRestriction : Prop :=
  ∀ H : Subgroup Gal(L/K),
    MHTwo.IsCohomologous
      (restrictedFundamentalCocycle K L H)
      (fixedFundamentalCocycle K L H)

set_option maxHeartbeats 5000000 in
-- Combining the norm and inclusion cocycle squares needs an extended normalization budget.
set_option synthInstance.maxHeartbeats 500000 in
/-- **Lemma III.3.2.** Formula (31) implies both local Artin tower diagrams:
the norm corresponds to subgroup inclusion on abelianizations, and field
inclusion corresponds to Verlag. -/
theorem fundamental_class_restriction
    (h31 : FundamentalClassRestriction K L) :
    LocalTowerCompatibility K L := by
  intro H
  exact ⟨norm_square_forward K L H
      (forward_square_cohomologous K L H (h31 H)),
    inclusion_square_forward K L H
      (forward_inclusion_cohomologous K L H (h31 H))⟩

set_option maxHeartbeats 5000000 in
-- Specializing the fixed-field base-change formula across all subgroups is normalization-heavy.
set_option synthInstance.maxHeartbeats 500000 in
/-- **Lemma III.3.2**, reduced to formula (31) for each fixed field. -/
theorem fixed_field_change
    (hbase : ∀ H : Subgroup Gal(L/K),
      SpectralChangeFormula K (F K L H)) :
    LocalTowerCompatibility K L := by
  apply fundamental_class_restriction K L
  intro H
  exact restricted_cocycle_cohomologous
    K L H (hbase H)

set_option maxHeartbeats 6000000 in
-- The final tower-compatibility package unfolds both large commuting-square proofs.
set_option synthInstance.maxHeartbeats 500000 in
/-- **Lemma III.3.2.** The norm and inclusion squares for finite local Artin
maps commute. -/
theorem artinTowerCompatibility : LocalTowerCompatibility K L := by
  apply fixed_field_change K L
  intro H
  let E := F K L H
  letI : Algebra.IsSeparable K E :=
    Algebra.isSeparable_tower_bot_of_isSeparable K E L
  exact spectral_change_separable K E

end

end Towers.CField.LRecip
