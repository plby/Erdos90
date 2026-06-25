import Towers.ClassField.LocalBrauer.CanonicalRelativeFrobenius
import Towers.ClassField.LocalBrauer.GaloisAlgEquiv
import Towers.ClassField.LocalBrauer.GaloisCarryRestriction
import Towers.ClassField.LocalBrauer.InvariantBaseChange
import Towers.ClassField.LocalBrauer.InvariantChangeCarry
import Towers.ClassField.LocalBrauer.InvariantChangeGeometric

/-!
# Local invariant base change through a canonical unramified extension

Restriction is computed after inflating a carry class to the common level
`U_{n f}`.  Frobenius-compatible subgroup coordinates identify its
restriction to `U_f` with the carry class over `U_f`; normalized order is
unchanged in the unramified extension.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option maxHeartbeats 3000000 in
-- The two invariant-level interfaces retain the canonical-extension telescope.
set_option synthInstance.maxHeartbeats 600000 in
/-- Formula (29) for the canonical unramified extension of every positive
degree. -/
theorem change_formula_level
    (f : ℕ) [NeZero f] :
    let F := canonicalUnramifiedLevel K f
    letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
    letI : NontriviallyNormedField F :=
      FLExt.nontriviallyNormedField K F
    letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
    letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel F := FLExt.valuativeRel K F
    letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
    letI : IsNonarchimedeanLocalField F :=
      FLExt.nonarchimedeanLocalField K F
    BCForm K F := by
  let F := canonicalUnramifiedLevel K f
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := FLExt.valuativeRel K F
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField K F
  apply BCForm.canon_factorial_carry
  intro r
  exact
    (factorial_carry_mapped
      K f r).trans
      (mapped_carry_invariant K f r)

end

end Towers.CField.LBrauer
