import Towers.ClassField.LocalBrauer.InvariantBaseGeometric

/-!
# The invariant consequence of geometric unramified carry transport
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
-- The result retains the full canonical-extension instance telescope.
set_option synthInstance.maxHeartbeats 600000 in
/-- Applying the canonical local invariant to geometric carry transport. -/
theorem factorial_carry_mapped
    (f r : ℕ) [NeZero f] :
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
    let n := invariantLevelDegree r
    letI : NeZero n := ⟨(invariant_level_pos r).ne'⟩
    let C := canonicalUnramifiedLevel F n
    carryBrauerInvariant F
        (brauerBaseChange K F
          ((FIData.carry K
            (factorialZMod K) r :
              brauerCofinalLevel K
                (unramifiedFactorialLevel K) r) : BrauerGroup K)) =
      carryBrauerInvariant F
        ((CProduc.brauerClass F C
          (galoisCarryCocycle F
            (levelZMod F n)
            (Units.map (algebraMap K F) (canonicalLocalUniformizer K)))) ^ f) := by
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
  let n := invariantLevelDegree r
  letI : NeZero n := ⟨(invariant_level_pos r).ne'⟩
  let C := canonicalUnramifiedLevel F n
  exact congrArg (carryBrauerInvariant F)
    (change_factorial_carry K f r)

end

end Towers.CField.LBrauer
