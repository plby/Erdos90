import Towers.ClassField.LocalBrauer.InvariantBaseChange
import Towers.ClassField.LocalBrauer.TotallyRamifiedChange

/-!
# Local invariant base change through a totally ramified extension

The Frobenius-normalized carry calculation implies the full local Brauer
invariant base-change formula, since the canonical factorial carry classes
generate the Brauer group.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open Towers.NumberTheory.Milne
open BGroups CProduca

variable (K F : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField F] [IsUltrametricDist F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  [Valuation.Compatible (NormedField.valuation (K := F))]
  [NormedAlgebra K F] [FiniteDimensional K F]
  [Algebra 𝒪[K] 𝒪[F]] [Module.Finite 𝒪[K] 𝒪[F]]
  [Module.IsTorsionFree 𝒪[K] 𝒪[F]]
  [IsScalarTower 𝒪[K] K F] [IsScalarTower 𝒪[K] 𝒪[F] F]

set_option maxHeartbeats 6000000 in
-- Reducing the invariant formula to canonical factorial carries requires
-- elaborating the full totally ramified transport tower.
set_option synthInstance.maxHeartbeats 500000 in
/-- Formula (29) for a finite totally ramified extension. -/
theorem formula_totally_ramified
    (htotal : TotallyRamified 𝒪[K] 𝒪[F]
      (IsLocalRing.maximalIdeal 𝒪[K])) :
    BCForm K F := by
  apply BCForm.canon_factorial_carry
  intro r
  let n := invariantLevelDegree r
  letI : NeZero n := ⟨(invariant_level_pos r).ne'⟩
  have hn : 1 < n := by
    simp [n, invariantLevelDegree]
  have hbase := change_totally_ramified
    K F n hn htotal
  change carryBrauerInvariant F
      (brauerBaseChange K F
        (CProduc.brauerClass K
          (canonicalUnramifiedLevel K n)
          (galoisCarryCocycle K
            (levelZMod K n)
            (canonicalLocalUniformizer K)))) = _
  rw [hbase, map_pow]
  rw [show CProduc.brauerClass F
      (canonicalUnramifiedLevel F n)
      (galoisCarryCocycle F
        (levelZMod F n)
        (canonicalLocalUniformizer F)) =
      ((FIData.carry F
        (factorialZMod F) r :
          brauerCofinalLevel F
            (unramifiedFactorialLevel F) r) : BrauerGroup F) by
    rfl]
  rw [carry_brauer_invariant]
  rw [carry_brauer_invariant]

end

end Towers.CField.LBrauer
