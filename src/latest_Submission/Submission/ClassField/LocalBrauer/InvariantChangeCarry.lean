import Submission.ClassField.LocalBrauer.InvariantBaseCarry

/-!
# The invariant consequence of canonical unramified carry comparison
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option maxHeartbeats 3000000 in
-- The canonical target field is elaborated together with its invariant formula.
set_option synthInstance.maxHeartbeats 600000 in
/-- The mapped carry has the invariant prescribed by formula (29). -/
theorem mapped_carry_invariant
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
        ((CProduc.brauerClass F C
          (galoisCarryCocycle F
            (levelZMod F n)
            (Units.map (algebraMap K F) (canonicalLocalUniformizer K)))) ^ f) =
      (carryBrauerInvariant K
        ((FIData.carry K
          (factorialZMod K) r :
            brauerCofinalLevel K
              (unramifiedFactorialLevel K) r) : BrauerGroup K)) ^
        Module.finrank K F := by
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
  let u : Fˣ := Units.map (algebraMap K F) (canonicalLocalUniformizer K)
  have horder : localUnitOrder F
      (Additive.ofMul u) = 1 := by
    obtain ⟨_hResidue, _hUnit, horderMap, _hOther⟩ :=
      unramified_level_data K f
    calc
      localUnitOrder F (Additive.ofMul u) =
          localUnitOrder K
            (Additive.ofMul (canonicalLocalUniformizer K)) := by
        simpa [u] using horderMap (canonicalLocalUniformizer K)
      _ = 1 := canonical_uniformizer_order K
  have hcarryEq := carry_brauer_factorial F r
    u horder
  calc
    carryBrauerInvariant F
        ((CProduc.brauerClass F C
          (galoisCarryCocycle F
            (levelZMod F n)
            u)) ^ f) =
        carryBrauerInvariant F
          (((FIData.carry F
            (factorialZMod F) r :
              brauerCofinalLevel F
                (unramifiedFactorialLevel F) r) : BrauerGroup F) ^ f) := by
      rw [hcarryEq]
    _ = (carryBrauerInvariant K
          ((FIData.carry K
            (factorialZMod K) r :
              brauerCofinalLevel K
                (unramifiedFactorialLevel K) r) : BrauerGroup K)) ^
          Module.finrank K F := by
      rw [map_pow, carry_brauer_invariant,
        carry_brauer_invariant,
        unramified_level_finrank K f]

end

end Submission.CField.LBrauer
