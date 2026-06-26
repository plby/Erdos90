import Towers.ClassField.LocalBrauer.InvariantBaseComparison

/-!
# The absolute Brauer-class form of canonical unramified carry comparison
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

variable (F : Type u)
  [NontriviallyNormedField F] [IsUltrametricDist F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  [Valuation.Compatible (NormedField.valuation (K := F))]

set_option maxHeartbeats 3000000 in
-- This wrapper discharges the local-field structure on the canonical level once.
set_option synthInstance.maxHeartbeats 600000 in
/-- The Frobenius-normalized carry and the factorial carry have the same
absolute Brauer class. -/
theorem carry_brauer_factorial
    (r : ℕ) (u : Fˣ)
    (horder : localUnitOrder F (Additive.ofMul u) = 1) :
    let n := invariantLevelDegree r
    letI : NeZero n := ⟨(invariant_level_pos r).ne'⟩
    let C := canonicalUnramifiedLevel F n
    CProduc.brauerClass F C
        (galoisCarryCocycle F
          (levelZMod F n) u) =
      ((FIData.carry F
        (factorialZMod F) r :
          brauerCofinalLevel F
            (unramifiedFactorialLevel F) r) : BrauerGroup F) := by
  let n := invariantLevelDegree r
  letI : NeZero n := ⟨(invariant_level_pos r).ne'⟩
  let C := canonicalUnramifiedLevel F n
  letI : Algebra.IsAlgebraic F C := Algebra.IsAlgebraic.of_finite F C
  letI : NontriviallyNormedField C :=
    FLExt.nontriviallyNormedField F C
  letI : NormedAlgebra F C := spectralNorm.normedAlgebra F C
  letI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra F
  letI : ValuativeRel C := FLExt.valuativeRel F C
  letI : Valuation.Compatible (NormedField.valuation (K := C)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := C))
  letI : IsNonarchimedeanLocalField C :=
    FLExt.nonarchimedeanLocalField F C
  exact congrArg Subtype.val
    (canonical_carry_factorial F r u horder)

end

end Towers.CField.LBrauer
