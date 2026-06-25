import Towers.ClassField.LocalBrauer.InvariantBaseChange

/-!
# Carry comparison used by unramified local-invariant base change
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

variable (F : Type u)
  [NontriviallyNormedField F] [IsUltrametricDist F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  [Valuation.Compatible (NormedField.valuation (K := F))]

set_option maxHeartbeats 6000000 in
-- The finite invariant installs the full residue and local norm data at a factorial level.
set_option synthInstance.maxHeartbeats 600000 in
/-- A Frobenius-normalized carry with unit order one is the canonical
factorial carry at the same level. -/
theorem canonical_carry_factorial
    (r : ℕ) (u : Fˣ)
    (horder : localUnitOrder F (Additive.ofMul u) = 1) :
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
    CProduc.relativeBrauerClass F C
        (galoisCarryCocycle F
          (levelZMod F n) u) =
      FIData.carry F
        (factorialZMod F) r := by
  let n := invariantLevelDegree r
  letI : NeZero n := ⟨(invariant_level_pos r).ne'⟩
  have hn : 1 < n := by simp [n, invariantLevelDegree]
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
  let mappedCarry : relativeBrauerGroup F C :=
    CProduc.relativeBrauerClass F C
      (galoisCarryCocycle F
        (levelZMod F n) u)
  let canonicalCarry : relativeBrauerGroup F C :=
    FIData.carry F
      (factorialZMod F) r
  let d := factorialInvariantData F
  letI : Algebra
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation F)))
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation C))) :=
    FIData.residueAlgebra d r
  let inv := FIData.finiteInvariant F d
    (factorialZMod F) r
  apply inv.injective
  have hmapped := unramified_mul_carry F C
    (levelZMod F n) hn
    (FLExt.integerUnitNorm F C)
    (FIData.localNormData F d r)
    (FIData.order_norm F d r) u
  have hcanonical := FIData.finiteInvariant_carry
    F d (factorialZMod F) r
  calc
    inv mappedCarry =
        Multiplicative.ofAdd
          (torsionZMod n
            (localUnitOrder F (Additive.ofMul u) : ZMod n)) := hmapped
    _ = Multiplicative.ofAdd (localDivTorsion n) := by
      rw [horder]
      simp [localDivTorsion]
    _ = inv canonicalCarry := by
      simpa [n] using hcanonical.symm

end

end Towers.CField.LBrauer
