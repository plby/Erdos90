import Towers.ClassField.LocalBrauer.CanonicalRelativeFrobenius
import Towers.ClassField.LocalBrauer.GaloisAlgEquiv
import Towers.ClassField.LocalBrauer.GaloisCarryRestriction
import Towers.ClassField.LocalBrauer.InvariantBaseChange

/-!
# Geometric carry transport through a canonical unramified extension
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option maxHeartbeats 7000000 in
-- This proof combines inflation, relative restriction, and coefficient transport.
set_option synthInstance.maxHeartbeats 600000 in
/-- Base change of the factorial carry to `U_f` is the `f`-th power of the
Frobenius-normalized carry over `U_f`. -/
theorem change_factorial_carry
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
    brauerBaseChange K F
        ((FIData.carry K
          (factorialZMod K) r :
            brauerCofinalLevel K
              (unramifiedFactorialLevel K) r) : BrauerGroup K) =
      (CProduc.brauerClass F C
        (galoisCarryCocycle F
          (levelZMod F n)
          (Units.map (algebraMap K F) (canonicalLocalUniformizer K)))) ^ f := by
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
  have hnPos : 0 < n := invariant_level_pos r
  letI : NeZero n := ⟨hnPos.ne'⟩
  let U := canonicalUnramifiedLevel K n
  let E := canonicalUnramifiedLevel K (n * f)
  have hnfPos : 0 < n * f := Nat.mul_pos hnPos (NeZero.pos f)
  letI : NeZero (n * f) := ⟨hnfPos.ne'⟩
  let hUE : U ≤ E := unramified_level K hnPos hnfPos
    (dvd_mul_right n f)
  let hFE : F ≤ E := unramified_level K (NeZero.pos f) hnfPos
    (dvd_mul_left f n)
  letI : Algebra F E := RingHom.toAlgebra (IntermediateField.inclusion hFE)
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : FiniteDimensional F E := FiniteDimensional.right K F E
  letI : IsGalois F E := IsGalois.tower_top_of_isGalois K F E
  let eK := levelZMod K (n * f)
  let eF := frobeniusZMod K n f
  let cU := galoisCarryCocycle K
    (levelZMod K n)
    (canonicalLocalUniformizer K)
  let cE := galoisCarryCocycle K eK (canonicalLocalUniformizer K)
  let cF := galoisCarryCocycle F eF
    (Units.map (algebraMap K F) (canonicalLocalUniformizer K))
  have hinflation : inflationHom K hUE (MHTwo.mk cU) =
      (MHTwo.mk cE) ^ f := by
    have h := inflation_frobenius_carry K (dvd_mul_right n f)
      (canonicalLocalUniformizer K)
    simpa [U, E, hUE, cU, cE, Nat.mul_div_cancel_left _ hnPos] using h
  have hsourceTop :
      CProduc.brauerClass K U cU =
        (CProduc.brauerClass K E cE) ^ f := by
    have h := h_2_inflation K hUE (MHTwo.mk cU)
    rw [hinflation, map_pow] at h
    exact h.symm
  have hrestriction :
      relativeBrauerChange K F E
          (CProduc.relativeBrauerClass K E cE) =
        CProduc.relativeBrauerClass F E cF := by
    exact brauer_change_carry K F E eK eF
      (frobenius_z_compatible K n f)
      (canonicalLocalUniformizer K)
  have htopBase :
      brauerBaseChange K F (CProduc.brauerClass K E cE) =
        CProduc.brauerClass F E cF :=
    congrArg Subtype.val hrestriction
  let C := canonicalUnramifiedLevel F n
  let e : E ≃ₐ[F] C := canonicalUnramifiedRelative K n f
  have hecoord : eF.trans e.autCongr =
      levelZMod F n := by
    apply MulEquiv.ext
    intro z
    change e.autCongr (e.autCongr.symm
      (levelZMod F n z)) = _
    exact e.autCongr.apply_symm_apply _
  have htransport : CProduc.brauerClass F E cF =
      CProduc.brauerClass F C
        (galoisCarryCocycle F
          (levelZMod F n)
          (Units.map (algebraMap K F) (canonicalLocalUniformizer K))) := by
    have h := brauer_carry_alg e eF
      (Units.map (algebraMap K F) (canonicalLocalUniformizer K))
    simpa [cF, hecoord] using h
  dsimp only
  rw [show ((FIData.carry K
      (factorialZMod K) r :
        brauerCofinalLevel K
          (unramifiedFactorialLevel K) r) : BrauerGroup K) =
      CProduc.brauerClass K U cU by rfl,
    hsourceTop, map_pow (brauerBaseChange K F), htopBase, htransport]

end

end Towers.CField.LBrauer
