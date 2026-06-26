import Towers.ClassField.LocalBrauer.CanonicalResidueCard

/-!
# A canonical unramified level viewed over a lower canonical level
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option maxHeartbeats 4000000 in
-- Unfolding both levels of the dependent canonical tower is elaboration-heavy.
set_option synthInstance.maxHeartbeats 300000 in
-- The relative tower requires synthesizing several transported field structures.
/-- The degree-`m*n` canonical unramified extension of `K`, viewed over its
degree-`n` canonical subfield, is the degree-`m` canonical unramified
extension of that subfield. -/
theorem nonempty_level_relative
    (m n : ℕ) [NeZero m] [NeZero n] :
    let F := canonicalUnramifiedLevel K n
    let E := canonicalUnramifiedLevel K (m * n)
    let hFE : F ≤ E := unramified_level K
      (NeZero.pos n) (Nat.mul_pos (NeZero.pos m) (NeZero.pos n))
      (dvd_mul_left n m)
    letI : Algebra F E := RingHom.toAlgebra (IntermediateField.inclusion hFE)
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
    Nonempty (E ≃ₐ[F] canonicalUnramifiedLevel F m) := by
  let F := canonicalUnramifiedLevel K n
  let E := canonicalUnramifiedLevel K (m * n)
  have hmnPos : 0 < m * n := Nat.mul_pos (NeZero.pos m) (NeZero.pos n)
  letI : NeZero (m * n) := ⟨hmnPos.ne'⟩
  let hFE : F ≤ E := unramified_level K
    (NeZero.pos n) hmnPos (dvd_mul_left n m)
  letI : Algebra F E := RingHom.toAlgebra (IntermediateField.inclusion hFE)
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : Module.Finite F E :=
    Module.Finite.of_restrictScalars_finite K F E
  letI : IsGalois F E := IsGalois.tower_top_of_isGalois K F E
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
  apply alg_level_splits F E m
  · have htower : m * n = n * Module.finrank F E := by
      calc
        m * n = Module.finrank K E :=
          (unramified_level_finrank K (m * n)).symm
        _ = Module.finrank K F * Module.finrank F E :=
          (Module.finrank_mul_finrank K F E).symm
        _ = n * Module.finrank F E := by
          rw [unramified_level_finrank K n]
    have htower' : n * m = n * Module.finrank F E := by
      simpa [Nat.mul_comm] using htower
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos n) htower'.symm
  · have hs := unramified_level_splits K (m * n)
    have hcard : localResidueCard F = localResidueCard K ^ n :=
      residue_unramified_level K n
    have hpoly :
        (localFrobeniusPolynomial F m).map (algebraMap F E) =
          (localFrobeniusPolynomial K (m * n)).map (algebraMap K E) := by
      have hpow : (localResidueCard K ^ n) ^ m =
          localResidueCard K ^ (m * n) := by
        rw [← pow_mul, Nat.mul_comm]
      simp [localFrobeniusPolynomial, hcard, hpow]
    rw [hpoly]
    exact hs

end

end Towers.CField.LBrauer
