import Submission.ClassField.LocalBrauer.CanonicalUnconditional
import Submission.ClassField.LocalBrauer.CanonicalFrobeniusRestriction
import Submission.ClassField.LocalBrauer.ConcreteInflationComparison
import Submission.ClassField.LocalBrauer.ConcreteInflationMorita

/-!
# The carry-normalized unconditional local invariant

The arithmetic-Frobenius cyclic coordinates on the canonical factorial tower satisfy the
carry-inflation formula unconditionally.  Consequently the original finite
invariants, without target-side strictification, assemble to the local Brauer
invariant and retain Milne's carry normalization at every finite level.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups CProduca

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

local instance canonicalCarryDegreeNeZero (r : ℕ) :
    NeZero (invariantLevelDegree r) :=
  ⟨(invariant_level_pos r).ne'⟩

set_option maxHeartbeats 1000000 in
-- Comparing the two dependent tower levels also needs a larger elaboration budget.
set_option synthInstance.maxHeartbeats 100000 in
-- The proof unfolds the dependent canonical tower at two arbitrary levels.
/-- The Frobenius-normalized cyclic coordinates make Milne's carry classes compatible
with abstract Brauer inflation at every pair of factorial levels. -/
theorem factorialCarryInflation :
    FactorialCarryInflation K
      (factorialZMod K) := by
  intro r s h
  let F := unramifiedFactorialLevel K r
  let E := unramifiedFactorialLevel K s
  let hFE : F ≤ E := factorial_level_monotone K h
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := FLExt.valuativeRel K F
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField K F
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  letI : Algebra 𝓀[K] 𝓀[F] :=
    (factorialInvariantData K).residueAlgebra r
  letI : Algebra 𝓀[K] 𝓀[E] :=
    (factorialInvariantData K).residueAlgebra s
  let n := invariantLevelDegree r
  let m := invariantLevelDegree s
  letI : NeZero n := ⟨(invariant_level_pos r).ne'⟩
  letI : NeZero m := ⟨(invariant_level_pos s).ne'⟩
  letI : Fact (F ≤ E) := ⟨hFE⟩
  let eR := factorialZMod K r
  let eS := factorialZMod K s
  let varpiK := canonicalLocalUniformizer K
  let cR := galoisCarryCocycle K eR varpiK
  have hcompat : ∀ z,
      galoisRestrictionHom K hFE (eS z) =
        eR (CCarry.indexReduction
          (invariant_level_dvd h) z) := by
    intro z
    rw [galois_restriction_factorial K h]
    exact factorial_z_compatible K h z
  have hmkR : MHTwo.mk cR =
      unramifiedCarryH K F eR varpiK := by
    dsimp only [cR]
    rw [carry_cocycle_unramified]
    exact mk_carry_cocycle K F eR varpiK
  have hmkE : MHTwo.mk
      (galoisCarryCocycle K eS varpiK) =
      unramifiedCarryH K E eS varpiK := by
    rw [carry_cocycle_unramified]
    exact mk_carry_cocycle K E eS varpiK
  have hconcrete : MHTwo.mk
        (concreteInflationCocycle K hFE cR) =
      MHTwo.mk
          (galoisCarryCocycle K eS varpiK) ^ (m / n) := by
    dsimp only [cR, m, n]
    exact inflation_carry_cocycle
      K (invariant_level_dvd h) hFE
        eR eS hcompat varpiK
  rw [← hmkR, ← hmkE]
  exact
    (inflation_concrete_cocycle
      (K := K) (F := F) (E := E) cR).trans hconcrete

/-- The original carry-normalized finite invariants form a compatible system,
without modifying their target equivalences. -/
noncomputable def canonicalCarrySystem :
    CanonicalFactorialSystem K :=
  FIData.finiteInvariantSystem K
    (factorialInvariantData K)
    (factorialZMod K)
    (factorialCarryInflation K)

set_option maxHeartbeats 1000000 in
-- Elaborating the cofinal assembly unfolds the dependent canonical tower.
/-- The unconditional carry-normalized local Brauer invariant. -/
noncomputable def carryBrauerInvariant :
    BrauerGroup K ≃* Multiplicative LocalInvariant :=
  assembleFactorialInvariant K
    (canonicalCarrySystem K)
    (factorialBrauerCofinal K)

set_option maxHeartbeats 1000000 in
-- Elaborating the cofinal assembly unfolds the dependent canonical tower.
/-- The carry-normalized invariant restricts to the original finite invariant
at every canonical factorial level. -/
@[simp]
theorem carry_brauer_coe
    (r : ℕ)
    (x : brauerCofinalLevel K (unramifiedFactorialLevel K) r) :
    carryBrauerInvariant K (x : BrauerGroup K) =
      invariantTorsionMul r
        ((canonicalCarrySystem K).equiv r x) :=
  assemble_factorial_coe K
    (canonicalCarrySystem K)
    (factorialBrauerCofinal K) r x

set_option maxHeartbeats 1000000 in
-- The finite invariant unfolds the spectral local-field data at level `r`.
/-- At every finite level, the canonical carry class has invariant `1 / n`. -/
@[simp]
theorem carry_brauer_invariant (r : ℕ) :
    carryBrauerInvariant K
        ((FIData.carry K
          (factorialZMod K) r :
            brauerCofinalLevel K
              (unramifiedFactorialLevel K) r) : BrauerGroup K) =
      invariantTorsionMul r
        (Multiplicative.ofAdd
          (localDivTorsion (invariantLevelDegree r))) := by
  rw [carry_brauer_coe]
  change invariantTorsionMul r
      (FIData.finiteInvariant K
        (factorialInvariantData K)
        (factorialZMod K) r
        (FIData.carry K
          (factorialZMod K) r)) = _
  rw [FIData.finiteInvariant_carry]

end

end Submission.CField.LBrauer
