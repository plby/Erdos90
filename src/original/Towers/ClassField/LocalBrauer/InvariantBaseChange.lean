import Towers.ClassField.BrauerGroups.BaseChangeTower
import Towers.ClassField.LocalBrauer.CanonicalCarryUnconditional
import Towers.ClassField.LocalBrauer.FiniteLocalExtension

/-!
# Base change for the local Brauer invariant

This file packages the formula

    inv_L (Res x) = [L : K] * inv_K x

in multiplicative notation and proves its transitivity in a field tower.  The
remaining arithmetic theorem is to establish the formula for the unramified
and totally ramified pieces of a finite local extension.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups

variable (K L : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
  [IsNonarchimedeanLocalField L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra K L] [FiniteDimensional K L]

/-- The local invariant restriction formula for a finite extension. -/
def BCForm : Prop :=
  ∀ x : BrauerGroup K,
    carryBrauerInvariant L (brauerBaseChange K L x) =
      (carryBrauerInvariant K x) ^ Module.finrank K L

/-- The same formula for an abstract finite extension, equipped internally
with its canonical spectral local-field structure. -/
def SpectralChangeFormula
    (F : Type u) [Field F] [Algebra K F] [FiniteDimensional K F] : Prop :=
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
  BCForm K F

set_option maxHeartbeats 1000000 in
-- Unfolding the dependent factorial tower in the cofinality witness is deep.
omit [FiniteDimensional K L] in
/-- It suffices to verify the base-change formula on the carry generator at
every canonical factorial level. -/
theorem BCForm.canon_factorial_carry
    (hcarry : ∀ r : ℕ,
      carryBrauerInvariant L
          (brauerBaseChange K L
            (((FIData.carry K
                (factorialZMod K) r :
              brauerCofinalLevel K
                (unramifiedFactorialLevel K) r) :
              BrauerGroup K))) =
        (carryBrauerInvariant K
          (((FIData.carry K
              (factorialZMod K) r :
            brauerCofinalLevel K
              (unramifiedFactorialLevel K) r) :
            BrauerGroup K))) ^ Module.finrank K L) :
    BCForm K L := by
  intro x
  obtain ⟨r, hx⟩ := factorialBrauerCofinal K x
  let y : brauerCofinalLevel K
      (unramifiedFactorialLevel K) r := ⟨x, hx⟩
  obtain ⟨i, hi⟩ :=
    FIData.carry_pow K
      (factorialInvariantData K)
      (factorialZMod K) r y
  let c : BrauerGroup K :=
    ((FIData.carry K
        (factorialZMod K) r :
      brauerCofinalLevel K (unramifiedFactorialLevel K) r) :
        BrauerGroup K)
  have hxpow : x = c ^ i := by
    change y.1 = c ^ i
    exact congrArg Subtype.val hi
  rw [hxpow, map_pow, map_pow, hcarry r, map_pow, ← pow_mul, ← pow_mul,
    Nat.mul_comm]

/-- The local invariant restriction formula composes through a tower. -/
theorem BCForm.trans
    (M : Type u)
    [NontriviallyNormedField M] [IsUltrametricDist M] [ValuativeRel M]
    [IsNonarchimedeanLocalField M]
    [Valuation.Compatible (NormedField.valuation (K := M))]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional L M] [FiniteDimensional K M]
    (hKL : BCForm K L)
    (hLM : BCForm L M) :
    BCForm K M := by
  intro x
  rw [← base_change_tower K L M x, hLM, hKL, ← pow_mul,
    Module.finrank_mul_finrank]

end

end Towers.CField.LBrauer
