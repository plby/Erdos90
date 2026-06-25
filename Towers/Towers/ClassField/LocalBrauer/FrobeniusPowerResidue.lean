import Towers.ClassField.NormCorrespondence.CanonicalNormalization
import Towers.ClassField.LocalBrauer.CanonicalFrobeniusRestriction
import Towers.ClassField.LocalBrauer.CanonicalTowerRelative

/-!
# Powers of arithmetic Frobenius on the canonical unramified tower

The residue calculation used by relative Frobenius transport is kept in a
separate module so that its large integral-model proof is elaborated and
cached independently of the target-field comparison.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel IsLocalRing
open Towers.CField.LFTheory
open scoped Valued

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev E (m n : ℕ) := canonicalUnramifiedLevel K (m * n)

local instance powerResidueProductNeZero (m n : ℕ) [NeZero m] [NeZero n] :
    NeZero (m * n) :=
  ⟨(Nat.mul_pos (NeZero.pos m) (NeZero.pos n)).ne'⟩

local instance powerResidueUpperAlgebraic (m n : ℕ) [NeZero m] [NeZero n] :
    Algebra.IsAlgebraic K (E K m n) :=
  Algebra.IsAlgebraic.of_finite K (E K m n)

local instance powerResidueUpperNontriviallyNormed
    (m n : ℕ) [NeZero m] [NeZero n] :
    NontriviallyNormedField (E K m n) :=
  FLExt.nontriviallyNormedField K (E K m n)

local instance powerResidueUpperNormedAlgebra
    (m n : ℕ) [NeZero m] [NeZero n] :
    NormedAlgebra K (E K m n) := spectralNorm.normedAlgebra K (E K m n)

local instance powerResidueUpperUltrametric (m n : ℕ) [NeZero m] [NeZero n] :
    IsUltrametricDist (E K m n) := IsUltrametricDist.of_normedAlgebra K

local instance powerResidueUpperValuative (m n : ℕ) [NeZero m] [NeZero n] :
    ValuativeRel (E K m n) :=
  FLExt.valuativeRel K (E K m n)

local instance powerResidueUpperCompatible (m n : ℕ) [NeZero m] [NeZero n] :
    Valuation.Compatible (NormedField.valuation (K := E K m n)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := E K m n))

local instance powerResidueUpperLocalField (m n : ℕ) [NeZero m] [NeZero n] :
    IsNonarchimedeanLocalField (E K m n) :=
  FLExt.nonarchimedeanLocalField K (E K m n)

set_option maxHeartbeats 3000000 in
-- Reduction of a Frobenius power reinstalls the full spectral integer model.
set_option synthInstance.maxHeartbeats 500000 in
/-- The `n`-th power of arithmetic Frobenius reduces to the
`q_K ^ n`-power map. -/
theorem arithmetic_frobenius_residue
    (m n : ℕ) [NeZero m] [NeZero n]
    (x : E K m n) (hx : ‖x‖ ≤ 1) :
    ‖(canonicalArithmeticFrobenius K (m * n) ^ n) x -
        x ^ (localResidueCardinality K ^ n)‖ < 1 := by
  let EE := E K m n
  let sigmaK : Gal(EE/K) := (canonicalArithmeticFrobenius K (m * n)) ^ n
  let A := Valuation.integer (ValuativeRel.valuation K)
  let N := Valuation.integer (NormedField.valuation (K := EE))
  letI : Algebra A N := valuativeSpectralAlgebra K EE
  obtain ⟨hfinite, hunramified, htower, hclosure⟩ :=
    level_spectral_data K (m * n)
  letI : Module.Finite A N := hfinite
  letI : Algebra.FormallyUnramified A N := hunramified
  letI : IsScalarTower A N EE := htower
  letI : IsIntegralClosure N A EE := hclosure
  letI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  letI : Module.IsTorsionFree A N := IsIntegralClosure.isTorsionFree A EE
  letI : IsLocalHom (algebraMap A N) := Algebra.IsIntegral.isLocalHom A N
  letI : Finite (ResidueField A) := local_field_residue K
  letI : Fintype (ResidueField A) := Fintype.ofFinite _
  letI : Module.Finite (ResidueField A) (ResidueField N) := inferInstance
  letI : Finite (ResidueField N) := Module.finite_of_finite (ResidueField A)
  letI : Fintype (ResidueField N) := Fintype.ofFinite _
  let y : N := ⟨x, by
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast hx⟩
  have hcardA : Fintype.card (ResidueField A) =
      localResidueCardinality K := by
    simpa [localResidueCardinality, Nat.card_eq_fintype_card,
      Valued.ResidueField] using
      Nat.card_congr
        (ResidueField.mapEquiv
          (valuativeIntegerNorm K)).toEquiv
  have hres :
      canonicalUnramifiedResidue K (m * n) sigmaK
          (residue N y) =
        (residue N y) ^ (localResidueCardinality K ^ n) := by
    dsimp only [sigmaK]
    rw [map_pow, canonical_unramified_frobenius]
    change ((FiniteField.frobeniusAlgEquivOfAlgebraic
      (ResidueField A) (ResidueField N)) ^ n) (residue N y) = _
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hcardA]
  rw [canonical_unramified_residue] at hres
  have hsigmaNorm : ‖sigmaK x‖ ≤ 1 := by
    rw [NormedAlgebra.norm_eq_spectralNorm K,
      ← spectralNorm_eq_of_equiv sigmaK x,
      ← NormedAlgebra.norm_eq_spectralNorm K]
    exact hx
  let sy : N := ⟨sigmaK x, by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
      exact_mod_cast hsigmaNorm⟩
  let dN : N := sy - y ^ (localResidueCardinality K ^ n)
  have hres' : residue N sy =
      (residue N y) ^ (localResidueCardinality K ^ n) := by
    convert hres using 1
  have hzero : residue N dN = 0 := by
    rw [map_sub, map_pow, hres', sub_self]
  have hmem : dN ∈ maximalIdeal N := (residue_eq_zero_iff dN).mp hzero
  have hval := (NormedField.valuation (K := EE)).mem_maximalIdeal_iff.mp hmem
  rw [NormedField.valuation_apply] at hval
  have hnorm : ‖(dN : EE)‖ < 1 := by exact_mod_cast hval
  simpa [dN, sy, y, sigmaK] using hnorm

end

end Towers.CField.LBrauer
