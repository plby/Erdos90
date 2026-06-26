import Submission.ClassField.LocalBrauer.CanonicalFrobeniusRestriction
import Submission.ClassField.LocalBrauer.CanonicalTowerRelative

/-!
# Relative arithmetic Frobenius in the canonical unramified tower

This file contains the field tower and the relative Frobenius element.  Its
residue-compatibility proof is kept in a separate module so both expensive
pieces elaborate independently.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

abbrev canonicalRelativeLevel (n : ℕ) := canonicalUnramifiedLevel K n
abbrev canonicalUpperLevel (m n : ℕ) :=
  canonicalUnramifiedLevel K (m * n)

instance canonicalRelativeNe
    (m n : ℕ) [NeZero m] [NeZero n] : NeZero (m * n) :=
  ⟨(Nat.mul_pos (NeZero.pos m) (NeZero.pos n)).ne'⟩

noncomputable def relativeLevel
    (m n : ℕ) [NeZero m] [NeZero n] :
    canonicalRelativeLevel K n ≤ canonicalUpperLevel K m n :=
  unramified_level K (NeZero.pos n)
    (Nat.mul_pos (NeZero.pos m) (NeZero.pos n)) (dvd_mul_left n m)

instance relativeLevelAlgebra
    (m n : ℕ) [NeZero m] [NeZero n] :
    Algebra (canonicalRelativeLevel K n)
      (canonicalUpperLevel K m n) :=
  RingHom.toAlgebra
    (IntermediateField.inclusion (relativeLevel K m n))

set_option maxHeartbeats 1000000 in
-- Comparing the two intermediate-field inclusions unfolds both canonical levels.
set_option synthInstance.maxHeartbeats 500000 in
instance relativeLevelTower
    (m n : ℕ) [NeZero m] [NeZero n] :
    IsScalarTower K (canonicalRelativeLevel K n)
      (canonicalUpperLevel K m n) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

instance canonicalRelativeAlgebraic (n : ℕ) [NeZero n] :
    Algebra.IsAlgebraic K (canonicalRelativeLevel K n) :=
  Algebra.IsAlgebraic.of_finite K _

instance relativeNontriviallyNormed (n : ℕ) [NeZero n] :
    NontriviallyNormedField (canonicalRelativeLevel K n) :=
  FLExt.nontriviallyNormedField K _

instance relativeNormedAlgebra (n : ℕ) [NeZero n] :
    NormedAlgebra K (canonicalRelativeLevel K n) :=
  spectralNorm.normedAlgebra K _

instance canonicalRelativeUltrametric (n : ℕ) [NeZero n] :
    IsUltrametricDist (canonicalRelativeLevel K n) :=
  IsUltrametricDist.of_normedAlgebra K

instance canonicalRelativeValuative (n : ℕ) [NeZero n] :
    ValuativeRel (canonicalRelativeLevel K n) :=
  FLExt.valuativeRel K _

instance canonicalRelativeCompatible (n : ℕ) [NeZero n] :
    Valuation.Compatible
      (NormedField.valuation (K := canonicalRelativeLevel K n)) :=
  Valuation.Compatible.ofValuation NormedField.valuation

instance canonicalRelativeField (n : ℕ) [NeZero n] :
    IsNonarchimedeanLocalField (canonicalRelativeLevel K n) :=
  FLExt.nonarchimedeanLocalField K _

abbrev relativeTargetLevel (m n : ℕ) [NeZero m] [NeZero n] :=
  canonicalUnramifiedLevel (canonicalRelativeLevel K n) m

instance upperAlgebraicBase
    (m n : ℕ) [NeZero m] [NeZero n] :
    Algebra.IsAlgebraic K (canonicalUpperLevel K m n) :=
  Algebra.IsAlgebraic.of_finite K _

instance upperNontriviallyNormed
    (m n : ℕ) [NeZero m] [NeZero n] :
    NontriviallyNormedField (canonicalUpperLevel K m n) :=
  FLExt.nontriviallyNormedField K _

instance upperNormedBase
    (m n : ℕ) [NeZero m] [NeZero n] :
    NormedAlgebra K (canonicalUpperLevel K m n) :=
  spectralNorm.normedAlgebra K _

instance relativeUpperUltrametric
    (m n : ℕ) [NeZero m] [NeZero n] :
    IsUltrametricDist (canonicalUpperLevel K m n) :=
  IsUltrametricDist.of_normedAlgebra K

instance relativeUpperValuative
    (m n : ℕ) [NeZero m] [NeZero n] :
    ValuativeRel (canonicalUpperLevel K m n) :=
  FLExt.valuativeRel K _

instance relativeUpperCompatible
    (m n : ℕ) [NeZero m] [NeZero n] :
    Valuation.Compatible
      (NormedField.valuation (K := canonicalUpperLevel K m n)) :=
  Valuation.Compatible.ofValuation NormedField.valuation

instance canonicalRelativeUpper
    (m n : ℕ) [NeZero m] [NeZero n] :
    IsNonarchimedeanLocalField (canonicalUpperLevel K m n) :=
  FLExt.nonarchimedeanLocalField K _

set_option maxHeartbeats 2000000 in
-- Restriction of scalars through nested canonical levels is expensive.
set_option synthInstance.maxHeartbeats 500000 in
instance relativeUpperFinite
    (m n : ℕ) [NeZero m] [NeZero n] :
    Module.Finite (canonicalRelativeLevel K n)
      (canonicalUpperLevel K m n) :=
  Module.Finite.of_restrictScalars_finite K _ _

set_option maxHeartbeats 2000000 in
-- Galois tower inference unfolds both canonical intermediate fields.
set_option synthInstance.maxHeartbeats 500000 in
instance relativeUpperGalois
    (m n : ℕ) [NeZero m] [NeZero n] :
    IsGalois (canonicalRelativeLevel K n)
      (canonicalUpperLevel K m n) :=
  IsGalois.tower_top_of_isGalois K _ _

set_option maxHeartbeats 1000000 in
-- Recovering algebraicity from the restricted finite module unfolds the tower.
set_option synthInstance.maxHeartbeats 500000 in
instance relativeUpperAlgebraic
    (m n : ℕ) [NeZero m] [NeZero n] :
    Algebra.IsAlgebraic (canonicalRelativeLevel K n)
      (canonicalUpperLevel K m n) :=
  Algebra.IsAlgebraic.of_finite _ _

set_option maxHeartbeats 1000000 in
-- The spectral norm over the intermediate canonical level unfolds a tower.
set_option synthInstance.maxHeartbeats 500000 in
instance upperNormedAlgebra
    (m n : ℕ) [NeZero m] [NeZero n] :
    NormedAlgebra (canonicalRelativeLevel K n)
      (canonicalUpperLevel K m n) :=
  spectralNorm.normedAlgebra' K _ _

set_option maxHeartbeats 1000000 in
-- The target is itself a canonical extension over the relative lower level.
set_option synthInstance.maxHeartbeats 500000 in
instance relativeTargetAlgebraic
    (m n : ℕ) [NeZero m] [NeZero n] :
    Algebra.IsAlgebraic (canonicalRelativeLevel K n)
      (relativeTargetLevel K m n) :=
  Algebra.IsAlgebraic.of_finite _ _

set_option maxHeartbeats 1000000 in
-- Installing the canonical target norm unfolds the nested lower level.
set_option synthInstance.maxHeartbeats 500000 in
instance targetNontriviallyNormed
    (m n : ℕ) [NeZero m] [NeZero n] :
    NontriviallyNormedField (relativeTargetLevel K m n) :=
  FLExt.nontriviallyNormedField
    (canonicalRelativeLevel K n) _

set_option maxHeartbeats 1000000 in
-- Constructing the target spectral norm unfolds both canonical levels.
set_option synthInstance.maxHeartbeats 500000 in
instance targetNormedAlgebra
    (m n : ℕ) [NeZero m] [NeZero n] :
    NormedAlgebra (canonicalRelativeLevel K n)
      (relativeTargetLevel K m n) :=
  spectralNorm.normedAlgebra _ _

set_option maxHeartbeats 1000000 in
-- The target metric is inferred through its nested spectral norm.
set_option synthInstance.maxHeartbeats 500000 in
instance relativeTargetUltrametric
    (m n : ℕ) [NeZero m] [NeZero n] :
    IsUltrametricDist (relativeTargetLevel K m n) :=
  IsUltrametricDist.of_normedAlgebra (canonicalRelativeLevel K n)

set_option maxHeartbeats 1000000 in
-- The target valuation relation is induced from the nested local extension.
set_option synthInstance.maxHeartbeats 500000 in
instance relativeTargetValuative
    (m n : ℕ) [NeZero m] [NeZero n] :
    ValuativeRel (relativeTargetLevel K m n) :=
  FLExt.valuativeRel
    (canonicalRelativeLevel K n) _

set_option maxHeartbeats 1000000 in
-- Compatibility depends on the just-installed target valuation relation.
set_option synthInstance.maxHeartbeats 500000 in
instance relativeTargetCompatible
    (m n : ℕ) [NeZero m] [NeZero n] :
    Valuation.Compatible
      (NormedField.valuation (K := relativeTargetLevel K m n)) :=
  Valuation.Compatible.ofValuation NormedField.valuation

set_option maxHeartbeats 1000000 in
-- The canonical target local-field instance unfolds both tower levels.
set_option synthInstance.maxHeartbeats 500000 in
instance canonicalRelativeTarget
    (m n : ℕ) [NeZero m] [NeZero n] :
    IsNonarchimedeanLocalField (relativeTargetLevel K m n) :=
  FLExt.nonarchimedeanLocalField
    (canonicalRelativeLevel K n) _

set_option maxHeartbeats 2000000 in
-- Constructing the relative automorphism restricts a power through the tower.
set_option synthInstance.maxHeartbeats 500000 in
/-- The `n`-th power of arithmetic Frobenius on `U_{m*n}/K`, regarded as
an automorphism over the degree-`n` subfield. -/
noncomputable def relativeArithmeticFrobenius
    (m n : ℕ) [NeZero m] [NeZero n] :
    Gal(canonicalUpperLevel K m n /
      canonicalRelativeLevel K n) := by
  let sigmaK : Gal(canonicalUpperLevel K m n/K) :=
    (canonicalArithmeticFrobenius K (m * n)) ^ n
  have hres : galoisRestrictionHom K
      (relativeLevel K m n) sigmaK = 1 := by
    dsimp only [sigmaK]
    rw [map_pow, arithmetic_frobenius_restrict K (dvd_mul_left n m)]
    simpa using pow_orderOf_eq_one (canonicalArithmeticFrobenius K n)
  exact
    { sigmaK with
      commutes' := by
        intro x
        have hx := AlgEquiv.restrictNormal_commutes sigmaK
          (canonicalRelativeLevel K n) x
        have hres' : sigmaK.restrictNormal
            (canonicalRelativeLevel K n) = 1 := hres
        rw [hres'] at hx
        simpa using hx.symm }

set_option maxHeartbeats 1000000 in
-- Cache the underlying action before later proofs compare the two tower models.
set_option synthInstance.maxHeartbeats 500000 in
theorem relative_arithmetic_frobenius
    (m n : ℕ) [NeZero m] [NeZero n]
    (x : canonicalUpperLevel K m n) :
    relativeArithmeticFrobenius K m n x =
      ((canonicalArithmeticFrobenius K (m * n)) ^ n) x :=
  rfl

end

end Submission.CField.LBrauer
