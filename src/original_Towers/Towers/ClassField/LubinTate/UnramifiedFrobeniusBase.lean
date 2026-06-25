import Towers.ClassField.LocalBrauer.CanonicalFrobeniusRestriction

/-! # Finite-level data for infinite unramified Frobenius -/

namespace Towers.CField.LTate

noncomputable section

open Towers.CField.LBrauer

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

local instance infiniteUnramifiedLevelDegree_neZero (r : ℕ) :
    NeZero (invariantLevelDegree r) :=
  ⟨(invariant_level_pos r).ne'⟩

/-- The infinite canonical unramified extension, presented as the directed
union of the factorial-degree canonical levels. -/
def infiniteUnramifiedField :
    IntermediateField K (SeparableClosure K) :=
  ⨆ r, (unramifiedFactorialLevel K r).toIntermediateField

theorem canonical_factorial_monotone :
    Monotone (fun r ↦
      (unramifiedFactorialLevel K r).toIntermediateField) := by
  intro r s hrs
  exact factorial_level_monotone K hrs

/-- The canonical inclusion of a finite factorial level into the infinite
unramified union. -/
noncomputable def factorialLevelInclusion (r : ℕ) :
    unramifiedFactorialLevel K r →ₐ[K]
      infiniteUnramifiedField K :=
  IntermediateField.inclusion (le_iSup
    (fun s ↦
      (unramifiedFactorialLevel K s).toIntermediateField) r)

/-- The `z`-th power of arithmetic Frobenius on one finite factorial level,
viewed in the ambient separable closure. -/
noncomputable def infiniteLevelAlg
    (z : ℤ) (r : ℕ) :
    unramifiedFactorialLevel K r →ₐ[K]
      SeparableClosure K :=
  (unramifiedFactorialLevel K r).toIntermediateField.val.comp
    ((canonicalArithmeticFrobenius K
      (invariantLevelDegree r)) ^ z).toAlgHom

set_option maxHeartbeats 2000000 in
-- Restriction through two dependent intermediate-field inclusions unfolds
-- the finite Galois tower structures.
/-- Frobenius powers commute with the transition maps of the canonical
factorial tower. -/
theorem infinite_frobenius_compatible
    (z : ℤ) {r s : ℕ} (hrs : r ≤ s)
    (x : unramifiedFactorialLevel K r) :
    IntermediateField.inclusion
        (factorial_level_monotone K hrs)
        (((canonicalArithmeticFrobenius K
          (invariantLevelDegree r)) ^ z) x) =
      ((canonicalArithmeticFrobenius K
        (invariantLevelDegree s)) ^ z)
        (IntermediateField.inclusion
          (factorial_level_monotone K hrs) x) := by
  let res := factorialRestrictionHom K hrs
  have hres : res
      (canonicalArithmeticFrobenius K (invariantLevelDegree s)) =
      canonicalArithmeticFrobenius K (invariantLevelDegree r) :=
    arithmetic_factorial_restriction K hrs
  have hresPow : res
      ((canonicalArithmeticFrobenius K
        (invariantLevelDegree s)) ^ z) =
      (canonicalArithmeticFrobenius K
        (invariantLevelDegree r)) ^ z := by
    calc
      res ((canonicalArithmeticFrobenius K
          (invariantLevelDegree s)) ^ z) =
        (res (canonicalArithmeticFrobenius K
          (invariantLevelDegree s))) ^ z :=
        res.map_zpow _ z
      _ = (canonicalArithmeticFrobenius K
          (invariantLevelDegree r)) ^ z :=
        congrArg (fun g ↦ g ^ z) hres
  rw [← hresPow]
  exact galois_restriction_hom K
    (factorial_level_monotone K hrs)
      ((canonicalArithmeticFrobenius K
        (invariantLevelDegree s)) ^ z) x

end

end Towers.CField.LTate
