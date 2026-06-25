import Towers.ClassField.BrauerLocalization.FiniteTateZero
import Towers.ClassField.BrauerLocalization.FiniteZeroDirect
import Towers.ClassField.BrauerLocalization.InfiniteTateZero

/-!
# Local Tate-zero assembly for Proposition VII.2.7

The finite calculation uses the spectral local-invariant base-change formula
already required by VIII.4.2.  The archimedean calculation is unconditional.
Together they discharge the local cardinality bridge left after Hilbert 90.
-/

namespace Towers.CField.BLoc

open NumberField
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

/-- Finite spectral base change supplies the complete local Tate-zero
cardinality input to Proposition VII.2.7. -/
theorem tate_cardinality_change
    (hbaseChange : FiniteSpectralChange.{u}) :
    TateCardinalityBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  intro v w
  cases v with
  | inl P =>
      exact cardinality_base_change
        hbaseChange P w
  | inr v =>
      exact infiniteTateCardinality v w

/-- Consequently the complete placewise Herbrand quotient assertion in
Proposition VII.2.7 follows from finite spectral base change. -/
theorem herbrand_spectral_change
    (hbaseChange : FiniteSpectralChange.{u}) :
    LocalHerbrandBridge.{u} :=
  herbrand_bridge_cardinality
    (tate_cardinality_change
      hbaseChange)

/-- Proposition VII.2.7 is reduced to its restricted-product Herbrand
assembly; its complete placewise input follows from finite spectral base
change. -/
theorem spectral_change_assembly
    (hbaseChange : FiniteSpectralChange.{u})
    (hassembly : HerbrandAssemblyBridge.{u}) :
    LocalHerbrandFormula.{u} :=
  coinvariants_invariants_assembly
    (herbrand_spectral_change hbaseChange)
    hassembly

/-- The direct finite-local calculation and the archimedean calculation
give the full placewise Tate-zero cardinality bridge unconditionally. -/
theorem localTateCardinality :
    TateCardinalityBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  intro v w
  cases v with
  | inl P =>
      exact tate_cardinality_direct P w
  | inr v =>
      exact infiniteTateCardinality v w

/-- The complete placewise Herbrand quotient assertion in Proposition
VII.2.7, with no auxiliary local-invariant hypothesis. -/
theorem localHerbrandBridge :
    LocalHerbrandBridge.{u} :=
  herbrand_bridge_cardinality
    localTateCardinality

end

end Towers.CField.BLoc
