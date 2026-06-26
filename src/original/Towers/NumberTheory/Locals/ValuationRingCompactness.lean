import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Compactness of a complete discrete valuation ring

This is the valued-field formulation of Milne's Proposition 7.46.
-/

namespace Towers.NumberTheory.Milne

open Valued.integer

open Valued

variable (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
variable [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne]

/-- Milne, Proposition 7.46: for a complete discrete valuation ring, the
ring of integers is compact exactly when its residue field is finite. -/
theorem valuation_compact_space
    [CompleteSpace 𝒪[K]] [IsDiscreteValuationRing 𝒪[K]] :
    CompactSpace 𝒪[K] ↔ Finite 𝓀[K] := by
  rw [compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  constructor
  · exact fun h ↦ h.2.2
  · exact fun h ↦ ⟨inferInstance, inferInstance, h⟩

end Towers.NumberTheory.Milne
