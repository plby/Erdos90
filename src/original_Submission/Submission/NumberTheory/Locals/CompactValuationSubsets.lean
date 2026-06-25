import Mathlib.Topology.Algebra.Ring.Compact
import Submission.NumberTheory.Locals.ValuationRingCompactness

/-!
# Compact subsets of a complete discrete valuation ring

This records Milne's Corollary 7.47.
-/

namespace Submission.NumberTheory.Milne

open Valued

variable (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
variable [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne]
variable [CompleteSpace 𝒪[K]] [IsDiscreteValuationRing 𝒪[K]]
variable [Finite 𝓀[K]]

private local instance valuationRingCompactSpace : CompactSpace 𝒪[K] :=
  (valuation_compact_space K Γ₀).2 inferInstance

/-- Powers of the maximal ideal are compact. -/
theorem maximal_ideal_compact (n : ℕ) :
    IsCompact (X := 𝒪[K])
      (↑(IsLocalRing.maximalIdeal 𝒪[K] ^ n) : Set 𝒪[K]) :=
  Ideal.isCompact_of_fg (IsNoetherian.noetherian _)

/-- The translates `1 + 𝔪^n` are compact. -/
theorem add_maximal_compact (n : ℕ) :
    IsCompact (X := 𝒪[K])
      ((fun x : 𝒪[K] ↦ 1 + x) ''
        (↑(IsLocalRing.maximalIdeal 𝒪[K] ^ n) : Set 𝒪[K])) :=
  (maximal_ideal_compact K Γ₀ n).image
    (continuous_const.add continuous_id)

/-- The unit locus of the valuation ring is compact. -/
theorem valuation_units_compact :
    IsCompact (X := 𝒪[K]) {x : 𝒪[K] | IsUnit x} := by
  apply IsClosed.isCompact
  rw [show {x : 𝒪[K] | IsUnit x} =
      (↑(IsLocalRing.maximalIdeal 𝒪[K]) : Set 𝒪[K])ᶜ by
    ext x
    simp [IsLocalRing.mem_maximalIdeal]]
  exact (IsLocalRing.isOpen_maximalIdeal 𝒪[K]).isClosed_compl

end Submission.NumberTheory.Milne
