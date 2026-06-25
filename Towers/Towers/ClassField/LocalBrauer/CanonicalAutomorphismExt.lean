import Towers.ClassField.LocalBrauer.RelativeTransportEstimate

/-!
# Extensionality for canonical unramified automorphisms

Two automorphisms of a canonical unramified extension agree when their
values on integral elements are congruent modulo the maximal ideal.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel IsLocalRing

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option maxHeartbeats 4000000 in
-- Passing from arbitrary residue classes to integral representatives unfolds
-- the canonical spectral integral model.
set_option synthInstance.maxHeartbeats 500000 in
theorem canonical_unramified_ext
    (n : ℕ) [NeZero n]
    (σ τ : Gal(canonicalUnramifiedLevel K n/K))
    (h : ∀ y : canonicalUnramifiedLevel K n, ‖y‖ ≤ 1 →
      ‖σ y - τ y‖ < 1) :
    σ = τ := by
  apply (canonicalUnramifiedResidue K n).injective
  apply DFunLike.ext _ _
  intro z
  obtain ⟨y, rfl⟩ := residue_surjective z
  rw [canonical_unramified_residue K n σ,
    canonical_unramified_residue K n τ]
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  apply (NormedField.valuation
    (K := canonicalUnramifiedLevel K n)).mem_maximalIdeal_iff.mpr
  rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe]
  apply h
  exact_mod_cast y.property

end

end Towers.CField.LBrauer
