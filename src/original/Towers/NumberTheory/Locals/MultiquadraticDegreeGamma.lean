import Towers.NumberTheory.Locals.MultiquadraticDegree
import Mathlib.Data.Finset.Max

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem quadratic_adjoin_tower
    (m : ℕ) (α : ℕ → K)
    (hnew : ∀ i < m, α i ∉ quadraticAdjoinTower (k := k) α i)
    (s : Finset ℕ) (hs : s.Nonempty) (hsupp : ∀ i ∈ s, i < m) :
    ∑ i ∈ s, α i ≠ 0 := by
  intro hzero
  let j := s.max' hs
  have hjmem : j ∈ s := s.max'_mem hs
  have hjlt : j < m := hsupp j hjmem
  apply hnew j hjlt
  have hrest : ∑ i ∈ s.erase j, α i ∈ quadraticAdjoinTower (k := k) α j := by
    apply (quadraticAdjoinTower (k := k) α j).sum_mem
    intro i hi
    rw [quadratic_tower_iio]
    apply IntermediateField.subset_adjoin
    exact ⟨i, s.lt_max'_of_mem_erase_max' hs hi, rfl⟩
  have hsum : (∑ i ∈ s.erase j, α i) + α j = 0 := by
    rw [Finset.sum_erase_add _ _ hjmem]
    exact hzero
  have hj : α j = -(∑ i ∈ s.erase j, α i) := by
    linear_combination hsum
  rw [hj]
  exact (quadraticAdjoinTower (k := k) α j).neg_mem hrest

end

end Towers.NumberTheory.Milne
