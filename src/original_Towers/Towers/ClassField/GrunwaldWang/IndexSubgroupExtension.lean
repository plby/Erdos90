import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Extending a finite-index subgroup from an embedded group

This is the abstract group-theoretic step in the paragraph preceding
Theorem VIII.2.3.  If an embedded subgroup has a prescribed subgroup `N`,
and an open finite-index subgroup of the ambient group meets the embedded
group inside `N`, adjoining the image of `N` produces an open finite-index
ambient subgroup whose pullback is exactly `N`.
-/

namespace Towers.CField.GWang

/-- Enlarge an open finite-index ambient subgroup by the image of `N`.
The resulting subgroup still has finite index and has exactly `N` as its
pullback along the embedding. -/
theorem open_index_comap
    {P C : Type*} [CommGroup P] [CommGroup C]
    [TopologicalSpace C] [IsTopologicalGroup C]
    (j : P →* C)
    (N : Subgroup P)
    (V : Subgroup C) (hVopen : IsOpen (V : Set C))
    (hVfinite : V.FiniteIndex) (hVsmall : V.comap j ≤ N) :
    ∃ U : Subgroup C,
      IsOpen (U : Set C) ∧ U.FiniteIndex ∧ U.comap j = N := by
  let U : Subgroup C := V ⊔ N.map j
  have hVU : V ≤ U := le_sup_left
  have hNU : N ≤ U.comap j := by
    intro x hx
    change j x ∈ U
    exact Subgroup.mem_sup_right ⟨x, hx, rfl⟩
  have hUN : U.comap j ≤ N := by
    intro x hx
    change j x ∈ V ⊔ N.map j at hx
    obtain ⟨v, hv, z, hz, hvz⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨y, hy, rfl⟩ := hz
    have hxy : x * y⁻¹ ∈ V.comap j := by
      change j (x * y⁻¹) ∈ V
      have heq : j x * (j y)⁻¹ = v := by
        rw [← hvz]
        simp
      simpa only [map_mul, map_inv, heq] using hv
    have hxyN : x * y⁻¹ ∈ N := hVsmall hxy
    have hyN : y ∈ N := hy
    simpa [mul_assoc] using N.mul_mem hxyN hyN
  refine ⟨U, Subgroup.isOpen_mono hVU hVopen, ?_, le_antisymm hUN hNU⟩
  letI : V.FiniteIndex := hVfinite
  exact Subgroup.finiteIndex_of_le hVU

end Towers.CField.GWang
