import Towers.NumberTheory.Dedekind.DedekindModules
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Milne, Algebraic Number Theory, determinant lines

This file develops the determinant-line machinery needed for the converse direction of
Theorem 3.31(b).
-/

namespace Towers.NumberTheory.Milne

/-- A linear equivalence induces a linear equivalence on every exterior power. -/
noncomputable def exteriorLinearEquiv
    (R M N : Type*) [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (n : ℕ) (e : M ≃ₗ[R] N) :
    (⋀[R]^n M) ≃ₗ[R] (⋀[R]^n N) :=
  LinearEquiv.ofLinear
    (exteriorPower.map n e.toLinearMap)
    (exteriorPower.map n e.symm.toLinearMap)
    (by
      rw [← exteriorPower.map_comp]
      have h : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
        ext x
        simp
      rw [h, exteriorPower.map_id])
    (by
      rw [← exteriorPower.map_comp]
      have h : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by
        ext x
        simp
      rw [h, exteriorPower.map_id])

end Towers.NumberTheory.Milne
