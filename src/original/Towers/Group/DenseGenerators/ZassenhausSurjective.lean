import Mathlib
import Towers.Algebra.DenseGenerators.FiniteGroupAlgebra

/-!
# Surjective transport for the Zassenhaus filtration

This file isolates the elementary surjective-transport lemma for the explicit
Zassenhaus filtration.  It deliberately avoids the power-width and
restricted-Burnside adapters.
-/

noncomputable section

namespace Towers

universe u

/-- Zassenhaus filtrations commute with surjective homomorphisms. -/
lemma filtration_without_width
    {p : ℕ}
    {Γ Λ : Type u} [Group Γ] [Group Λ]
    (n : ℕ)
    (φ : Γ →* Λ)
    (hφ : Function.Surjective φ) :
    Subgroup.map φ (zassenhausFiltration p Γ n) =
      zassenhausFiltration p Λ n := by
  rw [zassenhausFiltration, zassenhausFiltration,
    ← image_set_surjective p n φ hφ]
  exact MonoidHom.map_closure φ (zassenhausGeneratorSet p Γ n)

end Towers
