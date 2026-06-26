import Towers.ClassField.BrauerGroups.SkolemNoether

/-!
# Chapter IV, Corollary 2.12

Every automorphism of a finite-dimensional central simple algebra is inner.
-/

namespace Towers.CField.BGroups

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]

/-- Milne's Corollary IV.2.12. -/
theorem alg_equiv_inner (f : A ≃ₐ[k] A) :
    ∃ a : Aˣ, ∀ x : A,
      f x = (a : A) * x * (a⁻¹ : Aˣ) := by
  simpa using skolemNoether k A A f.toAlgHom (AlgHom.id k A)

end Towers.CField.BGroups
