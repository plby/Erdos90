import Towers.ClassField.BrauerGroups.SkolemNoether

/-!
# Chapter IV, Corollary 2.11

An isomorphism between two simple subalgebras of a central simple algebra is
induced by an inner automorphism of the ambient algebra.
-/

namespace Towers.CField.BGroups

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]

/-- Milne's Corollary IV.2.11. -/
theorem simple_subalgebra_inner
    (B₁ B₂ : Subalgebra k A) [IsSimpleRing B₁] [IsSimpleRing B₂]
    (f : B₁ ≃ₐ[k] B₂) :
    ∃ a : Aˣ, ∀ b : B₁,
      (f b : A) = (a : A) * (b : A) * (a⁻¹ : Aˣ) := by
  letI : Module.Finite k B₁ :=
    Module.Finite.of_injective B₁.val.toLinearMap B₁.val.injective
  let h : B₁ →ₐ[k] A := B₂.val.comp f.toAlgHom
  let g : B₁ →ₐ[k] A := B₁.val
  simpa [h, g] using skolemNoether k B₁ A h g

end Towers.CField.BGroups
