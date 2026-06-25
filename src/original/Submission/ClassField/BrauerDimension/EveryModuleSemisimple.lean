import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Chapter IV, Section 5, Theorem 5.5

Mathlib develops the classification of modules over a semisimple ring using
simple submodules and isotypic components.  The two structural assertions
below are the existence statements in Milne's Theorem 5.5.
-/

namespace Submission.CField.BDim

universe u v

variable (A : Type u) [Ring A] [IsSemisimpleRing A]
  (M : Type v) [AddCommGroup M] [Module A M]

/-- Every module over a semisimple ring is semisimple. -/
theorem every_module_semisimple : IsSemisimpleModule A M :=
  inferInstance

/-- A finite module over a semisimple ring is a finite direct sum of simple
submodules. -/
theorem module_linear_dfinsupp [Module.Finite A M] :
    ∃ (n : ℕ) (S : Fin n → Submodule A M)
      (_ : M ≃ₗ[A] Π₀ i : Fin n, S i),
      ∀ i, IsSimpleModule A (S i) :=
  IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A M

end Submission.CField.BDim
