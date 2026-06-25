import Mathlib.Algebra.Azumaya.Basic
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Towers.ClassField.BrauerGroups.CentralMatrix

/-!
# Chapter IV, Corollary 2.9

For a finite-dimensional central simple algebra `A` over a field `k`, the
canonical action of `A ⊗[k] Aᵐᵒᵖ` on `A` is an algebra isomorphism onto the
algebra of `k`-linear endomorphisms of `A`.
-/

namespace Towers.CField.BGroups

open scoped TensorProduct

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]

/-- Milne's Corollary IV.2.9: the canonical left-right action is bijective. -/
theorem mul_left_bijective :
    Function.Bijective (AlgHom.mulLeftRight k A) := by
  letI : IsSimpleRing (A ⊗[k] Aᵐᵒᵖ) :=
    tensor_simple_ring k A Aᵐᵒᵖ
  have hinj : Function.Injective (AlgHom.mulLeftRight k A) :=
    (AlgHom.mulLeftRight k A).toRingHom.injective
  have hdim :
      Module.finrank k (A ⊗[k] Aᵐᵒᵖ) = Module.finrank k (Module.End k A) := by
    rw [Module.finrank_tensorProduct, MulOpposite.finrank, Module.finrank_linearMap]
  have hsurj : Function.Surjective (AlgHom.mulLeftRight k A).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨hinj, hsurj⟩

/-- The canonical algebra equivalence supplied by Corollary IV.2.9. -/
noncomputable def tensorEquivEnd :
    A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Module.End k A :=
  AlgEquiv.ofBijective (AlgHom.mulLeftRight k A) (mul_left_bijective k A)

@[simp]
theorem tensor_end_alg :
    (tensorEquivEnd k A).toAlgHom = AlgHom.mulLeftRight k A :=
  AlgEquiv.toAlgHom_ofBijective _ _

/-- After choosing the canonical finite basis, the endomorphism algebra is the
full matrix algebra of size `[A : k]`. -/
noncomputable def tensorEquivMatrix :
    A ⊗[k] Aᵐᵒᵖ ≃ₐ[k]
      Matrix (Fin (Module.finrank k A)) (Fin (Module.finrank k A)) k :=
  (tensorEquivEnd k A).trans
    (algEquivMatrix (Module.finBasis k A))

end Towers.CField.BGroups
