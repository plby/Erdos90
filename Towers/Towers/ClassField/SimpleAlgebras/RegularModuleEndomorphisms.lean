import Mathlib.Algebra.Algebra.Opposite

/-!
# Milne, Class Field Theory, Statement IV.1.8

Endomorphisms of the left regular module are right multiplications, so their
composition law identifies the endomorphism algebra with the opposite algebra.
-/

namespace Towers.CField.SAlgebr

universe u v

variable (k : Type u) (A : Type v)
variable [CommSemiring k] [Semiring A] [Algebra k A]

/-- **Statement IV.1.8.** Evaluation at `1` identifies endomorphisms of the
left regular `A`-module with `A` with its multiplication reversed. -/
noncomputable def regularModuleEnd :
    Module.End A A ≃ₐ[k] Aᵐᵒᵖ :=
  (AlgEquiv.moduleEndSelf (A := A) k).symm

@[simp]
theorem regular_module_end (f : Module.End A A) :
    regularModuleEnd k A f = MulOpposite.op (f 1) :=
  rfl

@[simp]
theorem regular_end_symm (a : Aᵐᵒᵖ) (x : A) :
    (regularModuleEnd k A).symm a x = x * MulOpposite.unop a :=
  rfl

end Towers.CField.SAlgebr
