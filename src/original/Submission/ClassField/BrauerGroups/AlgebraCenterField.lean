import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.SimpleRing.Field

/-!
# Milne, Class Field Theory, Corollary IV.2.4

The centre of a simple algebra is a field.
-/

namespace Submission.CField.BGroups

universe u v

variable (k : Type u) (A : Type v)
variable [Field k] [Ring A] [Algebra k A] [IsSimpleRing A]

/-- **Corollary IV.2.4.** The centre of a simple `k`-algebra is a field. -/
theorem algebra_center_field : IsField (Subalgebra.center k A) := by
  let e : Subalgebra.center k A ≃+* Subring.center A :=
    { toFun := fun x ↦ ⟨x, x.2⟩
      invFun := fun x ↦ ⟨x, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  exact e.toMulEquiv.isField (IsSimpleRing.isField_center A)

end Submission.CField.BGroups
