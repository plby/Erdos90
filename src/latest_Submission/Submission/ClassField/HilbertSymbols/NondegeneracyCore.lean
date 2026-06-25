import Mathlib.Algebra.Group.Basic

/-!
# Milne, Class Field Theory, Theorem III.4.4: nondegeneracy core

In the proof of Theorem III.4.4, Proposition III.4.3 gives triviality of the
left kernel of the Hilbert pairing.  Milne then obtains triviality of the
right kernel from skew-symmetry.  The following theorem is that argument in
its natural abstract form.
-/

namespace Submission.CField.HSymbol

universe u v

/-- A skew-symmetric pairing with trivial left kernel also has trivial right
kernel. -/
theorem nondegenerate_skew_symmetric
    {A : Type u} [One A] {C : Type v} [Group C]
    (pairing : A → A → C)
    (left_nondegenerate : ∀ a,
      (∀ b, pairing a b = 1) → a = 1)
    (skew : ∀ a b, pairing b a = (pairing a b)⁻¹) :
    ∀ b, (∀ a, pairing a b = 1) → b = 1 := by
  intro b hb
  apply left_nondegenerate b
  intro a
  rw [skew a b, hb a, inv_one]

end Submission.CField.HSymbol
