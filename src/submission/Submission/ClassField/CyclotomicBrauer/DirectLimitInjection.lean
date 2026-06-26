import Mathlib.Order.DirectedInverseSystem

/-!
# The direct-limit step in Theorem VII.7.1

Milne proves Theorem VII.7.1 first for finite Galois extensions and obtains
the possibly infinite case by passing to the direct limit over the finite
Galois subextensions.  This file records the precise set-level fact used in
that last step.
-/

namespace Submission.CField.CBrauer

universe u v w

variable {I : Type u} [Preorder I] [IsDirectedOrder I]
variable {A : I → Type v} {B : I → Type w}
variable {TA : ∀ ⦃i j : I⦄, i ≤ j → Type*}
variable {TB : ∀ ⦃i j : I⦄, i ≤ j → Type*}
variable (f : ∀ i j (h : i ≤ j), TA h)
variable (g : ∀ i j (h : i ≤ j), TB h)
variable [∀ i j (h : i ≤ j), FunLike (TA h) (A i) (A j)]
variable [∀ i j (h : i ≤ j), FunLike (TB h) (B i) (B j)]
variable [DirectedSystem A (f · · ·)] [DirectedSystem B (g · · ·)]

/-- A compatible family of injective maps induces an injective map on
direct limits, provided the transition maps in the target system are
injective. -/
theorem direct_limit_injective
    (localize : ∀ i, A i → B i)
    (compat : ∀ i j (h : i ≤ j) (x : A i),
      g i j h (localize i x) = localize j (f i j h x))
    (hlocalize : ∀ i, Function.Injective (localize i))
    (hg : ∀ i j (h : i ≤ j), Function.Injective (g i j h)) :
    Function.Injective (DirectLimit.map f g localize compat) := by
  apply DirectLimit.lift_injective
  intro i
  exact (DirectLimit.mk_injective (F := B) (f := fun i j h => g i j h)
    hg i).comp (hlocalize i)

/-- **Theorem VII.7.1, passage to possibly infinite extensions.**
If the finite-level localization maps are injective and commute with the
inflation maps, their map on continuous cohomology (the direct limit over
finite Galois levels) is injective. -/
theorem directLimit
    (localize : ∀ i, A i → B i)
    (compat : ∀ i j (h : i ≤ j) (x : A i),
      g i j h (localize i x) = localize j (f i j h x))
    (finite : ∀ i, Function.Injective (localize i))
    (localInflation_injective :
      ∀ i j (h : i ≤ j), Function.Injective (g i j h)) :
    Function.Injective (DirectLimit.map f g localize compat) :=
  direct_limit_injective f g localize compat finite
    localInflation_injective

end Submission.CField.CBrauer
