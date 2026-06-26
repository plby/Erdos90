import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Chapter VIII, Section 4: the algebra of a fundamental class

Theorem 4.7 identifies `H^2(L/K)` with the cyclic group of order `[L : K]` by the global
invariant map and defines the fundamental class as the element of invariant `1 / [L : K]`.
The global invariant is not presently constructed in the project.  Once an additive equivalence
with `ZMod n` is supplied, however, its formal consequences and the canonical generator are
completely algebraic; those are recorded here.

Lemma 4.6 (the invariant is multiplied by the extension degree under restriction), the
compatibility of fundamental classes, and Theorem 4.8 require restriction/inflation/corestriction
on idele-class cohomology and are therefore beyond the current API.
-/

namespace Submission.CField.GClass

/-- The fundamental class attached to an additive invariant isomorphism.  Under the usual
identification `ZMod n ~= (1/n) Z / Z`, the element `1` corresponds to `1/n`. -/
def fundamentalClassInvariant
    {H : Type*} [AddGroup H] {n : ℕ} (inv : H ≃+ ZMod n) : H :=
  inv.symm 1

@[simp]
theorem invariant_fundamental
    {H : Type*} [AddGroup H] {n : ℕ} (inv : H ≃+ ZMod n) :
    inv (fundamentalClassInvariant inv) = 1 := by
  simp [fundamentalClassInvariant]

/-- **Theorem 4.7, order assertion.** The fundamental class has order `n`. -/
theorem add_fundamental_invariant
    {H : Type*} [AddGroup H] {n : ℕ} (inv : H ≃+ ZMod n) :
    addOrderOf (fundamentalClassInvariant inv) = n := by
  calc
    addOrderOf (fundamentalClassInvariant inv) =
        addOrderOf (inv (fundamentalClassInvariant inv)) :=
      (inv.addOrderOf_eq _).symm
    _ = n := by simp

/-- **Theorem 4.7, cyclicity assertion.** An additive group admitting the invariant
isomorphism with `ZMod n` is cyclic. -/
theorem add_cyclic_invariant
    {H : Type*} [AddGroup H] {n : ℕ} (inv : H ≃+ ZMod n) :
    IsAddCyclic H := by
  exact isAddCyclic_of_surjective inv.symm inv.symm.surjective

/-- **Theorem 4.7, cardinality assertion.** The group on the source of an
invariant isomorphism with `ZMod n` has cardinality `n`. -/
theorem nat_card_invariant
    {H : Type*} [AddGroup H] {n : ℕ} (inv : H ≃+ ZMod n) :
    Nat.card H = n := by
  rw [Nat.card_congr inv.toEquiv, Nat.card_zmod]

/-- Every element is an integral multiple of the fundamental class. -/
theorem zmultiples_fundamental_invariant
    {H : Type*} [AddGroup H] {n : ℕ} (inv : H ≃+ ZMod n) (x : H) :
    x ∈ AddSubgroup.zmultiples (fundamentalClassInvariant inv) := by
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨ZMod.cast (inv x), ?_⟩
  apply inv.injective
  simp [fundamentalClassInvariant]

/-- Thus the fundamental class is a generator of the whole additive group. -/
theorem zmultiples_fundamental_top
    {H : Type*} [AddGroup H] {n : ℕ} (inv : H ≃+ ZMod n) :
    AddSubgroup.zmultiples (fundamentalClassInvariant inv) = ⊤ := by
  apply top_unique
  intro x _
  exact zmultiples_fundamental_invariant inv x

end Submission.CField.GClass
