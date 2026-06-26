import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Chapter IV, Section 5, Example 5.1

A finite product of finite-dimensional simple algebras is semisimple.
-/

namespace Towers.CField.BDim

universe u

/-- Milne, Example IV.5.1. -/
theorem product_semisimple_ring
    (k : Type u) [Field k] (I : Type u) [Finite I]
    (A : I → Type u) [∀ i, Ring (A i)] [∀ i, Algebra k (A i)]
    [∀ i, IsSimpleRing (A i)] [∀ i, Module.Finite k (A i)] :
    IsSemisimpleRing (∀ i, A i) := by
  letI (i : I) : IsArtinianRing (A i) := IsArtinianRing.of_finite k (A i)
  letI (i : I) : IsSemisimpleRing (A i) := inferInstance
  infer_instance

end Towers.CField.BDim
