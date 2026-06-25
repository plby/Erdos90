import Towers.ClassField.CrossedProducts.TensorEquivLeft
import Towers.ClassField.CrossedProducts.FieldEmbeddingMul

/-!
# Chapter IV, Section 3: crossed products in the relative Brauer group

This file records the structural part of Milne's Theorem 3.14.  A crossed
product attached to a normalized cocycle is a finite-dimensional central
simple algebra over the base field, has dimension `[L : k]^2`, and is split
by `L`.
-/

namespace Towers.CField.CProduca

noncomputable section

universe u

attribute [local instance] Units.mulDistribMulActionRight

namespace CProduc

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))

instance : IsScalarTower k L (CProduc c) where
  smul_assoc r a x := by
    change (r • a) • x = algebraMap k L r • (a • x)
    rw [Algebra.smul_def]
    exact mul_smul _ _ _

instance : Module.Finite k (CProduc c) :=
  Module.Finite.trans L (CProduc c)

/-- The crossed product has the square of the extension degree as its
dimension over the base field. -/
theorem finrank_over_base :
    Module.finrank k (CProduc c) = (Module.finrank k L) ^ 2 := by
  rw [← Module.finrank_mul_finrank k L (CProduc c),
    finrank_over_extension]
  exact (pow_two _).symm

/-- The crossed product, packaged as a central simple algebra over `k`. -/
def centralSimpleCSA : CSA.{u, u} k :=
  BGroups.centralSimpleCSA k (CProduc c)

/-- The defining Galois extension splits its crossed product. -/
theorem isSplitBy : BGroups.ISBy k L (CProduc c) := by
  rw [split_similar_containing]
  refine ⟨centralSimpleCSA k L c, fieldEmbedding k L c,
    fieldEmbedding_injective k L c, finrank_over_base k L c, ?_⟩
  exact IsBrauerEquivalent.refl _

/-- The Brauer class represented by a normalized Galois crossed product. -/
def brauerClass : BrauerGroup.{u, u} k :=
  BGroups.brauerClass k (centralSimpleCSA k L c)

end CProduc

end

end Towers.CField.CProduca
