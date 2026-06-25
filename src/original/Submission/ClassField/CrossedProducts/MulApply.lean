import Submission.ClassField.BrauerGroups.TensorProductCentral
import Submission.ClassField.CrossedProducts.CrossedProductBrauer

/-!
# Chapter IV, Section 3, Lemma 3.15

This file sets up Milne's tensor-product compatibility statement. The sum
of additive cohomology classes is represented multiplicatively by the
pointwise product of normalized factor sets.
-/

namespace Submission.CField.CProduca

noncomputable section

universe u

attribute [local instance] Units.mulDistribMulActionRight

namespace NMCocycl₂

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- Pointwise multiplication of normalized multiplicative `2`-cocycles. -/
def mul (c d : NMCocycl₂ (G := G) (M := M)) :
    NMCocycl₂ (G := G) (M := M) where
  toFun p := c p * d p
  isMulCocycle₂ g h j := by
    calc
      (c (g * h, j) * d (g * h, j)) * (c (g, h) * d (g, h)) =
          (c (g * h, j) * c (g, h)) *
            (d (g * h, j) * d (g, h)) := by ac_rfl
      _ = (g • c (h, j) * c (g, h * j)) *
            (g • d (h, j) * d (g, h * j)) := by
              rw [c.isMulCocycle₂, d.isMulCocycle₂]
      _ = g • (c (h, j) * d (h, j)) *
            (c (g, h * j) * d (g, h * j)) := by
              rw [smul_mul']
              ac_rfl
  map_one_fst g := by simp
  map_one_snd g := by simp

@[simp]
theorem mul_apply (c d : NMCocycl₂ (G := G) (M := M))
    (p : G × G) : mul c d p = c p * d p :=
  rfl

end NMCocycl₂

namespace CProduc

open scoped TensorProduct

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (c d : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))

instance tensorSimpleRing :
    IsSimpleRing (CProduc c ⊗[k] CProduc d) :=
  BGroups.tensor_simple_ring
    k (CProduc c) (CProduc d)

instance tensorIsCentral :
    Algebra.IsCentral k (CProduc c ⊗[k] CProduc d) :=
  BGroups.tensor_product_central
    k (CProduc c) (CProduc d)

instance tensorModuleFinite :
    Module.Finite k (CProduc c ⊗[k] CProduc d) :=
  Module.Finite.tensorProduct k (CProduc c) (CProduc d)

/-- The tensor product in Lemma IV.3.15, packaged as a central simple
algebra. -/
def tensorSimpleCSA : CSA.{u, u} k :=
  BGroups.centralSimpleCSA k
    (CProduc c ⊗[k] CProduc d)

/-- The exact Brauer-equivalence assertion of Milne's Lemma IV.3.15. -/
def TensorCompatibility : Prop :=
  IsBrauerEquivalent
    (centralSimpleCSA k L (NMCocycl₂.mul c d))
    (tensorSimpleCSA k L c d)

end CProduc

end

end Submission.CField.CProduca
