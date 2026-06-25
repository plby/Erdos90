import Submission.ClassField.CrossedProducts.TensorRightCongr

/-!
# Chapter VII, Section 7: the Brauer local-global principle

Theorem 7.1 injects the relative Brauer group into the direct sum of its
local counterparts.  The project does not yet have the localization maps on
Mathlib's `BrauerGroup`, nor the comparison of `H^2` of ideles with the sum of
local `H^2` groups.  This file isolates the exact Brauer-class consequence of
that injectivity.  In particular, it proves the first concrete restatement:
if the localization map is injective and a central simple algebra has the
same class as the base field at every place, then it is split over the base
field.

The hypotheses are phrased for an arbitrary family of local class types.
They can be instantiated directly once completion and scalar-extension maps
on the Brauer quotient are available.
-/

namespace Submission.CField.CBrauer

open scoped TensorProduct

noncomputable section

universe u v w

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private noncomputable def tensorLidSelf (k : Type u) [Field k] :
    k ⊗[k] k ≃ₐ[k] k :=
  { Algebra.TensorProduct.lid k k with
    commutes' := by
      intro x
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      simp }

/-- **Theorem VII.7.1, Brauer-class consequence.** An injective family of
localization maps detects Brauer equivalence of central simple algebras. -/
theorem brauer_equivalent_localizations
    (k : Type u) [Field k]
    {ι : Type v} (LClass : ι → Type w)
    (localize : BrauerGroup.{u, u} k → ∀ i, LClass i)
    (hlocalize : Function.Injective localize)
    (A B : CSA.{u, u} k)
    (hAB : ∀ i, localize (BGroups.brauerClass k A) i =
      localize (BGroups.brauerClass k B) i) :
    IsBrauerEquivalent A B := by
  apply (BGroups.brauer_class k A B).1
  apply hlocalize
  funext i
  exact hAB i

/-- The base field, regarded as a central simple algebra, is split over
itself. -/
theorem base_split_self (k : Type u) [Field k] :
    BGroups.ISBy k k k := by
  refine ⟨1, ⟨one_ne_zero⟩, ⟨?_⟩⟩
  exact (tensorLidSelf k).trans
    (BGroups.matrixFinAlg k k).symm

/-- The first concrete formulation following Lemma 7.3: under the injective
localization map of Theorem 7.1, a central simple algebra whose local classes
are all split is already split over the number field. -/
theorem split_self_localizations
    (k A : Type u) [Field k]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Module.Finite k A]
    {ι : Type v} (LClass : ι → Type w)
    (localize : BrauerGroup.{u, u} k → ∀ i, LClass i)
    (hlocalize : Function.Injective localize)
    (hA : ∀ i,
      localize (BGroups.brauerClass k (BGroups.centralSimpleCSA k A)) i =
        localize (BGroups.brauerClass k (BGroups.baseFieldCSA k)) i) :
    BGroups.ISBy k k A := by
  have hBrauer :
      IsBrauerEquivalent (BGroups.centralSimpleCSA k A)
        (BGroups.baseFieldCSA k) :=
    brauer_equivalent_localizations k LClass localize hlocalize
      (BGroups.centralSimpleCSA k A) (BGroups.baseFieldCSA k) hA
  exact CProduca.split_equivalent k k A k hBrauer
    (base_split_self k)

end

end Submission.CField.CBrauer
