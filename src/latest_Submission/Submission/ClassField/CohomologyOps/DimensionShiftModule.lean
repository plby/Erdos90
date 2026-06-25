import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.RepresentationTheory.Coinduced

/-!
# Milne, Class Field Theory, Lemma II.1.37

For a `G`-module `A`, let `A_*` be the coinduced module of functions `G → A` and embed `A` by
`a ↦ (g ↦ g • a)`.  After forgetting the `G`-action, evaluation at `1` retracts this embedding.
Consequently the cokernel sequence

`0 → A → A_* → A_† → 0`

splits, and `A_*` is the direct sum of `A` and `A_†`.
-/

namespace Submission.CField.COps

open CategoryTheory CategoryTheory.Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Milne's module `A_*`: coinduction of `A` restricted to the trivial subgroup. -/
noncomputable abbrev dimensionShiftModule (A : Rep k G) : Rep k G :=
  coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A)

/-- The map `A → A_*` sending `a` to the function `g ↦ g • a`, after forgetting the action. -/
noncomputable def dimensionShiftEmbedding (A : Rep k G) :
    ModuleCat.of k A ⟶ ModuleCat.of k (dimensionShiftModule A) :=
  ModuleCat.ofHom ((resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.app A).hom.toLinearMap

@[simp]
lemma shift_embedding (A : Rep k G) (a : A) (g : G) :
    ((dimensionShiftEmbedding A).hom a :
      Representation.coindV (⊥ : Subgroup G).subtype
        (A.ρ.comp (⊥ : Subgroup G).subtype)).1 g = A.ρ g a := by
  rfl

/-- Evaluation at the identity is a retraction of `dimensionShiftEmbedding`. -/
noncomputable def dimensionShiftRetraction (A : Rep k G) :
    ModuleCat.of k (dimensionShiftModule A) ⟶ ModuleCat.of k A :=
  ModuleCat.ofHom <|
    LinearMap.proj 1 ∘ₗ
      (Representation.coindV (⊥ : Subgroup G).subtype
        (A.ρ.comp (⊥ : Subgroup G).subtype)).subtype

@[simp]
lemma shift_retraction (A : Rep k G) (f : dimensionShiftModule A) :
    (dimensionShiftRetraction A).hom f = f.1 1 := by
  rfl

/-- Evaluation at `1` composed with `a ↦ (g ↦ g • a)` is the identity. -/
@[simp]
theorem dimension_shift_retraction (A : Rep k G) :
    dimensionShiftEmbedding A ≫ dimensionShiftRetraction A = 𝟙 (ModuleCat.of k A) := by
  ext a
  change A.ρ 1 a = a
  simp

/-- The underlying module map `A → A_*` is split injective. -/
noncomputable def dimensionShiftMono (A : Rep k G) :
    SplitMono (dimensionShiftEmbedding A) where
  retraction := dimensionShiftRetraction A
  id := dimension_shift_retraction A

noncomputable instance dimension_shift_mono (A : Rep k G) :
    IsSplitMono (dimensionShiftEmbedding A) :=
  IsSplitMono.mk' (dimensionShiftMono A)

/-- Milne's `A_†`, realized as the cokernel of `A → A_*`. -/
noncomputable abbrev dimensionShiftQuotient (A : Rep k G) : ModuleCat k :=
  (ModuleCat.cokernelCocone (dimensionShiftEmbedding A)).pt

/-- The split cokernel diagram with middle term `A_*`. -/
noncomputable def dimensionShiftBicone (A : Rep k G) :
    BinaryBicone (ModuleCat.of k A) (dimensionShiftQuotient A) :=
  binaryBiconeOfIsSplitMonoOfCokernel
    (ModuleCat.cokernelIsColimit (dimensionShiftEmbedding A))

/-- The cokernel sequence `0 → A → A_* → A_† → 0` is split exact. -/
noncomputable def shiftBiconeBilimit (A : Rep k G) :
    (dimensionShiftBicone A).IsBilimit :=
  isBilimitBinaryBiconeOfIsSplitMonoOfCokernel
    (ModuleCat.cokernelIsColimit (dimensionShiftEmbedding A))

/-- Milne's decomposition `A_* ≃ A ⊕ A_†` as underlying `k`-modules. -/
noncomputable def dimensionShiftDecomposition (A : Rep k G) :
    ModuleCat.of k (dimensionShiftModule A) ≅
      ModuleCat.of k A ⊞ dimensionShiftQuotient A :=
  biprod.uniqueUpToIso _ _ (shiftBiconeBilimit A)

end Submission.CField.COps
