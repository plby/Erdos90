import Mathlib


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers
namespace TBluepr

theorem restrict_normal_implies
    {M : Type*} [Field M] [Algebra ℚ M]
    (S : IntermediateField ℚ M) [IsGalois ℚ ↥S] [Normal ℚ ↥S]
    [IsScalarTower ℚ ↥S M]
    {σ τ : Gal(M/ℚ)} {y : M} (hy : y ∈ S)
    (hrest :
      ((((AlgEquiv.restrictNormalHom S) σ) ⟨y, hy⟩ : M) =
        (((AlgEquiv.restrictNormalHom S) τ) ⟨y, hy⟩ : M))) :
    σ y = τ y := by
  letI : Normal ℚ ↥S := inferInstance
  have hσ : (((AlgEquiv.restrictNormalHom S) σ) ⟨y, hy⟩ : M) = σ y := by
    change ↑((σ.restrictNormal S) ⟨y, hy⟩) = σ y
    exact AlgEquiv.restrictNormal_commutes (χ := σ) (E := S) ⟨y, hy⟩
  have hτ : (((AlgEquiv.restrictNormalHom S) τ) ⟨y, hy⟩ : M) = τ y := by
    change ↑((τ.restrictNormal S) ⟨y, hy⟩) = τ y
    exact AlgEquiv.restrictNormal_commutes (χ := τ) (E := S) ⟨y, hy⟩
  exact hσ.symm.trans (hrest.trans hτ)

end TBluepr
end Towers
