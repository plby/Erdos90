import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.Homotopy

/-!
# Chapter II, Appendix, Proposition A.8

A morphism extends to a morphism of injective resolutions, and any two such
extensions induce the same morphism on cohomology after applying an additive
functor.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Towers.CField.Homological

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The extension of a morphism to chosen injective resolutions in
Proposition A.8. -/
noncomputable def extendInjectiveResolutions {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y) :
    I.cocomplex ⟶ J.cocomplex :=
  InjectiveResolution.desc f J I

@[reassoc]
theorem extend_resolutions_commutes {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y) :
    I.ι ≫ extendInjectiveResolutions f I J =
      (CochainComplex.single₀ C).map f ≫ J.ι :=
  InjectiveResolution.desc_commutes f J I

/-- The more precise uniqueness assertion used in Proposition A.8: any two
extensions of the same morphism are homotopic. -/
noncomputable def resolutionExtensionsHomotopy {X Y : C} (f : X ⟶ Y)
    {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (g h : I.cocomplex ⟶ J.cocomplex)
    (hg : I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι)
    (hh : I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι) :
    Homotopy g h :=
  InjectiveResolution.descHomotopy f g h hg hh

/-- Consequently the cohomology map is independent of the chosen extension,
as asserted in Proposition A.8. -/
theorem resolution_extensions_homology
    (F : C ⥤ D) [F.Additive] {X Y : C} (f : X ⟶ Y)
    {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (g h : I.cocomplex ⟶ J.cocomplex)
    (hg : I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι)
    (hh : I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι)
    (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map g) n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map h) n :=
  (F.mapHomotopy (resolutionExtensionsHomotopy f g h hg hh)).homologyMap_eq n

end Towers.CField.Homological
