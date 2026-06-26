import Towers.Algebra.Magnus.MagnusEmbedding

/-!
# Functoriality of Magnus series in the coefficient ring

Ring homomorphisms act coefficientwise on Magnus series.  This file proves
that this action is a ring homomorphism and commutes with the Magnus expansion.
-/

noncomputable section

namespace EChapma
namespace MSeries

variable {R S X : Type*} [CommRing R] [CommRing S]

/-- Apply a ring homomorphism to every coefficient of a Magnus series. -/
def mapCoefficients
    (σ : R →+* S) (f : MSeries R X) :
    MSeries S X :=
  ⟨fun w => σ (f w)⟩

@[simp]
theorem mapCoefficients_apply
    (σ : R →+* S) (f : MSeries R X) (w : FreeMonoid X) :
    mapCoefficients σ f w = σ (f w) :=
  rfl

@[simp]
theorem mapCoefficients_shift
    (σ : R →+* S) (x : X) (f : MSeries R X) :
    mapCoefficients σ (shift x f) =
      shift x (mapCoefficients σ f) := by
  ext w
  rfl

theorem map_convolutionList
    (σ : R →+* S) (f g : MSeries R X) (xs : List X) :
    σ (convolutionList f g xs) =
      convolutionList (mapCoefficients σ f)
        (mapCoefficients σ g) xs := by
  induction xs generalizing f with
  | nil =>
      simp [convolutionList]
  | cons x xs ih =>
      simp only [convolutionList, map_add, map_mul,
        mapCoefficients_apply]
      rw [ih (f := shift x f)]
      rw [mapCoefficients_shift]

/-- Coefficientwise base change is a ring homomorphism of Magnus rings. -/
def coefficientsRingHom
    (σ : R →+* S) :
    MSeries R X →+* MSeries S X where
  toFun := mapCoefficients σ
  map_zero' := by
    ext w
    simp
  map_one' := by
    ext w
    simp [mapCoefficients, one_apply]
  map_add' f g := by
    ext w
    simp
  map_mul' f g := by
    ext w
    change
      σ (convolutionList f g w.toList) =
        convolutionList (mapCoefficients σ f)
          (mapCoefficients σ g) w.toList
    exact map_convolutionList σ f g w.toList

@[simp]
theorem coefficients_ring_hom
    (σ : R →+* S) (f : MSeries R X) (w : FreeMonoid X) :
    coefficientsRingHom (X := X) σ f w = σ (f w) :=
  rfl

@[simp]
theorem coefficients_variable_series
    (σ : R →+* S) (x : X) :
    coefficientsRingHom (X := X) σ
        (variableSeries (R := R) x) =
      variableSeries (R := S) x := by
  ext w
  simp [coefficientsRingHom, mapCoefficients, variableSeries]

/-- Base change commutes with the full Magnus expansion. -/
theorem coefficients_magnus_series
    (σ : R →+* S) (g : FreeGroup X) :
    coefficientsRingHom (X := X) σ
        (magnusSeries (R := R) g) =
      magnusSeries (R := S) g := by
  let h : FreeGroup X →* (MSeries S X)ˣ :=
    (Units.map (coefficientsRingHom (X := X) σ)).comp
      (magnusUnitHom (R := R) (X := X))
  have hgen :
      ∀ x : X,
        h (FreeGroup.of x) =
          magnusUnitHom (R := S) (X := X) (FreeGroup.of x) := by
    intro x
    apply Units.ext
    change
      coefficientsRingHom (X := X) σ
          (magnusSeries (R := R) (FreeGroup.of x)) =
        magnusSeries (R := S) (FreeGroup.of x)
    simp
  have hh :
      h g =
        FreeGroup.lift
          (fun x =>
            magnusUnitHom (R := S) (X := X)
              (FreeGroup.of x)) g :=
    FreeGroup.lift_unique h hgen
  have htarget :
      magnusUnitHom (R := S) (X := X) g =
        FreeGroup.lift
          (fun x =>
            magnusUnitHom (R := S) (X := X)
              (FreeGroup.of x)) g :=
    FreeGroup.lift_unique
      (magnusUnitHom (R := S) (X := X)) (fun _ => rfl)
  have heq : h g = magnusUnitHom (R := S) (X := X) g :=
    hh.trans htarget.symm
  exact congrArg Units.val heq

@[simp]
theorem coefficients_magnus_difference
    (σ : R →+* S) (g : FreeGroup X) :
    coefficientsRingHom (X := X) σ
        (magnusDifference (R := R) g) =
      magnusDifference (R := S) g := by
  simp [magnusDifference, coefficients_magnus_series]

end MSeries
end EChapma
