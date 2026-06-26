import Mathlib.FieldTheory.Galois.Profinite
import Submission.ClassField.CrossedProducts.RelativeGroupMono

/-!
# Chapter IV, Section 4: concrete cochain inflation

This file contains the generic cochain-level inflation construction, separated
from the canonical unramified tower so that the Morita comparison can be proved
without importing local-field infrastructure.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open CProduca

variable (K : Type u) [Field K]
variable {Omega : Type u} [Field Omega] [Algebra K Omega]
variable {F E : FiniteGaloisIntermediateField K Omega}

local instance finiteGaloisUnitsActionF :
    MulDistribMulAction Gal(F/K) Fˣ :=
  Units.mulDistribMulActionRight

local instance finiteGaloisUnitsActionE :
    MulDistribMulAction Gal(E/K) Eˣ :=
  Units.mulDistribMulActionRight

/-- Restriction of Galois automorphisms along an inclusion of finite Galois
intermediate fields. -/
noncomputable def galoisRestrictionHom (hFE : F ≤ E) :
    Gal(E/K) →* Gal(F/K) :=
  (finGaloisGroupMap ((CategoryTheory.homOfLE hFE).op)).hom.hom

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate fields require deeper scalar-tower instance search.
/-- Galois restriction is surjective for finite Galois intermediate fields. -/
theorem galois_restriction_surjective (hFE : F ≤ E) :
    Function.Surjective (galoisRestrictionHom K hFE) := by
  let S : (FiniteGaloisIntermediateField K Omega)ᵒᵖ :=
    Opposite.op E
  let R : (FiniteGaloisIntermediateField K Omega)ᵒᵖ :=
    Opposite.op F
  let f : S ⟶ R := (CategoryTheory.homOfLE hFE).op
  letI : Normal K R.unop := IsGalois.to_normal
  letI : Algebra R.unop S.unop :=
    RingHom.toAlgebra (Subsemiring.inclusion <| CategoryTheory.leOfHom f.1)
  letI : IsScalarTower K R.unop S.unop :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  change Function.Surjective (finGaloisGroupMap f).hom.hom
  unfold finGaloisGroupMap
  exact AlgEquiv.restrictNormalHom_surjective S.unop

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
/-- Restriction acts on an element of the smaller field by applying the
ambient automorphism after including that element in the larger field. -/
theorem galois_restriction_hom
    (hFE : F ≤ E) (sigma : Gal(E/K)) (x : F) :
    IntermediateField.inclusion hFE
        (galoisRestrictionHom K hFE sigma x) =
      sigma (IntermediateField.inclusion hFE x) := by
  letI : Algebra F E :=
    RingHom.toAlgebra (Subsemiring.inclusion hFE)
  letI : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  change algebraMap F E (galoisRestrictionHom K hFE sigma x) =
    sigma (algebraMap F E x)
  unfold galoisRestrictionHom finGaloisGroupMap
  exact AlgEquiv.restrictNormal_commutes sigma F x

/-- Inclusion of coefficient-field unit groups. -/
def coefficientUnitsHom (hFE : F ≤ E) : Fˣ →* Eˣ :=
  Units.map (IntermediateField.inclusion hFE)

set_option synthInstance.maxHeartbeats 100000 in
-- Unfolding restriction through nested subtype fields needs deeper search.
/-- Coefficient inclusion is equivariant for Galois restriction. -/
theorem coefficient_units_hom
    (hFE : F ≤ E) (sigma : Gal(E/K)) (x : Fˣ) :
    coefficientUnitsHom K hFE
        (Units.map (galoisRestrictionHom K hFE sigma) x) =
      Units.map sigma (coefficientUnitsHom K hFE x) := by
  letI : Algebra F E :=
    RingHom.toAlgebra (Subsemiring.inclusion hFE)
  letI : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  apply Units.ext
  change algebraMap F E
      ((galoisRestrictionHom K hFE sigma) (x : F)) =
    sigma (algebraMap F E (x : F))
  unfold galoisRestrictionHom finGaloisGroupMap
  exact AlgEquiv.restrictNormal_commutes sigma F (x : F)

/-- The standard cochain-level inflation: restrict both Galois arguments and
include the coefficient in the larger field. -/
def concreteInflationCocycle (hFE : F ≤ E)
    (c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ)) :
    NMCocycl₂ (G := Gal(E/K)) (M := Eˣ) where
  toFun p := coefficientUnitsHom K hFE
    (c (galoisRestrictionHom K hFE p.1,
      galoisRestrictionHom K hFE p.2))
  isMulCocycle₂ := by
    intro g h j
    change coefficientUnitsHom K hFE
          (c (galoisRestrictionHom K hFE (g * h),
            galoisRestrictionHom K hFE j)) *
        coefficientUnitsHom K hFE
          (c (galoisRestrictionHom K hFE g,
            galoisRestrictionHom K hFE h)) =
      Units.map g (coefficientUnitsHom K hFE
          (c (galoisRestrictionHom K hFE h,
            galoisRestrictionHom K hFE j))) *
        coefficientUnitsHom K hFE
          (c (galoisRestrictionHom K hFE g,
            galoisRestrictionHom K hFE (h * j)))
    rw [← coefficient_units_hom K hFE]
    rw [← map_mul, ← map_mul]
    apply congrArg (coefficientUnitsHom K hFE)
    simpa only [map_mul] using c.isMulCocycle₂
      (galoisRestrictionHom K hFE g)
      (galoisRestrictionHom K hFE h)
      (galoisRestrictionHom K hFE j)
  map_one_fst g := by simp
  map_one_snd g := by simp

@[simp]
theorem concrete_inflation_cocycle (hFE : F ≤ E)
    (c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ))
    (g h : Gal(E/K)) :
    concreteInflationCocycle K hFE c (g, h) =
      coefficientUnitsHom K hFE
        (c (galoisRestrictionHom K hFE g,
          galoisRestrictionHom K hFE h)) :=
  rfl

end

end Submission.CField.LBrauer
