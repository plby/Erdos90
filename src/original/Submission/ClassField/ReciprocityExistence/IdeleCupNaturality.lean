import Submission.ClassField.ReciprocityExistence.GlobalFieldCup
import Submission.ClassField.ReciprocityExistence.GlobalIdeleCup

/-!
# Naturality of the field and idèle cup products

The diagonal embedding `Lˣ → I_L` carries the literal field cup class
`a ∪ δχ` to the literal idèle cup class of the principal idèle of `a`.
-/

namespace Submission.CField.RExist

open CategoryTheory MonoidalCategory Rep
open scoped MonoidalCategory
open IsDedekindDomain NumberField
open Submission.CField.COps.CPBuild
open Submission.CField.LRecip
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex

noncomputable section

variable (K L : Type) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

private noncomputable abbrev ideleAction :
    IAData (K := K) (L := L) :=
  concreteActionData

private abbrev ideleRep := (ideleAction K L).representation

omit [FiniteDimensional K L] in
/-- The equivariant principal-idèle embedding carries the invariant attached
to a base-field unit to the invariant attached to its principal idèle. -/
theorem global_base_principal (a : Kˣ) :
    ((Rep.invariantsFunctor ℤ Gal(L/K)).map
      (ideleAction K L).principalIdeleHom).hom
        (globalUnitInvariant K L a) =
      globalBaseInvariant K L
        (principalIdele (NumberField.RingOfIntegers K) K a) := by
  apply Subtype.ext
  change Additive.ofMul
      (principalIdele (NumberField.RingOfIntegers L) L
        (Units.map (algebraMap K L) a)) =
    Additive.ofMul
      (ideleExtensionMonoid (K := K) (L := L)
        (principalIdele (NumberField.RingOfIntegers K) K a))
  congr 1
  exact (idele_extension_principal (K := K) (L := L) a).symm

omit [FiniteDimensional K L] in
/-- Degree-zero cohomology sends a base-field unit to the class of its
principal idèle. -/
theorem global_0_principal (a : Kˣ) :
    groupCohomology.map (MonoidHom.id Gal(L/K))
        (ideleAction K L).principalIdeleHom 0
        (globalH0 K L a) =
      globalBase0 K L
        (principalIdele (NumberField.RingOfIntegers K) K a) := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.H0Iso (ideleRep K L)).hom).1 inferInstance
  have hmap :
      (groupCohomology.H0Iso (ideleRep K L)).hom
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (ideleAction K L).principalIdeleHom 0
          (globalH0 K L a)) =
        ((Rep.invariantsFunctor ℤ Gal(L/K)).map
          (ideleAction K L).principalIdeleHom).hom
            (globalUnitInvariant K L a) := by
              have h := groupCohomology.map_id_comp_H0Iso_hom
                (ideleAction K L).principalIdeleHom
              have h' := congrArg (fun f => f (globalH0 K L a)) h
              change (groupCohomology.H0Iso (ideleRep K L)).hom
                  (groupCohomology.map (MonoidHom.id Gal(L/K))
                    (ideleAction K L).principalIdeleHom 0
                    (globalH0 K L a)) =
                ((Rep.invariantsFunctor ℤ Gal(L/K)).map
                  (ideleAction K L).principalIdeleHom).hom
                    ((groupCohomology.H0Iso
                      (Rep.ofAlgebraAutOnUnits K L)).hom
                        (globalH0 K L a)) at h'
              rw [globalH0,
                groupCohomology.π_comp_H0Iso_hom_apply,
                Iso.inv_hom_id_apply] at h'
              exact h'
  rw [hmap, global_base_principal]
  simp only [globalBase0,
    groupCohomology.π_comp_H0Iso_hom_apply,
    Iso.inv_hom_id_apply]

/-- The diagonal embedding carries the literal field cup class to the
literal idèle cup class of the corresponding principal idèle. -/
theorem global_boundary_principal
    (a : Kˣ) (chi : RationalCharacter Gal(L/K)) :
    groupCohomology.map (MonoidHom.id Gal(L/K))
        (ideleAction K L).principalIdeleHom 2
        (globalCharacterBoundary K L a chi) =
      globalCupBoundary K L
        (principalIdele (NumberField.RingOfIntegers K) K a) chi := by
  let M : Rep ℤ Gal(L/K) := Rep.ofAlgebraAutOnUnits K L
  let I : Rep ℤ Gal(L/K) := ideleRep K L
  let T : Rep ℤ Gal(L/K) := Rep.trivial ℤ Gal(L/K) ℤ
  let f : M ⟶ I := (ideleAction K L).principalIdeleHom
  let x : groupCohomology M 0 := globalH0 K L a
  let y : groupCohomology T 2 := characterBoundary Gal(L/K) chi
  let z : groupCohomology (M ⊗ T : Rep ℤ Gal(L/K)) 2 :=
    cupCohomology M T 0 2 x y
  have hunit :
      groupCohomology.map (MonoidHom.id Gal(L/K)) (𝟙 T) 2 y = y := by
    rw [groupCohomology.map_id]
    rfl
  have hcup :
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (f ⊗ₘ 𝟙 T) 2 z =
        cupCohomology I T 0 2
          (groupCohomology.map (MonoidHom.id Gal(L/K)) f 0 x) y := by
    simpa only [z, hunit] using
      (cupCohomology_natural f (𝟙 T) 0 2 x y)
  have hright :
      (f ⊗ₘ 𝟙 T) ≫ (ρ_ I).hom = (ρ_ M).hom ≫ f := by
    exact MonoidalCategory.rightUnitor_naturality f
  change groupCohomology.map (MonoidHom.id Gal(L/K)) f 2
        (groupCohomology.map (MonoidHom.id Gal(L/K)) (ρ_ M).hom 2 z) =
      groupCohomology.map (MonoidHom.id Gal(L/K)) (ρ_ I).hom 2
        (cupCohomology I T 0 2
          (globalBase0 K L
            (principalIdele (NumberField.RingOfIntegers K) K a)) y)
  calc
    groupCohomology.map (MonoidHom.id Gal(L/K)) f 2
        (groupCohomology.map (MonoidHom.id Gal(L/K)) (ρ_ M).hom 2 z) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        ((ρ_ M).hom ≫ f) 2 z := by
          exact (congrArg (fun q => q z)
            (groupCohomology.map_id_comp (ρ_ M).hom f 2)).symm
    _ = groupCohomology.map (MonoidHom.id Gal(L/K))
        ((f ⊗ₘ 𝟙 T) ≫ (ρ_ I).hom) 2 z := by
          exact congrArg
            (fun q ↦ groupCohomology.map
              (MonoidHom.id Gal(L/K)) q 2 z) hright.symm
    _ = groupCohomology.map (MonoidHom.id Gal(L/K)) (ρ_ I).hom 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (f ⊗ₘ 𝟙 T) 2 z) := by
            exact congrArg (fun q => q z)
              (groupCohomology.map_id_comp (f ⊗ₘ 𝟙 T) (ρ_ I).hom 2)
    _ = groupCohomology.map (MonoidHom.id Gal(L/K)) (ρ_ I).hom 2
        (cupCohomology I T 0 2
          (groupCohomology.map (MonoidHom.id Gal(L/K)) f 0 x) y) := by
            rw [hcup]
    _ = groupCohomology.map (MonoidHom.id Gal(L/K)) (ρ_ I).hom 2
        (cupCohomology I T 0 2
          (globalBase0 K L
            (principalIdele (NumberField.RingOfIntegers K) K a)) y) := by
              rw [global_0_principal K L a]

end

end Submission.CField.RExist
