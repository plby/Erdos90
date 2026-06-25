import Towers.ClassField.ReciprocityExistence.FieldCup
import Towers.ClassField.ReciprocityExistence.IdeleCup
import Towers.ClassField.BrauerLocalization.H2Naturality
import Towers.ClassField.BrauerLocalization.KernelLiftingAssembly

/-!
# Naturality of the universe-polymorphic cup maps

The principal-idèle embedding maps Milne's literal field cocycle
`(g,h) |-> a ^ n(g,h)` to the corresponding literal idèle cocycle.
-/

namespace Towers.CField.RExist

open scoped IsMulCommutative
open CategoryTheory
open IsDedekindDomain NumberField
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.NIndex
open Towers.CField.HNorm
open Towers.CField.BLoc
open groupCohomology

noncomputable section

universe u

section CoefficientNaturality

variable {G M N : Type u} [Group G]
  [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N]

/-- An equivariant multiplicative coefficient map, linearized over the
universe lift of `ℤ`. -/
noncomputable def uliftCoefficientHom
    (f : M →* N) (hf : ∀ g : G, ∀ x : M, f (g • x) = g • f x) :
    uliftMulRepresentation (G := G) (M := M) ⟶
      uliftMulRepresentation (G := G) (M := N) := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (f x.toMul)
          map_add' := fun x y => congrArg Additive.ofMul (map_mul f x.toMul y.toMul)
          map_smul' := fun r x => by
            change Additive.ofMul (f (x.toMul ^ r.down)) =
              Additive.ofMul ((f x.toMul) ^ r.down)
            exact congrArg Additive.ofMul (map_zpow f x.toMul r.down) }
      isIntertwining' := fun g => by
        ext x
        exact congrArg Additive.ofMul (hf g x.toMul) }

/-- The resized categorical realization of multiplicative `H²` is natural
under equivariant coefficient maps. -/
theorem multiplicative_u_coefficients
    (f : M →* N) (hf : ∀ g : G, ∀ x : M, f (g • x) = g • f x)
    (x : MHTwo G M) :
    groupCohomology.map (MonoidHom.id G)
        (uliftCoefficientHom f hf) 2
        (multiplicativeLiftAdditive x) =
      multiplicativeLiftAdditive
        (MHTwo.mapCoefficientsHom f hf x) := by
  obtain ⟨c, rfl⟩ := MHTwo.exists_mk_eq x
  rw [MHTwo.coefficients_hom_mk,
    multiplicative_additive_mk,
    multiplicative_additive_mk,
    normalizedCocycleU,
    normalizedCocycleU,
    H2π_comp_map_apply]
  congr 1

end CoefficientNaturality

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

attribute [local instance] Units.mulDistribMulActionRight

private noncomputable abbrev ideleAction :
    IAData (K := K) (L := L) :=
  concreteActionData

local instance concreteIdeleMulActionForCupNaturality :
    MulDistribMulAction Gal(L/K)
      (IdeleGroup (NumberField.RingOfIntegers L) L) :=
  (ideleAction K L).action

private def principalIdeleEquivariant
    (g : Gal(L/K)) (x : Lˣ) :
    principalIdele (NumberField.RingOfIntegers L) L (g • x) =
      g • principalIdele (NumberField.RingOfIntegers L) L x := by
  exact ((ideleAction K L).smul_principalIdele g x).symm

omit [FiniteDimensional K L] in
/-- The field and idèle cup classes already commute before passing from
multiplicative cocycles to categorical cohomology. -/
theorem multiplicative_cup_principal
    (a : Kˣ) (chi : CharacterModule (Additive Gal(L/K))) :
    MHTwo.mapCoefficientsHom
        (principalIdele (NumberField.RingOfIntegers L) L)
        (principalIdeleEquivariant K L)
        (multiplicativeCupClass K L a chi) =
      globalMultiplicativeClass K L
        (principalIdele (NumberField.RingOfIntegers K) K a) chi := by
  rw [multiplicativeCupClass, globalMultiplicativeClass,
    invariantCharacterCup, invariantCharacterCup,
    MHTwo.coefficients_hom_mk]
  apply congrArg MHTwo.mk
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change principalIdele (NumberField.RingOfIntegers L) L
      ((Units.map (algebraMap K L).toMonoidHom a) ^
        rationalBoundaryExponent chi g h) =
    (ideleExtensionMonoid (K := K) (L := L)
      (principalIdele (NumberField.RingOfIntegers K) K a)) ^
        rationalBoundaryExponent chi g h
  rw [map_zpow, idele_extension_principal]

/-- The coefficient morphism between the two direct multiplicative
presentations of global units and idèles. -/
noncomputable def uliftPrincipalHom :
    hasseGlobalRepresentation K L ⟶
      uliftMulRepresentation
        (G := Gal(L/K))
        (M := IdeleGroup (NumberField.RingOfIntegers L) L) :=
  uliftCoefficientHom
    (principalIdele (NumberField.RingOfIntegers L) L)
    (principalIdeleEquivariant K L)

omit [IsMulCommutative Gal(L/K)] in
/-- The direct multiplicative coefficient morphism is the same morphism as
the principal-idèle arrow in the resized idèle short exact sequence. -/
theorem resized_idele_path :
    (resizedIsoHasse K L).inv ≫
        (resizedShortComplex K L).f =
      uliftPrincipalHom K L ≫
        (multiplicativeIsoConcrete K L).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

omit [IsMulCommutative Gal(L/K)] in
/-- Functoriality carries the equality of the two principal-idèle
coefficient paths to an equality of the corresponding maps on `H²`.  Keeping
this as an equality of linear maps prevents later proofs from unfolding the
large resized representations while comparing applications. -/
theorem resized_principal_path :
    groupCohomology.map
          (A := hasseGlobalRepresentation K L)
          (B := resizedRepresentation K L)
          (MonoidHom.id Gal(L/K))
          (resizedIsoHasse K L).inv 2 ≫
        groupCohomology.map
          (A := resizedRepresentation K L)
          (B := resizedConcreteRepresentation K L)
          (MonoidHom.id Gal(L/K))
          (resizedShortComplex K L).f 2 =
      groupCohomology.map
          (A := hasseGlobalRepresentation K L)
          (B := uliftMulRepresentation
            (G := Gal(L/K))
            (M := IdeleGroup (NumberField.RingOfIntegers L) L))
          (MonoidHom.id Gal(L/K))
          (uliftPrincipalHom K L) 2 ≫
        groupCohomology.map
          (A := uliftMulRepresentation
            (G := Gal(L/K))
            (M := IdeleGroup (NumberField.RingOfIntegers L) L))
          (B := resizedConcreteRepresentation K L)
          (MonoidHom.id Gal(L/K))
          (multiplicativeIsoConcrete K L).hom 2 := by
  rw [← groupCohomology.map_id_comp, ← groupCohomology.map_id_comp]
  exact congrArg
    (fun q : hasseGlobalRepresentation K L ⟶
        resizedConcreteRepresentation K L ↦
      groupCohomology.map
        (A := hasseGlobalRepresentation K L)
        (B := resizedConcreteRepresentation K L)
        (MonoidHom.id Gal(L/K)) q 2)
    (resized_idele_path K L)

omit [FiniteDimensional K L] in
/-- At the resized cohomology level, the principal-idèle coefficient map
carries the literal field cup class to the literal idèle cup class. -/
theorem global_multiplicative_raw
    (a : Kˣ) (chi : CharacterModule (Additive Gal(L/K))) :
    groupCohomology.map (MonoidHom.id Gal(L/K))
        (uliftPrincipalHom K L) 2
        (multiplicativeLiftAdditive
          (multiplicativeCupClass K L a chi)) =
      multiplicativeLiftAdditive
        (globalMultiplicativeClass K L
          (principalIdele (NumberField.RingOfIntegers K) K a) chi) := by
  letI : MulDistribMulAction Gal(L/K)
      ((InfiniteAdeleRing L)ˣ ×
        FiniteIdeles (NumberField.RingOfIntegers L) L) :=
    (ideleAction K L).action
  calc
    _ = multiplicativeLiftAdditive
        (MHTwo.mapCoefficientsHom
          (principalIdele (NumberField.RingOfIntegers L) L)
          (principalIdeleEquivariant K L)
          (multiplicativeCupClass K L a chi)) := by
      change groupCohomology.map (MonoidHom.id Gal(L/K))
          (uliftCoefficientHom
            (principalIdele (NumberField.RingOfIntegers L) L)
            (principalIdeleEquivariant K L)) 2
          (multiplicativeLiftAdditive
            (multiplicativeCupClass K L a chi)) = _
      exact multiplicative_u_coefficients
        (principalIdele (NumberField.RingOfIntegers L) L)
        (principalIdeleEquivariant K L)
        (multiplicativeCupClass K L a chi)
    _ = _ := congrArg multiplicativeLiftAdditive
      (multiplicative_cup_principal K L a chi)

set_option maxHeartbeats 500000 in
-- Comparing the two universe-resized coefficient paths requires unfolding
-- the dependent idèle action and both categorical `H²` realizations.
/-- The resized idèle `H²` class of a principal idèle is the image of the
corresponding relative Brauer cup class. -/
theorem global_multiplicative_principal
    (a : Kˣ) (chi : CharacterModule (Additive Gal(L/K))) :
    relativeResized2 K L
        (multiplicativeFieldCup K L chi (Additive.ofMul a)) =
      globalMultiplicative2 K L
        (principalIdele (NumberField.RingOfIntegers K) K a) chi := by
  letI : MulDistribMulAction Gal(L/K)
      ((InfiniteAdeleRing L)ˣ ×
        FiniteIdeles (NumberField.RingOfIntegers L) L) :=
    (ideleAction K L).action
  let c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ) :=
    invariantCupCocycle
      (Units.map (algebraMap K L).toMonoidHom a)
      (multiplicative_base_fixed K L a) chi
  let x : H2 (hasseGlobalRepresentation K L) :=
    multiplicativeLiftAdditive
      (multiplicativeCupClass K L a chi)
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedShortComplex K L).f 2
      (relativeBrauerResized K L
        (Additive.ofMul
          (CProduc.hRelativeBrauer K L
            (MHTwo.mk c)))) = _
  rw [show CProduc.hRelativeBrauer K L
      (MHTwo.mk c) =
        CProduc.relativeBrauerClass K L c by rfl,
    relative_brauer_resized]
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedShortComplex K L).f 2
      (groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedIsoHasse K L).inv 2 x) = _
  calc
    groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedShortComplex K L).f 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIsoHasse K L).inv 2 x) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (multiplicativeIsoConcrete K L).hom 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (uliftPrincipalHom K L) 2 x) := by
            exact congrArg (fun q => q x)
              (resized_principal_path K L)
    _ = groupCohomology.map (MonoidHom.id Gal(L/K))
        (multiplicativeIsoConcrete K L).hom 2
        (multiplicativeLiftAdditive
          (globalMultiplicativeClass K L
            (principalIdele (NumberField.RingOfIntegers K) K a) chi)) := by
              exact congrArg
                (fun y : H2 (uliftMulRepresentation
                    (G := Gal(L/K))
                    (M := IdeleGroup (NumberField.RingOfIntegers L) L)) ↦
                  groupCohomology.map
                    (A := uliftMulRepresentation
                      (G := Gal(L/K))
                      (M := IdeleGroup (NumberField.RingOfIntegers L) L))
                    (B := resizedConcreteRepresentation K L)
                    (MonoidHom.id Gal(L/K))
                    (multiplicativeIsoConcrete K L).hom 2 y)
                (by simpa only [x] using
                  (global_multiplicative_raw K L a chi))
    _ = globalMultiplicative2 K L
        (principalIdele (NumberField.RingOfIntegers K) K a) chi := rfl

/-- The left square in Lemma VII.8.5 for the actual relative-Brauer
localization and the universe-polymorphic literal cup maps. -/
theorem global_multiplicative_naturality
    (data : BData K) :
    CupProductNaturality
      (principalIdele (NumberField.RingOfIntegers K) K)
      (relativeLocalization K data L)
      (multiplicativeFieldCup K L)
      (multiplicativeIdeleCup K L) := by
  intro chi a
  let beta : Additive (relativeBrauerGroup K L) :=
    multiplicativeFieldCup K L chi (Additive.ofMul a)
  have hlocalization :=
    localization_brauer_cohomological
      K L (completionChoice K L) data beta
  change data.localization.localization
      (Additive.ofMul (beta.toMul : BrauerGroup K)) =
    multiplicativeIdeleCup K L chi
      (Additive.ofMul
        (principalIdele (NumberField.RingOfIntegers K) K a))
  rw [hlocalization]
  apply congrArg
    (brauerDirectInclusion K L
      (completionChoice K L))
  change (directRelativeBrauer
      K L (completionChoice K L))
      (resizedHDecomposition
        (K := K) (L := L)
        (relativeResized2 K L beta)) =
    (directRelativeBrauer
      K L (completionChoice K L))
      (resizedHDecomposition
        (K := K) (L := L)
        (globalMultiplicative2 K L
          (principalIdele (NumberField.RingOfIntegers K) K a) chi))
  rw [show beta = multiplicativeFieldCup K L chi
      (Additive.ofMul a) by rfl,
    global_multiplicative_principal K L a chi]

end

end Towers.CField.RExist
