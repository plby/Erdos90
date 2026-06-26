import Towers.ClassField.HasseNorm.IdeleCochainSupport
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Degree-two idèle cohomology as a finite-stage direct limit

Every idèle-valued degree-two cocycle is supported in one of Milne's finite
stages `I_{L,S}`.  Moreover, if a class at one stage dies after inclusion in
the full idèle group, a one-cochain witnessing this already belongs to a
larger finite stage.  These two finite-support statements identify the
degree-two cohomology of the concrete restricted idèle group with the
direct limit of the degree-two cohomology groups of the finite stages.

This is the directed-union passage in Proposition VII.2.5(b).  It is purely
formal once the cochain support results have been established and requires
no additional arithmetic hypothesis.
-/

namespace Towers.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The map on degree-two cohomology induced by enlarging the finite set of
exceptional places. -/
noncomputable def idelesPlacesTransition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    H2 (resizedPlacesRepresentation (K := K) (L := L) S) →ₗ[ULift.{u} ℤ]
      H2 (resizedPlacesRepresentation (K := K) (L := L) T) :=
  (groupCohomology.map (MonoidHom.id Gal(L/K))
    (resizedIdeles (K := K) (L := L) hST) 2).hom

omit [FiniteDimensional K L] in
/-- Enlarging a stage by the reflexive inclusion induces the identity on
degree-two cohomology. -/
theorem resized_places_self
    (S : Finset (NumberFieldPlace K))
    (x : H2 (resizedPlacesRepresentation (K := K) (L := L) S)) :
    idelesPlacesTransition (K := K) (L := L)
      (show S ⊆ S from fun _ h ↦ h) x = x := by
  have htransition :
      resizedIdeles (K := K) (L := L)
          (show S ⊆ S from fun _ h ↦ h) =
        𝟙 (resizedPlacesRepresentation (K := K) (L := L) S) := by
    ext y
    rfl
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedIdeles (K := K) (L := L)
        (show S ⊆ S from fun _ h ↦ h)) 2 x = x
  rw [htransition, groupCohomology.map_id]
  rfl

omit [FiniteDimensional K L] in
/-- Successive enlargements of finite idèle stages induce the composite
transition map on degree-two cohomology. -/
theorem resized_places_comp
    {S T U : Finset (NumberFieldPlace K)}
    (hST : S ⊆ T) (hTU : T ⊆ U)
    (x : H2 (resizedPlacesRepresentation (K := K) (L := L) S)) :
    idelesPlacesTransition (K := K) (L := L) hTU
        (idelesPlacesTransition (K := K) (L := L) hST x) =
      idelesPlacesTransition (K := K) (L := L)
        (hST.trans hTU) x := by
  have htransition :
      resizedIdeles (K := K) (L := L) hST ≫
          resizedIdeles (K := K) (L := L) hTU =
        resizedIdeles (K := K) (L := L)
          (hST.trans hTU) := by
    ext y
    rfl
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedIdeles (K := K) (L := L) hTU) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIdeles (K := K) (L := L) hST) 2 x) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedIdeles (K := K) (L := L)
          (hST.trans hTU)) 2 x
  rw [← htransition]
  exact congrArg (fun f ↦ f x)
    (groupCohomology.map_id_comp
      (resizedIdeles (K := K) (L := L) hST)
      (resizedIdeles (K := K) (L := L) hTU) 2).symm

/-- The degree-two cohomology groups of the finite idèle stages form a
directed system under enlargement of the exceptional set. -/
noncomputable instance idelesDirectedSystem :
    DirectedSystem
      (fun S : Finset (NumberFieldPlace K) ↦
        H2 (resizedPlacesRepresentation (K := K) (L := L) S))
      (fun {_ _} h ↦ idelesPlacesTransition
        (K := K) (L := L) h) where
  map_self := resized_places_self (K := K) (L := L)
  map_map := by
    intro k j i hST hTU x
    exact resized_places_comp
      (K := K) (L := L) hST hTU x

/-- The directed limit of degree-two cohomology over Milne's finite idèle
stages. -/
abbrev ResizedPlacesLimit (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  DirectLimit
    (fun S : Finset (NumberFieldPlace K) ↦
      H2 (resizedPlacesRepresentation (K := K) (L := L) S))
    (fun _ _ h ↦ idelesPlacesTransition
      (K := K) (L := L) h)

/-- The map from the degree-two cohomology of one finite stage to the
degree-two cohomology of the full idèle representation. -/
noncomputable def resizedPlacesInclusion
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedPlacesRepresentation (K := K) (L := L) S) →ₗ[ULift.{u} ℤ]
      H2 (resizedConcreteRepresentation K L) :=
  (groupCohomology.map (MonoidHom.id Gal(L/K))
    (resizedInclusion (K := K) (L := L) S) 2).hom

/-- Inclusion into the full idèle representation is compatible with
enlarging a finite stage. -/
theorem ideles_places_inclusion
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : H2 (resizedPlacesRepresentation (K := K) (L := L) S)) :
    resizedPlacesInclusion (K := K) (L := L) T
        (idelesPlacesTransition (K := K) (L := L) hST x) =
      resizedPlacesInclusion (K := K) (L := L) S x := by
  have hinclusion :
      resizedIdeles (K := K) (L := L) hST ≫
          resizedInclusion (K := K) (L := L) T =
        resizedInclusion (K := K) (L := L) S := by
    ext y
    rfl
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedInclusion (K := K) (L := L) T) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIdeles (K := K) (L := L) hST) 2 x) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedInclusion (K := K) (L := L) S) 2 x
  rw [← hinclusion]
  exact congrArg (fun f ↦ f x)
    (groupCohomology.map_id_comp
      (resizedIdeles (K := K) (L := L) hST)
      (resizedInclusion (K := K) (L := L) T) 2).symm

/-- The canonical map from the finite-stage direct limit to the cohomology
of the concrete restricted idèle representation. -/
noncomputable def resizedLimitConcrete :
    ResizedPlacesLimit K L →+
      H2 (resizedConcreteRepresentation K L) where
  toFun := DirectLimit.lift
    (ι := Finset (NumberFieldPlace K))
    (F := fun S : Finset (NumberFieldPlace K) ↦
      H2 (resizedPlacesRepresentation (K := K) (L := L) S))
    (fun _ _ h ↦ idelesPlacesTransition
      (K := K) (L := L) h)
    (fun (S : Finset (NumberFieldPlace K))
        (x : H2 (resizedPlacesRepresentation
          (K := K) (L := L) S)) ↦
      resizedPlacesInclusion (K := K) (L := L) S x)
    (fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T)
        (x : H2 (resizedPlacesRepresentation
          (K := K) (L := L) S)) ↦
      (ideles_places_inclusion
        (K := K) (L := L) h x).symm)
  map_zero' := by
    rw [DirectLimit.zero_def (∅ : Finset (NumberFieldPlace K)),
      DirectLimit.lift_def]
    exact map_zero (resizedPlacesInclusion
      (K := K) (L := L) ∅)
  map_add' q q' := by
    induction q, q' using DirectLimit.induction₂ with
    | _ S x y =>
        rw [DirectLimit.add_def, DirectLimit.lift_def,
          DirectLimit.lift_def, DirectLimit.lift_def]
        exact map_add (resizedPlacesInclusion
          (K := K) (L := L) S) x y

/-- Every idèle cohomology class comes from the finite-stage direct limit. -/
theorem ideles_places_limit :
    Function.Surjective
      (resizedLimitConcrete (K := K) (L := L)) := by
  intro q
  obtain ⟨S, qS, hqS⟩ :=
    ideles_h_preimage (K := K) (L := L) q
  refine ⟨(⟦⟨S, qS⟩⟧ : ResizedPlacesLimit K L), ?_⟩
  change resizedPlacesInclusion (K := K) (L := L) S qS = q
  exact hqS

/-- A direct-limit class mapping to zero is already zero at a sufficiently
large finite idèle stage. -/
theorem ideles_limit_injective :
    Function.Injective
      (resizedLimitConcrete (K := K) (L := L)) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hzero : resizedLimitConcrete
      (K := K) (L := L) (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  let F : Finset (NumberFieldPlace K) → Type u :=
    fun S : Finset (NumberFieldPlace K) ↦
    H2 (resizedPlacesRepresentation (K := K) (L := L) S)
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) ↦
    idelesPlacesTransition (K := K) (L := L) h
  obtain ⟨S, qS, hq⟩ := DirectLimit.exists_eq_mk f (q - q')
  rw [hq] at hzero ⊢
  have hstage : groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedInclusion (K := K) (L := L) S) 2 qS = 0 := by
    exact hzero
  obtain ⟨T, hST, hT⟩ :=
    ideles_places_h
      (K := K) (L := L) S qS hstage
  change f S T hST qS = 0 at hT
  calc
    (⟦⟨S, qS⟩⟧ : DirectLimit F f) =
        ⟦⟨T, f S T hST qS⟩⟧ :=
      DirectLimit.eq_of_le (f := f) ⟨S, qS⟩ T hST
    _ = ⟦⟨T, 0⟩⟧ := congrArg (fun z ↦ (⟦⟨T, z⟩⟧ : DirectLimit F f)) hT
    _ = 0 := (DirectLimit.zero_def T).symm

/-- Degree-two cohomology of the concrete restricted idèle group is the
direct limit of the degree-two cohomology groups of its finite stages. -/
noncomputable def resizedHLimit :
    ResizedPlacesLimit K L ≃+
      H2 (resizedConcreteRepresentation K L) :=
  AddEquiv.ofBijective
    (resizedLimitConcrete (K := K) (L := L))
    ⟨ideles_limit_injective
      (K := K) (L := L),
     ideles_places_limit
      (K := K) (L := L)⟩

end

end Towers.CField.HNorm
