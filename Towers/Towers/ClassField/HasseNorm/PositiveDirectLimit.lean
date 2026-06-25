import Towers.ClassField.HasseNorm.IdelePositiveStage
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Positive idèle cohomology as a finite-stage direct limit

For a finite Galois group, every finite-degree idèle-valued cochain has a
common finite exceptional set.  The same is true of a cochain witnessing
that a cocycle is a boundary.  Consequently positive group cohomology of the
restricted idèle group is the direct limit of the cohomology of Milne's
finite stages, uniformly in the degree.
-/

namespace Towers.CField.HNorm

open CategoryTheory CategoryTheory.Limits Representation
open IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- A cocycle representative is zero in cohomology exactly when it is the
differential of a cochain in the preceding degree. -/
theorem cohomology_pi_boundary
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (r : ℕ) (x : cocycles A (r + 1)) :
    π A (r + 1) x = 0 ↔
      ∃ a : (Fin r → G) → A, toCocycles A r (r + 1) a = x := by
  constructor
  · intro hx
    let C := inhomogeneousCochains A
    let S := ShortComplex.mk (C.toCycles r (r + 1))
      (C.homologyπ (r + 1)) (by simp)
    have hExact : S.Exact :=
      S.exact_of_g_is_cokernel
        (C.homologyIsCokernel r (r + 1) (by simp))
    have hrange :=
      (ShortComplex.moduleCat_exact_iff_range_eq_ker S).1 hExact
    have hxker : x ∈ LinearMap.ker (C.homologyπ (r + 1)).hom := hx
    rw [← hrange] at hxker
    exact hxker
  · rintro ⟨a, rfl⟩
    exact ConcreteCategory.congr_hom
      ((inhomogeneousCochains A).toCycles_comp_homologyπ r (r + 1)) a

/-- The underlying cochain of the image of a cocycle is obtained by applying
the coefficient morphism pointwise.  This scalar-polymorphic version avoids
repeatedly unfolding the rather large homological-complex construction. -/
theorem i_cocycles_general
    {k G : Type u} [CommRing k] [Group G]
    {A B : Rep k G} (f : A ⟶ B) (n : ℕ) (x : cocycles A n) :
    iCocycles B n (cocyclesMap (MonoidHom.id G) f n x) =
      fun g ↦ f (iCocycles A n x g) := by
  have h := congrArg (fun q ↦ q x)
    (HomologicalComplex.cyclesMap_i (cochainsMap (MonoidHom.id G) f) n)
  simpa only [ConcreteCategory.comp_apply,
    cochainsMap_id_f_hom_eq_compLeft, LinearMap.compLeft_apply] using h

/-- Naturality of the inhomogeneous differential for a coefficient morphism,
in the pointwise form used by the finite-stage descent argument. -/
theorem cochain_differential_general
    {k G : Type u} [CommRing k] [Group G]
    {A B : Rep k G} (f : A ⟶ B) (n : ℕ)
    (a : (Fin n → G) → A) :
    ((cochainsMap (MonoidHom.id G) f).f (n + 1))
        ((inhomogeneousCochains A).d n (n + 1) a) =
      (inhomogeneousCochains B).d n (n + 1)
        (((cochainsMap (MonoidHom.id G) f).f n) a) := by
  have h := congrArg (fun q ↦ q a)
    ((cochainsMap (MonoidHom.id G) f).comm n (n + 1))
  simpa only [ConcreteCategory.comp_apply] using h.symm

/-- Every idèle-valued cochain in a fixed finite degree is contained in one
finite idèle stage. -/
theorem ideles_idele_cochain
    (n : ℕ)
    (f : (Fin n → Gal(L/K)) → resizedConcreteRepresentation K L) :
    ∃ S : Finset (NumberFieldPlace K),
      ∀ g, (f g).toMul ∈ idelesAtPlaces (K := K) (L := L) S :=
  ideles_places_family
    (K := K) (L := L) (fun g ↦ (f g).toMul)

/-- Lift a supported cochain to its finite idèle stage. -/
noncomputable def resizedIdeleCochain
    (S : Finset (NumberFieldPlace K)) (n : ℕ)
    (f : (Fin n → Gal(L/K)) → resizedConcreteRepresentation K L)
    (hf : ∀ g, (f g).toMul ∈ idelesAtPlaces (K := K) (L := L) S) :
    (Fin n → Gal(L/K)) →
      resizedPlacesRepresentation (K := K) (L := L) S :=
  fun g ↦ Additive.ofMul ⟨(f g).toMul, hf g⟩

@[simp]
theorem places_inclusion_cochain
    (S : Finset (NumberFieldPlace K)) (n : ℕ)
    (f : (Fin n → Gal(L/K)) → resizedConcreteRepresentation K L)
    (hf : ∀ g, (f g).toMul ∈ idelesAtPlaces (K := K) (L := L) S)
    (g : Fin n → Gal(L/K)) :
    (resizedInclusion (K := K) (L := L) S).hom
      (resizedIdeleCochain S n f hf g) = f g :=
  rfl

/-- A supported cocycle remains a cocycle after lifting to its finite
stage. -/
theorem lift_cochain_cocycle
    (S : Finset (NumberFieldPlace K)) (n : ℕ)
    (x : cocycles (resizedConcreteRepresentation K L) n)
    (hx : ∀ g,
      (iCocycles (resizedConcreteRepresentation K L) n x g).toMul ∈
        idelesAtPlaces (K := K) (L := L) S) :
    inhomogeneousCochains.d
      (resizedPlacesRepresentation (K := K) (L := L) S) n
      (resizedIdeleCochain S n
        (iCocycles (resizedConcreteRepresentation K L) n x) hx) = 0 := by
  apply funext
  intro g
  apply resized_inclusion_injective (K := K) (L := L) S
  have hcomm := ConcreteCategory.congr_hom
    ((cochainsMap (MonoidHom.id Gal(L/K))
      (resizedInclusion (K := K) (L := L) S)).comm n (n + 1))
      (resizedIdeleCochain S n
        (iCocycles (resizedConcreteRepresentation K L) n x) hx)
  have hmap : ((cochainsMap (MonoidHom.id Gal(L/K))
      (resizedInclusion (K := K) (L := L) S)).f n)
      (resizedIdeleCochain S n
        (iCocycles (resizedConcreteRepresentation K L) n x) hx) =
        iCocycles (resizedConcreteRepresentation K L) n x := by
    rfl
  have hxzero :
      (inhomogeneousCochains
        (resizedConcreteRepresentation K L)).d n (n + 1)
      (iCocycles (resizedConcreteRepresentation K L) n x) = 0 := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom
        ((inhomogeneousCochains
          (resizedConcreteRepresentation K L)).iCycles_d n (n + 1)) x
  change (resizedInclusion (K := K) (L := L) S).hom
      (inhomogeneousCochains.d
        (resizedPlacesRepresentation (K := K) (L := L) S) n
        (resizedIdeleCochain S n
          (iCocycles (resizedConcreteRepresentation K L) n x) hx) g) = _
  have hg := congrFun hcomm g
  simp only [ConcreteCategory.comp_apply] at hg
  rw [hmap, hxzero] at hg
  change (0 : resizedConcreteRepresentation K L) =
    (resizedInclusion (K := K) (L := L) S).hom
      (((inhomogeneousCochains
        (resizedPlacesRepresentation (K := K) (L := L) S)).d n (n + 1))
          (resizedIdeleCochain S n
            (iCocycles (resizedConcreteRepresentation K L) n x) hx) g) at hg
  rw [inhomogeneousCochains.d_def] at hg
  rw [show (0 : (Fin (n + 1) → Gal(L/K)) →
      resizedPlacesRepresentation (K := K) (L := L) S) g = 0 by rfl,
    map_zero]
  exact hg.symm

/-- Lift a supported cocycle as an element of the finite-stage cocycle
module. -/
noncomputable def liftResizedCocycle
    (S : Finset (NumberFieldPlace K)) (n : ℕ)
    (x : cocycles (resizedConcreteRepresentation K L) n)
    (hx : ∀ g,
      (iCocycles (resizedConcreteRepresentation K L) n x g).toMul ∈
        idelesAtPlaces (K := K) (L := L) S) :
    cocycles (resizedPlacesRepresentation (K := K) (L := L) S) n :=
  cocyclesMk
    (resizedIdeleCochain S n
      (iCocycles (resizedConcreteRepresentation K L) n x) hx)
    (lift_cochain_cocycle S n x hx)

/-- Mapping a lifted cocycle back to the full idèle representation recovers
the original cocycle. -/
theorem cocycles_resized_cocycle
    (S : Finset (NumberFieldPlace K)) (n : ℕ)
    (x : cocycles (resizedConcreteRepresentation K L) n)
    (hx : ∀ g,
      (iCocycles (resizedConcreteRepresentation K L) n x g).toMul ∈
        idelesAtPlaces (K := K) (L := L) S) :
    cocyclesMap (MonoidHom.id Gal(L/K))
        (resizedInclusion (K := K) (L := L) S) n
        (liftResizedCocycle S n x hx) = x := by
  apply (ModuleCat.mono_iff_injective
    (iCocycles (resizedConcreteRepresentation K L) n)).1 inferInstance
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (MonoidHom.id Gal(L/K))
        (resizedInclusion (K := K) (L := L) S)) n)
      (liftResizedCocycle S n x hx)
  calc
    iCocycles (resizedConcreteRepresentation K L) n
        (cocyclesMap (MonoidHom.id Gal(L/K))
          (resizedInclusion (K := K) (L := L) S) n
          (liftResizedCocycle S n x hx)) =
      ((cochainsMap (MonoidHom.id Gal(L/K))
        (resizedInclusion (K := K) (L := L) S)).f n)
        (iCocycles
          (resizedPlacesRepresentation (K := K) (L := L) S) n
          (liftResizedCocycle S n x hx)) := by
            simpa only [ConcreteCategory.comp_apply] using h
    _ = iCocycles (resizedConcreteRepresentation K L) n x := by
      apply funext
      intro g
      unfold liftResizedCocycle
      rw [iCocycles_mk]
      rfl

/-- Every positive-degree idèle cohomology class comes from a finite idèle
stage. -/
theorem ideles_cohomology_preimage
    (r : ℕ)
    (q : groupCohomology (resizedConcreteRepresentation K L) (r + 1)) :
    ∃ (S : Finset (NumberFieldPlace K))
      (qS : groupCohomology
        (resizedPlacesRepresentation (K := K) (L := L) S) (r + 1)),
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedInclusion (K := K) (L := L) S) (r + 1) qS = q := by
  induction q using groupCohomology_induction_on with
  | h x =>
      obtain ⟨S, hx⟩ := ideles_idele_cochain
        (K := K) (L := L) (r + 1)
        (iCocycles (resizedConcreteRepresentation K L) (r + 1) x)
      refine ⟨S, π _ (r + 1) (liftResizedCocycle S (r + 1) x hx), ?_⟩
      rw [π_map_apply]
      rw [cocycles_resized_cocycle]

/-! The transition-to-zero lemma and the direct-limit equivalence are
proved below after packaging the degree-uniform transition system. -/

/-- The map on cohomology induced by enlarging the finite exceptional set. -/
noncomputable def resizedCohomologyTransition
    (n : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    groupCohomology
        (resizedPlacesRepresentation (K := K) (L := L) S) n →ₗ[ULift.{u} ℤ]
      groupCohomology
        (resizedPlacesRepresentation (K := K) (L := L) T) n :=
  (groupCohomology.map (MonoidHom.id Gal(L/K))
    (resizedIdeles (K := K) (L := L) hST) n).hom

set_option maxHeartbeats 4000000 in
-- The direct-limit argument normalizes cochain representatives across two stages.
set_option synthInstance.maxHeartbeats 500000 in
-- The cochain representatives carry dependent finite-stage actions.
/-- If a positive-degree class at one finite stage dies in the full idèle
group, it dies after enlarging the exceptional set. -/
theorem ideles_places_cohomology
    (r : ℕ) (S : Finset (NumberFieldPlace K))
    (qS : groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) (r + 1))
    (hq : groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedInclusion (K := K) (L := L) S) (r + 1) qS = 0) :
    ∃ (T : Finset (NumberFieldPlace K)) (hST : S ⊆ T),
      resizedCohomologyTransition
        (K := K) (L := L) (r + 1) hST qS = 0 := by
  classical
  induction qS using groupCohomology_induction_on with
  | h x =>
      let A := resizedConcreteRepresentation K L
      let AS := resizedPlacesRepresentation (K := K) (L := L) S
      let incS := resizedInclusion (K := K) (L := L) S
      let mappedX := cocyclesMap (MonoidHom.id Gal(L/K)) incS (r + 1) x
      have hmapped : π A (r + 1) mappedX = 0 := by
        rw [← π_map_apply]
        exact hq
      obtain ⟨a, ha⟩ :=
        (cohomology_pi_boundary A r mappedX).1 hmapped
      obtain ⟨T₀, haT₀⟩ := ideles_idele_cochain
        (K := K) (L := L) r a
      let T := S ∪ T₀
      have hST : S ⊆ T := Finset.subset_union_left
      have hT₀T : T₀ ⊆ T := Finset.subset_union_right
      have haT : ∀ g, (a g).toMul ∈
          idelesAtPlaces (K := K) (L := L) T := fun g ↦
        ideles_places_mono (K := K) (L := L) hT₀T (haT₀ g)
      let AT := resizedPlacesRepresentation (K := K) (L := L) T
      let incT := resizedInclusion (K := K) (L := L) T
      let trans := resizedIdeles (K := K) (L := L) hST
      let aT := resizedIdeleCochain T r a haT
      let xT := cocyclesMap (MonoidHom.id Gal(L/K)) trans (r + 1) x
      have hfull :
          (inhomogeneousCochains A).d r (r + 1) a =
            fun g ↦ incS (iCocycles AS (r + 1) x g) := by
        calc
          (inhomogeneousCochains A).d r (r + 1) a =
              iCocycles A (r + 1) (toCocycles A r (r + 1) a) := by
            symm
            exact ConcreteCategory.congr_hom
              ((inhomogeneousCochains A).toCycles_i r (r + 1)) a
          _ = iCocycles A (r + 1) mappedX := congrArg
            (fun z ↦ iCocycles A (r + 1) z) ha
          _ = fun g ↦ incS (iCocycles AS (r + 1) x g) :=
            i_cocycles_general incS (r + 1) x
      have hboundary : toCocycles AT r (r + 1) aT = xT := by
        apply (ModuleCat.mono_iff_injective (iCocycles AT (r + 1))).1 inferInstance
        have hleft : iCocycles AT (r + 1)
            (toCocycles AT r (r + 1) aT) =
              (inhomogeneousCochains AT).d r (r + 1) aT :=
          ConcreteCategory.congr_hom
            ((inhomogeneousCochains AT).toCycles_i r (r + 1)) aT
        rw [hleft]
        apply funext
        intro g
        apply resized_inclusion_injective (K := K) (L := L) T
        change incT.hom
            ((inhomogeneousCochains AT).d r (r + 1) aT g) =
          incT.hom (iCocycles AT (r + 1) xT g)
        calc
          incT.hom ((inhomogeneousCochains AT).d r (r + 1) aT g) =
              ((inhomogeneousCochains A).d r (r + 1)
                (((cochainsMap (MonoidHom.id Gal(L/K)) incT).f r) aT)) g :=
            congrFun (cochain_differential_general incT r aT) g
          _ =
              (inhomogeneousCochains A).d r (r + 1) a g := by
            rfl
          _ = incS.hom (iCocycles AS (r + 1) x g) := congrFun hfull g
          _ = incT.hom (trans.hom (iCocycles AS (r + 1) x g)) := by
            rfl
          _ = incT.hom (iCocycles AT (r + 1) xT g) := by
            congr 1
            symm
            exact congrFun
              (i_cocycles_general trans (r + 1) x) g
      refine ⟨T, hST, ?_⟩
      change (groupCohomology.map (MonoidHom.id Gal(L/K)) trans (r + 1)).hom
        (π AS (r + 1) x) = 0
      rw [π_map_apply]
      change π AT (r + 1) xT = 0
      exact (cohomology_pi_boundary AT r xT).2
        ⟨aT, hboundary⟩

omit [FiniteDimensional K L] in
/-- Enlarging a stage by the reflexive inclusion induces the identity in
every cohomological degree. -/
theorem ideles_places_self
    (n : ℕ) (S : Finset (NumberFieldPlace K))
    (x : groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) n) :
    resizedCohomologyTransition (K := K) (L := L) n
      (show S ⊆ S from fun _ h ↦ h) x = x := by
  have htransition :
      resizedIdeles (K := K) (L := L)
          (show S ⊆ S from fun _ h ↦ h) =
        𝟙 (resizedPlacesRepresentation (K := K) (L := L) S) := by
    ext y
    rfl
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedIdeles (K := K) (L := L)
        (show S ⊆ S from fun _ h ↦ h)) n x = x
  rw [htransition, groupCohomology.map_id]
  rfl

omit [FiniteDimensional K L] in
/-- Successive enlargements of finite idèle stages induce the composite
map in every cohomological degree. -/
theorem ideles_places_comp
    (n : ℕ) {S T U : Finset (NumberFieldPlace K)}
    (hST : S ⊆ T) (hTU : T ⊆ U)
    (x : groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) n) :
    resizedCohomologyTransition (K := K) (L := L) n hTU
        (resizedCohomologyTransition
          (K := K) (L := L) n hST x) =
      resizedCohomologyTransition (K := K) (L := L) n
        (hST.trans hTU) x := by
  have htransition :
      resizedIdeles (K := K) (L := L) hST ≫
          resizedIdeles (K := K) (L := L) hTU =
        resizedIdeles (K := K) (L := L)
          (hST.trans hTU) := by
    ext y
    rfl
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedIdeles (K := K) (L := L) hTU) n
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIdeles (K := K) (L := L) hST) n x) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedIdeles (K := K) (L := L)
          (hST.trans hTU)) n x
  rw [← htransition]
  exact congrArg (fun f ↦ f x)
    (groupCohomology.map_id_comp
      (resizedIdeles (K := K) (L := L) hST)
      (resizedIdeles (K := K) (L := L) hTU) n).symm

/-- In a fixed degree, the cohomology groups of the finite idèle stages form
a directed system under enlargement of the exceptional set. -/
noncomputable instance placesDirectedSystem
    (n : ℕ) :
    DirectedSystem
      (fun S : Finset (NumberFieldPlace K) ↦ groupCohomology
        (resizedPlacesRepresentation (K := K) (L := L) S) n)
      (fun {_ _} h ↦ resizedCohomologyTransition
        (K := K) (L := L) n h) where
  map_self := ideles_places_self
    (K := K) (L := L) n
  map_map := by
    intro k j i hST hTU x
    exact ideles_places_comp
      (K := K) (L := L) n hST hTU x

/-- The directed limit, in degree `n`, of the cohomology of the finite idèle
stages. -/
abbrev IdelesPlacesLimit (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (n : ℕ) :=
  DirectLimit
    (fun S : Finset (NumberFieldPlace K) ↦ groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) n)
    (fun _ _ h ↦ resizedCohomologyTransition
      (K := K) (L := L) n h)

/-- The map from one finite stage to the cohomology of the full restricted
idèle representation. -/
noncomputable def idelesPlacesInclusion
    (n : ℕ) (S : Finset (NumberFieldPlace K)) :
    groupCohomology
        (resizedPlacesRepresentation (K := K) (L := L) S) n
          →ₗ[ULift.{u} ℤ]
      groupCohomology (resizedConcreteRepresentation K L) n :=
  (groupCohomology.map (MonoidHom.id Gal(L/K))
    (resizedInclusion (K := K) (L := L) S) n).hom

/-- Inclusion into the full idèle representation is compatible with a
finite-stage transition. -/
theorem resized_cohomology_inclusion
    (n : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) n) :
    idelesPlacesInclusion (K := K) (L := L) n T
        (resizedCohomologyTransition
          (K := K) (L := L) n hST x) =
      idelesPlacesInclusion (K := K) (L := L) n S x := by
  have hinclusion :
      resizedIdeles (K := K) (L := L) hST ≫
          resizedInclusion (K := K) (L := L) T =
        resizedInclusion (K := K) (L := L) S := by
    ext y
    rfl
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedInclusion (K := K) (L := L) T) n
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIdeles (K := K) (L := L) hST) n x) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedInclusion (K := K) (L := L) S) n x
  rw [← hinclusion]
  exact congrArg (fun f ↦ f x)
    (groupCohomology.map_id_comp
      (resizedIdeles (K := K) (L := L) hST)
      (resizedInclusion (K := K) (L := L) T) n).symm

/-- The canonical map from the finite-stage direct limit to the cohomology
of the concrete restricted idèle representation. -/
noncomputable def idelesLimitConcrete (n : ℕ) :
    IdelesPlacesLimit K L n →+
      groupCohomology (resizedConcreteRepresentation K L) n where
  toFun := DirectLimit.lift
    (ι := Finset (NumberFieldPlace K))
    (F := fun S : Finset (NumberFieldPlace K) ↦ groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) n)
    (fun _ _ h ↦ resizedCohomologyTransition
      (K := K) (L := L) n h)
    (fun S x ↦ idelesPlacesInclusion
      (K := K) (L := L) n S x)
    (fun S T h x ↦
      (resized_cohomology_inclusion
        (K := K) (L := L) n h x).symm)
  map_zero' := by
    rw [DirectLimit.zero_def (∅ : Finset (NumberFieldPlace K)),
      DirectLimit.lift_def]
    exact map_zero (idelesPlacesInclusion
      (K := K) (L := L) n ∅)
  map_add' q q' := by
    induction q, q' using DirectLimit.induction₂ with
    | _ S x y =>
        rw [DirectLimit.add_def, DirectLimit.lift_def,
          DirectLimit.lift_def, DirectLimit.lift_def]
        exact map_add (idelesPlacesInclusion
          (K := K) (L := L) n S) x y

/-- Every positive-degree idèle cohomology class comes from the finite-stage
direct limit. -/
theorem resized_limit_surjective
    (r : ℕ) : Function.Surjective
      (idelesLimitConcrete
        (K := K) (L := L) (r + 1)) := by
  intro q
  obtain ⟨S, qS, hqS⟩ :=
    ideles_cohomology_preimage (K := K) (L := L) r q
  refine ⟨(⟦⟨S, qS⟩⟧ :
    IdelesPlacesLimit K L (r + 1)), ?_⟩
  change idelesPlacesInclusion
    (K := K) (L := L) (r + 1) S qS = q
  exact hqS

/-- A positive-degree direct-limit class mapping to zero is already zero at
a sufficiently large finite idèle stage. -/
theorem resized_limit_injective
    (r : ℕ) : Function.Injective
      (idelesLimitConcrete
        (K := K) (L := L) (r + 1)) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hzero : idelesLimitConcrete
      (K := K) (L := L) (r + 1) (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  let F : Finset (NumberFieldPlace K) → Type u :=
    fun S : Finset (NumberFieldPlace K) ↦ groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) (r + 1)
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) ↦
    resizedCohomologyTransition
      (K := K) (L := L) (r + 1) h
  obtain ⟨S, qS, hq⟩ := DirectLimit.exists_eq_mk f (q - q')
  rw [hq] at hzero ⊢
  have hstage : groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedInclusion (K := K) (L := L) S) (r + 1) qS = 0 := by
    exact hzero
  obtain ⟨T, hST, hT⟩ :=
    ideles_places_cohomology
      (K := K) (L := L) r S qS hstage
  change f S T hST qS = 0 at hT
  calc
    (⟦⟨S, qS⟩⟧ : DirectLimit F f) =
        ⟦⟨T, f S T hST qS⟩⟧ :=
      DirectLimit.eq_of_le (f := f) ⟨S, qS⟩ T hST
    _ = ⟦⟨T, 0⟩⟧ :=
      congrArg (fun z ↦ (⟦⟨T, z⟩⟧ : DirectLimit F f)) hT
    _ = 0 := (DirectLimit.zero_def T).symm

/-- In every positive degree, cohomology of the concrete restricted idèle
group is the direct limit of the cohomology of its finite stages. -/
noncomputable def idelesPlacesLimit
    (r : ℕ) :
    IdelesPlacesLimit K L (r + 1) ≃+
      groupCohomology (resizedConcreteRepresentation K L) (r + 1) :=
  AddEquiv.ofBijective
    (idelesLimitConcrete
      (K := K) (L := L) (r + 1))
    ⟨resized_limit_injective
      (K := K) (L := L) r,
     resized_limit_surjective
      (K := K) (L := L) r⟩

end

end Towers.CField.HNorm
