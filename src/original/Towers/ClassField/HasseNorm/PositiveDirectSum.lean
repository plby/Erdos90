import Towers.ClassField.HasseNorm.PositiveDirectLimit
import Towers.ClassField.HasseNorm.InfiniteCompletionPlaces
import Towers.ClassField.CohomologyOps.GroupFiniteIso
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# The positive-degree idèle cohomology direct sum

This file passes the degree-uniform finite-stage calculation through the
restricted-product direct limit.  It keeps the infinite completion orbits
as a finite product and extends the finitely many exceptional finite orbits
by zero; the resulting limit is the direct sum over all places.
-/

namespace Towers.CField.HNorm

open CategoryTheory CategoryTheory.Limits Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.COps
open Towers.CField.Ideles
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance positiveDirectSumRepModule
    (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
    Module (ULift.{u} ℤ) X := X.hV2

local instance positiveDirectSumNumberFieldPlaceDecidableEq :
    DecidableEq (NumberFieldPlace K) := Classical.decEq _

local instance positiveDirectSumFinitePrimeDecidableEq :
    DecidableEq (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  Classical.decEq _

private abbrev infiniteProductFamily
    (v : InfinitePlace K) : Rep (ULift.{u} ℤ) Gal(L/K) :=
  resizedPlaceRepresentation (K := K) (L := L) (.inr v)

set_option synthInstance.maxHeartbeats 300000 in
-- Evaluating the categorical product synthesizes its dependent representation modules.
set_option maxHeartbeats 1000000 in
-- The product comparison unfolds every infinite-place evaluation map.
/-- Evaluation from the categorical product of the infinite completion
orbits to the concrete pointwise product representation. -/
noncomputable def categoricalProductsPointwise :
    (∏ᶜ fun v : InfinitePlace K ↦
      infiniteProductFamily (K := K) (L := L) v) ⟶
      resizedProductsRepresentation K L := by
  letI repModule (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) X := X.hV2
  let A := fun v : InfinitePlace K ↦
    infiniteProductFamily (K := K) (L := L) v
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x v ↦ (Pi.π A v).hom x
          map_add' := fun x y ↦ by
            funext v
            exact (Pi.π A v).hom.map_add x y
          map_smul' := fun r x ↦ by
            funext v
            exact (Pi.π A v).hom.map_smul r x }
      isIntertwining' := fun sigma ↦ by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        funext v
        exact congrArg Additive.toMul
          (Rep.hom_comm_apply (Pi.π A v) sigma x) }

set_option synthInstance.maxHeartbeats 300000 in
-- Bijectivity reconstructs the concrete product through the categorical limit instance.
/-- The preceding evaluation map is bijective on carriers. -/
theorem categorical_products_pointwise :
    Function.Bijective
      (categoricalProductsPointwise
        (K := K) (L := L)) := by
  letI repModule (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) X := X.hV2
  let A := fun v : InfinitePlace K ↦
    infiniteProductFamily (K := K) (L := L) v
  letI : PreservesLimit (Discrete.functor A)
      (forget (Rep (ULift.{u} ℤ) Gal(L/K))) := by
    change PreservesLimit (Discrete.functor A)
      (forget₂ (Rep (ULift.{u} ℤ) Gal(L/K))
        (ModuleCat (ULift.{u} ℤ)) ⋙ forget (ModuleCat (ULift.{u} ℤ)))
    infer_instance
  constructor
  · intro x y hxy
    apply (Concrete.productEquiv A).injective
    funext v
    rw [Concrete.productEquiv_apply_apply,
      Concrete.productEquiv_apply_apply]
    exact congrFun hxy v
  · intro y
    let x := (Concrete.productEquiv A).symm y
    refine ⟨x, ?_⟩
    funext v
    change (Pi.π A v).hom ((Concrete.productEquiv A).symm y) = y v
    exact Concrete.productEquiv_symm_apply_π A y v

set_option synthInstance.maxHeartbeats 300000 in
-- Building the inverse representation isomorphism reuses the dependent product limit.
/-- The pointwise infinite completion-product representation is its
categorical product presentation. -/
noncomputable def productsIsoCategorical :
    resizedProductsRepresentation K L ≅
      (∏ᶜ fun v : InfinitePlace K ↦
        infiniteProductFamily (K := K) (L := L) v) := by
  letI repModule (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) X := X.hV2
  exact (Rep.mkIso
    ((categoricalProductsPointwise
      (K := K) (L := L)).hom.ofBijective
        (categorical_products_pointwise
          (K := K) (L := L)))).symm

/-- Cohomology of the infinite idèle factor is the direct sum of its
completion-orbit cohomology groups in every degree. -/
noncomputable def idelesDirectSum
    (n : ℕ) :
    groupCohomology (resizedInfiniteRepresentation K L) n ≃+
      DirectSum (InfinitePlace K) (fun v ↦ groupCohomology
        (resizedPlaceRepresentation
          (K := K) (L := L) (.inr v)) n) := by
  let A := fun v : InfinitePlace K ↦
    infiniteProductFamily (K := K) (L := L) v
  let e₁ := ((groupCohomology.functor
    (ULift.{u} ℤ) Gal(L/K) n).mapIso
      ((resizedIsoProducts
        (K := K) (L := L)).trans
          (productsIsoCategorical
            (K := K) (L := L)))).toLinearEquiv.toAddEquiv
  let e₂ := (groupProductIso
    (ULift.{u} ℤ) Gal(L/K) A n).toLinearEquiv.toAddEquiv
  let e₃ := moduleCatPi
    (fun v ↦ groupCohomology (A v) n)
  exact (e₁.trans (e₂.trans e₃)).trans
    (DirectSum.addEquivProd
      (fun v : InfinitePlace K ↦ groupCohomology (A v) n)).symm

private abbrev stageInfiniteRepresentation :
    Rep (ULift.{u} ℤ) Gal(L/K) := resizedInfiniteRepresentation K L

private abbrev stageFiniteRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep (ULift.{u} ℤ) Gal(L/K) :=
  resizedStageRepresentation (K := K) (L := L) S

set_option synthInstance.maxHeartbeats 300000 in
-- The binary categorical product requires both stage representation modules simultaneously.
set_option maxHeartbeats 1000000 in
-- Regrouping infinite and finite coordinates unfolds both categorical projections.
/-- The categorical binary product of the infinite and finite stage factors
maps to the concrete regrouped stage. -/
noncomputable def categoricalIdelesPointwise
    (S : Finset (NumberFieldPlace K)) :
    stageInfiniteRepresentation (K := K) (L := L) ⨯
        stageFiniteRepresentation (K := K) (L := L) S ⟶
      resizedIdelesRepresentation (K := K) (L := L) S := by
  let A := stageInfiniteRepresentation (K := K) (L := L)
  let B := stageFiniteRepresentation (K := K) (L := L) S
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x ↦ Additive.ofMul
            (((Limits.prod.fst : A ⨯ B ⟶ A) x).toMul,
             ((Limits.prod.snd : A ⨯ B ⟶ B) x).toMul)
          map_add' := fun x y ↦ by
            apply Additive.toMul.injective
            apply Prod.ext
            · exact congrArg Additive.toMul
                ((Limits.prod.fst : A ⨯ B ⟶ A).hom.map_add x y)
            · exact congrArg Additive.toMul
                ((Limits.prod.snd : A ⨯ B ⟶ B).hom.map_add x y)
          map_smul' := fun r x ↦ by
            apply Additive.toMul.injective
            apply Prod.ext
            · exact congrArg Additive.toMul
                ((Limits.prod.fst : A ⨯ B ⟶ A).hom.map_smul r x)
            · exact congrArg Additive.toMul
                ((Limits.prod.snd : A ⨯ B ⟶ B).hom.map_smul r x) }
      isIntertwining' := fun sigma ↦ by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        apply Prod.ext
        · exact congrArg Additive.toMul
            (Rep.hom_comm_apply (Limits.prod.fst : A ⨯ B ⟶ A) sigma x)
        · exact congrArg Additive.toMul
            (Rep.hom_comm_apply (Limits.prod.snd : A ⨯ B ⟶ B) sigma x) }

set_option synthInstance.maxHeartbeats 300000 in
-- Bijectivity of the regrouping map synthesizes the concrete binary-product limit.
/-- The concrete regrouped stage is the categorical binary product of its
infinite and finite factors. -/
theorem categorical_pointwise_bijective
    (S : Finset (NumberFieldPlace K)) :
    Function.Bijective
      (categoricalIdelesPointwise
        (K := K) (L := L) S) := by
  let A := stageInfiniteRepresentation (K := K) (L := L)
  let B := stageFiniteRepresentation (K := K) (L := L) S
  letI : PreservesLimit (pair A B)
      (forget (Rep (ULift.{u} ℤ) Gal(L/K))) := by
    change PreservesLimit (pair A B)
      (forget₂ (Rep (ULift.{u} ℤ) Gal(L/K))
        (ModuleCat (ULift.{u} ℤ)) ⋙ forget (ModuleCat (ULift.{u} ℤ)))
    infer_instance
  constructor
  · intro x y hxy
    apply (Concrete.prodEquiv A B).injective
    apply Prod.ext
    · rw [Concrete.prodEquiv_apply_fst, Concrete.prodEquiv_apply_fst]
      exact congrArg (fun z ↦ Additive.ofMul z.toMul.1) hxy
    · rw [Concrete.prodEquiv_apply_snd, Concrete.prodEquiv_apply_snd]
      exact congrArg (fun z ↦ Additive.ofMul z.toMul.2) hxy
  · intro y
    let p : A × B :=
      (Additive.ofMul y.toMul.1, Additive.ofMul y.toMul.2)
    refine ⟨(Concrete.prodEquiv A B).symm p, ?_⟩
    apply Additive.toMul.injective
    apply Prod.ext
    · exact congrArg Additive.toMul
        (Concrete.prodEquiv_symm_apply_fst A B p)
    · exact congrArg Additive.toMul
        (Concrete.prodEquiv_symm_apply_snd A B p)

/-- The concrete regrouped stage as a categorical binary product. -/
noncomputable def resizedIsoCategorical
    (S : Finset (NumberFieldPlace K)) :
    resizedIdelesRepresentation (K := K) (L := L) S ≅
      stageInfiniteRepresentation (K := K) (L := L) ⨯
        stageFiniteRepresentation (K := K) (L := L) S :=
  (Rep.mkIso
    ((categoricalIdelesPointwise
      (K := K) (L := L) S).hom.ofBijective
        (categorical_pointwise_bijective
          (K := K) (L := L) S))).symm

/-- The categorical product presentation has the expected infinite
projection. -/
theorem iso_categorical_fst
    (S : Finset (NumberFieldPlace K)) :
    (resizedIsoCategorical
        (K := K) (L := L) S).hom ≫
        (Limits.prod.fst :
          stageInfiniteRepresentation (K := K) (L := L) ⨯
              stageFiniteRepresentation (K := K) (L := L) S ⟶
            stageInfiniteRepresentation (K := K) (L := L)) =
      resizedPlacesInfinite (K := K) (L := L) S := by
  rw [← cancel_epi
    (resizedIsoCategorical
      (K := K) (L := L) S).inv]
  simp only [Iso.inv_hom_id_assoc]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- The categorical product presentation has the expected finite
projection. -/
theorem iso_categorical_snd
    (S : Finset (NumberFieldPlace K)) :
    (resizedIsoCategorical
        (K := K) (L := L) S).hom ≫
        (Limits.prod.snd :
          stageInfiniteRepresentation (K := K) (L := L) ⨯
              stageFiniteRepresentation (K := K) (L := L) S ⟶
            stageFiniteRepresentation (K := K) (L := L) S) =
      resizedIdelesFinite (K := K) (L := L) S := by
  rw [← cancel_epi
    (resizedIsoCategorical
      (K := K) (L := L) S).inv]
  simp only [Iso.inv_hom_id_assoc]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- A finite idèle stage splits into its constant infinite factor and its
finite-prime factor in every cohomological degree. -/
noncomputable def resizedIdelesCohomology
    (S : Finset (NumberFieldPlace K)) (n : ℕ) :
    groupCohomology
        (resizedPlacesRepresentation (K := K) (L := L) S) n ≃+
      groupCohomology (resizedInfiniteRepresentation K L) n ×
        groupCohomology
          (resizedStageRepresentation
            (K := K) (L := L) S) n := by
  let A := stageInfiniteRepresentation (K := K) (L := L)
  let B := stageFiniteRepresentation (K := K) (L := L) S
  let eRep : resizedPlacesRepresentation
      (K := K) (L := L) S ≅ A ⨯ B :=
    (resizedRepresentationIso
      (K := K) (L := L) S).trans <|
      (resizedIsoCategorical
        (K := K) (L := L) S)
  let F := groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) n
  let e₁ := (F.mapIso eRep ≪≫
    PreservesLimitPair.iso F A B).toLinearEquiv.toAddEquiv
  let e₂ : (↑(groupCohomology A n ⨯ groupCohomology B n :
      ModuleCat (ULift.{u} ℤ)) : Type u) ≃+
      groupCohomology A n × groupCohomology B n :=
    { toEquiv := Concrete.prodEquiv
        (groupCohomology A n) (groupCohomology B n)
      map_add' := fun x y ↦ by
        apply Prod.ext
        · change (Concrete.prodEquiv _ _ (x + y)).1 =
            (Concrete.prodEquiv _ _ x).1 + (Concrete.prodEquiv _ _ y).1
          simp only [Concrete.prodEquiv_apply_fst]
          exact (Limits.prod.fst : groupCohomology A n ⨯
            groupCohomology B n ⟶ groupCohomology A n).hom.map_add x y
        · change (Concrete.prodEquiv _ _ (x + y)).2 =
            (Concrete.prodEquiv _ _ x).2 + (Concrete.prodEquiv _ _ y).2
          simp only [Concrete.prodEquiv_apply_snd]
          exact (Limits.prod.snd : groupCohomology A n ⨯
            groupCohomology B n ⟶ groupCohomology B n).hom.map_add x y }
  exact e₁.trans e₂

/-- The infinite coordinate of the stage splitting is the cohomology map
induced by the literal infinite projection. -/
theorem resized_cohomology_fst
    (S : Finset (NumberFieldPlace K)) (n : ℕ)
    (q : groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) n) :
    (resizedIdelesCohomology
      (K := K) (L := L) S n q).1 =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        ((resizedRepresentationIso
          (K := K) (L := L) S).hom ≫
            resizedPlacesInfinite
              (K := K) (L := L) S) n q := by
  let A := stageInfiniteRepresentation (K := K) (L := L)
  let B := stageFiniteRepresentation (K := K) (L := L) S
  let eRep : resizedPlacesRepresentation
      (K := K) (L := L) S ≅ A ⨯ B :=
    (resizedRepresentationIso
      (K := K) (L := L) S).trans
        (resizedIsoCategorical
          (K := K) (L := L) S)
  let F := groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) n
  change (Concrete.prodEquiv (F.obj A) (F.obj B)
      ((PreservesLimitPair.iso F A B).hom (F.map eRep.hom q))).1 = _
  rw [Concrete.prodEquiv_apply_fst]
  have hcomparison : (PreservesLimitPair.iso F A B).hom ≫
      (Limits.prod.fst : F.obj A ⨯ F.obj B ⟶ F.obj A) =
        F.map (Limits.prod.fst : A ⨯ B ⟶ A) := by
    simpa only [PreservesLimitPair.iso_hom] using
      prodComparison_fst F A B
  rw [← ConcreteCategory.comp_apply, hcomparison]
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  have hproj : eRep.hom ≫ (Limits.prod.fst : A ⨯ B ⟶ A) =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
          resizedPlacesInfinite
            (K := K) (L := L) S := by
    rw [show eRep.hom =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
          (resizedIsoCategorical
            (K := K) (L := L) S).hom from rfl,
      Category.assoc,
      iso_categorical_fst]
  rw [hproj]
  rfl

/-- The finite coordinate of the stage splitting is the cohomology map
induced by the literal finite projection. -/
theorem ideles_places_snd
    (S : Finset (NumberFieldPlace K)) (n : ℕ)
    (q : groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) n) :
    (resizedIdelesCohomology
      (K := K) (L := L) S n q).2 =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        ((resizedRepresentationIso
          (K := K) (L := L) S).hom ≫
            resizedIdelesFinite
              (K := K) (L := L) S) n q := by
  let A := stageInfiniteRepresentation (K := K) (L := L)
  let B := stageFiniteRepresentation (K := K) (L := L) S
  let eRep : resizedPlacesRepresentation
      (K := K) (L := L) S ≅ A ⨯ B :=
    (resizedRepresentationIso
      (K := K) (L := L) S).trans
        (resizedIsoCategorical
          (K := K) (L := L) S)
  let F := groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) n
  change (Concrete.prodEquiv (F.obj A) (F.obj B)
      ((PreservesLimitPair.iso F A B).hom (F.map eRep.hom q))).2 = _
  rw [Concrete.prodEquiv_apply_snd]
  have hcomparison : (PreservesLimitPair.iso F A B).hom ≫
      (Limits.prod.snd : F.obj A ⨯ F.obj B ⟶ F.obj B) =
        F.map (Limits.prod.snd : A ⨯ B ⟶ B) := by
    simpa only [PreservesLimitPair.iso_hom] using
      prodComparison_snd F A B
  rw [← ConcreteCategory.comp_apply, hcomparison]
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  have hproj : eRep.hom ≫ (Limits.prod.snd : A ⨯ B ⟶ B) =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
          resizedIdelesFinite
            (K := K) (L := L) S := by
    rw [show eRep.hom =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
          (resizedIsoCategorical
            (K := K) (L := L) S).hom from rfl,
      Category.assoc,
      iso_categorical_snd]
  rw [hproj]
  rfl

/-- The cohomology map induced by enlargement of the finite-prime product
factor. -/
noncomputable def stageCohomologyTransition
    (n : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    groupCohomology
        (resizedStageRepresentation
          (K := K) (L := L) S) n →+
      groupCohomology
        (resizedStageRepresentation
          (K := K) (L := L) T) n :=
  (groupCohomology.map (MonoidHom.id Gal(L/K))
    (ideleStageTransition
      (K := K) (L := L) hST) n).hom.toAddMonoidHom

set_option maxHeartbeats 1000000 in
-- Naturality unfolds the uniform splitting and both stage-transition components.
/-- The degree-uniform stage splitting is natural under enlargement: the
infinite coordinate is fixed and the finite coordinate uses the actual
finite-stage transition. -/
theorem resized_ideles_cohomology
    (n : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) n) :
    resizedIdelesCohomology
        (K := K) (L := L) T n
        (resizedCohomologyTransition
          (K := K) (L := L) n hST q) =
      ((resizedIdelesCohomology
          (K := K) (L := L) S n q).1,
       stageCohomologyTransition
          (K := K) (L := L) n hST
          (resizedIdelesCohomology
            (K := K) (L := L) S n q).2) := by
  apply Prod.ext
  · rw [resized_cohomology_fst,
      resized_cohomology_fst]
    let pS := (resizedRepresentationIso
      (K := K) (L := L) S).hom ≫
        resizedPlacesInfinite (K := K) (L := L) S
    let pT := (resizedRepresentationIso
      (K := K) (L := L) T).hom ≫
        resizedPlacesInfinite (K := K) (L := L) T
    have hsquare : resizedIdeles
          (K := K) (L := L) hST ≫ pT = pS := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rfl
    change groupCohomology.map (MonoidHom.id Gal(L/K)) pT n
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIdeles (K := K) (L := L) hST) n q) =
      groupCohomology.map (MonoidHom.id Gal(L/K)) pS n q
    rw [← hsquare]
    exact congrArg (fun f ↦ f q)
      (groupCohomology.map_id_comp
        (resizedIdeles (K := K) (L := L) hST) pT n).symm
  · rw [ideles_places_snd,
      ideles_places_snd]
    let pS := (resizedRepresentationIso
      (K := K) (L := L) S).hom ≫
        resizedIdelesFinite (K := K) (L := L) S
    let pT := (resizedRepresentationIso
      (K := K) (L := L) T).hom ≫
        resizedIdelesFinite (K := K) (L := L) T
    let f := ideleStageTransition
      (K := K) (L := L) hST
    have hsquare : resizedIdeles
          (K := K) (L := L) hST ≫ pT = pS ≫ f := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      funext P
      apply Subtype.ext
      rfl
    change groupCohomology.map (MonoidHom.id Gal(L/K)) pT n
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIdeles (K := K) (L := L) hST) n q) =
      groupCohomology.map (MonoidHom.id Gal(L/K)) f n
        (groupCohomology.map (MonoidHom.id Gal(L/K)) pS n q)
    have hleft := congrArg (fun z ↦ z q)
      (groupCohomology.map_id_comp
        (resizedIdeles (K := K) (L := L) hST) pT n)
    have hright := congrArg (fun z ↦ z q)
      (groupCohomology.map_id_comp pS f n)
    have hmiddle : groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedIdeles
          (K := K) (L := L) hST ≫ pT) n q =
      groupCohomology.map (MonoidHom.id Gal(L/K)) (pS ≫ f) n q := by
      exact congrArg (fun φ ↦
        groupCohomology.map (MonoidHom.id Gal(L/K)) φ n q) hsquare
    exact hleft.symm.trans (hmiddle.trans hright)

/-! ## Positive cohomology of the finite-prime product, coordinatewise -/

/-- The coordinate map from positive cohomology of a finite-prime stage
product to the product of the orbit cohomology groups. -/
noncomputable def resizedCohomologyPi
    (S : Finset (NumberFieldPlace K)) (r : ℕ) :
    groupCohomology
        (resizedStageRepresentation
          (K := K) (L := L) S) (r + 1) →+
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        groupCohomology
          (stageOrbitRepresentation
            (K := K) (L := L) S P) (r + 1)) where
  toFun q P := groupCohomology.map (MonoidHom.id Gal(L/K))
    (resizedStageEvaluation
      (K := K) (L := L) S P) (r + 1) q
  map_zero' := by
    funext P
    exact map_zero _
  map_add' x y := by
    funext P
    exact map_add _ x y

set_option maxHeartbeats 2000000 in
-- Surjectivity chooses and assembles cocycle representatives at every finite prime.
omit [FiniteDimensional K L] in
/-- Every family of positive-degree orbit classes has a product-valued
cocycle representative. -/
theorem stage_pi_surjective
    (S : Finset (NumberFieldPlace K)) (r : ℕ) :
    Function.Surjective
      (resizedCohomologyPi
        (K := K) (L := L) S r) := by
  intro q
  have hrepresentative
      (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
      ∃ xP : cocycles
          (stageOrbitRepresentation
            (K := K) (L := L) S P) (r + 1),
        π _ (r + 1) xP = q P := by
    induction q P using groupCohomology_induction_on with
    | h xP => exact ⟨xP, rfl⟩
  choose x hx using hrepresentative
  let zFun : (Fin (r + 1) → Gal(L/K)) →
      resizedStageRepresentation (K := K) (L := L) S :=
    fun g ↦ Additive.ofMul (fun P ↦
      (iCocycles
        (stageOrbitRepresentation
          (K := K) (L := L) S P) (r + 1) (x P) g).toMul)
  have hz : (inhomogeneousCochains
      (resizedStageRepresentation
        (K := K) (L := L) S)).d (r + 1) (r + 2) zFun = 0 := by
    apply funext
    intro g
    apply Additive.toMul.injective
    funext P
    let eP := resizedStageEvaluation
      (K := K) (L := L) S P
    have hdiff := cochain_differential_general eP (r + 1) zFun
    have hmap : ((cochainsMap (MonoidHom.id Gal(L/K)) eP).f (r + 1)) zFun =
        iCocycles
          (stageOrbitRepresentation
            (K := K) (L := L) S P) (r + 1) (x P) := by
      rfl
    have hcycle : (inhomogeneousCochains
        (stageOrbitRepresentation
          (K := K) (L := L) S P)).d (r + 1) (r + 2)
          (iCocycles
            (stageOrbitRepresentation
              (K := K) (L := L) S P) (r + 1) (x P)) = 0 := by
      simpa only [ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom
          ((inhomogeneousCochains
            (stageOrbitRepresentation
              (K := K) (L := L) S P)).iCycles_d (r + 1) (r + 2)) (x P)
    rw [hmap, hcycle] at hdiff
    have hg := congrFun hdiff g
    exact congrArg Additive.toMul hg
  let z : cocycles
      (resizedStageRepresentation
        (K := K) (L := L) S) (r + 1) :=
    cocyclesMk zFun (by
      have hdeg : r + 2 = (r + 1) + 1 := by omega
      have hz' : (inhomogeneousCochains
          (resizedStageRepresentation
            (K := K) (L := L) S)).d (r + 1) ((r + 1) + 1) zFun = 0 := by
        simpa only [hdeg] using hz
      rw [inhomogeneousCochains.d_def] at hz'
      exact hz')
  refine ⟨π _ (r + 1) z, ?_⟩
  funext P
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedStageEvaluation
        (K := K) (L := L) S P) (r + 1) (π _ (r + 1) z) = q P
  rw [π_map_apply, ← hx P]
  congr 1
  apply (ModuleCat.mono_iff_injective
    (iCocycles
      (stageOrbitRepresentation
        (K := K) (L := L) S P) (r + 1))).1 inferInstance
  rw [i_cocycles_general]
  funext g
  unfold z
  rw [iCocycles_mk]
  rfl

set_option maxHeartbeats 3000000 in
-- Injectivity reduces a product cocycle to all of its finite-prime coordinates.
omit [FiniteDimensional K L] in
/-- The positive-degree coordinate map for the finite-prime stage product
is injective. -/
theorem stage_pi_injective
    (S : Finset (NumberFieldPlace K)) (r : ℕ) :
    Function.Injective
      (resizedCohomologyPi
        (K := K) (L := L) S r) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hcoord : resizedCohomologyPi
      (K := K) (L := L) S r (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  clear hqq'
  have hkernel
      (w : groupCohomology
        (resizedStageRepresentation
          (K := K) (L := L) S) (r + 1))
      (hw : resizedCohomologyPi
        (K := K) (L := L) S r w = 0) : w = 0 := by
    induction w using groupCohomology_induction_on with
    | h z =>
      have hzero (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
          π (stageOrbitRepresentation
              (K := K) (L := L) S P) (r + 1)
            (cocyclesMap (MonoidHom.id Gal(L/K))
              (resizedStageEvaluation
                (K := K) (L := L) S P) (r + 1) z) = 0 := by
        rw [← π_map_apply]
        exact congrFun hw P
      have hwitness (P : HeightOneSpectrum
          (NumberField.RingOfIntegers K)) :
          ∃ aP : (Fin r → Gal(L/K)) →
              stageOrbitRepresentation
                (K := K) (L := L) S P,
            toCocycles
                (stageOrbitRepresentation
                  (K := K) (L := L) S P) r (r + 1) aP =
              cocyclesMap (MonoidHom.id Gal(L/K))
                (resizedStageEvaluation
                  (K := K) (L := L) S P) (r + 1) z :=
        (cohomology_pi_boundary _ r _).1 (hzero P)
      choose a ha using hwitness
      let aProduct : (Fin r → Gal(L/K)) →
          resizedStageRepresentation
            (K := K) (L := L) S :=
        fun g ↦ Additive.ofMul (fun P ↦ (a P g).toMul)
      apply (cohomology_pi_boundary _ r z).2
      refine ⟨aProduct, ?_⟩
      apply (ModuleCat.mono_iff_injective
        (iCocycles
          (resizedStageRepresentation
            (K := K) (L := L) S) (r + 1))).1 inferInstance
      have hleft : iCocycles
          (resizedStageRepresentation
            (K := K) (L := L) S) (r + 1)
          (toCocycles
            (resizedStageRepresentation
              (K := K) (L := L) S) r (r + 1) aProduct) =
        (inhomogeneousCochains
          (resizedStageRepresentation
            (K := K) (L := L) S)).d r (r + 1) aProduct :=
        ConcreteCategory.congr_hom
          ((inhomogeneousCochains
            (resizedStageRepresentation
              (K := K) (L := L) S)).toCycles_i r (r + 1)) aProduct
      rw [hleft]
      apply funext
      intro g
      apply Additive.toMul.injective
      funext P
      let eP := resizedStageEvaluation
        (K := K) (L := L) S P
      have hdiff := cochain_differential_general eP r aProduct
      have hmap : ((cochainsMap (MonoidHom.id Gal(L/K)) eP).f r) aProduct =
          a P := by
        rfl
      have htoCycles : iCocycles
          (stageOrbitRepresentation
            (K := K) (L := L) S P) (r + 1)
          (toCocycles
            (stageOrbitRepresentation
              (K := K) (L := L) S P) r (r + 1) (a P)) =
        (inhomogeneousCochains
          (stageOrbitRepresentation
            (K := K) (L := L) S P)).d r (r + 1) (a P) :=
        ConcreteCategory.congr_hom
          ((inhomogeneousCochains
            (stageOrbitRepresentation
              (K := K) (L := L) S P)).toCycles_i r (r + 1)) (a P)
      have hboundary :
          (inhomogeneousCochains
            (stageOrbitRepresentation
              (K := K) (L := L) S P)).d r (r + 1) (a P) =
            fun g ↦ eP (iCocycles
              (resizedStageRepresentation
                (K := K) (L := L) S) (r + 1) z g) := by
        calc
          _ = iCocycles
              (stageOrbitRepresentation
                (K := K) (L := L) S P) (r + 1)
              (toCocycles
                (stageOrbitRepresentation
                  (K := K) (L := L) S P) r (r + 1) (a P)) :=
            htoCycles.symm
          _ = iCocycles
              (stageOrbitRepresentation
                (K := K) (L := L) S P) (r + 1)
              (cocyclesMap (MonoidHom.id Gal(L/K)) eP (r + 1) z) :=
            congrArg (fun w ↦ iCocycles
              (stageOrbitRepresentation
                (K := K) (L := L) S P) (r + 1) w) (ha P)
          _ = fun g ↦ eP (iCocycles
              (resizedStageRepresentation
                (K := K) (L := L) S) (r + 1) z g) :=
            i_cocycles_general eP (r + 1) z
      rw [hmap] at hdiff
      have hgDiff := congrFun hdiff g
      have hgBoundary := congrFun hboundary g
      exact congrArg Additive.toMul (hgDiff.trans hgBoundary)
  exact hkernel (q - q') hcoord

/-- Positive cohomology of the finite-prime product is the product of the
positive cohomology groups of its orbit factors. -/
noncomputable def stageCohomologyPi
    (S : Finset (NumberFieldPlace K)) (r : ℕ) :
    groupCohomology
        (resizedStageRepresentation
          (K := K) (L := L) S) (r + 1) ≃+
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        groupCohomology
          (stageOrbitRepresentation
            (K := K) (L := L) S P) (r + 1)) :=
  AddEquiv.ofBijective
    (resizedCohomologyPi
      (K := K) (L := L) S r)
    ⟨stage_pi_injective
      (K := K) (L := L) S r,
     stage_pi_surjective
      (K := K) (L := L) S r⟩

/-! ## Exceptional finite coordinates and extension by zero -/

/-- The unrestricted completion-orbit cohomology at one finite prime. -/
abbrev OrbitPositiveCohomology
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (r : ℕ)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) : Type u :=
  groupCohomology
    (resizedAboveRepresentation
      (K := K) (L := L) P) (r + 1)

/-- The finite family of unrestricted finite completion-orbit cohomology
groups selected by a finite idèle stage. -/
abbrev ExceptionalPositiveCohomology
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NumberFieldPlace K)) (r : ℕ) :=
  ∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ S},
    OrbitPositiveCohomology K L r P.1

/-- Outside a cofinal stage containing every ramified finite prime, all
positive cohomology of the local-unit orbit vanishes. -/
theorem cofinal_stage_subsingleton
    (T : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉
      cofinalIdeleStage K L T) (r : ℕ) :
    Subsingleton
      (groupCohomology
        (stageOrbitRepresentation
          (K := K) (L := L) (cofinalIdeleStage K L T) P) (r + 1)) := by
  apply cohomology_subsingleton_outside
    (K := K) (L := L) (cofinalIdeleStage K L T)
  · intro P' hP' Q
    exact unramified_stage_spec (K := K) (L := L) P'
      (fun h ↦ hP' (Finset.mem_union_left _ h)) Q
  · exact hP
  · omega

/-- Delete the cohomologically trivial finite-prime coordinates outside an
exceptional set and identify the remaining orbit stages with unrestricted
completion orbits. -/
noncomputable def stagePiExceptional
    (S : Finset (NumberFieldPlace K)) (r : ℕ)
    (houtside :
      ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Sum.inl P : NumberFieldPlace K) ∉ S →
          Subsingleton
            (groupCohomology
              (stageOrbitRepresentation
                (K := K) (L := L) S P) (r + 1))) :
    (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        groupCohomology
          (stageOrbitRepresentation
            (K := K) (L := L) S P) (r + 1)) ≃+
      ExceptionalPositiveCohomology K L S r where
  toFun x P :=
    stageCohomologyFull
      (K := K) (L := L) S P.1 P.2 (r + 1) (x P.1)
  invFun x P := if hP : (Sum.inl P : NumberFieldPlace K) ∈ S then
    (stageCohomologyFull
      (K := K) (L := L) S P hP (r + 1)).symm (x ⟨P, hP⟩)
  else
    0
  left_inv x := by
    funext P
    by_cases hP : (Sum.inl P : NumberFieldPlace K) ∈ S
    · change (if hP' : (Sum.inl P : NumberFieldPlace K) ∈ S then
          (stageCohomologyFull
            (K := K) (L := L) S P hP' (r + 1)).symm
            ((stageCohomologyFull
              (K := K) (L := L) S P hP' (r + 1)) (x P))
        else 0) = x P
      simp only [dif_pos hP, AddEquiv.symm_apply_apply]
    · letI := houtside P hP
      exact Subsingleton.elim _ _
  right_inv x := by
    funext P
    change (stageCohomologyFull
      (K := K) (L := L) S P.1 P.2 (r + 1))
        (if hP' : (Sum.inl P.1 : NumberFieldPlace K) ∈ S then
          (stageCohomologyFull
            (K := K) (L := L) S P.1 hP' (r + 1)).symm
              (x ⟨P.1, hP'⟩)
        else 0) = x P
    simp only [dif_pos P.2, AddEquiv.apply_symm_apply]
  map_add' x y := by
    funext P
    exact (stageCohomologyFull
      (K := K) (L := L) S P.1 P.2 (r + 1)).map_add (x P.1) (y P.1)

/-- Positive cohomology of a cofinal finite-prime stage is the finite family
of unrestricted completion-orbit groups at its exceptional primes. -/
noncomputable def cofinalStageExceptional
    (T : Finset (NumberFieldPlace K)) (r : ℕ) :
    groupCohomology
        (resizedStageRepresentation
          (K := K) (L := L) (cofinalIdeleStage K L T)) (r + 1) ≃+
      ExceptionalPositiveCohomology
        K L (cofinalIdeleStage K L T) r :=
  (stageCohomologyPi
    (K := K) (L := L) (cofinalIdeleStage K L T) r).trans
      (stagePiExceptional
        (K := K) (L := L) (cofinalIdeleStage K L T) r
          (fun P hP ↦
            cofinal_stage_subsingleton
              (K := K) (L := L) T P hP r))

/-- Reindex an exceptional family by the literal finite preimage used by
`DirectSum.mk`. -/
noncomputable def exceptionalCohomologyFamily
    (S : Finset (NumberFieldPlace K)) (r : ℕ) :
    ExceptionalPositiveCohomology K L S r ≃+
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          P ∈ exceptionalBasePrimes (K := K) S},
        OrbitPositiveCohomology K L r P.1) where
  toFun x P := x ⟨P.1,
    (exceptional_base_primes (K := K) S P.1).mp P.2⟩
  invFun x P := x ⟨P.1,
    (exceptional_base_primes (K := K) S P.1).mpr P.2⟩
  left_inv x := by funext P; rfl
  right_inv x := by funext P; rfl
  map_add' _ _ := rfl

/-- Extend an exceptional positive-cohomology family by zero to the direct
sum over all finite base primes. -/
noncomputable def resizedExceptionalDirect
    (S : Finset (NumberFieldPlace K)) (r : ℕ) :
    ExceptionalPositiveCohomology K L S r →+
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitPositiveCohomology K L r) :=
  (DirectSum.mk (OrbitPositiveCohomology K L r)
    (exceptionalBasePrimes (K := K) S)).comp
      (exceptionalCohomologyFamily
        (K := K) (L := L) S r).toAddMonoidHom

@[simp]
theorem exceptional_direct_sum
    (S : Finset (NumberFieldPlace K)) (r : ℕ)
    (x : ExceptionalPositiveCohomology K L S r)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    resizedExceptionalDirect
      (K := K) (L := L) S r x P = x ⟨P, hP⟩ := by
  change DirectSum.mk (OrbitPositiveCohomology K L r)
      (exceptionalBasePrimes (K := K) S)
      (exceptionalCohomologyFamily
        (K := K) (L := L) S r x) P = x ⟨P, hP⟩
  rw [DirectSum.mk_apply_of_mem
    ((exceptional_base_primes (K := K) S P).mpr hP)]
  rfl

@[simp]
theorem resized_exceptional_direct
    (S : Finset (NumberFieldPlace K)) (r : ℕ)
    (x : ExceptionalPositiveCohomology K L S r)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    resizedExceptionalDirect
      (K := K) (L := L) S r x P = 0 := by
  change DirectSum.mk (OrbitPositiveCohomology K L r)
      (exceptionalBasePrimes (K := K) S)
      (exceptionalCohomologyFamily
        (K := K) (L := L) S r x) P = 0
  rw [DirectSum.mk_apply_of_notMem]
  exact fun h ↦ hP ((exceptional_base_primes (K := K) S P).mp h)

/-- Extension by zero at a fixed stage is injective. -/
theorem exceptional_direct_injective
    (S : Finset (NumberFieldPlace K)) (r : ℕ) :
    Function.Injective
      (resizedExceptionalDirect
        (K := K) (L := L) S r) :=
  (DirectSum.mk_injective
    (exceptionalBasePrimes (K := K) S)).comp
      (exceptionalCohomologyFamily
        (K := K) (L := L) S r).injective

/-- Every finite-prime direct-sum element is supported at some finite idèle
stage. -/
theorem exceptional_direct_preimage
    (r : ℕ)
    (y : DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (OrbitPositiveCohomology K L r)) :
    ∃ (S : Finset (NumberFieldPlace K))
      (x : ExceptionalPositiveCohomology K L S r),
      resizedExceptionalDirect
        (K := K) (L := L) S r x = y := by
  classical
  let S : Finset (NumberFieldPlace K) :=
    y.support.image (fun P ↦ (Sum.inl P : NumberFieldPlace K))
  have hmem (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
      (Sum.inl P : NumberFieldPlace K) ∈ S ↔ P ∈ y.support := by
    simp only [S, Finset.mem_image]
    constructor
    · rintro ⟨Q, hQ, hQP⟩
      exact Sum.inl_injective hQP |>.symm ▸ hQ
    · exact fun hP ↦ ⟨P, hP, rfl⟩
  let x : ExceptionalPositiveCohomology K L S r := fun P ↦ y P.1
  refine ⟨S, x, ?_⟩
  apply DirectSum.ext
  intro P
  by_cases hP : P ∈ y.support
  · rw [exceptional_direct_sum
      (K := K) (L := L) S r x P ((hmem P).mpr hP)]
  · rw [resized_exceptional_direct
      (K := K) (L := L) S r x P (fun h ↦ hP ((hmem P).mp h))]
    exact (DFinsupp.notMem_support_iff.mp hP).symm

/-- Enlarge an exceptional positive-cohomology family by assigning zero to
every newly added finite prime. -/
noncomputable def resizedExceptionalTransition
    (r : ℕ) {S T : Finset (NumberFieldPlace K)} (_hST : S ⊆ T) :
    ExceptionalPositiveCohomology K L S r →+
      ExceptionalPositiveCohomology K L T r where
  toFun x P := if hP : (Sum.inl P.1 : NumberFieldPlace K) ∈ S then
    x ⟨P.1, hP⟩
  else
    0
  map_zero' := by
    funext P
    split <;> rfl
  map_add' x y := by
    funext P
    by_cases hP : (Sum.inl P.1 : NumberFieldPlace K) ∈ S
    · simp only [hP, ↓reduceDIte, Pi.add_apply]
    · simp only [hP, ↓reduceDIte, Pi.add_apply, add_zero]

@[simp]
theorem resized_exceptional_transition
    (r : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalPositiveCohomology K L S r)
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ T})
    (hP : (Sum.inl P.1 : NumberFieldPlace K) ∈ S) :
    resizedExceptionalTransition
      (K := K) (L := L) r hST x P = x ⟨P.1, hP⟩ := by
  simp [resizedExceptionalTransition, hP]

@[simp]
theorem resized_exceptional_cohomology
    (r : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalPositiveCohomology K L S r)
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ T})
    (hP : (Sum.inl P.1 : NumberFieldPlace K) ∉ S) :
    resizedExceptionalTransition
      (K := K) (L := L) r hST x P = 0 := by
  simp [resizedExceptionalTransition, hP]

/-- Extension by zero is compatible with enlargement of the exceptional
family. -/
theorem exceptional_direct_transition
    (r : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalPositiveCohomology K L S r) :
    resizedExceptionalDirect
        (K := K) (L := L) T r
        (resizedExceptionalTransition
          (K := K) (L := L) r hST x) =
      resizedExceptionalDirect
        (K := K) (L := L) S r x := by
  apply DirectSum.ext
  intro P
  by_cases hPS : (Sum.inl P : NumberFieldPlace K) ∈ S
  · have hPT : (Sum.inl P : NumberFieldPlace K) ∈ T := hST hPS
    rw [exceptional_direct_sum
      (K := K) (L := L) T r _ P hPT,
      resized_exceptional_transition
        (K := K) (L := L) r hST _ ⟨P, hPT⟩ hPS,
      exceptional_direct_sum
        (K := K) (L := L) S r x P hPS]
  · rw [resized_exceptional_direct
      (K := K) (L := L) S r x P hPS]
    by_cases hPT : (Sum.inl P : NumberFieldPlace K) ∈ T
    · rw [exceptional_direct_sum
        (K := K) (L := L) T r _ P hPT,
        resized_exceptional_cohomology
          (K := K) (L := L) r hST _ ⟨P, hPT⟩ hPS]
    · rw [resized_exceptional_direct
        (K := K) (L := L) T r _ P hPT]

omit [FiniteDimensional K L] in
/-- The positive finite-product coordinate map is natural for inclusion of
finite idèle stages. -/
theorem resized_pi_transition
    (r : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : groupCohomology
      (resizedStageRepresentation
        (K := K) (L := L) S) (r + 1))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    resizedCohomologyPi
        (K := K) (L := L) T r
        (stageCohomologyTransition
          (K := K) (L := L) (r + 1) hST q) P =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (stageOrbitTransition
          (K := K) (L := L) hST P) (r + 1)
        (resizedCohomologyPi
          (K := K) (L := L) S r q P) := by
  have hsquare := resized_stage_evaluation
    (K := K) (L := L) hST P
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedStageEvaluation
        (K := K) (L := L) T P) (r + 1)
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (ideleStageTransition
            (K := K) (L := L) hST) (r + 1) q) =
    groupCohomology.map (MonoidHom.id Gal(L/K))
      (stageOrbitTransition
        (K := K) (L := L) hST P) (r + 1)
      (groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedStageEvaluation
          (K := K) (L := L) S P) (r + 1) q)
  have hleft := congrArg (fun f ↦ f q)
    (groupCohomology.map_id_comp
      (ideleStageTransition (K := K) (L := L) hST)
      (resizedStageEvaluation (K := K) (L := L) T P)
      (r + 1))
  have hright := congrArg (fun f ↦ f q)
    (groupCohomology.map_id_comp
      (resizedStageEvaluation (K := K) (L := L) S P)
      (stageOrbitTransition (K := K) (L := L) hST P)
      (r + 1))
  have hmiddle :
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (ideleStageTransition
            (K := K) (L := L) hST ≫
            resizedStageEvaluation
              (K := K) (L := L) T P) (r + 1) q =
        groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedStageEvaluation
            (K := K) (L := L) S P ≫
            stageOrbitTransition
              (K := K) (L := L) hST P) (r + 1) q := by
    exact congrArg (fun φ ↦
      groupCohomology.map (MonoidHom.id Gal(L/K)) φ (r + 1) q) hsquare
  exact hleft.symm.trans (hmiddle.trans hright)

omit [FiniteDimensional K L] in
/-- At a prime already exceptional in the smaller stage, the unrestricted
orbit identification is unchanged by the stage transition. -/
theorem resized_full_transition
    (r : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hPS : (Sum.inl P : NumberFieldPlace K) ∈ S)
    (q : groupCohomology
      (stageOrbitRepresentation
        (K := K) (L := L) S P) (r + 1)) :
    stageCohomologyFull
        (K := K) (L := L) T P (hST hPS) (r + 1)
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (stageOrbitTransition
            (K := K) (L := L) hST P) (r + 1) q) =
      stageCohomologyFull
        (K := K) (L := L) S P hPS (r + 1) q := by
  have hsquare :
      stageOrbitTransition (K := K) (L := L) hST P ≫
          (stageIsoFull
            (K := K) (L := L) T P (hST hPS)).hom =
        (stageIsoFull
          (K := K) (L := L) S P hPS).hom := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    rfl
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (stageIsoFull
        (K := K) (L := L) T P (hST hPS)).hom (r + 1)
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (stageOrbitTransition
            (K := K) (L := L) hST P) (r + 1) q) =
    groupCohomology.map (MonoidHom.id Gal(L/K))
      (stageIsoFull
        (K := K) (L := L) S P hPS).hom (r + 1) q
  rw [← hsquare]
  exact congrArg (fun f ↦ f q)
    (groupCohomology.map_id_comp
      (stageOrbitTransition (K := K) (L := L) hST P)
      (stageIsoFull
        (K := K) (L := L) T P (hST hPS)).hom (r + 1)).symm

/-- The exceptional-coordinate equivalence on cofinal stages commutes with
actual stage inclusion and extension by zero. -/
theorem cofinal_stage_exceptional
    (r : ℕ) {T U : Finset (NumberFieldPlace K)} (hTU : T ⊆ U)
    (q : groupCohomology
      (resizedStageRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T)) (r + 1)) :
    cofinalStageExceptional
        (K := K) (L := L) U r
        (stageCohomologyTransition
          (K := K) (L := L) (r + 1)
          (cofinal_stage_mono (K := K) (L := L) hTU) q) =
      resizedExceptionalTransition
        (K := K) (L := L) r
        (cofinal_stage_mono (K := K) (L := L) hTU)
        (cofinalStageExceptional
          (K := K) (L := L) T r q) := by
  funext P
  let hStage : cofinalIdeleStage K L T ⊆
      cofinalIdeleStage K L U :=
    cofinal_stage_mono (K := K) (L := L) hTU
  by_cases hPT : (Sum.inl P.1 : NumberFieldPlace K) ∈
      cofinalIdeleStage K L T
  · change stageCohomologyFull
        (K := K) (L := L) (cofinalIdeleStage K L U) P.1 P.2 (r + 1)
        (resizedCohomologyPi
          (K := K) (L := L) (cofinalIdeleStage K L U) r
          (stageCohomologyTransition
            (K := K) (L := L) (r + 1) hStage q) P.1) = _
    rw [resized_pi_transition
      (K := K) (L := L) r hStage q P.1]
    rw [resized_exceptional_transition
      (K := K) (L := L) r hStage _ P hPT]
    exact resized_full_transition
      (K := K) (L := L) r hStage P.1 hPT _
  · change stageCohomologyFull
        (K := K) (L := L) (cofinalIdeleStage K L U) P.1 P.2 (r + 1)
        (resizedCohomologyPi
          (K := K) (L := L) (cofinalIdeleStage K L U) r
          (stageCohomologyTransition
            (K := K) (L := L) (r + 1) hStage q) P.1) = _
    rw [resized_exceptional_cohomology
      (K := K) (L := L) r hStage _ P hPT]
    rw [resized_pi_transition
      (K := K) (L := L) r hStage q P.1]
    letI := cofinal_stage_subsingleton
      (K := K) (L := L) T P.1 hPT r
    have hzero : resizedCohomologyPi
        (K := K) (L := L) (cofinalIdeleStage K L T) r q P.1 = 0 :=
      Subsingleton.elim _ _
    rw [hzero, map_zero,
      (stageCohomologyFull
        (K := K) (L := L) (cofinalIdeleStage K L U)
          P.1 P.2 (r + 1)).map_zero]

/-! ## Passing the supported stage decomposition to the direct limit -/

/-- The split target: infinite completion orbits and finite completion
orbits, each with finite support. -/
abbrev ResizedPositiveSplit
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (r : ℕ) :=
  DirectSum (InfinitePlace K) (fun v ↦ groupCohomology
      (resizedPlaceRepresentation
        (K := K) (L := L) (.inr v)) (r + 1)) ×
    DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (OrbitPositiveCohomology K L r)

/-- Map one cofinal idèle stage to the fixed split direct-sum target. -/
noncomputable def cofinalIdelesSplit
    (T : Finset (NumberFieldPlace K)) (r : ℕ) :
    groupCohomology
        (resizedPlacesRepresentation
          (K := K) (L := L) (cofinalIdeleStage K L T)) (r + 1) →+
      ResizedPositiveSplit K L r where
  toFun q :=
    let e := resizedIdelesCohomology
      (K := K) (L := L) (cofinalIdeleStage K L T) (r + 1) q
    ((idelesDirectSum
        (K := K) (L := L) (r + 1)) e.1,
      resizedExceptionalDirect
        (K := K) (L := L) (cofinalIdeleStage K L T) r
        (cofinalStageExceptional
          (K := K) (L := L) T r e.2))
  map_zero' := by
    simp
  map_add' x y := by
    simp

/-- The cofinal-stage map to the split target is injective. -/
theorem cofinal_ideles_places
    (T : Finset (NumberFieldPlace K)) (r : ℕ) :
    Function.Injective
      (cofinalIdelesSplit
        (K := K) (L := L) T r) := by
  intro q q' hqq'
  apply (resizedIdelesCohomology
    (K := K) (L := L) (cofinalIdeleStage K L T) (r + 1)).injective
  apply Prod.ext
  · apply (idelesDirectSum
      (K := K) (L := L) (r + 1)).injective
    exact congrArg Prod.fst hqq'
  · apply (cofinalStageExceptional
      (K := K) (L := L) T r).injective
    apply exceptional_direct_injective
      (K := K) (L := L) (cofinalIdeleStage K L T) r
    exact congrArg Prod.snd hqq'

/-- Cofinal-stage maps to the split target are unchanged by enlargement. -/
theorem cofinal_ideles_transition
    (r : ℕ) {T U : Finset (NumberFieldPlace K)} (hTU : T ⊆ U)
    (q : groupCohomology
      (resizedPlacesRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T)) (r + 1)) :
    cofinalIdelesSplit
        (K := K) (L := L) U r
        (resizedCohomologyTransition
          (K := K) (L := L) (r + 1)
          (cofinal_stage_mono (K := K) (L := L) hTU) q) =
      cofinalIdelesSplit
        (K := K) (L := L) T r q := by
  let hStage := cofinal_stage_mono (K := K) (L := L) hTU
  have hsplit :=
    resized_ideles_cohomology
      (K := K) (L := L) (r + 1) hStage q
  change
    ((idelesDirectSum
        (K := K) (L := L) (r + 1))
        (resizedIdelesCohomology
          (K := K) (L := L) (cofinalIdeleStage K L U) (r + 1)
          (resizedCohomologyTransition
            (K := K) (L := L) (r + 1) hStage q)).1,
      resizedExceptionalDirect
        (K := K) (L := L) (cofinalIdeleStage K L U) r
        (cofinalStageExceptional
          (K := K) (L := L) U r
          (resizedIdelesCohomology
            (K := K) (L := L) (cofinalIdeleStage K L U) (r + 1)
            (resizedCohomologyTransition
              (K := K) (L := L) (r + 1) hStage q)).2)) = _
  rw [hsplit]
  apply Prod.ext
  · rfl
  · rw [cofinal_stage_exceptional
      (K := K) (L := L) r hTU]
    exact exceptional_direct_transition
      (K := K) (L := L) r hStage _

/-- Promote an arbitrary finite idèle stage to the fixed cofinal family and
then map it to the split direct-sum target. -/
noncomputable def idelesPlacesStage
    (S : Finset (NumberFieldPlace K)) (r : ℕ) :
    groupCohomology
        (resizedPlacesRepresentation (K := K) (L := L) S) (r + 1) →+
      ResizedPositiveSplit K L r :=
  (cofinalIdelesSplit
    (K := K) (L := L) S r).comp
      (resizedCohomologyTransition
        (K := K) (L := L) (r + 1)
        (show S ⊆ cofinalIdeleStage K L S from
          Finset.subset_union_right)).toAddMonoidHom

/-- The promoted one-stage maps respect enlargement of the original finite
stage. -/
theorem ideles_stage_transition
    (r : ℕ) {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) (r + 1)) :
    idelesPlacesStage
        (K := K) (L := L) T r
        (resizedCohomologyTransition
          (K := K) (L := L) (r + 1) hST q) =
      idelesPlacesStage
        (K := K) (L := L) S r q := by
  let hS : S ⊆ cofinalIdeleStage K L S := Finset.subset_union_right
  let hT : T ⊆ cofinalIdeleStage K L T := Finset.subset_union_right
  let hC : cofinalIdeleStage K L S ⊆
      cofinalIdeleStage K L T :=
    cofinal_stage_mono (K := K) (L := L) hST
  have hpromote :
      resizedCohomologyTransition
          (K := K) (L := L) (r + 1) hT
          (resizedCohomologyTransition
            (K := K) (L := L) (r + 1) hST q) =
        resizedCohomologyTransition
          (K := K) (L := L) (r + 1) hC
          (resizedCohomologyTransition
            (K := K) (L := L) (r + 1) hS q) := by
    rw [ideles_places_comp,
      ideles_places_comp]
  change cofinalIdelesSplit
      (K := K) (L := L) T r
      (resizedCohomologyTransition
        (K := K) (L := L) (r + 1) hT
        (resizedCohomologyTransition
          (K := K) (L := L) (r + 1) hST q)) = _
  rw [hpromote]
  exact cofinal_ideles_transition
    (K := K) (L := L) r hST _

/-- The canonical map from the finite-stage direct limit to the split local
direct sums. -/
noncomputable def idelesLimitSplit
    (r : ℕ) :
    IdelesPlacesLimit K L (r + 1) →+
      ResizedPositiveSplit K L r where
  toFun := DirectLimit.lift
    (F := fun S : Finset (NumberFieldPlace K) ↦ groupCohomology
      (resizedPlacesRepresentation (K := K) (L := L) S) (r + 1))
    (fun _ _ h ↦ resizedCohomologyTransition
      (K := K) (L := L) (r + 1) h)
    (fun S q ↦ idelesPlacesStage
      (K := K) (L := L) S r q)
    (fun _ _ h q ↦
      (ideles_stage_transition
        (K := K) (L := L) r h q).symm)
  map_zero' := by
    rw [DirectLimit.zero_def (∅ : Finset (NumberFieldPlace K)),
      DirectLimit.lift_def]
    exact map_zero _
  map_add' q q' := by
    induction q, q' using DirectLimit.induction₂ with
    | _ S x y =>
        rw [DirectLimit.add_def, DirectLimit.lift_def,
          DirectLimit.lift_def, DirectLimit.lift_def]
        exact map_add _ x y

/-- The direct-limit map to the split local direct sums is injective. -/
theorem resized_limit_split
    (r : ℕ) : Function.Injective
      (idelesLimitSplit
        (K := K) (L := L) r) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hzero : idelesLimitSplit
      (K := K) (L := L) r (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  let F : Finset (NumberFieldPlace K) → Type u := fun S ↦ groupCohomology
    (resizedPlacesRepresentation (K := K) (L := L) S) (r + 1)
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) ↦
    resizedCohomologyTransition
      (K := K) (L := L) (r + 1) h
  obtain ⟨S, qS, hq⟩ := DirectLimit.exists_eq_mk f (q - q')
  rw [hq] at hzero ⊢
  let hS : S ⊆ cofinalIdeleStage K L S := Finset.subset_union_right
  have hstage : cofinalIdelesSplit
      (K := K) (L := L) S r (f S (cofinalIdeleStage K L S) hS qS) = 0 :=
    hzero
  have hqSzero : f S (cofinalIdeleStage K L S) hS qS = 0 :=
    cofinal_ideles_places
      (K := K) (L := L) S r (hstage.trans (map_zero _).symm)
  calc
    (⟦⟨S, qS⟩⟧ : DirectLimit F f) =
        ⟦⟨cofinalIdeleStage K L S,
          f S (cofinalIdeleStage K L S) hS qS⟩⟧ :=
      DirectLimit.eq_of_le (f := f) ⟨S, qS⟩
        (cofinalIdeleStage K L S) hS
    _ = ⟦⟨cofinalIdeleStage K L S, 0⟩⟧ :=
      congrArg (fun z ↦ (⟦⟨cofinalIdeleStage K L S, z⟩⟧ :
        DirectLimit F f)) hqSzero
    _ = 0 := (DirectLimit.zero_def _).symm

/-- The direct-limit map to the split local direct sums is surjective. -/
theorem resized_ideles_split
    (r : ℕ) : Function.Surjective
      (idelesLimitSplit
        (K := K) (L := L) r) := by
  intro y
  obtain ⟨S, xS, hxS⟩ :=
    exceptional_direct_preimage
      (K := K) (L := L) r y.2
  let C := cofinalIdeleStage K L S
  let hS : S ⊆ C := Finset.subset_union_right
  let xC : ExceptionalPositiveCohomology K L C r :=
    resizedExceptionalTransition
      (K := K) (L := L) r hS xS
  let qInf :=
    (idelesDirectSum
      (K := K) (L := L) (r + 1)).symm y.1
  let qFin :=
    (cofinalStageExceptional
      (K := K) (L := L) S r).symm xC
  let qC := (resizedIdelesCohomology
    (K := K) (L := L) C (r + 1)).symm (qInf, qFin)
  refine ⟨(⟦⟨C, qC⟩⟧ :
    IdelesPlacesLimit K L (r + 1)), ?_⟩
  change idelesPlacesStage
      (K := K) (L := L) C r qC = y
  let hC : C ⊆ cofinalIdeleStage K L C := Finset.subset_union_right
  rw [show idelesPlacesStage
      (K := K) (L := L) C r qC =
        cofinalIdelesSplit
          (K := K) (L := L) S r qC by
    exact cofinal_ideles_transition
      (K := K) (L := L) r hS qC]
  change
    ((idelesDirectSum
        (K := K) (L := L) (r + 1))
        (resizedIdelesCohomology
          (K := K) (L := L) C (r + 1) qC).1,
      resizedExceptionalDirect
        (K := K) (L := L) C r
        (cofinalStageExceptional
          (K := K) (L := L) S r
          (resizedIdelesCohomology
            (K := K) (L := L) C (r + 1) qC).2)) = y
  rw [show resizedIdelesCohomology
      (K := K) (L := L) C (r + 1) qC = (qInf, qFin) from
    AddEquiv.apply_symm_apply _ _]
  apply Prod.ext
  · exact AddEquiv.apply_symm_apply _ _
  · rw [show cofinalStageExceptional
        (K := K) (L := L) S r qFin = xC from AddEquiv.apply_symm_apply _ _]
    rw [exceptional_direct_transition
      (K := K) (L := L) r hS xS]
    exact hxS

/-- The finite-stage direct limit is the split direct sum of all infinite
and finite completion-orbit cohomology groups. -/
noncomputable def resizedIdelesSplit
    (r : ℕ) :
    IdelesPlacesLimit K L (r + 1) ≃+
      ResizedPositiveSplit K L r :=
  AddEquiv.ofBijective
    (idelesLimitSplit
      (K := K) (L := L) r)
    ⟨resized_limit_split
      (K := K) (L := L) r,
     resized_ideles_split
      (K := K) (L := L) r⟩

/-! ## Recombining finite and infinite places -/

/-- The finite completion orbit used in the stage limit is the completion
product at the corresponding finite number-field place, in every positive
degree. -/
noncomputable def resizedCohomologyPlace
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) (r : ℕ) :
    OrbitPositiveCohomology K L r P ≃+
      groupCohomology
        (resizedPlaceRepresentation
          (K := K) (L := L) (.inl P)) (r + 1) :=
  (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) (r + 1)).mapIso
    (resizedIsoOrbit
      (K := K) (L := L) P)).toLinearEquiv.toAddEquiv).symm

/-- Assemble the finite-prime completion-orbit comparisons. -/
noncomputable def resizedCohomologyDirect
    (r : ℕ) :
    DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitPositiveCohomology K L r) ≃+
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (fun P ↦ groupCohomology
          (resizedPlaceRepresentation
            (K := K) (L := L) (.inl P)) (r + 1)) :=
  DirectSum.congrAddEquiv fun P ↦
    resizedCohomologyPlace
      (K := K) (L := L) P r

private abbrev PlacePositiveCohomology
    (r : ℕ) (v : NumberFieldPlace K) : Type u :=
  groupCohomology
    (resizedPlaceRepresentation (K := K) (L := L) v) (r + 1)

private noncomputable def positiveDirectSplit
    (r : ℕ) :
    DirectSum (NumberFieldPlace K)
        (PlacePositiveCohomology (K := K) (L := L) r) →+
      (DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
          (fun P ↦ PlacePositiveCohomology
            (K := K) (L := L) r (.inl P))) ×
        DirectSum (InfinitePlace K)
          (fun v ↦ PlacePositiveCohomology
            (K := K) (L := L) r (.inr v)) where
  toFun x :=
    (DFinsupp.comapDomain Sum.inl Sum.inl_injective x,
      DFinsupp.comapDomain Sum.inr Sum.inr_injective x)
  map_zero' := by
    apply Prod.ext
    · exact DFinsupp.comapDomain_zero Sum.inl Sum.inl_injective
    · exact DFinsupp.comapDomain_zero Sum.inr Sum.inr_injective
  map_add' x y := by
    apply Prod.ext
    · exact DFinsupp.comapDomain_add Sum.inl Sum.inl_injective x y
    · exact DFinsupp.comapDomain_add Sum.inr Sum.inr_injective x y

private noncomputable def directSumInclusion
    (r : ℕ) :
    DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (fun P ↦ PlacePositiveCohomology
          (K := K) (L := L) r (.inl P)) →+
      DirectSum (NumberFieldPlace K)
        (PlacePositiveCohomology
          (K := K) (L := L) r) := by
  classical
  exact DirectSum.toAddMonoid fun P ↦
    DirectSum.of
      (PlacePositiveCohomology
        (K := K) (L := L) r) (.inl P)

private noncomputable def positiveDirectInclusion
    (r : ℕ) :
    DirectSum (InfinitePlace K)
        (fun v ↦ PlacePositiveCohomology
          (K := K) (L := L) r (.inr v)) →+
      DirectSum (NumberFieldPlace K)
        (PlacePositiveCohomology
          (K := K) (L := L) r) := by
  classical
  exact DirectSum.toAddMonoid fun v ↦
    DirectSum.of
      (PlacePositiveCohomology
        (K := K) (L := L) r) (.inr v)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
private theorem positive_completion_inclusion
    (r : ℕ)
    (a : DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (fun P ↦ PlacePositiveCohomology
        (K := K) (L := L) r (.inl P))) :
    DFinsupp.comapDomain Sum.inl Sum.inl_injective
        (directSumInclusion
          (K := K) (L := L) r a) = a := by
  classical
  induction a using DirectSum.induction_on with
  | zero =>
      exact DFinsupp.comapDomain_zero
        (β := PlacePositiveCohomology
          (K := K) (L := L) r) Sum.inl Sum.inl_injective
  | of P q =>
      simpa only [directSumInclusion,
          DirectSum.toAddMonoid_of] using
        (DFinsupp.comapDomain_single
          (β := PlacePositiveCohomology
            (K := K) (L := L) r) Sum.inl Sum.inl_injective P q)
  | add a b ha hb =>
      change (positiveDirectSplit
        (K := K) (L := L) r
        (directSumInclusion
          (K := K) (L := L) r (a + b))).1 = a + b
      rw [(directSumInclusion
          (K := K) (L := L) r).map_add,
        (positiveDirectSplit
          (K := K) (L := L) r).map_add]
      change DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (directSumInclusion
            (K := K) (L := L) r a) +
        DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (directSumInclusion
            (K := K) (L := L) r b) = a + b
      rw [ha, hb]
      rfl

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
private theorem positive_infinite_inclusion
    (r : ℕ)
    (b : DirectSum (InfinitePlace K)
      (fun v ↦ PlacePositiveCohomology
        (K := K) (L := L) r (.inr v))) :
    DFinsupp.comapDomain Sum.inl Sum.inl_injective
        (positiveDirectInclusion
          (K := K) (L := L) r b) = 0 := by
  classical
  induction b using DirectSum.induction_on with
  | zero =>
      exact DFinsupp.comapDomain_zero
        (β := PlacePositiveCohomology
          (K := K) (L := L) r) Sum.inl Sum.inl_injective
  | of v q =>
      apply DirectSum.ext
      intro P
      simp [positiveDirectInclusion,
        DFinsupp.comapDomain_apply, DirectSum.toAddMonoid_of,
        DirectSum.of_eq_of_ne]
  | add a b ha hb =>
      change (positiveDirectSplit
        (K := K) (L := L) r
        (positiveDirectInclusion
          (K := K) (L := L) r (a + b))).1 = 0
      rw [(positiveDirectInclusion
          (K := K) (L := L) r).map_add,
        (positiveDirectSplit
          (K := K) (L := L) r).map_add]
      change DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (positiveDirectInclusion
            (K := K) (L := L) r a) +
        DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (positiveDirectInclusion
            (K := K) (L := L) r b) = 0
      rw [ha, hb, add_zero]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
private theorem positive_inclusion_infinite
    (r : ℕ)
    (a : DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (fun P ↦ PlacePositiveCohomology
        (K := K) (L := L) r (.inl P))) :
    DFinsupp.comapDomain Sum.inr Sum.inr_injective
        (directSumInclusion
          (K := K) (L := L) r a) = 0 := by
  classical
  induction a using DirectSum.induction_on with
  | zero =>
      exact DFinsupp.comapDomain_zero
        (β := PlacePositiveCohomology
          (K := K) (L := L) r) Sum.inr Sum.inr_injective
  | of P q =>
      apply DirectSum.ext
      intro v
      simp [directSumInclusion,
        DFinsupp.comapDomain_apply, DirectSum.toAddMonoid_of,
        DirectSum.of_eq_of_ne]
  | add a b ha hb =>
      change (positiveDirectSplit
        (K := K) (L := L) r
        (directSumInclusion
          (K := K) (L := L) r (a + b))).2 = 0
      rw [(directSumInclusion
          (K := K) (L := L) r).map_add,
        (positiveDirectSplit
          (K := K) (L := L) r).map_add]
      change DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (directSumInclusion
            (K := K) (L := L) r a) +
        DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (directSumInclusion
            (K := K) (L := L) r b) = 0
      rw [ha, hb, add_zero]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
private theorem positive_split_inclusion
    (r : ℕ)
    (b : DirectSum (InfinitePlace K)
      (fun v ↦ PlacePositiveCohomology
        (K := K) (L := L) r (.inr v))) :
    DFinsupp.comapDomain Sum.inr Sum.inr_injective
        (positiveDirectInclusion
          (K := K) (L := L) r b) = b := by
  classical
  induction b using DirectSum.induction_on with
  | zero =>
      exact DFinsupp.comapDomain_zero
        (β := PlacePositiveCohomology
          (K := K) (L := L) r) Sum.inr Sum.inr_injective
  | of v q =>
      simpa only [positiveDirectInclusion,
          DirectSum.toAddMonoid_of] using
        (DFinsupp.comapDomain_single
          (β := PlacePositiveCohomology
            (K := K) (L := L) r) Sum.inr Sum.inr_injective v q)
  | add a b ha hb =>
      change (positiveDirectSplit
        (K := K) (L := L) r
        (positiveDirectInclusion
          (K := K) (L := L) r (a + b))).2 = a + b
      rw [(positiveDirectInclusion
          (K := K) (L := L) r).map_add,
        (positiveDirectSplit
          (K := K) (L := L) r).map_add]
      change DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (positiveDirectInclusion
            (K := K) (L := L) r a) +
        DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (positiveDirectInclusion
            (K := K) (L := L) r b) = a + b
      rw [ha, hb]
      rfl

/-- A direct sum over all number-field places is the product of its finite
and infinite direct sums, in every positive degree. -/
noncomputable def positiveDirectInfinite
    (r : ℕ) :
    DirectSum (NumberFieldPlace K)
        (PlacePositiveCohomology (K := K) (L := L) r) ≃+
      (DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
          (fun P ↦ PlacePositiveCohomology
            (K := K) (L := L) r (.inl P))) ×
        DirectSum (InfinitePlace K)
          (fun v ↦ PlacePositiveCohomology
            (K := K) (L := L) r (.inr v)) := by
  classical
  apply AddEquiv.ofBijective
    (positiveDirectSplit (K := K) (L := L) r)
  constructor
  · intro x y h
    apply DirectSum.ext
    intro v
    cases v with
    | inl P => exact congrArg (fun z ↦ z.1 P) h
    | inr v => exact congrArg (fun z ↦ z.2 v) h
  · intro y
    refine ⟨directSumInclusion
        (K := K) (L := L) r y.1 +
      positiveDirectInclusion
        (K := K) (L := L) r y.2, ?_⟩
    apply Prod.ext
    · change (positiveDirectSplit
          (K := K) (L := L) r
          (directSumInclusion
              (K := K) (L := L) r y.1 +
            positiveDirectInclusion
              (K := K) (L := L) r y.2)).1 = y.1
      rw [(positiveDirectSplit
        (K := K) (L := L) r).map_add]
      change DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (directSumInclusion
            (K := K) (L := L) r y.1) +
        DFinsupp.comapDomain Sum.inl Sum.inl_injective
          (positiveDirectInclusion
            (K := K) (L := L) r y.2) = y.1
      rw [positive_completion_inclusion,
        positive_infinite_inclusion, add_zero]
    · change (positiveDirectSplit
          (K := K) (L := L) r
          (directSumInclusion
              (K := K) (L := L) r y.1 +
            positiveDirectInclusion
              (K := K) (L := L) r y.2)).2 = y.2
      rw [(positiveDirectSplit
        (K := K) (L := L) r).map_add]
      change DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (directSumInclusion
            (K := K) (L := L) r y.1) +
        DFinsupp.comapDomain Sum.inr Sum.inr_injective
          (positiveDirectInclusion
            (K := K) (L := L) r y.2) = y.2
      rw [positive_inclusion_infinite,
        positive_split_inclusion, zero_add]

/-- Positive-degree cohomology of the concrete restricted idèle group is
the direct sum of the completion-product cohomology groups over all places. -/
noncomputable def resizedCohomologyDecomposition
    (r : ℕ) :
    groupCohomology (resizedConcreteRepresentation K L) (r + 1) ≃+
      DirectSum (NumberFieldPlace K)
        (fun v ↦ groupCohomology
          (resizedPlaceRepresentation
            (K := K) (L := L) v) (r + 1)) :=
  (idelesPlacesLimit
    (K := K) (L := L) r).symm |>.trans
    ((resizedIdelesSplit
      (K := K) (L := L) r).trans <|
      (AddEquiv.prodCongr
        (AddEquiv.refl _)
        (resizedCohomologyDirect
          (K := K) (L := L) r)).trans <|
        AddEquiv.prodComm |>.trans
          (positiveDirectInfinite
            (K := K) (L := L) r).symm)

/-! ## Placewise Shapiro and Proposition VII.2.5(b), positive degrees -/

/-- Shapiro identifies a completion orbit with one chosen completion in
every positive degree. -/
noncomputable def resizedCohomologyStabilizer
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) (r : ℕ) :
    groupCohomology
        (resizedPlaceRepresentation
          (K := K) (L := L) v) (r + 1) ≃+
      groupCohomology
        (chosenUnitsRepresentation
          (K := K) (L := L) completion v) (r + 1) := by
  cases v with
  | inl P =>
      letI : MulAction.IsPretransitive Gal(L/K)
          (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
        completion_above_pretransitive P
      exact (uliftShapiroIso
        (K := K) (L := L) (FinitePlace.mk P).val
          (hasseChosenPlace completion (.inl P))
          (r + 1)).toLinearEquiv.toAddEquiv
  | inr v =>
      letI : MulAction.IsPretransitive Gal(L/K)
          (CompletionPlacesAbove (L := L) v.1) :=
        places_above_pretransitive v
      exact (uliftShapiroIso
        (K := K) (L := L) v.1
          (hasseChosenPlace completion (.inr v))
          (r + 1)).toLinearEquiv.toAddEquiv

/-- Assemble the positive-degree Shapiro equivalences over all places. -/
noncomputable def cohomologyDirectStabilizer
    (completion : HasseCompletionData K L) (r : ℕ) :
    DirectSum (NumberFieldPlace K)
        (fun v ↦ groupCohomology
          (resizedPlaceRepresentation
            (K := K) (L := L) v) (r + 1)) ≃+
      DirectSum (NumberFieldPlace K)
        (fun v ↦ groupCohomology
          (chosenUnitsRepresentation
            (K := K) (L := L) completion v) (r + 1)) :=
  DirectSum.congrAddEquiv fun v ↦
    resizedCohomologyStabilizer
      (K := K) (L := L) completion v r

/-- **Proposition VII.2.5(b), positive-degree part.**  For the concrete
restricted idèle representation, ordinary cohomology in every degree at
least one is the direct sum of the local decomposition-group cohomology. -/
theorem resized_cohomology_direct
    (completion : HasseCompletionData K L) :
    CohomologyDirectSum
      (resizedConcreteRepresentation K L)
      (fun v ↦ CompletionPlaceStabilizer
        (hasseAbsoluteValue v)
        (hasseChosenPlace completion v))
      (fun v ↦ chosenUnitsRepresentation
        (K := K) (L := L) completion v) := by
  intro r
  exact ⟨(resizedCohomologyDecomposition
    (K := K) (L := L) r).trans
      (cohomologyDirectStabilizer
        (K := K) (L := L) completion r)⟩

end

end Towers.CField.HNorm
