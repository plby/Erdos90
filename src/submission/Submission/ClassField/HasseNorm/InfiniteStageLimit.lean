import Submission.ClassField.HasseNorm.H2Limit
import Submission.ClassField.HasseNorm.FiniteDirectLimit

/-!
# Splitting the finite-stage idèle limit into infinite and finite parts

The infinite factor in every finite idèle stage is unrestricted and does
not change when the finite exceptional set is enlarged.  This file makes
that observation precise on degree-two cohomology and then passes it through
the directed limit.  The result separates the full finite-stage idèle limit
into the constant infinite-idèle cohomology and the cofinal finite-place
limit constructed in `HasseNormFiniteStageDirectLimit`.
-/

namespace Submission.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance infiniteFiniteStageNumberFieldPlaceDecidableEq :
    DecidableEq (NumberFieldPlace K) :=
  Classical.decEq _

/-- The constant infinite-idèle factor occurring in every finite idèle
stage. -/
noncomputable def resizedInfiniteRepresentation (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Rep (ULift.{u} ℤ) Gal(L/K) := by
  letI := infiniteIdelesAction (K := K) (L := L)
  exact uliftMulRepresentation
    (G := Gal(L/K)) (M := (InfiniteAdeleRing L)ˣ)

/-- Projection of the regrouped finite stage onto its constant infinite
factor. -/
noncomputable def resizedPlacesInfinite
    (S : Finset (NumberFieldPlace K)) :
    resizedIdelesRepresentation (K := K) (L := L) S ⟶
      resizedInfiniteRepresentation K L := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul x.toMul.1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := ?_ }
  intro sigma
  ext x
  rfl

set_option maxHeartbeats 1000000 in
-- Projecting through the regrouped representation unfolds the dependent
-- infinite/finite product equivalence.
set_option synthInstance.maxHeartbeats 300000 in
-- The dependent finite-place product requires deeper instance search.
/-- Projection of the regrouped finite stage onto its finite-place product
factor. -/
noncomputable def resizedIdelesFinite
    (S : Finset (NumberFieldPlace K)) :
    resizedIdelesRepresentation (K := K) (L := L) S ⟶
      resizedStageRepresentation
        (K := K) (L := L) S := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul x.toMul.2
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := ?_ }
  intro sigma
  ext x
  rfl

/-- The canonical pair of coordinate maps on degree-two cohomology of a
regrouped finite idèle stage. -/
noncomputable def resizedIdelesH
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedIdelesRepresentation
      (K := K) (L := L) S) →+
      H2 (resizedInfiniteRepresentation K L) ×
        H2 (resizedStageRepresentation
          (K := K) (L := L) S) where
  toFun q :=
    (groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedPlacesInfinite
        (K := K) (L := L) S) 2 q,
     groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedIdelesFinite
        (K := K) (L := L) S) 2 q)
  map_zero' := by
    ext <;> exact map_zero _
  map_add' x y := by
    ext <;> exact map_add _ x y

/-- Every pair of infinite and finite degree-two classes is represented by
one cocycle in the regrouped finite idèle stage. -/
theorem resized_places_surjective
    (S : Finset (NumberFieldPlace K)) :
    Function.Surjective
      (resizedIdelesH
        (K := K) (L := L) S) := by
  intro q
  rcases q with ⟨qInfinite, qFinite⟩
  induction qInfinite using H2_induction_on with
  | h x =>
    induction qFinite using H2_induction_on with
    | h y =>
      let zFun : Gal(L/K) × Gal(L/K) →
          resizedIdelesRepresentation
            (K := K) (L := L) S :=
        fun gh => Additive.ofMul ((x gh).toMul, (y gh).toMul)
      have hz : zFun ∈ cocycles₂
          (resizedIdelesRepresentation
            (K := K) (L := L) S) := by
        apply (mem_cocycles₂_iff zFun).2
        intro g h j
        apply Additive.toMul.injective
        apply Prod.ext
        · exact congrArg Additive.toMul
            ((mem_cocycles₂_iff x).1 x.2 g h j)
        · exact congrArg Additive.toMul
            ((mem_cocycles₂_iff y).1 y.2 g h j)
      let z : cocycles₂ (resizedIdelesRepresentation
          (K := K) (L := L) S) := ⟨zFun, hz⟩
      refine ⟨H2π _ z, ?_⟩
      apply Prod.ext
      · change groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedPlacesInfinite
              (K := K) (L := L) S) 2 (H2π _ z) = H2π _ x
        rw [H2π_comp_map_apply]
        congr 1
      · change groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedIdelesFinite
              (K := K) (L := L) S) 2 (H2π _ z) = H2π _ y
        rw [H2π_comp_map_apply]
        congr 1

/-- The pair of infinite and finite degree-two coordinate maps is
injective. -/
theorem resized_ideles_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (resizedIdelesH
        (K := K) (L := L) S) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hcoord : resizedIdelesH
      (K := K) (L := L) S (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  clear hqq'
  have hkernel (r : H2 (resizedIdelesRepresentation
      (K := K) (L := L) S))
      (hr : resizedIdelesH
        (K := K) (L := L) S r = 0) : r = 0 := by
    induction r using H2_induction_on with
    | h z =>
      have hinfinite :
          H2π (resizedInfiniteRepresentation K L)
            (mapCocycles₂ (MonoidHom.id Gal(L/K))
              (resizedPlacesInfinite
                (K := K) (L := L) S) z) = 0 := by
        rw [← H2π_comp_map_apply]
        exact congrArg Prod.fst hr
      have hfinite :
          H2π (resizedStageRepresentation
              (K := K) (L := L) S)
            (mapCocycles₂ (MonoidHom.id Gal(L/K))
              (resizedIdelesFinite
                (K := K) (L := L) S) z) = 0 := by
        rw [← H2π_comp_map_apply]
        exact congrArg Prod.snd hr
      obtain ⟨a, ha⟩ := (H2π_eq_zero_iff _).1 hinfinite
      obtain ⟨b, hb⟩ := (H2π_eq_zero_iff _).1 hfinite
      let c : Gal(L/K) →
          resizedIdelesRepresentation
            (K := K) (L := L) S :=
        fun g => Additive.ofMul ((a g).toMul, (b g).toMul)
      apply (H2π_eq_zero_iff z).2
      refine ⟨c, ?_⟩
      funext gh
      apply Additive.toMul.injective
      apply Prod.ext
      · have ha' := congrFun ha gh
        change
          (resizedInfiniteRepresentation K L).ρ gh.1 (a gh.2) -
              a (gh.1 * gh.2) + a gh.1 =
            Additive.ofMul (z gh).toMul.1 at ha'
        exact congrArg Additive.toMul ha'
      · have hb' := congrFun hb gh
        change
          (resizedStageRepresentation
              (K := K) (L := L) S).ρ gh.1 (b gh.2) -
              b (gh.1 * gh.2) + b gh.1 =
            Additive.ofMul (z gh).toMul.2 at hb'
        exact congrArg Additive.toMul hb'
  exact hkernel (q - q') hcoord

/-- Degree-two cohomology of the regrouped stage is the product of the
constant infinite factor and the finite-place stage factor. -/
noncomputable def resizedIdelesPlaces
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedIdelesRepresentation
      (K := K) (L := L) S) ≃+
      H2 (resizedInfiniteRepresentation K L) ×
        H2 (resizedStageRepresentation
          (K := K) (L := L) S) :=
  AddEquiv.ofBijective
    (resizedIdelesH
      (K := K) (L := L) S)
    ⟨resized_ideles_injective
      (K := K) (L := L) S,
     resized_places_surjective
      (K := K) (L := L) S⟩

/-- Degree-two cohomology of one literal finite idèle stage, split into
its infinite and finite factors. -/
noncomputable def resizedPlacesH
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedPlacesRepresentation (K := K) (L := L) S) ≃+
      H2 (resizedInfiniteRepresentation K L) ×
        H2 (resizedStageRepresentation
          (K := K) (L := L) S) :=
  (resizedIdelesProduct
    (K := K) (L := L) S).trans
      (resizedIdelesPlaces
        (K := K) (L := L) S)

set_option maxHeartbeats 1000000 in
-- Enlargement combines an identity map with a dependent exceptional-stage
-- inclusion and its equivariance proof.
set_option synthInstance.maxHeartbeats 300000 in
-- The enlarged dependent product requires deeper instance search.
/-- Enlargement of the finite exceptional set on the regrouped product:
identity on the infinite factor and inclusion on the finite factor. -/
noncomputable def resizedProductTransition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    resizedIdelesRepresentation (K := K) (L := L) S ⟶
      resizedIdelesRepresentation (K := K) (L := L) T := by
  apply Rep.ofHom
  let f := ideleStageInclusion (K := K) (L := L) hST
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (x.toMul.1, f x.toMul.2)
          map_add' := fun x y => by
            apply Additive.toMul.injective
            exact congrArg (fun z => (x.toMul.1 * y.toMul.1, z))
              (f.map_mul x.toMul.2 y.toMul.2)
          map_smul' := fun r x => by
            apply Additive.toMul.injective
            apply Prod.ext
            · rfl
            · exact map_zpow f x.toMul.2 r.down }
      isIntertwining' := ?_ }
  intro sigma
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Prod.ext
  · rfl
  · funext P
    apply Subtype.ext
    rfl

omit [FiniteDimensional K L] in
/-- Regrouping a stage commutes with enlargement of its exceptional set. -/
theorem resized_ideles_product
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    resizedIdeles (K := K) (L := L) hST ≫
        (resizedRepresentationIso
          (K := K) (L := L) T).hom =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
        resizedProductTransition
          (K := K) (L := L) hST := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Prod.ext
  · rfl
  · funext P
    apply Subtype.ext
    rfl

/-- The induced map on regrouped-product degree-two cohomology. -/
noncomputable def resizedIdelesTransition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    H2 (resizedIdelesRepresentation
      (K := K) (L := L) S) →+
      H2 (resizedIdelesRepresentation
        (K := K) (L := L) T) where
  toFun q := groupCohomology.map (MonoidHom.id Gal(L/K))
    (resizedProductTransition
      (K := K) (L := L) hST) 2 q
  map_zero' := map_zero _
  map_add' := map_add _

set_option maxHeartbeats 1000000 in
-- Naturality of the product-coordinate equivalence requires normalizing both
-- categorical product factors.
/-- The product-coordinate equivalence is natural: enlargement fixes the
infinite coordinate and applies the actual finite-stage transition to the
finite coordinate. -/
theorem resized_ideles_transition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : H2 (resizedIdelesRepresentation
      (K := K) (L := L) S)) :
    resizedIdelesPlaces
        (K := K) (L := L) T
        (resizedIdelesTransition
          (K := K) (L := L) hST q) =
      ((resizedIdelesPlaces
          (K := K) (L := L) S q).1,
       resizedStageH
          (K := K) (L := L) hST
          (resizedIdelesPlaces
            (K := K) (L := L) S q).2) := by
  apply Prod.ext
  · have hsquare :
        resizedProductTransition
            (K := K) (L := L) hST ≫
            resizedPlacesInfinite
              (K := K) (L := L) T =
          resizedPlacesInfinite
            (K := K) (L := L) S := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rfl
    change groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedPlacesInfinite
          (K := K) (L := L) T) 2
          (groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedProductTransition
              (K := K) (L := L) hST) 2 q) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedPlacesInfinite
          (K := K) (L := L) S) 2 q
    rw [← hsquare]
    exact congrArg (fun f => f q)
      (groupCohomology.map_id_comp
        (resizedProductTransition
          (K := K) (L := L) hST)
        (resizedPlacesInfinite
          (K := K) (L := L) T) 2).symm
  · have hsquare :
        resizedProductTransition
            (K := K) (L := L) hST ≫
            resizedIdelesFinite
              (K := K) (L := L) T =
          resizedIdelesFinite
              (K := K) (L := L) S ≫
            ideleStageTransition
              (K := K) (L := L) hST := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      funext P
      apply Subtype.ext
      rfl
    change groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedIdelesFinite
          (K := K) (L := L) T) 2
          (groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedProductTransition
              (K := K) (L := L) hST) 2 q) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (ideleStageTransition
          (K := K) (L := L) hST) 2
          (groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedIdelesFinite
              (K := K) (L := L) S) 2 q)
    have hleft := congrArg (fun f => f q)
      (groupCohomology.map_id_comp
        (resizedProductTransition
          (K := K) (L := L) hST)
        (resizedIdelesFinite
          (K := K) (L := L) T) 2)
    have hright := congrArg (fun f => f q)
      (groupCohomology.map_id_comp
        (resizedIdelesFinite
          (K := K) (L := L) S)
        (ideleStageTransition
          (K := K) (L := L) hST) 2)
    have hmiddle :
        groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedProductTransition
              (K := K) (L := L) hST ≫
              resizedIdelesFinite
                (K := K) (L := L) T) 2 q =
          groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedIdelesFinite
                (K := K) (L := L) S ≫
              ideleStageTransition
                (K := K) (L := L) hST) 2 q := by
      exact congrArg (fun f => f q)
        (congrArg (fun φ => groupCohomology.map
          (MonoidHom.id Gal(L/K)) φ 2) hsquare)
    exact hleft.symm.trans
      (hmiddle.trans hright)

set_option maxHeartbeats 1000000 in
-- The literal splitting naturality proof expands the finite-stage cohomology
-- transition through the regrouping isomorphism.
/-- The literal finite-stage splitting is natural for enlargement. -/
theorem ideles_places_transition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : H2 (resizedPlacesRepresentation
      (K := K) (L := L) S)) :
    resizedPlacesH
        (K := K) (L := L) T
        (idelesPlacesTransition
          (K := K) (L := L) hST q) =
      ((resizedPlacesH
          (K := K) (L := L) S q).1,
       resizedStageH
          (K := K) (L := L) hST
          (resizedPlacesH
            (K := K) (L := L) S q).2) := by
  have hsquare := resized_ideles_product
    (K := K) (L := L) hST
  have hleft := congrArg (fun f => f q)
    (groupCohomology.map_id_comp
      (resizedIdeles (K := K) (L := L) hST)
      (resizedRepresentationIso
        (K := K) (L := L) T).hom 2)
  have hright := congrArg (fun f => f q)
    (groupCohomology.map_id_comp
      (resizedRepresentationIso
        (K := K) (L := L) S).hom
      (resizedProductTransition
        (K := K) (L := L) hST) 2)
  have hmiddle :
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIdeles
              (K := K) (L := L) hST ≫
            (resizedRepresentationIso
              (K := K) (L := L) T).hom) 2 q =
        groupCohomology.map (MonoidHom.id Gal(L/K))
          ((resizedRepresentationIso
              (K := K) (L := L) S).hom ≫
            resizedProductTransition
              (K := K) (L := L) hST) 2 q := by
    exact congrArg (fun f => f q)
      (congrArg (fun φ => groupCohomology.map
        (MonoidHom.id Gal(L/K)) φ 2) hsquare)
  have hproduct :
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedRepresentationIso
            (K := K) (L := L) T).hom 2
          (groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedIdeles
              (K := K) (L := L) hST) 2 q) =
        groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedProductTransition
            (K := K) (L := L) hST) 2
          (groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedRepresentationIso
              (K := K) (L := L) S).hom 2 q) :=
    hleft.symm.trans (hmiddle.trans hright)
  change resizedIdelesPlaces
      (K := K) (L := L) T
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedRepresentationIso
            (K := K) (L := L) T).hom 2
          (groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedIdeles
              (K := K) (L := L) hST) 2 q)) = _
  rw [hproduct]
  exact resized_ideles_transition
    (K := K) (L := L) hST _

/-- Promote an arbitrary finite idèle stage to the fixed cofinal family and
then split its degree-two cohomology into infinite and finite parts. -/
noncomputable def resizedIdelesCofinal
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedPlacesRepresentation (K := K) (L := L) S) →+
      H2 (resizedInfiniteRepresentation K L) ×
        H2 (resizedStageRepresentation
          (K := K) (L := L) (cofinalIdeleStage K L S)) :=
  (resizedPlacesH
    (K := K) (L := L) (cofinalIdeleStage K L S)).toAddMonoidHom.comp
      (idelesPlacesTransition (K := K) (L := L)
        (show S ⊆ cofinalIdeleStage K L S from
          Finset.subset_union_right)).toAddMonoidHom

/-- Promoting to the cofinal family is compatible with enlargement of the
original stage. -/
theorem resized_ideles_cofinal
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : H2 (resizedPlacesRepresentation
      (K := K) (L := L) S)) :
    resizedIdelesCofinal
        (K := K) (L := L) T
        (idelesPlacesTransition
          (K := K) (L := L) hST q) =
      ((resizedIdelesCofinal
          (K := K) (L := L) S q).1,
       resizedCofinalTransition
          (K := K) (L := L) hST
          (resizedIdelesCofinal
            (K := K) (L := L) S q).2) := by
  let hS : S ⊆ cofinalIdeleStage K L S :=
    Finset.subset_union_right
  let hT : T ⊆ cofinalIdeleStage K L T :=
    Finset.subset_union_right
  let hC : cofinalIdeleStage K L S ⊆
      cofinalIdeleStage K L T :=
    cofinal_stage_mono (K := K) (L := L) hST
  have hpromote :
      idelesPlacesTransition (K := K) (L := L) hT
          (idelesPlacesTransition
            (K := K) (L := L) hST q) =
        idelesPlacesTransition (K := K) (L := L) hC
          (idelesPlacesTransition
            (K := K) (L := L) hS q) := by
    rw [resized_places_comp,
      resized_places_comp]
  change resizedPlacesH
      (K := K) (L := L) (cofinalIdeleStage K L T)
        (idelesPlacesTransition (K := K) (L := L) hT
          (idelesPlacesTransition
            (K := K) (L := L) hST q)) = _
  rw [hpromote]
  exact ideles_places_transition
    (K := K) (L := L) hC _

/-- The contribution of one literal stage to the split target consisting of
the infinite cohomology and the cofinal finite direct limit. -/
noncomputable def resizedIdelesStage
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedPlacesRepresentation (K := K) (L := L) S) →+
      H2 (resizedInfiniteRepresentation K L) ×
        ResizedCofinalLimit K L where
  toFun q :=
    let e := resizedIdelesCofinal
      (K := K) (L := L) S q
    (e.1, (⟦⟨S, e.2⟩⟧ : ResizedCofinalLimit K L))
  map_zero' := by
    rw [map_zero]
    apply Prod.ext
    · rfl
    · exact (DirectLimit.zero_def S).symm
  map_add' x y := by
    rw [map_add]
    apply Prod.ext
    · rfl
    · exact (DirectLimit.add_def S _ _).symm

/-- The one-stage maps to the split limit respect enlargement. -/
theorem resized_stage_transition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : H2 (resizedPlacesRepresentation
      (K := K) (L := L) S)) :
    resizedIdelesStage
        (K := K) (L := L) T
        (idelesPlacesTransition
          (K := K) (L := L) hST q) =
      resizedIdelesStage
        (K := K) (L := L) S q := by
  change
    ((resizedIdelesCofinal
        (K := K) (L := L) T
        (idelesPlacesTransition
          (K := K) (L := L) hST q)).1,
      (⟦⟨T, (resizedIdelesCofinal
        (K := K) (L := L) T
        (idelesPlacesTransition
          (K := K) (L := L) hST q)).2⟩⟧ :
        ResizedCofinalLimit K L)) =
    ((resizedIdelesCofinal
        (K := K) (L := L) S q).1,
      (⟦⟨S, (resizedIdelesCofinal
        (K := K) (L := L) S q).2⟩⟧ :
        ResizedCofinalLimit K L))
  rw [show resizedIdelesCofinal
      (K := K) (L := L) T
      (idelesPlacesTransition
        (K := K) (L := L) hST q) =
      ((resizedIdelesCofinal
        (K := K) (L := L) S q).1,
       resizedCofinalTransition
        (K := K) (L := L) hST
        (resizedIdelesCofinal
          (K := K) (L := L) S q).2) from
    resized_ideles_cofinal
      (K := K) (L := L) hST q]
  apply Prod.ext
  · rfl
  · exact (DirectLimit.eq_of_le
      (f := fun _ _ h => resizedCofinalTransition
        (K := K) (L := L) h)
      ⟨S, (resizedIdelesCofinal
        (K := K) (L := L) S q).2⟩ T hST).symm

/-- The canonical map from the all-stage idèle `H²` limit to the product
of the constant infinite `H²` and the cofinal finite-place `H²` limit. -/
noncomputable def resizedPlacesLimit :
    ResizedPlacesLimit K L →+
      H2 (resizedInfiniteRepresentation K L) ×
        ResizedCofinalLimit K L where
  toFun := DirectLimit.lift
    (F := fun S : Finset (NumberFieldPlace K) =>
      H2 (resizedPlacesRepresentation (K := K) (L := L) S))
    (fun _ _ h => idelesPlacesTransition
      (K := K) (L := L) h)
    (fun S q => resizedIdelesStage
      (K := K) (L := L) S q)
    (by
      intro S T hST q
      exact (resized_stage_transition
        (K := K) (L := L) hST q).symm)
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

set_option maxHeartbeats 2000000 in
-- Detecting zero at a larger stage combines direct-limit representatives with
-- both infinite and finite splitting naturality calculations.
/-- If the image of a class represented at one literal stage is zero in the
split target, then that representative is already zero at a larger literal
stage. -/
theorem resized_ideles_limit
    (S : Finset (NumberFieldPlace K))
    (qS : H2 (resizedPlacesRepresentation
      (K := K) (L := L) S))
    (hzero : resizedIdelesStage
      (K := K) (L := L) S qS = 0) :
    (⟦⟨S, qS⟩⟧ : ResizedPlacesLimit K L) = 0 := by
  let F : Finset (NumberFieldPlace K) → Type u := fun S =>
    H2 (resizedPlacesRepresentation (K := K) (L := L) S)
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) =>
    idelesPlacesTransition (K := K) (L := L) h
  let e := resizedIdelesCofinal
    (K := K) (L := L) S qS
  have heInf : e.1 = 0 := congrArg Prod.fst hzero
  have heFin :
      (⟦⟨S, e.2⟩⟧ : ResizedCofinalLimit K L) = 0 :=
    congrArg Prod.snd hzero
  rw [DirectLimit.zero_def S] at heFin
  obtain ⟨T, hST, hST', hT⟩ := Quotient.eq.mp heFin
  have hTzero : resizedCofinalTransition
      (K := K) (L := L) hST e.2 = 0 := by
    simpa using hT
  let hS : S ⊆ cofinalIdeleStage K L S :=
    Finset.subset_union_right
  let hCT : cofinalIdeleStage K L S ⊆
      cofinalIdeleStage K L T :=
    cofinal_stage_mono (K := K) (L := L) hST
  have hsplit :
      resizedPlacesH
          (K := K) (L := L) (cofinalIdeleStage K L T)
          (idelesPlacesTransition (K := K) (L := L) hCT
            (idelesPlacesTransition
              (K := K) (L := L) hS qS)) = 0 := by
    rw [ideles_places_transition]
    apply Prod.ext
    · exact heInf
    · exact hTzero
  have hstagezero :
      idelesPlacesTransition (K := K) (L := L) hCT
          (idelesPlacesTransition
            (K := K) (L := L) hS qS) = 0 := by
    apply (resizedPlacesH
      (K := K) (L := L) (cofinalIdeleStage K L T)).injective
    exact hsplit.trans
      (resizedPlacesH
        (K := K) (L := L) (cofinalIdeleStage K L T)).map_zero.symm
  have htotal : S ⊆ cofinalIdeleStage K L T := hS.trans hCT
  have hqSzero : idelesPlacesTransition
      (K := K) (L := L) htotal qS = 0 := by
    rw [← resized_places_comp]
    exact hstagezero
  calc
    (⟦⟨S, qS⟩⟧ : DirectLimit F f) =
        ⟦⟨cofinalIdeleStage K L T,
          idelesPlacesTransition
            (K := K) (L := L) htotal qS⟩⟧ :=
      DirectLimit.eq_of_le (f := f) ⟨S, qS⟩
        (cofinalIdeleStage K L T) htotal
    _ = ⟦⟨cofinalIdeleStage K L T, 0⟩⟧ :=
      congrArg (fun z =>
        (⟦⟨cofinalIdeleStage K L T, z⟩⟧ : DirectLimit F f)) hqSzero
    _ = 0 := (DirectLimit.zero_def _).symm

/-- The all-stage-to-split-limit map is injective. -/
theorem resized_ideles_places :
    Function.Injective
      (resizedPlacesLimit
        (K := K) (L := L)) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hzero : resizedPlacesLimit
      (K := K) (L := L) (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) =>
    idelesPlacesTransition (K := K) (L := L) h
  obtain ⟨S, qS, hqS⟩ := DirectLimit.exists_eq_mk f (q - q')
  have hstage : resizedIdelesStage
      (K := K) (L := L) S qS = 0 := by
    have hmapped := congrArg
      (resizedPlacesLimit
        (K := K) (L := L)) hqS
    exact hmapped.symm.trans hzero
  rw [hqS]
  exact resized_ideles_limit
    (K := K) (L := L) S qS hstage

/-- The all-stage-to-split-limit map is surjective. -/
theorem resized_ideles_surjective :
    Function.Surjective
      (resizedPlacesLimit
        (K := K) (L := L)) := by
  intro y
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) =>
    resizedCofinalTransition (K := K) (L := L) h
  obtain ⟨T, qT, hqT⟩ := DirectLimit.exists_eq_mk f y.2
  let C := cofinalIdeleStage K L T
  let qC : H2 (resizedPlacesRepresentation
      (K := K) (L := L) C) :=
    (resizedPlacesH
      (K := K) (L := L) C).symm (y.1, qT)
  refine ⟨(⟦⟨C, qC⟩⟧ : ResizedPlacesLimit K L), ?_⟩
  change resizedIdelesStage
      (K := K) (L := L) C qC = y
  let hC : C ⊆ cofinalIdeleStage K L C :=
    Finset.subset_union_right
  change
    ((resizedIdelesCofinal
        (K := K) (L := L) C qC).1,
      (⟦⟨C, (resizedIdelesCofinal
        (K := K) (L := L) C qC).2⟩⟧ :
        ResizedCofinalLimit K L)) = y
  rw [show resizedIdelesCofinal
      (K := K) (L := L) C qC =
        (y.1, resizedCofinalTransition
          (K := K) (L := L)
          (show T ⊆ C from Finset.subset_union_right) qT) by
    change resizedPlacesH
        (K := K) (L := L) (cofinalIdeleStage K L C)
        (idelesPlacesTransition
          (K := K) (L := L) hC qC) = _
    rw [ideles_places_transition]
    rw [AddEquiv.apply_symm_apply]
    rfl]
  apply Prod.ext
  · rfl
  · change
      (⟦⟨C, resizedCofinalTransition
        (K := K) (L := L)
        (show T ⊆ C from Finset.subset_union_right) qT⟩⟧ :
          ResizedCofinalLimit K L) = y.2
    rw [hqT]
    exact (DirectLimit.eq_of_le
      (f := f) ⟨T, qT⟩ C
        (show T ⊆ C from Finset.subset_union_right)).symm

/-- The direct limit of all finite idèle stages is the product of the
constant infinite-idèle cohomology and the cofinal finite-place limit. -/
noncomputable def resizedIdelesLimit :
    ResizedPlacesLimit K L ≃+
      H2 (resizedInfiniteRepresentation K L) ×
        ResizedCofinalLimit K L :=
  AddEquiv.ofBijective
    (resizedPlacesLimit
      (K := K) (L := L))
    ⟨resized_ideles_places
      (K := K) (L := L),
     resized_ideles_surjective
      (K := K) (L := L)⟩

end

end Submission.CField.HNorm
