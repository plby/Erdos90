import Submission.ClassField.BrauerLocalization.RelativeIdele
import Submission.ClassField.BrauerLocalization.H2Comparison
import Submission.ClassField.HasseNorm.IdeleDecomposition
import Submission.ClassField.CohomologyOps.RestrictionCompatibility
import Submission.ClassField.Shifting.ShapiroNaturality

/-!
# The diagonal completion-product map underlying Brauer localization

This file exposes the coefficient morphism which the restricted-idèle
`H²` decomposition must produce on the coordinate at a place `v`.  On
underlying multiplicative groups it is the diagonal embedding

`Lˣ → (∏ w | v, L_w)ˣ`.

Making this map explicit separates the remaining compatibility proof into
two naturality statements: the restricted-idèle decomposition must send the
principal-idèle map to this diagonal map, and Shapiro plus local crossed
products must send this diagonal map to Brauer scalar extension.
-/

namespace Submission.CField.BLoc

open CategoryTheory Representation groupCohomology
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.BGroups
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- A morphism into a coinduced representation, followed by Shapiro, is the
single cohomology map obtained by subgroup restriction and its adjoint
coefficient morphism. -/
private theorem res_coind_iso
    {k G : Type u} [CommRing k] [Group G]
    (H : Subgroup G) [H.FiniteIndex]
    {A : Rep k G} {B : Rep k H} (f : Rep.res H.subtype A ⟶ B)
    (n : ℕ) :
    groupCohomology.map (MonoidHom.id G)
        (Rep.resCoindToHom H.subtype A B f) n ≫
      (groupCohomology.coindIso B n).hom =
    groupCohomology.map H.subtype f n := by
  have hadj :
      Rep.resCoindToHom H.subtype A B f =
        (Rep.resCoindAdjunction k H.subtype).unit.app A ≫
          (Rep.coindFunctor k H.subtype).map f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext g
    rfl
  rw [hadj]
  let unit := (Rep.resCoindAdjunction k H.subtype).unit.app A
  let coindf := (Rep.coindFunctor k H.subtype).map f
  have hmap := groupCohomology.map_id_comp unit coindf n
  have hcoind :=
    Submission.CField.Shifting.coindIso_naturality f n
  calc
    groupCohomology.map (MonoidHom.id G) (unit ≫ coindf) n ≫
          (groupCohomology.coindIso B n).hom =
        (groupCohomology.map (MonoidHom.id G) unit n ≫
          groupCohomology.map (MonoidHom.id G) coindf n) ≫
          (groupCohomology.coindIso B n).hom :=
      congrArg (fun q => q ≫ (groupCohomology.coindIso B n).hom) hmap
    _ = groupCohomology.map (MonoidHom.id G) unit n ≫
        (groupCohomology.map (MonoidHom.id G) coindf n ≫
          (groupCohomology.coindIso B n).hom) := Category.assoc _ _ _
    _ = groupCohomology.map (MonoidHom.id G) unit n ≫
        ((groupCohomology.coindIso (Rep.res H.subtype A) n).hom ≫
          groupCohomology.map (MonoidHom.id H) f n) := by
      simpa [coindf] using congrArg
        (fun q => groupCohomology.map (MonoidHom.id G) unit n ≫ q)
        hcoind.symm
    _ = Submission.CField.COps.shapiroRestriction
          A H n ≫ groupCohomology.map (MonoidHom.id H) f n := by
      rfl
    _ = Submission.CField.COps.restriction
          A H n ≫ groupCohomology.map (MonoidHom.id H) f n := by
      rw [Submission.CField.COps.restriction_shapiro]
    _ = groupCohomology.map H.subtype f n := by
      rw [Submission.CField.COps.restriction,
        ← groupCohomology.map_comp]
      rfl

/-- The diagonal embedding of `L` into the product of all completions above
one absolute value of `K`. -/
noncomputable def globalEmbeddingHom
    (v : AbsoluteValue K ℝ) :
    L →+* (∀ w : CompletionPlacesAbove (L := L) v,
      CompletionFamilyAbove v w) where
  toFun := completionGlobalEmbedding v
  map_zero' := by
    funext w
    exact map_zero (completionEmbedding w.1)
  map_one' := by
    funext w
    exact map_one (completionEmbedding w.1)
  map_add' x y := by
    funext w
    exact map_add (completionEmbedding w.1) x y
  map_mul' x y := by
    funext w
    exact map_mul (completionEmbedding w.1) x y

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem global_embedding_hom
    (v : AbsoluteValue K ℝ) (x : L) :
    globalEmbeddingHom (L := L) v x =
      completionGlobalEmbedding v x :=
  rfl

/-- The diagonal embedding on multiplicative groups. -/
noncomputable def globalUnitsHom
    (v : AbsoluteValue K ℝ) :
    Lˣ →* (∀ w : CompletionPlacesAbove (L := L) v,
      CompletionFamilyAbove v w)ˣ :=
  Units.map (globalEmbeddingHom (L := L) v)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem global_units_val
    (v : AbsoluteValue K ℝ) (x : Lˣ) :
    ((globalUnitsHom (L := L) v x :
        (∀ w : CompletionPlacesAbove (L := L) v,
          CompletionFamilyAbove v w)ˣ) :
      ∀ w : CompletionPlacesAbove (L := L) v,
        CompletionFamilyAbove v w) =
      completionGlobalEmbedding v (x : L) :=
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- On the infinite idèle factor, the explicit normalized-completion
decomposition sends a principal idèle to the same diagonal family. -/
theorem infinite_ideles_normalized
    (x : Lˣ) (v : InfinitePlace K)
    (w : CompletionPlacesAbove (L := L) v.1) :
    (((infiniteIdelesUnits
        (K := K) (L := L)
        (principalIdele (NumberField.RingOfIntegers L) L x).1 v :
          ((z : CompletionPlacesAbove (L := L) v.1) →
            z.1.Completion)ˣ) :
      (z : CompletionPlacesAbove (L := L) v.1) →
        z.1.Completion) w) =
      completionEmbedding w.1 (x : L) := by
  rw [infinite_ideles_units]
  change ((MulEquiv.piUnits
    (principalIdele (NumberField.RingOfIntegers L) L x).1
      (normalizedInfinitePlace
        (K := K) (L := L) v w) :
      (normalizedInfinitePlace
        (K := K) (L := L) v w).1.Completionˣ) :
    (normalizedInfinitePlace
      (K := K) (L := L) v w).1.Completion) = _
  rw [principal_idele_infinite]
  rfl

private theorem
    pi_primes_above
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : Lˣ)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    piPrimesAbove
        (K := K) (L := L) P
        (globalUnitsHom
          (L := L) (FinitePlace.mk P).val x)
        (upperPrimesAbove (K := K) (L := L) P
          (placesAboveFactors
            (K := K) (L := L) P w)) =
      Units.map (algebraMap L
        (((upperPrimesAbove (K := K) (L := L) P
          (placesAboveFactors
            (K := K) (L := L) P w)).1).adicCompletion L)) x := by
  apply Units.ext
  change (Equiv.piCongrLeft
      (fun Q : FinitePrimesAbove (K := K) (L := L) P =>
        Q.1.adicCompletion L)
      (upperPrimesAbove (K := K) (L := L) P)
      (Equiv.piCongrLeft
        (fun Q : UpperPrimeFactors (K := K) (L := L) P =>
          (upperPrime (K := K) (L := L) P Q).adicCompletion L)
        (placesAboveFactors
          (K := K) (L := L) P)
        (fun z => completionPlaceAdic
          (K := K) (L := L) P z
            (completionEmbedding z.1 (x : L))))
      ((upperPrimesAbove (K := K) (L := L) P)
        ((placesAboveFactors
          (K := K) (L := L) P) w))) = _
  rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
  exact place_adic_embedding
    (K := K) (L := L) P w (x : L)

/-- The finite completion/adic reindexing also sends the diagonal family to
the finite coordinates of a principal idèle. -/
theorem pi_above_global
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : Lˣ) (Q : FinitePrimesAbove (K := K) (L := L) P) :
    piPrimesAbove
        (K := K) (L := L) P
        (globalUnitsHom
          (L := L) (FinitePlace.mk P).val x) Q =
      Units.map (algebraMap L (Q.1.adicCompletion L)) x := by
  let q := (upperPrimesAbove
    (K := K) (L := L) P).symm Q
  let w := (placesAboveFactors
    (K := K) (L := L) P).symm q
  have h :=
    pi_primes_above
      (K := K) (L := L) P x w
  dsimp only [w, q] at h
  rw [(placesAboveFactors
    (K := K) (L := L) P).apply_symm_apply] at h
  rw [(upperPrimesAbove
    (K := K) (L := L) P).apply_symm_apply] at h
  exact h

/-- The diagonal map as a morphism of the integral Galois
representations. -/
noncomputable def globalUnitsRepresentation
    (v : AbsoluteValue K ℝ) :
    Rep.ofAlgebraAutOnUnits K L ⟶
      completionUnitsRepresentation (K := K) (L := L) v :=
  Rep.ofHom
    { toLinearMap :=
        (MonoidHom.toAdditive
          (globalUnitsHom (L := L) v)).toIntLinearMap
      isIntertwining' := fun sigma => by
        apply LinearMap.ext
        intro x
        apply Additive.ofMul.injective
        apply Units.ext
        change completionGlobalEmbedding v
            (sigma (x.toMul : L)) =
          completionProductAction v sigma
            (completionGlobalEmbedding v (x.toMul : L))
        exact (action_global_embedding
          v sigma (x.toMul : L)).symm }

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem global_units_representation
    (v : AbsoluteValue K ℝ)
    (x : Rep.ofAlgebraAutOnUnits K L) :
    (globalUnitsRepresentation
      (K := K) (L := L) v).hom x =
      Additive.ofMul
        (globalUnitsHom (L := L) v x.toMul) :=
  rfl

/-- The same diagonal coefficient morphism in the `ULift ℤ`
presentations used by the number-field idèle decomposition. -/
noncomputable def resizedGlobalRepresentation
    (v : NumberFieldPlace K) :
    resizedRepresentation K L ⟶
      resizedPlaceRepresentation
        (K := K) (L := L) v :=
  uliftIntegralHom
    (globalUnitsRepresentation
      (K := K) (L := L) (hasseAbsoluteValue v))

/-- Restriction to the chosen decomposition group followed by the natural
embedding of `L` into the chosen completion. -/
noncomputable def unitsChosenRepresentation
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    Rep.res
        (CompletionPlaceStabilizer (hasseAbsoluteValue v)
          (hasseChosenPlace completion v)).subtype
        (resizedRepresentation K L) ⟶
      chosenUnitsRepresentation
        (K := K) (L := L) completion v := by
  let w := hasseChosenPlace completion v
  let f : Lˣ →* w.1.Completionˣ := Units.map (completionEmbedding w.1)
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (f x.toMul)
          map_add' := fun x y =>
            congrArg Additive.ofMul (f.map_mul x.toMul y.toMul)
          map_smul' := fun r x => map_zsmul f.toAdditive r.down x }
      isIntertwining' := ?_ }
  intro sigma
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Units.ext
  exact (place_stabilizer_embedding
    (hasseAbsoluteValue v) w sigma
      ((show Lˣ from x.toMul) : L)).symm

@[simp]
theorem resized_global_chosen
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K)
    (x : resizedRepresentation K L) :
    (unitsChosenRepresentation
      (K := K) (L := L) completion v).hom x =
      Additive.ofMul
        (Units.map
          (completionEmbedding
            (hasseChosenPlace completion v).1).toMonoidHom
          x.toMul) :=
  by
    change Additive.ofMul
      (Units.map
        (completionEmbedding
          (hasseChosenPlace completion v).1).toMonoidHom
        x.toMul) = _
    rfl

/-- Evaluation of the resized completion product at the completion selected
by `completion`. -/
noncomputable def resizedUnitsEvaluation
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    Rep.res
        (CompletionPlaceStabilizer (hasseAbsoluteValue v)
          (hasseChosenPlace completion v)).subtype
        (resizedPlaceRepresentation
          (K := K) (L := L) v) ⟶
      chosenUnitsRepresentation
        (K := K) (L := L) completion v :=
  uliftIntegralHom
    (completionUnitsEvaluation
      (K := K) (L := L) (hasseAbsoluteValue v)
        (hasseChosenPlace completion v))

/-- Evaluation of the diagonal completion family is the natural embedding
into the chosen completion. -/
theorem resized_global_evaluation
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    (Rep.resFunctor
      (CompletionPlaceStabilizer (hasseAbsoluteValue v)
        (hasseChosenPlace completion v)).subtype).map
      (resizedGlobalRepresentation
        (K := K) (L := L) v) ≫
      resizedUnitsEvaluation
        (K := K) (L := L) completion v =
    unitsChosenRepresentation
      (K := K) (L := L) completion v := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Units.ext
  rfl

/-- Under the explicit coinduced-module isomorphism, the diagonal map is the
adjunction map associated to the chosen-completion embedding. -/
theorem resized_global_induced
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (hasseAbsoluteValue v))] :
    resizedGlobalRepresentation
        (K := K) (L := L) v ≫
      (uliftInducedIso
        (K := K) (L := L) (hasseAbsoluteValue v)
          (hasseChosenPlace completion v)).hom =
    Rep.resCoindToHom
      (CompletionPlaceStabilizer (hasseAbsoluteValue v)
        (hasseChosenPlace completion v)).subtype
      (resizedRepresentation K L)
      (chosenUnitsRepresentation
        (K := K) (L := L) completion v)
      (unitsChosenRepresentation
        (K := K) (L := L) completion v) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext sigma
  apply Additive.toMul.injective
  apply Units.ext
  change completionProductAction (hasseAbsoluteValue v) sigma
      (completionGlobalEmbedding
        (hasseAbsoluteValue v) ((show Lˣ from x.toMul) : L))
      (hasseChosenPlace completion v) = _
  rw [action_global_embedding]
  rfl

/-- At a finite place, the coefficient square between principal idèles,
literal prime-adic evaluation, and the normalized completion product
commutes. -/
theorem global_units_naturality
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    resizedGlobalRepresentation
        (K := K) (L := L) (.inl P) ≫
      (resizedIsoOrbit
        (K := K) (L := L) P).hom =
    (resizedShortComplex K L).f ≫
      resizedConcreteAbove
        (K := K) (L := L) P := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change piPrimesAbove
      (K := K) (L := L) P
      (globalUnitsHom
        (L := L) (FinitePlace.mk P).val x.toMul) =
    primesAboveMonoid (K := K) (L := L) P
      (principalIdele (NumberField.RingOfIntegers L) L x.toMul)
  funext Q
  rw [pi_above_global]
  exact principal_idele_finite x.toMul Q.1

/-- Projection of the concrete idèle representation to its infinite
factor. -/
noncomputable def resizedInfiniteIdeles :
    resizedConcreteRepresentation K L ⟶
      resizedInfiniteRepresentation K L := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul x.toMul.1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := ?_ }
  intro sigma
  apply LinearMap.ext
  intro x
  rfl

/-- At an infinite place, principal-idèle projection, normalized regrouping,
and evaluation agree with the diagonal completion-product morphism. -/
theorem resized_infinite_naturality
    (v : InfinitePlace K) :
    resizedGlobalRepresentation
        (K := K) (L := L) (.inr v) =
      (resizedShortComplex K L).f ≫
        resizedInfiniteIdeles (K := K) (L := L) ≫
        (resizedIsoProducts
          (K := K) (L := L)).hom ≫
        resizedProductsEvaluation
          (K := K) (L := L) v := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change globalUnitsHom (L := L) v.1 x.toMul =
    infiniteIdelesUnits
      (K := K) (L := L)
      (principalIdele (NumberField.RingOfIntegers L) L x.toMul).1 v
  apply Units.ext
  funext w
  exact (infinite_ideles_normalized
    (K := K) (L := L) x.toMul v w).symm

/-- The degree-two cohomology map induced by the diagonal completion-product
embedding at `v`. -/
noncomputable def resizedGlobalUnits
    (v : NumberFieldPlace K) :
    H2 (resizedRepresentation K L) →+
      H2 (resizedPlaceRepresentation
        (K := K) (L := L) v) :=
  (groupCohomology.map (MonoidHom.id Gal(L/K))
    (resizedGlobalRepresentation
      (K := K) (L := L) v) 2).hom.toAddMonoidHom

/-- Restriction of a global-units `H²` class to the chosen decomposition
group, with coefficients embedded into the chosen completed field. -/
noncomputable def resizedGlobalChosen
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    H2 (resizedRepresentation K L) →+
      H2 (chosenUnitsRepresentation
        (K := K) (L := L) completion v) :=
  (groupCohomology.map
    (CompletionPlaceStabilizer (hasseAbsoluteValue v)
      (hasseChosenPlace completion v)).subtype
    (unitsChosenRepresentation
      (K := K) (L := L) completion v) 2).hom.toAddMonoidHom

/-- Shapiro sends the diagonal completion-product class to subgroup
restriction with coefficients embedded into the selected completion. -/
theorem resized_shapiro_diagonal
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (hasseAbsoluteValue v))]
    (x : H2 (resizedRepresentation K L)) :
    uliftCompletionUnits
        (K := K) (L := L) (hasseAbsoluteValue v)
        (hasseChosenPlace completion v)
        (resizedGlobalUnits
          (K := K) (L := L) v x) =
      resizedGlobalChosen
        (K := K) (L := L) completion v x := by
  let H := CompletionPlaceStabilizer (hasseAbsoluteValue v)
    (hasseChosenPlace completion v)
  let A := resizedRepresentation K L
  let B := chosenUnitsRepresentation
    (K := K) (L := L) completion v
  let diagonal := resizedGlobalRepresentation
    (K := K) (L := L) v
  let completed := unitsChosenRepresentation
    (K := K) (L := L) completion v
  let induced := uliftInducedIso
    (K := K) (L := L) (hasseAbsoluteValue v)
    (hasseChosenPlace completion v)
  let F := groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2
  have hinduced : diagonal ≫ induced.hom =
      Rep.resCoindToHom H.subtype A B completed :=
    resized_global_induced
      (K := K) (L := L) completion v
  have hshapiro := res_coind_iso
    H completed 2
  change (groupCohomology.coindIso B 2).hom
      (F.map induced.hom (F.map diagonal x)) =
    groupCohomology.map H.subtype completed 2 x
  calc
    _ = (groupCohomology.coindIso B 2).hom
        (F.map (diagonal ≫ induced.hom) x) := by
      rw [F.map_comp]
      rfl
    _ = (groupCohomology.coindIso B 2).hom
        (F.map (Rep.resCoindToHom H.subtype A B completed) x) := by
      rw [hinduced]
      rfl
    _ = _ := by
      simpa only [Category.comp_apply] using
        congrArg (fun q => q x) hshapiro

/-- Degree-two consequence of the finite coefficient square. -/
theorem resized_units_naturality
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : H2 (resizedRepresentation K L)) :
    groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedIsoOrbit
          (K := K) (L := L) P).hom 2
        (resizedGlobalUnits
          (K := K) (L := L) (.inl P) x) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedConcreteAbove
          (K := K) (L := L) P) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedShortComplex K L).f 2 x) := by
  let F := groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2
  change (F.map (resizedIsoOrbit
      (K := K) (L := L) P).hom)
        (F.map (resizedGlobalRepresentation
          (K := K) (L := L) (.inl P)) x) =
    (F.map (resizedConcreteAbove
      (K := K) (L := L) P))
        (F.map (resizedShortComplex K L).f x)
  calc
    _ = F.map
        (resizedGlobalRepresentation
          (K := K) (L := L) (.inl P) ≫
        (resizedIsoOrbit
          (K := K) (L := L) P).hom) x := by
          rw [F.map_comp]
          rfl
    _ = F.map ((resizedShortComplex K L).f ≫
        resizedConcreteAbove
          (K := K) (L := L) P) x := by
          rw [global_units_naturality]
          rfl
    _ = _ := by
      rw [F.map_comp]
      rfl

/-- Degree-two consequence of the infinite coefficient square. -/
theorem resized_global_naturality
    (v : InfinitePlace K)
    (x : H2 (resizedRepresentation K L)) :
    resizedGlobalUnits
        (K := K) (L := L) (.inr v) x =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedProductsEvaluation
          (K := K) (L := L) v) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIsoProducts
            (K := K) (L := L)).hom 2
          (groupCohomology.map (MonoidHom.id Gal(L/K))
            (resizedInfiniteIdeles (K := K) (L := L)) 2
            (groupCohomology.map (MonoidHom.id Gal(L/K))
              (resizedShortComplex K L).f 2 x))) := by
  let F := groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2
  change F.map (resizedGlobalRepresentation
      (K := K) (L := L) (.inr v)) x =
    F.map (resizedProductsEvaluation
      (K := K) (L := L) v)
      (F.map (resizedIsoProducts
        (K := K) (L := L)).hom
        (F.map (resizedInfiniteIdeles (K := K) (L := L))
          (F.map (resizedShortComplex K L).f x)))
  calc
    _ = F.map ((resizedShortComplex K L).f ≫
        resizedInfiniteIdeles (K := K) (L := L) ≫
        (resizedIsoProducts
          (K := K) (L := L)).hom ≫
        resizedProductsEvaluation
          (K := K) (L := L) v) x := by
      rw [resized_infinite_naturality]
      rfl
    _ = _ := by
      rw [F.map_comp, F.map_comp, F.map_comp]
      rfl

/-- Application rule for the inverse of the concrete-idèle/direct-limit
equivalence on a class coming from one finite stage. -/
theorem resized_ideles_inclusion
    (S : Finset (NumberFieldPlace K))
    (x : H2 (resizedPlacesRepresentation
      (K := K) (L := L) S)) :
    (resizedHLimit
        (K := K) (L := L)).symm
      (groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedInclusion (K := K) (L := L) S) 2 x) =
      (⟦⟨S, x⟩⟧ : ResizedPlacesLimit K L) := by
  apply (resizedHLimit
    (K := K) (L := L)).injective
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- Application rule for splitting an all-stage direct-limit class into its
constant infinite part and cofinal finite part. -/
theorem resized_ideles_mk
    (S : Finset (NumberFieldPlace K))
    (x : H2 (resizedPlacesRepresentation
      (K := K) (L := L) S)) :
    resizedIdelesLimit
        (K := K) (L := L)
        (⟦⟨S, x⟩⟧ : ResizedPlacesLimit K L) =
      resizedIdelesStage
        (K := K) (L := L) S x := by
  rfl

/-- Application rule for the cofinal finite-stage limit equivalence. -/
theorem resized_cofinal_mk
    (S : Finset (NumberFieldPlace K))
    (x : H2 (resizedStageRepresentation
      (K := K) (L := L) (cofinalIdeleStage K L S))) :
    resizedCofinalStage
        (K := K) (L := L)
        (⟦⟨S, x⟩⟧ : ResizedCofinalLimit K L) =
      cofinalStageDirect (K := K) (L := L) S x := by
  rfl

/-- Coordinate rule for the infinite-idèle completion-product direct-sum
equivalence. -/
theorem resized_ideles_direct
    (x : H2 (resizedInfiniteRepresentation K L))
    (v : InfinitePlace K) :
    resizedDirectSum
        (K := K) (L := L) x v =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedProductsEvaluation
          (K := K) (L := L) v) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIsoProducts
            (K := K) (L := L)).hom 2 x) := by
  rfl

/-- Inclusion of a literal finite idèle stage followed by projection to the
infinite idèles agrees with first regrouping the stage and then taking its
infinite factor. -/
theorem resized_inclusion_infinite
    (S : Finset (NumberFieldPlace K)) :
    resizedInclusion (K := K) (L := L) S ≫
        resizedInfiniteIdeles (K := K) (L := L) =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
        resizedPlacesInfinite
          (K := K) (L := L) S := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- At a finite prime already present in a literal stage, regrouping,
evaluation at that prime, and removal of the vacuous stage condition agree
with direct evaluation of the corresponding concrete idèle. -/
theorem resized_inclusion_finite
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    resizedInclusion (K := K) (L := L) S ≫
        resizedConcreteAbove
          (K := K) (L := L) P =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
        resizedIdelesFinite
          (K := K) (L := L) S ≫
        resizedStageEvaluation
          (K := K) (L := L) S P ≫
        (stageIsoFull
          (K := K) (L := L) S P hP).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  funext Q
  rfl

/-- Cohomological form of the infinite stage-projection square. -/
theorem ideles_places_fst
    (S : Finset (NumberFieldPlace K))
    (x : H2 (resizedPlacesRepresentation
      (K := K) (L := L) S)) :
    (resizedPlacesH
        (K := K) (L := L) S x).1 =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedInfiniteIdeles (K := K) (L := L)) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedInclusion (K := K) (L := L) S) 2 x) := by
  let F := groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2
  change F.map (resizedPlacesInfinite
      (K := K) (L := L) S)
      (F.map (resizedRepresentationIso
        (K := K) (L := L) S).hom x) =
    F.map (resizedInfiniteIdeles (K := K) (L := L))
      (F.map (resizedInclusion (K := K) (L := L) S) x)
  calc
    _ = F.map ((resizedRepresentationIso
          (K := K) (L := L) S).hom ≫
        resizedPlacesInfinite
          (K := K) (L := L) S) x := by
      rw [F.map_comp]
      rfl
    _ = F.map (resizedInclusion (K := K) (L := L) S ≫
        resizedInfiniteIdeles (K := K) (L := L)) x := by
      rw [resized_inclusion_infinite]
    _ = _ := by
      rw [F.map_comp]
      rfl

/-- Cohomological form of the finite stage-evaluation square. -/
theorem resized_ideles_snd
    (S : Finset (NumberFieldPlace K))
    (x : H2 (resizedPlacesRepresentation
      (K := K) (L := L) S))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    ideleStageFull
        (K := K) (L := L) S P hP
        (stageHPi
          (K := K) (L := L) S
          (resizedPlacesH
            (K := K) (L := L) S x).2 P) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedConcreteAbove
          (K := K) (L := L) P) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedInclusion (K := K) (L := L) S) 2 x) := by
  let F := groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2
  change F.map (stageIsoFull
      (K := K) (L := L) S P hP).hom
      (F.map (resizedStageEvaluation
        (K := K) (L := L) S P)
        (F.map (resizedIdelesFinite
          (K := K) (L := L) S)
          (F.map (resizedRepresentationIso
            (K := K) (L := L) S).hom x))) =
    F.map (resizedConcreteAbove
      (K := K) (L := L) P)
      (F.map (resizedInclusion
        (K := K) (L := L) S) x)
  calc
    _ = F.map ((resizedRepresentationIso
          (K := K) (L := L) S).hom ≫
        resizedIdelesFinite
          (K := K) (L := L) S ≫
        resizedStageEvaluation
          (K := K) (L := L) S P ≫
        (stageIsoFull
          (K := K) (L := L) S P hP).hom) x := by
      rw [F.map_comp, F.map_comp, F.map_comp]
      rfl
    _ = F.map (resizedInclusion (K := K) (L := L) S ≫
        resizedConcreteAbove
          (K := K) (L := L) P) x := by
      rw [resized_inclusion_finite]
    _ = _ := by
      rw [F.map_comp]
      rfl

/-- If a finite prime belongs to the auxiliary stage, the corresponding
coordinate of the promoted cofinal finite-stage class is direct evaluation
of the original concrete idèle class. -/
theorem cofinal_direct_promoted
    (T : Finset (NumberFieldPlace K))
    (x : H2 (resizedPlacesRepresentation
      (K := K) (L := L) T))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ T) :
    cofinalStageDirect
        (K := K) (L := L) T
        (resizedIdelesCofinal
          (K := K) (L := L) T x).2 P =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedConcreteAbove
          (K := K) (L := L) P) 2
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedInclusion (K := K) (L := L) T) 2 x) := by
  letI : DecidableEq (NumberFieldPlace K) :=
    finiteStageLimitNumberFieldPlaceDecidableEq
  let hT : T ⊆ cofinalIdeleStage K L T :=
    Finset.subset_union_right
  have hPC : (Sum.inl P : NumberFieldPlace K) ∈
      cofinalIdeleStage K L T := hT hP
  change resizedExceptionalSum
      (K := K) (L := L) (cofinalIdeleStage K L T)
      (cofinalHExceptional
        (K := K) (L := L) T
        (resizedIdelesCofinal
          (K := K) (L := L) T x).2) P = _
  rw [resized_exceptional_sum
    (K := K) (L := L) (cofinalIdeleStage K L T) _ P hPC]
  change ideleStageFull
      (K := K) (L := L) (cofinalIdeleStage K L T) P hPC
      (stageHPi
        (K := K) (L := L) (cofinalIdeleStage K L T)
        (resizedIdelesCofinal
          (K := K) (L := L) T x).2 P) = _
  change ideleStageFull
      (K := K) (L := L) (cofinalIdeleStage K L T) P hPC
      (stageHPi
        (K := K) (L := L) (cofinalIdeleStage K L T)
        (resizedPlacesH
          (K := K) (L := L) (cofinalIdeleStage K L T)
          (idelesPlacesTransition
            (K := K) (L := L) hT x)).2 P) = _
  rw [resized_ideles_snd]
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedConcreteAbove
        (K := K) (L := L) P) 2
      (resizedPlacesInclusion
        (K := K) (L := L) (cofinalIdeleStage K L T)
        (idelesPlacesTransition
          (K := K) (L := L) hT x)) = _
  rw [ideles_places_inclusion]
  rfl

/-- The infinite factor of the all-stage direct limit is induced by the
concrete infinite-idèle projection. -/
theorem resized_ideles_fst
    (z : ResizedPlacesLimit K L) :
    (resizedIdelesLimit
        (K := K) (L := L) z).1 =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedInfiniteIdeles (K := K) (L := L)) 2
        (resizedHLimit
          (K := K) (L := L) z) := by
  letI : DecidableEq (NumberFieldPlace K) :=
    finiteStageLimitNumberFieldPlaceDecidableEq
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) =>
    idelesPlacesTransition (K := K) (L := L) h
  obtain ⟨S, x, hz⟩ := DirectLimit.exists_eq_mk f z
  rw [hz]
  change (resizedIdelesStage
      (K := K) (L := L) S x).1 = _
  let hS : S ⊆ cofinalIdeleStage K L S :=
    Finset.subset_union_right
  have hsplit := ideles_places_transition
    (K := K) (L := L) hS x
  have hinfinite := congrArg Prod.fst hsplit
  change (resizedPlacesH
      (K := K) (L := L) (cofinalIdeleStage K L S)
      (idelesPlacesTransition
        (K := K) (L := L) hS x)).1 = _
  rw [hinfinite,
    ideles_places_fst]
  rfl

/-- Each finite coordinate of the cofinal direct-limit factor is induced
by evaluation of the concrete idèle representation at that finite orbit. -/
theorem resized_cofinal_limit
    (z : ResizedPlacesLimit K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    resizedCofinalStage
        (K := K) (L := L)
        (resizedIdelesLimit
          (K := K) (L := L) z).2 P =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedConcreteAbove
          (K := K) (L := L) P) 2
        (resizedHLimit
          (K := K) (L := L) z) := by
  letI : DecidableEq (NumberFieldPlace K) :=
    finiteStageLimitNumberFieldPlaceDecidableEq
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) =>
    idelesPlacesTransition (K := K) (L := L) h
  obtain ⟨S, x, hz⟩ := DirectLimit.exists_eq_mk f z
  let T : Finset (NumberFieldPlace K) :=
    insert (Sum.inl P) S
  let hST : S ⊆ T := Finset.subset_insert _ _
  let xT := idelesPlacesTransition
    (K := K) (L := L) hST x
  have hzT : z = (⟦⟨T, xT⟩⟧ : ResizedPlacesLimit K L) :=
    hz.trans (DirectLimit.eq_of_le (f := f) ⟨S, x⟩ T hST)
  rw [hzT, resized_ideles_mk]
  change resizedCofinalStage
      (K := K) (L := L)
      (⟦⟨T, (resizedIdelesCofinal
        (K := K) (L := L) T xT).2⟩⟧ :
        ResizedCofinalLimit K L) P = _
  rw [resized_cofinal_mk]
  rw [cofinal_direct_promoted
    (K := K) (L := L) T xT P]
  · rfl
  · exact Finset.mem_insert_self _ _

/-- Coordinate rule for the finite completion-orbit direct-sum
equivalence. -/
theorem resized_h_direct
    (x : DirectSum
      (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (OrbitH2 K L))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    resizedHDirect
        (K := K) (L := L) x P =
      resizedPlaceProduct
        (K := K) (L := L) P (x P) := by
  rfl

/-- The finite coordinate of the final idèle decomposition is the finite
coordinate produced by the cofinal-stage direct limit. -/
theorem resized_idele_decomposition
    (q : H2 (resizedConcreteRepresentation K L))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    resizedHDecomposition
        (K := K) (L := L) q (.inl P) =
      resizedHDirect
        (K := K) (L := L)
        (resizedCofinalStage
          (K := K) (L := L)
          (resizedIdelesLimit
            (K := K) (L := L)
            ((resizedHLimit
              (K := K) (L := L)).symm q)).2) P := by
  let a := resizedDirectSum
    (K := K) (L := L)
    (resizedIdelesLimit
      (K := K) (L := L)
      ((resizedHLimit
        (K := K) (L := L)).symm q)).1
  let b := resizedHDirect
    (K := K) (L := L)
    (resizedCofinalStage
      (K := K) (L := L)
      (resizedIdelesLimit
        (K := K) (L := L)
        ((resizedHLimit
          (K := K) (L := L)).symm q)).2)
  let e := completionDirectInfinite
    (K := K) (L := L)
  have h := congrArg (fun y => y.1 P) (e.apply_symm_apply (b, a))
  change e.symm (b, a) (.inl P) = b P at h
  simpa only [resizedHDecomposition,
    AddEquiv.trans_apply, a, b, e] using h

/-- The infinite coordinate of the final idèle decomposition is the
coordinate produced by the constant infinite-idèle factor. -/
theorem resized_decomposition_infinite
    (q : H2 (resizedConcreteRepresentation K L))
    (v : InfinitePlace K) :
    resizedHDecomposition
        (K := K) (L := L) q (.inr v) =
      resizedDirectSum
        (K := K) (L := L)
        (resizedIdelesLimit
          (K := K) (L := L)
          ((resizedHLimit
            (K := K) (L := L)).symm q)).1 v := by
  let a := resizedDirectSum
    (K := K) (L := L)
    (resizedIdelesLimit
      (K := K) (L := L)
      ((resizedHLimit
        (K := K) (L := L)).symm q)).1
  let b := resizedHDirect
    (K := K) (L := L)
    (resizedCofinalStage
      (K := K) (L := L)
      (resizedIdelesLimit
        (K := K) (L := L)
        ((resizedHLimit
          (K := K) (L := L)).symm q)).2)
  let e := completionDirectInfinite
    (K := K) (L := L)
  have h := congrArg (fun y => y.2 v) (e.apply_symm_apply (b, a))
  change e.symm (b, a) (.inr v) = a v at h
  simpa only [resizedHDecomposition,
    AddEquiv.trans_apply, a, b, e] using h

/-- Exact coordinate formulas still required from the direct-limit
construction of the restricted-idèle `H²` decomposition.  All maps in the
right-hand sides are already concrete representation morphisms. -/
def ResizedIdeleFormula : Prop :=
  (∀ (q : H2 (resizedConcreteRepresentation K L))
      (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
    resizedHDecomposition
        (K := K) (L := L) q (.inl P) =
      resizedPlaceProduct
        (K := K) (L := L) P
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedConcreteAbove
            (K := K) (L := L) P) 2 q)) ∧
  (∀ (q : H2 (resizedConcreteRepresentation K L))
      (v : InfinitePlace K),
    resizedHDecomposition
        (K := K) (L := L) q (.inr v) =
      resizedDirectSum
        (K := K) (L := L)
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedInfiniteIdeles (K := K) (L := L)) 2 q) v)

/-- The explicit direct-limit construction of the idèle decomposition has
the expected concrete finite and infinite coordinate maps. -/
theorem resizedIdeleFormula :
    ResizedIdeleFormula
      (K := K) (L := L) := by
  constructor
  · intro q P
    rw [resized_idele_decomposition,
      resized_h_direct,
      resized_cofinal_limit,
      AddEquiv.apply_symm_apply]
  · intro q v
    rw [resized_decomposition_infinite,
      resized_ideles_fst,
      AddEquiv.apply_symm_apply]

/-- The placewise composite of Shapiro and the inverse local crossed-product
comparison.  This is the coordinate map hidden inside the assembled direct
sum equivalence. -/
noncomputable def completionRelativeBrauer
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    H2 (resizedPlaceRepresentation
        (K := K) (L := L) v) ≃+
      Additive (localRelativeBrauer K L completion v) :=
  (resizedPlaceStabilizer
      (K := K) (L := L) completion v).trans
    (resizedChosen2
      K L completion v).symm

/-- The assembled direct-sum comparison acts coordinatewise by
`completionRelativeBrauer`. -/
theorem direct_relative_brauer
    (completion : HasseCompletionData K L)
    (y : DirectSum (NumberFieldPlace K)
      (fun v => H2 (resizedPlaceRepresentation
        (K := K) (L := L) v)))
    (v : NumberFieldPlace K) :
    directRelativeBrauer
        K L completion y v =
      completionRelativeBrauer
        (K := K) (L := L) completion v (y v) := by
  rfl

/-- Naturality statement still required from the explicit restricted-idèle
decomposition: a principal idèle has at `v` the diagonal completion-product
cohomology class. -/
def ResizedPrincipalNaturality : Prop :=
  ∀ (x : H2 (resizedRepresentation K L))
    (v : NumberFieldPlace K),
    (resizedHDecomposition
        (K := K) (L := L)
      ((groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedShortComplex K L).f 2).hom x)) v =
      resizedGlobalUnits
        (K := K) (L := L) v x

/-- The direct-limit coordinate formulas imply principal-idèle naturality;
the finite and infinite endpoint squares used here are already proved. -/
theorem resized_naturality_formula
    (hcoord : ResizedIdeleFormula
      (K := K) (L := L)) :
    ResizedPrincipalNaturality
      (K := K) (L := L) := by
  intro x v
  cases v with
  | inl P =>
      rw [hcoord.1]
      let e :=
        ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
          (resizedIsoOrbit
            (K := K) (L := L) P)).toLinearEquiv.toAddEquiv
      change e.symm _ = _
      apply e.injective
      rw [AddEquiv.apply_symm_apply]
      exact (resized_units_naturality
        (K := K) (L := L) P x).symm
  | inr v =>
      rw [hcoord.2,
        resized_ideles_direct]
      exact (resized_global_naturality
        (K := K) (L := L) v x).symm

/-- Principal-idèle naturality for the unconditional completion-product
decomposition. -/
theorem resizedPrincipalNaturality :
    ResizedPrincipalNaturality
      (K := K) (L := L) :=
  resized_naturality_formula
    (K := K) (L := L)
    (resizedIdeleFormula
      (K := K) (L := L))

/-- The second local naturality statement: Shapiro followed by local crossed
products sends the diagonal completion-product class to scalar extension of
the original Brauer class. -/
def CompletionBrauerCompatibility
    (completion : HasseCompletionData K L) : Prop :=
  ∀ (x : relativeBrauerGroup K L) (v : NumberFieldPlace K),
    (((completionRelativeBrauer
          (K := K) (L := L) completion v
        (resizedGlobalUnits
          (K := K) (L := L) v
          (relativeBrauerResized K L
            (Additive.ofMul x)))).toMul :
        localRelativeBrauer K L completion v) :
      BrauerGroup (hasseAbsoluteValue v).Completion) =
      brauerBaseChange K (hasseAbsoluteValue v).Completion
        (x : BrauerGroup K)

/-- Shapiro-side half of the remaining local square: the diagonal
completion-product class becomes subgroup restriction with coefficients
embedded in the chosen completion. -/
def ShapiroDiagonalNaturality
    (completion : HasseCompletionData K L) : Prop :=
  ∀ (x : H2 (resizedRepresentation K L))
    (v : NumberFieldPlace K),
    resizedPlaceStabilizer
        (K := K) (L := L) completion v
        (resizedGlobalUnits
          (K := K) (L := L) v x) =
      resizedGlobalChosen
        (K := K) (L := L) completion v x

/-- The explicit completion-product Shapiro equivalence satisfies diagonal
naturality at every finite and infinite number-field place. -/
theorem shapiroDiagonalNaturality
    (completion : HasseCompletionData K L) :
    ShapiroDiagonalNaturality
      (K := K) (L := L) completion := by
  intro x v
  cases v with
  | inl P =>
      letI : MulAction.IsPretransitive Gal(L/K)
          (CompletionPlacesAbove (L := L)
            (hasseAbsoluteValue (Sum.inl P))) := by
        simpa [hasseAbsoluteValue] using
          (completion_above_pretransitive P)
      exact resized_shapiro_diagonal
        (K := K) (L := L) completion (.inl P) x
  | inr v =>
      letI : MulAction.IsPretransitive Gal(L/K)
          (CompletionPlacesAbove (L := L)
            (hasseAbsoluteValue (Sum.inr v))) := by
        simpa [hasseAbsoluteValue] using
          (places_above_pretransitive v)
      exact resized_shapiro_diagonal
        (K := K) (L := L) completion (.inr v) x

/-- Crossed-product half of the remaining local square: completed subgroup
restriction represents scalar extension of the original global Brauer
class. -/
def ChosenCompletionCompatibility
    (completion : HasseCompletionData K L) : Prop :=
  ∀ (x : relativeBrauerGroup K L) (v : NumberFieldPlace K),
    ((((resizedChosen2
          K L completion v).symm
        (resizedGlobalChosen
          (K := K) (L := L) completion v
          (relativeBrauerResized K L
            (Additive.ofMul x)))).toMul :
        localRelativeBrauer K L completion v) :
      BrauerGroup (hasseAbsoluteValue v).Completion) =
      brauerBaseChange K (hasseAbsoluteValue v).Completion
        (x : BrauerGroup K)

/-- Finite-place part of the chosen-completion crossed-product comparison. -/
def CompletionCrossedCompatibility
    (completion : HasseCompletionData K L) : Prop :=
  ∀ (x : relativeBrauerGroup K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ((((resizedChosen2
          K L completion (.inl P)).symm
        (resizedGlobalChosen
          (K := K) (L := L) completion (.inl P)
          (relativeBrauerResized K L
            (Additive.ofMul x)))).toMul :
        localRelativeBrauer K L completion (.inl P)) :
      BrauerGroup
        (hasseAbsoluteValue (Sum.inl P)).Completion) =
      brauerBaseChange K
        (hasseAbsoluteValue (Sum.inl P)).Completion
        (x : BrauerGroup K)

/-- Infinite-place part of the chosen-completion crossed-product comparison. -/
def ChosenCrossedCompatibility
    (completion : HasseCompletionData K L) : Prop :=
  ∀ (x : relativeBrauerGroup K L) (v : InfinitePlace K),
    ((((resizedChosen2
          K L completion (.inr v)).symm
        (resizedGlobalChosen
          (K := K) (L := L) completion (.inr v)
          (relativeBrauerResized K L
            (Additive.ofMul x)))).toMul :
        localRelativeBrauer K L completion (.inr v)) :
      BrauerGroup
        (hasseAbsoluteValue (Sum.inr v)).Completion) =
      brauerBaseChange K
        (hasseAbsoluteValue (Sum.inr v)).Completion
        (x : BrauerGroup K)

/-- Finite and infinite crossed-product comparisons assemble into the
uniform chosen-completion statement. -/
theorem chosen_compatibility_infinite
    (completion : HasseCompletionData K L)
    (hfinite : CompletionCrossedCompatibility
      (K := K) (L := L) completion)
    (hinfinite : ChosenCrossedCompatibility
      (K := K) (L := L) completion) :
    ChosenCompletionCompatibility
      (K := K) (L := L) completion := by
  intro x v
  cases v with
  | inl P => exact hfinite x P
  | inr v => exact hinfinite x v

/-- The two atomic local compatibilities imply the placewise
Shapiro/crossed-product compatibility used by global localization. -/
theorem brauer_compatibility_parts
    (completion : HasseCompletionData K L)
    (hshapiro : ShapiroDiagonalNaturality
      (K := K) (L := L) completion)
    (hcrossed : ChosenCompletionCompatibility
      (K := K) (L := L) completion) :
    CompletionBrauerCompatibility
      (K := K) (L := L) completion := by
  intro x v
  change ((((resizedChosen2
        K L completion v).symm
      (resizedPlaceStabilizer
        (K := K) (L := L) completion v
        (resizedGlobalUnits
          (K := K) (L := L) v
          (relativeBrauerResized K L
            (Additive.ofMul x))))).toMul :
      localRelativeBrauer K L completion v) :
    BrauerGroup (hasseAbsoluteValue v).Completion) = _
  rw [hshapiro]
  exact hcrossed x v

/-- With Shapiro diagonal naturality proved unconditionally, the local
Brauer-coordinate theorem depends only on crossed-product base change. -/
theorem brauer_compatibility_crossed
    (completion : HasseCompletionData K L)
    (hcrossed : ChosenCompletionCompatibility
      (K := K) (L := L) completion) :
    CompletionBrauerCompatibility
      (K := K) (L := L) completion :=
  brauer_compatibility_parts
    (K := K) (L := L) completion
    (shapiroDiagonalNaturality
      (K := K) (L := L) completion) hcrossed

end

end Submission.CField.BLoc
