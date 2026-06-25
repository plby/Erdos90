import Towers.ClassField.IdeleCohomology.CompletionProductAction
import Towers.ClassField.IdeleCohomology.InducedModule
import Towers.NumberTheory.Galois.FinitePlaceGroup

/-!
# Completion products and decomposition-group modules

This file begins the proof of Milne, Chapter VII, Proposition 2.2.  For a
chosen place `w0` above `v`, it constructs the action of its stabilizer on
`L_w0` by extending the corresponding global automorphisms.  It also packages
the additive and multiplicative representations which occur in Proposition
2.2 and the Shapiro decomposition of Proposition 2.3.
-/

namespace Towers.CField.ICohomo

open AbsoluteValue
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The decomposition group of a chosen extension `w0` of `v`. -/
abbrev CompletionPlaceStabilizer
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :=
  MulAction.stabilizer Gal(L/K) w0

/-- A stabilizer element preserves the absolute value belonging to `w0`. -/
theorem place_stabilizer_preserves
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0) (x : L) :
    w0.1 (sigma.1 x) = w0.1 x := by
  have hfix : sigma.1 • w0.1 = w0.1 := congrArg Subtype.val sigma.2
  simpa using (DFunLike.congr_fun hfix (sigma.1 x)).symm

/-- The endomorphism of `L_w0` extending an element of the decomposition
group. -/
def stabilizerRingHom
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0) :
    w0.1.Completion →+* w0.1.Completion :=
  Classical.choose (completion_universal w0.1
    ((completionEmbedding w0.1).comp sigma.1.toRingEquiv.toRingHom)
    (fun x => by
      rw [RingHom.comp_apply, norm_completionEmbedding]
      exact place_stabilizer_preserves v w0 sigma x))

/-- The extended stabilizer action is isometric. -/
theorem place_stabilizer_isometry
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0) :
    Isometry (stabilizerRingHom v w0 sigma) :=
  (Classical.choose_spec (completion_universal w0.1
    ((completionEmbedding w0.1).comp sigma.1.toRingEquiv.toRingHom)
    (fun x => by
      rw [RingHom.comp_apply, norm_completionEmbedding]
      exact place_stabilizer_preserves v w0 sigma x))).1.1

/-- The extended action agrees with the original automorphism on `L`. -/
@[simp]
theorem place_stabilizer_embedding
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0) (x : L) :
    stabilizerRingHom v w0 sigma (completionEmbedding w0.1 x) =
      completionEmbedding w0.1 (sigma.1 x) := by
  have hcomp := (Classical.choose_spec (completion_universal w0.1
    ((completionEmbedding w0.1).comp sigma.1.toRingEquiv.toRingHom)
    (fun y => by
      rw [RingHom.comp_apply, norm_completionEmbedding]
      exact place_stabilizer_preserves v w0 sigma y))).1.2
  exact RingHom.congr_fun hcomp x

/-- The decomposition group acts on its chosen completion. -/
@[reducible]
def stabilizerSemiringAction
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :
    MulSemiringAction (CompletionPlaceStabilizer v w0) w0.1.Completion where
  smul sigma := stabilizerRingHom v w0 sigma
  one_smul x := by
    have hfun :
        (stabilizerRingHom v w0 1 :
          w0.1.Completion → w0.1.Completion) = id :=
      (dense_range_embedding w0.1).equalizer
        (place_stabilizer_isometry v w0 1).continuous
        continuous_id
        (funext fun y => by
          change stabilizerRingHom v w0 1
              (completionEmbedding w0.1 y) = completionEmbedding w0.1 y
          rw [place_stabilizer_embedding]
          simp)
    exact congrFun hfun x
  mul_smul sigma tau x := by
    have hfun :
        (stabilizerRingHom v w0 (sigma * tau) :
          w0.1.Completion → w0.1.Completion) =
        fun y => stabilizerRingHom v w0 sigma
          (stabilizerRingHom v w0 tau y) :=
      (dense_range_embedding w0.1).equalizer
        (place_stabilizer_isometry v w0 (sigma * tau)).continuous
        ((place_stabilizer_isometry v w0 sigma).continuous.comp
          (place_stabilizer_isometry v w0 tau).continuous)
        (funext fun y => by
          change stabilizerRingHom v w0 (sigma * tau)
              (completionEmbedding w0.1 y) =
            stabilizerRingHom v w0 sigma
              (stabilizerRingHom v w0 tau
                (completionEmbedding w0.1 y))
          rw [place_stabilizer_embedding,
            place_stabilizer_embedding,
            place_stabilizer_embedding]
          rfl)
    exact congrFun hfun x
  smul_zero sigma := (stabilizerRingHom v w0 sigma).map_zero
  smul_add sigma x y := (stabilizerRingHom v w0 sigma).map_add x y
  smul_one sigma := (stabilizerRingHom v w0 sigma).map_one
  smul_mul sigma x y := (stabilizerRingHom v w0 sigma).map_mul x y

/-- A stabilizer element also fixes `w0` after applying its inverse. -/
theorem place_stabilizer_smul
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0) :
    sigma.1⁻¹ • w0 = w0 :=
  (sigma⁻¹).2

/-- Transport an element of the chosen fiber to the definitionally correct
source fiber for `completionFamilyTransport`. -/
def placeCastInv
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0) :
    CompletionFamilyAbove v w0 ≃+* CompletionFamilyAbove v (sigma.1⁻¹ • w0) :=
  RingEquiv.cast (R := CompletionFamilyAbove (L := L) v)
    (place_stabilizer_smul v w0 sigma).symm

private theorem completion_cast_embedding
    (v : AbsoluteValue K ℝ) {w w' : CompletionPlacesAbove (L := L) v}
    (h : w = w') (x : L) :
    RingEquiv.cast (R := CompletionFamilyAbove (L := L) v) h
        (completionEmbedding w.1 x) =
      completionEmbedding w'.1 x := by
  subst w'
  rfl

private theorem completion_cast_isometry
    (v : AbsoluteValue K ℝ) {w w' : CompletionPlacesAbove (L := L) v}
    (h : w = w') :
    Isometry (RingEquiv.cast (R := CompletionFamilyAbove (L := L) v) h) := by
  subst w'
  exact isometry_id

private theorem completion_family_cast
    (v : AbsoluteValue K ℝ) {w w' : CompletionPlacesAbove (L := L) v}
    (h : w = w')
    (alpha : ∀ u : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v u) :
    alpha w' = RingEquiv.cast (R := CompletionFamilyAbove (L := L) v) h (alpha w) := by
  subst w'
  rfl

/-- The fiber cast sends an embedded global element to the same embedded
element in the conjugate fiber. -/
@[simp]
theorem cast_inv_embedding
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0) (x : L) :
    placeCastInv v w0 sigma (completionEmbedding w0.1 x) =
      completionEmbedding (sigma.1⁻¹ • w0).1 x := by
  unfold placeCastInv
  exact completion_cast_embedding v
    (place_stabilizer_smul v w0 sigma).symm x

/-- The fiber cast is an isometry. -/
theorem cast_inv_isometry
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0) :
    Isometry (placeCastInv v w0 sigma) := by
  unfold placeCastInv
  exact completion_cast_isometry v
    (place_stabilizer_smul v w0 sigma).symm

/-- On the stabilized coordinate, the global transport agrees with the
local action obtained from the completion universal property. -/
theorem completion_transport_stabilizer
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0) (x : CompletionFamilyAbove v w0) :
    completionFamilyTransport v sigma.1 w0
        (placeCastInv v w0 sigma x) =
      stabilizerRingHom v w0 sigma x := by
  have hfun :
      (fun y : CompletionFamilyAbove v w0 =>
        completionFamilyTransport v sigma.1 w0
          (placeCastInv v w0 sigma y)) =
      fun y => stabilizerRingHom v w0 sigma y :=
    (dense_range_embedding w0.1).equalizer
      ((completionTransport_isometry sigma.1 w0.1).continuous.comp
        (cast_inv_isometry v w0 sigma).continuous)
      (place_stabilizer_isometry v w0 sigma).continuous
      (funext fun y => by
        change completionFamilyTransport v sigma.1 w0
            (placeCastInv v w0 sigma
              (completionEmbedding w0.1 y)) =
          stabilizerRingHom v w0 sigma
            (completionEmbedding w0.1 y)
        rw [cast_inv_embedding,
          place_stabilizer_embedding]
        exact completion_transport_embedding sigma.1 w0.1 y)
  exact congrFun hfun x

/-- Evaluation of the product action at a stabilized coordinate is the
local decomposition-group action. -/
theorem action_stabilizer_coordinate
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (sigma : CompletionPlaceStabilizer v w0)
    (alpha : ∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) :
    completionProductAction v sigma.1 alpha w0 =
      stabilizerRingHom v w0 sigma (alpha w0) := by
  rw [completion_product_action]
  rw [completion_family_cast v
    (place_stabilizer_smul v w0 sigma).symm alpha]
  exact completion_transport_stabilizer v w0 sigma (alpha w0)

/-- The additive integral representation on the full product of completions
above `v`. -/
def completionAdditiveRepresentation
    (v : AbsoluteValue K ℝ) : Rep ℤ Gal(L/K) := by
  letI : MulSemiringAction Gal(L/K)
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) :=
    completionSemiringAction v
  exact Rep.ofDistribMulAction ℤ Gal(L/K)
    (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w)

/-- The additive integral representation on the chosen completion. -/
def placeAdditiveRepresentation
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :
    Rep ℤ (CompletionPlaceStabilizer v w0) := by
  letI : MulSemiringAction (CompletionPlaceStabilizer v w0) w0.1.Completion :=
    stabilizerSemiringAction v w0
  exact Rep.ofDistribMulAction ℤ (CompletionPlaceStabilizer v w0) w0.1.Completion

/-- Evaluation at `w0`, regarded as a morphism from the restricted product
representation to the decomposition-group representation on `L_w0`. -/
def completionProductEvaluation
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :
    Rep.res (CompletionPlaceStabilizer v w0).subtype
        (completionAdditiveRepresentation v) ⟶
      placeAdditiveRepresentation v w0 :=
  Rep.ofHom
    { toLinearMap := LinearMap.proj w0
      isIntertwining' := fun sigma => by
        ext alpha
        exact action_stabilizer_coordinate v w0 sigma alpha }

/-- **Proposition VII.2.2, forward map.** The family `alpha` is sent to the
coinduced function whose value at `sigma` is
`sigma (alpha (sigma^-1 * w0))`. -/
def completionProductCoinduced
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :
    completionAdditiveRepresentation v ⟶
      milneInducedModule (CompletionPlaceStabilizer v w0)
        (placeAdditiveRepresentation v w0) :=
  Rep.resCoindToHom (CompletionPlaceStabilizer v w0).subtype
    (completionAdditiveRepresentation v)
    (placeAdditiveRepresentation v w0)
    (completionProductEvaluation v w0)

/-- The forward morphism of Proposition VII.2.2 has Milne's displayed
coordinate formula. -/
@[simp]
theorem completion_coinduced
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (alpha : ∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w)
    (sigma : Gal(L/K)) :
    ((completionProductCoinduced v w0) alpha).1 sigma =
      completionProductAction v sigma alpha w0 :=
  rfl

/-- The forward map of Proposition VII.2.2 is injective whenever the Galois
group acts transitively on the places above `v`. -/
theorem completion_coinduced_injective
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)] :
    Function.Injective (completionProductCoinduced v w0) := by
  intro alpha beta hab
  funext w
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Gal(L/K) w0 w
  apply (completionFamilyTransport v g⁻¹ w0).injective
  have heval := congrArg (fun f => f.1 g⁻¹) hab
  simpa only [completion_coinduced, completion_product_action,
    inv_inv] using heval

/-- A chosen Galois element carrying `w` back to the distinguished place
`w0`. -/
def completionPlaceReturn
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v) : Gal(L/K) :=
  Classical.choose (MulAction.exists_smul_eq Gal(L/K) w w0)

@[simp]
theorem place_return_smul
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v) :
    completionPlaceReturn v w0 w • w = w0 :=
  Classical.choose_spec (MulAction.exists_smul_eq Gal(L/K) w w0)

/-- A family supported at the distinguished place, used to express Milne's
inverse without exposing dependent casts in its definition. -/
def completionFamilyAt
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (x : CompletionFamilyAbove v w0) :
    ∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w :=
  by
    classical
    exact fun w => if h : w0 = w then
      RingEquiv.cast (R := CompletionFamilyAbove (L := L) v) h x
    else 0

@[simp]
theorem completion_family_self
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (x : CompletionFamilyAbove v w0) :
    completionFamilyAt v w0 x w0 = x := by
  simp [completionFamilyAt]

/-- Milne's inverse construction: if `r * w = w0`, the `w`-coordinate is
`r^-1 (f r)`. -/
def coinducedCompletionProduct
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)]
    (f : milneInducedModule (CompletionPlaceStabilizer v w0)
      (placeAdditiveRepresentation v w0)) :
    ∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w :=
  fun w =>
    let r := completionPlaceReturn v w0 w
    completionProductAction v r⁻¹
      (completionFamilyAt v w0 (f.1 r)) w

/-- Milne's inverse construction is a right inverse to the forward map. -/
theorem completion_product_coinduced
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)]
    (f : milneInducedModule (CompletionPlaceStabilizer v w0)
      (placeAdditiveRepresentation v w0)) :
    completionProductCoinduced v w0 (coinducedCompletionProduct v w0 f) = f := by
  apply Subtype.ext
  funext sigma
  let w := sigma⁻¹ • w0
  let r := completionPlaceReturn v w0 w
  have hr : r • w = w0 := place_return_smul v w0 w
  have hr_inv : r⁻¹ • w0 = w := by
    rw [← hr]
    simp
  let theta : CompletionPlaceStabilizer v w0 :=
    ⟨sigma * r⁻¹, by
      change (sigma * r⁻¹) • w0 = w0
      rw [mul_smul, hr_inv]
      simp [w]⟩
  change completionProductAction v sigma
      (coinducedCompletionProduct v w0 f) w0 = f.1 sigma
  rw [completion_product_action]
  change completionFamilyTransport v sigma w0
      (completionProductAction v r⁻¹
        (completionFamilyAt v w0 (f.1 r)) w) = f.1 sigma
  change completionProductAction v sigma
      (completionProductAction v r⁻¹
        (completionFamilyAt v w0 (f.1 r))) w0 = f.1 sigma
  rw [← completion_action_mul]
  change completionProductAction v theta.1
      (completionFamilyAt v w0 (f.1 r)) w0 = f.1 sigma
  rw [action_stabilizer_coordinate, completion_family_self]
  have hcov : f.1 r =
      (placeAdditiveRepresentation v w0).ρ theta⁻¹ (f.1 sigma) := by
    simpa [theta] using f.2 theta⁻¹ sigma
  change (placeAdditiveRepresentation v w0).ρ theta (f.1 r) = f.1 sigma
  rw [hcov, ← Module.End.mul_apply, ← map_mul]
  simp

/-- The forward map in Proposition VII.2.2 is surjective under transitivity
of the action on places above `v`. -/
theorem completion_coinduced_surjective
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)] :
    Function.Surjective (completionProductCoinduced v w0) := by
  intro f
  exact ⟨coinducedCompletionProduct v w0 f,
    completion_product_coinduced v w0 f⟩

/-- **Proposition VII.2.2 (additive form).** Under transitivity on the places
above `v`, the product of completions is the representation coinduced from
the completion at `w0`. -/
noncomputable def productsInducedIso
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)] :
    completionAdditiveRepresentation v ≅
      milneInducedModule (CompletionPlaceStabilizer v w0)
        (placeAdditiveRepresentation v w0) :=
  Rep.mkIso ((completionProductCoinduced v w0).hom.ofBijective
    ⟨completion_coinduced_injective v w0,
      completion_coinduced_surjective v w0⟩)

/-- The concrete completion representations satisfy the additive assertion
of Proposition VII.2.2. -/
theorem productsCompletionsInduced
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)] :
    ProductsCompletionsInduced
      (completionAdditiveRepresentation v)
      (CompletionPlaceStabilizer v w0)
      (placeAdditiveRepresentation v w0) :=
  ⟨productsInducedIso v w0⟩

/-- **Proposition VII.2.3 (additive completion form).** Cohomology of the
product of all completions above `v` is canonically identified, after a
choice of `w0`, with cohomology of the decomposition group acting on the
single completion `L_w0`. -/
noncomputable def productShapiroIso
    {K₀ L₀ : Type} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (v : AbsoluteValue K₀ ℝ) (w0 : CompletionPlacesAbove (L := L₀) v)
    [MulAction.IsPretransitive Gal(L₀/K₀) (CompletionPlacesAbove (L := L₀) v)]
    (r : ℕ) :
    groupCohomology
        (completionAdditiveRepresentation (K := K₀) (L := L₀) v) r ≅
      groupCohomology
        (placeAdditiveRepresentation (K := K₀) (L := L₀) v w0) r :=
  (groupCohomology.functor ℤ Gal(L₀/K₀) r).mapIso
      (productsInducedIso (K := K₀) (L := L₀) v w0) ≪≫
    shapiro
      (CompletionPlaceStabilizer (K := K₀) (L := L₀) v w0)
      (placeAdditiveRepresentation (K := K₀) (L := L₀) v w0) r

/-- The concrete completion representations satisfy Proposition VII.2.3 in
every nonnegative cohomological degree. -/
theorem completion_local_shapiro
    {K₀ L₀ : Type} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (v : AbsoluteValue K₀ ℝ) (w0 : CompletionPlacesAbove (L := L₀) v)
    [MulAction.IsPretransitive Gal(L₀/K₀) (CompletionPlacesAbove (L := L₀) v)] :
    LocalShapiroDecomposition
      (completionAdditiveRepresentation (K := K₀) (L := L₀) v)
      (CompletionPlaceStabilizer (K := K₀) (L := L₀) v w0)
      (placeAdditiveRepresentation (K := K₀) (L := L₀) v w0) := by
  intro r
  exact ⟨productShapiroIso (K₀ := K₀) (L₀ := L₀) v w0 r⟩

/-- The induced action on the multiplicative group of the chosen
completion. -/
@[reducible]
def completionDistribAction
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :
    MulDistribMulAction (CompletionPlaceStabilizer v w0) w0.1.Completionˣ := by
  letI : MulSemiringAction (CompletionPlaceStabilizer v w0) w0.1.Completion :=
    stabilizerSemiringAction v w0
  exact Units.mulDistribMulActionRight

/-- The integral representation on `L_w0^x`. -/
def placeUnitsRepresentation
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :
    Rep ℤ (CompletionPlaceStabilizer v w0) := by
  letI : MulDistribMulAction (CompletionPlaceStabilizer v w0) w0.1.Completionˣ :=
    completionDistribAction v w0
  exact Rep.ofMulDistribMulAction (CompletionPlaceStabilizer v w0) w0.1.Completionˣ

/-- Evaluation at `w0` on the multiplicative completion product. -/
noncomputable def unitsEvaluationMonoid
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :
    ((∀ w : CompletionPlacesAbove (L := L) v,
        CompletionFamilyAbove (L := L) v w)ˣ →*
      (CompletionFamilyAbove (L := L) v w0)ˣ) :=
  (Pi.evalMonoidHom (fun w : CompletionPlacesAbove (L := L) v ↦
      (CompletionFamilyAbove (L := L) v w)ˣ) w0).comp
    (completionUnitsPi (K := K) (L := L) v).toMonoidHom

/-- Evaluation at `w0` is equivariant for the decomposition-group action. -/
noncomputable def completionUnitsEvaluation
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :
    Rep.res (CompletionPlaceStabilizer v w0).subtype
        (completionUnitsRepresentation v) ⟶
      placeUnitsRepresentation v w0 :=
  Rep.ofHom
    { toLinearMap :=
        (unitsEvaluationMonoid v w0).toAdditive.toIntLinearMap
      isIntertwining' := fun sigma => by
        ext alpha
        exact action_stabilizer_coordinate v w0 sigma alpha.toMul.val }

/-- The multiplicative forward map in Proposition VII.2.2. -/
noncomputable def completionUnitsCoinduced
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v) :
    completionUnitsRepresentation v ⟶
      milneInducedModule (CompletionPlaceStabilizer v w0)
        (placeUnitsRepresentation v w0) :=
  Rep.resCoindToHom (CompletionPlaceStabilizer v w0).subtype
    (completionUnitsRepresentation v)
    (placeUnitsRepresentation v w0)
    (completionUnitsEvaluation v w0)

/-- The multiplicative forward map has Milne's displayed coordinate formula. -/
@[simp]
theorem product_units_coinduced
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (alpha : completionUnitsRepresentation v)
    (sigma : Gal(L/K)) :
    (((completionUnitsCoinduced v w0) alpha).1 sigma).toMul.val =
      completionProductAction v sigma alpha.toMul.val w0 :=
  rfl

/-- The multiplicative forward map is injective under transitivity on the
places above `v`. -/
theorem units_coinduced_injective
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)] :
    Function.Injective (completionUnitsCoinduced v w0) := by
  intro alpha beta hab
  apply Additive.toMul.injective
  apply Units.ext
  funext w
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Gal(L/K) w0 w
  apply (completionFamilyTransport v g⁻¹ w0).injective
  have heval := congrArg (fun f => (f.1 g⁻¹).toMul.val) hab
  simpa only [product_units_coinduced,
    completion_product_action, inv_inv] using heval

/-- A unit family supported at the distinguished place, with value `1` on
all other coordinates. -/
noncomputable def completionProductUnit
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (x : (CompletionFamilyAbove (L := L) v w0)ˣ) :
    (∀ w : CompletionPlacesAbove (L := L) v,
      CompletionFamilyAbove (L := L) v w)ˣ := by
  classical
  exact (completionUnitsPi (K := K) (L := L) v).symm
    (fun w => if h : w0 = w then
      Units.mapEquiv
        (RingEquiv.cast (R := CompletionFamilyAbove (L := L) v) h).toMulEquiv x
      else 1)

@[simp]
theorem completion_unit_self
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    (x : (CompletionFamilyAbove (L := L) v w0)ˣ) :
    (completionUnitsPi (K := K) (L := L) v)
      (completionProductUnit v w0 x) w0 = x := by
  simp only [completionProductUnit, MulEquiv.apply_symm_apply]
  apply Units.ext
  rfl

/-- Milne's inverse construction for the multiplicative completion product. -/
noncomputable def coinducedCompletionUnits
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)]
    (f : milneInducedModule (CompletionPlaceStabilizer v w0)
      (placeUnitsRepresentation v w0)) :
    completionUnitsRepresentation (K := K) (L := L) v :=
  Additive.ofMul <|
    (completionUnitsPi (K := K) (L := L) v).symm
      (fun w =>
        let r := completionPlaceReturn (K := K) (L := L) v w0 w
        (completionUnitsPi (K := K) (L := L) v
          ((unitsDistribAction (K := K) (L := L) v).smul r⁻¹
            (completionProductUnit v w0 (f.1 r).toMul))) w)

/-- Milne's multiplicative inverse is a right inverse to the forward map. -/
theorem completion_units_coinduced
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)]
    (f : milneInducedModule (CompletionPlaceStabilizer v w0)
      (placeUnitsRepresentation v w0)) :
    completionUnitsCoinduced v w0
        (coinducedCompletionUnits v w0 f) = f := by
  apply Subtype.ext
  funext sigma
  apply Additive.toMul.injective
  apply Units.ext
  let w := sigma⁻¹ • w0
  let r := completionPlaceReturn v w0 w
  have hr : r • w = w0 := place_return_smul v w0 w
  have hr_inv : r⁻¹ • w0 = w := by
    rw [← hr]
    simp
  let theta : CompletionPlaceStabilizer v w0 :=
    ⟨sigma * r⁻¹, by
      change (sigma * r⁻¹) • w0 = w0
      rw [mul_smul, hr_inv]
      simp [w]⟩
  change completionProductAction v sigma
      (coinducedCompletionUnits v w0 f).toMul.val w0 =
        (f.1 sigma).toMul.val
  change completionFamilyTransport v sigma w0
      ((completionUnitsPi (K := K) (L := L) v
        ((unitsDistribAction (K := K) (L := L) v).smul r⁻¹
          (completionProductUnit v w0 (f.1 r).toMul))) w) =
        (f.1 sigma).toMul.val
  change completionProductAction v sigma
      (completionProductAction v r⁻¹
        (completionProductUnit v w0 (f.1 r).toMul).val) w0 =
      (f.1 sigma).toMul.val
  rw [← completion_action_mul]
  change completionProductAction v theta.1
      (completionProductUnit v w0 (f.1 r).toMul).val w0 =
        (f.1 sigma).toMul.val
  rw [action_stabilizer_coordinate]
  rw [show (completionProductUnit v w0 (f.1 r).toMul).val w0 =
      (f.1 r).toMul.val by
    exact congrArg Units.val (completion_unit_self v w0 (f.1 r).toMul)]
  have hcov : f.1 r =
      (placeUnitsRepresentation v w0).ρ theta⁻¹ (f.1 sigma) := by
    simpa [theta] using f.2 theta⁻¹ sigma
  have hfinal :
      (placeUnitsRepresentation v w0).ρ theta (f.1 r) = f.1 sigma := by
    rw [hcov, ← Module.End.mul_apply, ← map_mul]
    simp
  exact congrArg (fun x => x.toMul.val) hfinal

/-- The multiplicative forward map is surjective. -/
theorem units_coinduced_surjective
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)] :
    Function.Surjective (completionUnitsCoinduced v w0) := by
  intro f
  exact ⟨coinducedCompletionUnits v w0 f,
    completion_units_coinduced v w0 f⟩

/-- **Proposition VII.2.2 (multiplicative form).** The product
`prod_{w | v} L_wˣ` is coinduced from `L_w0ˣ` with its decomposition-group
action. -/
noncomputable def completionInducedIso
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)] :
    completionUnitsRepresentation v ≅
      milneInducedModule (CompletionPlaceStabilizer v w0)
        (placeUnitsRepresentation v w0) :=
  Rep.mkIso ((completionUnitsCoinduced v w0).hom.ofBijective
    ⟨units_coinduced_injective v w0,
      units_coinduced_surjective v w0⟩)

/-- The concrete multiplicative completion representations satisfy
Proposition VII.2.2. -/
theorem completionUnitsInduced
    (v : AbsoluteValue K ℝ) (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K) (CompletionPlacesAbove (L := L) v)] :
    ProductsCompletionsInduced
      (completionUnitsRepresentation v)
      (CompletionPlaceStabilizer v w0)
      (placeUnitsRepresentation v w0) :=
  ⟨completionInducedIso v w0⟩

/-- **Proposition VII.2.3.** Shapiro identifies the cohomology of
`prod_{w | v} L_wˣ` with that of the single local multiplicative group
`L_w0ˣ` under its decomposition group. -/
noncomputable def completionShapiroIso
    {K₀ L₀ : Type} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (v : AbsoluteValue K₀ ℝ) (w0 : CompletionPlacesAbove (L := L₀) v)
    [MulAction.IsPretransitive Gal(L₀/K₀) (CompletionPlacesAbove (L := L₀) v)]
    (r : ℕ) :
    groupCohomology
        (completionUnitsRepresentation (K := K₀) (L := L₀) v) r ≅
      groupCohomology
        (placeUnitsRepresentation (K := K₀) (L := L₀) v w0) r :=
  (groupCohomology.functor ℤ Gal(L₀/K₀) r).mapIso
      (completionInducedIso (K := K₀) (L := L₀) v w0) ≪≫
    shapiro
      (CompletionPlaceStabilizer (K := K₀) (L := L₀) v w0)
      (placeUnitsRepresentation (K := K₀) (L := L₀) v w0) r

/-- The concrete multiplicative completion representations satisfy
Proposition VII.2.3 in every nonnegative cohomological degree. -/
theorem completion_units_shapiro
    {K₀ L₀ : Type} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (v : AbsoluteValue K₀ ℝ) (w0 : CompletionPlacesAbove (L := L₀) v)
    [MulAction.IsPretransitive Gal(L₀/K₀) (CompletionPlacesAbove (L := L₀) v)] :
    LocalShapiroDecomposition
      (completionUnitsRepresentation (K := K₀) (L := L₀) v)
      (CompletionPlaceStabilizer (K := K₀) (L := L₀) v w0)
      (placeUnitsRepresentation (K := K₀) (L := L₀) v w0) := by
  intro r
  exact ⟨completionShapiroIso (K₀ := K₀) (L₀ := L₀) v w0 r⟩

/-- Proposition VII.2.2 for a finite place of a number field.  In this
arithmetic specialization, transitivity of the Galois action on the places
above `p` is a theorem rather than an additional hypothesis. -/
noncomputable def unitsInducedIso
    {K₀ L₀ : Type} [Field K₀] [Field L₀]
    [NumberField K₀] [NumberField L₀] [Algebra K₀ L₀]
    [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K₀))
    (w0 : CompletionPlacesAbove (L := L₀) (FinitePlace.mk p).val) :
    completionUnitsRepresentation (K := K₀) (L := L₀)
        (FinitePlace.mk p).val ≅
      milneInducedModule
        (CompletionPlaceStabilizer (K := K₀) (L := L₀)
          (FinitePlace.mk p).val w0)
        (placeUnitsRepresentation (K := K₀) (L := L₀)
          (FinitePlace.mk p).val w0) := by
  letI := completion_above_pretransitive (K := K₀) (L := L₀) p
  exact completionInducedIso (K := K₀) (L := L₀)
    (FinitePlace.mk p).val w0

/-- **Proposition VII.2.3, finite-place form.** For a finite place `p`, the
cohomology of the multiplicative completion product is the cohomology of one
completion under its decomposition group, with no extra transitivity
assumption. -/
noncomputable def unitsShapiroIso
    {K₀ L₀ : Type} [Field K₀] [Field L₀]
    [NumberField K₀] [NumberField L₀] [Algebra K₀ L₀]
    [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K₀))
    (w0 : CompletionPlacesAbove (L := L₀) (FinitePlace.mk p).val)
    (r : ℕ) :
    groupCohomology
        (completionUnitsRepresentation (K := K₀) (L := L₀)
          (FinitePlace.mk p).val) r ≅
      groupCohomology
        (placeUnitsRepresentation (K := K₀) (L := L₀)
          (FinitePlace.mk p).val w0) r := by
  letI := completion_above_pretransitive (K := K₀) (L := L₀) p
  exact completionShapiroIso (K₀ := K₀) (L₀ := L₀)
    (FinitePlace.mk p).val w0 r

end

end Towers.CField.ICohomo
