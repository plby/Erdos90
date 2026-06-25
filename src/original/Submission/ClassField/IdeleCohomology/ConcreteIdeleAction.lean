import Submission.ClassField.IdeleCohomology.FiniteIdeleAction
import Submission.ClassField.IdeleCohomology.InfiniteIdeleAction
import Submission.ClassField.IdeleCohomology.RestrictedProductAction

/-!
# The concrete Galois action on number-field ideles

This file combines the finite restricted-product action and the action on
the product of archimedean completions.  The result is the actual
`IAData` used in Chapter VII.
-/

namespace Submission.CField.ICohomo

open Filter IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
/-- Continuous ring equivalences between two infinite-place completions are
equal when they agree on the dense image of the number field. -/
theorem infinite_ext_continuous
    (v w : InfinitePlace L)
    (e f : v.Completion ≃+* w.Completion)
    (he : Continuous e) (hf : Continuous f)
    (h : ∀ x : L, e (completionEmbedding v.1 x) =
      f (completionEmbedding v.1 x)) :
    e = f := by
  apply RingEquiv.ext
  intro y
  have hfun : (fun z : v.Completion ↦ e z) = fun z ↦ f z :=
    (dense_range_embedding v.1).equalizer he hf (funext h)
  exact congrFun hfun y

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- The explicit action in `InfiniteIdeleAction` agrees with Mathlib's
standard action on infinite places. -/
theorem infinite_action_smul
    (sigma : Gal(L/K)) (w : InfinitePlace L) :
    infinitePlaceAction sigma w = sigma • w := by
  apply Subtype.ext
  exact infinite_action_val sigma w

omit [NumberField L] in
private theorem infinite_place_embedding
    {v w : InfinitePlace L} (h : v = w) (x : L) :
    RingEquiv.cast (R := fun u : InfinitePlace L ↦ u.Completion) h
        (completionEmbedding v.1 x) = completionEmbedding w.1 x := by
  subst w
  rfl

omit [NumberField L] in
private theorem infinite_place_continuous
    {v w : InfinitePlace L} (h : v = w) :
    Continuous (RingEquiv.cast
      (R := fun u : InfinitePlace L ↦ u.Completion) h) := by
  subst w
  exact continuous_id

/-- Coordinate transport, expressed against Mathlib's standard action on
infinite places. -/
def numberInfiniteTransport
    (sigma : Gal(L/K)) (w : InfinitePlace L) :
    (sigma⁻¹ • w).Completion ≃+* w.Completion :=
  (RingEquiv.cast (R := fun u : InfinitePlace L ↦ u.Completion)
      (infinite_action_smul sigma⁻¹ w).symm).trans <| by
    letI := infinitePlacesAction (K := K) (L := L)
    exact infinitePlaceTransport sigma w

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
theorem number_transport_continuous
    (sigma : Gal(L/K)) (w : InfinitePlace L) :
    Continuous (numberInfiniteTransport sigma w) := by
  unfold numberInfiniteTransport
  exact (continuous_infinite_transport sigma w).comp
    (infinite_place_continuous
      (infinite_action_smul sigma⁻¹ w).symm)

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
@[simp]
theorem number_transport_embedding
    (sigma : Gal(L/K)) (w : InfinitePlace L) (x : L) :
    numberInfiniteTransport sigma w
        (completionEmbedding (sigma⁻¹ • w).1 x) =
      completionEmbedding w.1 (sigma x) := by
  unfold numberInfiniteTransport
  rw [RingEquiv.trans_apply, infinite_place_embedding]
  exact infinite_transport_embedding sigma w x

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- The identity automorphism induces the identity transport at every
infinite place. -/
theorem number_place_transport
    (w : InfinitePlace L) :
    numberInfiniteTransport (K := K) (1 : Gal(L/K)) w =
      RingEquiv.refl _ := by
  apply infinite_ext_continuous
  · exact number_transport_continuous 1 w
  · exact continuous_id
  · intro x
    rw [number_transport_embedding]
    rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- Transport for a product of Galois automorphisms is the composite of
the two transports. -/
theorem number_infinite_transport
    (sigma tau : Gal(L/K)) (w : InfinitePlace L) :
    numberInfiniteTransport (K := K) (sigma * tau) w =
      (numberInfiniteTransport (K := K) tau (sigma⁻¹ • w)).trans
        (numberInfiniteTransport (K := K) sigma w) := by
  apply infinite_ext_continuous
  · exact number_transport_continuous (sigma * tau) w
  · exact (number_transport_continuous sigma w).comp
      (number_transport_continuous tau (sigma⁻¹ • w))
  · intro x
    have hplace : (sigma * tau)⁻¹ • w =
        tau⁻¹ • sigma⁻¹ • w := by
      rw [mul_inv_rev, mul_smul]
    cases hplace
    change _ = numberInfiniteTransport sigma w
      (numberInfiniteTransport tau (sigma⁻¹ • w)
        (completionEmbedding (tau⁻¹ • sigma⁻¹ • w).1 x))
    rw [
      number_transport_embedding,
      number_transport_embedding,
      number_transport_embedding]
    rfl

/-- The coordinatewise Galois action on the infinite adele ring. -/
@[reducible]
def infiniteAdeleAction :
    MulSemiringAction Gal(L/K) (InfiniteAdeleRing L) := by
  exact
    { smul := fun sigma x w ↦
        numberInfiniteTransport (K := K) sigma w (x (sigma⁻¹ • w))
      one_smul := fun x ↦ by
        funext w
        change numberInfiniteTransport (K := K) 1 w
            (x ((1 : Gal(L/K))⁻¹ • w)) = x w
        rw [number_place_transport]
        rfl
      mul_smul := fun sigma tau x ↦ by
        funext w
        change numberInfiniteTransport (K := K) (sigma * tau) w
            (x (tau⁻¹ • sigma⁻¹ • w)) =
          numberInfiniteTransport sigma w
            (numberInfiniteTransport tau (sigma⁻¹ • w)
              (x (tau⁻¹ • sigma⁻¹ • w)))
        rw [number_infinite_transport]
        rfl
      smul_zero := fun sigma ↦ by
        funext w
        exact (numberInfiniteTransport sigma w).map_zero
      smul_add := fun sigma x y ↦ by
        funext w
        exact (numberInfiniteTransport sigma w).map_add _ _
      smul_one := fun sigma ↦ by
        funext w
        exact (numberInfiniteTransport sigma w).map_one
      smul_mul := fun sigma x y ↦ by
        funext w
        exact (numberInfiniteTransport sigma w).map_mul _ _ }

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
@[simp]
theorem infinite_adele_action
    (sigma : Gal(L/K)) (x : InfiniteAdeleRing L) (w : InfinitePlace L) :
    letI := infiniteAdeleAction (K := K) (L := L)
    (sigma • x) w =
      numberInfiniteTransport (K := K) sigma w (x (sigma⁻¹ • w)) :=
  rfl

/-- The induced multiplicative action on units of the infinite adele ring. -/
@[reducible]
def infiniteIdelesAction :
    MulDistribMulAction Gal(L/K) (InfiniteAdeleRing L)ˣ := by
  letI := infiniteAdeleAction (K := K) (L := L)
  exact Units.mulDistribMulActionRight

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- The infinite-idele action is continuous for each Galois element. -/
theorem infinite_ideles_continuous (sigma : Gal(L/K)) :
    letI := infiniteIdelesAction (K := K) (L := L)
    Continuous (fun x : (InfiniteAdeleRing L)ˣ ↦ sigma • x) := by
  letI := infiniteAdeleAction (K := K) (L := L)
  letI := infiniteIdelesAction (K := K) (L := L)
  change Continuous (Units.map
    (MulSemiringAction.toRingHom Gal(L/K)
      (InfiniteAdeleRing L) sigma).toMonoidHom)
  apply Continuous.units_map
  exact continuous_pi fun w ↦
    (number_transport_continuous sigma w).comp
      (continuous_apply (sigma⁻¹ • w))

/-- The Galois action on the disjoint union of finite and infinite places. -/
@[reducible]
def numberGaloisAction :
    MulAction Gal(L/K) (NumberFieldPlace L) := by
  letI := finitePrimeAction (K := K) (L := L)
  exact
    { smul := fun sigma w ↦ match w with
        | .inl P => .inl (sigma • P)
        | .inr v => .inr (sigma • v)
      one_smul := fun w ↦ by
        cases w with
        | inl P => exact congrArg Sum.inl (one_smul Gal(L/K) P)
        | inr v => exact congrArg Sum.inr (one_smul Gal(L/K) v)
      mul_smul := fun sigma tau w ↦ by
        cases w with
        | inl P => exact congrArg Sum.inl (mul_smul sigma tau P)
        | inr v => exact congrArg Sum.inr (mul_smul sigma tau v) }

/-- The local transport on units at a finite or infinite place. -/
def numberPlaceTransport
    (sigma : Gal(L/K)) (w : NumberFieldPlace L) :
    letI := numberGaloisAction (K := K) (L := L)
    PlaceUnits L (sigma⁻¹ • w) ≃* PlaceUnits L w := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := numberGaloisAction (K := K) (L := L)
  cases w with
  | inl P =>
      exact Units.mapEquiv (finitePlaceTransport (K := K) sigma P).toMulEquiv
  | inr v =>
      exact Units.mapEquiv
        (numberInfiniteTransport (K := K) sigma v).toMulEquiv

omit [FiniteDimensional K L] in
theorem field_transport_continuous
    (sigma : Gal(L/K)) (w : NumberFieldPlace L) :
    letI := numberGaloisAction (K := K) (L := L)
    Continuous (numberPlaceTransport (K := K) sigma w) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := numberGaloisAction (K := K) (L := L)
  cases w with
  | inl P => exact (finite_transport_continuous sigma P).units_map
  | inr v =>
      exact (number_transport_continuous sigma v).units_map

/-- The product action on the full idele group. -/
@[reducible]
def idelesGaloisAction :
    MulDistribMulAction Gal(L/K) (IdeleGroup (RingOfIntegers L) L) := by
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := finitePrimeAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  exact
    { smul := fun sigma x ↦ (sigma • x.1, sigma • x.2)
      one_smul := fun x ↦ by
        apply Prod.ext
        · exact one_smul Gal(L/K) x.1
        · exact one_smul Gal(L/K) x.2
      mul_smul := fun sigma tau x ↦ by
        apply Prod.ext
        · exact mul_smul sigma tau x.1
        · exact mul_smul sigma tau x.2
      smul_one := fun sigma ↦ by
        apply Prod.ext
        · exact smul_one sigma
        · exact smul_one sigma
      smul_mul := fun sigma x y ↦ by
        apply Prod.ext
        · exact smul_mul' sigma x.1 y.1
        · exact smul_mul' sigma x.2 y.2 }

omit [FiniteDimensional K L] in
/-- The product idele action satisfies Milne's local-coordinate formula. -/
theorem ideles_galois_action
    (sigma : Gal(L/K)) (x : IdeleGroup (RingOfIntegers L) L)
    (w : NumberFieldPlace L) :
    letI := numberGaloisAction (K := K) (L := L)
    letI := idelesGaloisAction (K := K) (L := L)
    ideleCoordinate (sigma • x) w =
      numberPlaceTransport (K := K) sigma w
        (ideleCoordinate x (sigma⁻¹ • w)) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := numberGaloisAction (K := K) (L := L)
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  letI := idelesGaloisAction (K := K) (L := L)
  cases w with
  | inl P =>
      exact ideles_action_coordinate sigma x.2 P
  | inr v =>
      apply Units.ext
      rfl

omit [FiniteDimensional K L] in
/-- Local transport carries a principal coordinate to the corresponding
coordinate of the Galois-conjugate principal idele. -/
theorem number_transport_principal
    (sigma : Gal(L/K)) (w : NumberFieldPlace L) (x : Lˣ) :
    letI := numberGaloisAction (K := K) (L := L)
    numberPlaceTransport (K := K) sigma w
        (placePrincipalUnit (sigma⁻¹ • w) x) =
      placePrincipalUnit w (Units.map sigma.toRingEquiv.toRingHom x) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := numberGaloisAction (K := K) (L := L)
  cases w with
  | inl P =>
      apply Units.ext
      exact place_transport_embedding sigma P x
  | inr v =>
      apply Units.ext
      exact number_transport_embedding sigma v x

omit [FiniteDimensional K L] in
/-- The action of each Galois element on ideles is continuous. -/
theorem ideles_galois_continuous (sigma : Gal(L/K)) :
    letI := idelesGaloisAction (K := K) (L := L)
    Continuous (fun x : IdeleGroup (RingOfIntegers L) L ↦ sigma • x) := by
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := finitePrimeAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  letI := idelesGaloisAction (K := K) (L := L)
  exact (infinite_ideles_continuous sigma).prodMap
    (ideles_action_continuous sigma)

/-- The canonical Galois action on number-field ideles, with its placewise
transport and continuity properties. -/
noncomputable def concreteActionData :
    IAData (K := K) (L := L) where
  placeAction := numberGaloisAction (K := K) (L := L)
  preserves_finite sigma P :=
    ⟨(finitePrimeAction (K := K) (L := L)).smul sigma P, rfl⟩
  preserves_infinite sigma v :=
    ⟨sigma • v, rfl⟩
  transport := numberPlaceTransport (K := K)
  continuous_transport := field_transport_continuous (K := K)
  action := idelesGaloisAction (K := K) (L := L)
  transport_principal := number_transport_principal (K := K)
  coordinate_formula := ideles_galois_action (K := K)
  continuous_action := ideles_galois_continuous (K := K)

end

end Submission.CField.ICohomo
