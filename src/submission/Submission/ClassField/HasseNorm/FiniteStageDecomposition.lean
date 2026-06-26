import Submission.ClassField.HasseNorm.FinitePlaceBridge
import Submission.ClassField.HasseNorm.IdeleCochainSupport
import Submission.ClassField.CohomologyOps.Arbitrary

/-!
# Finite-place orbit representations for the idèle decomposition

This file reorganizes the literal prime-adic coordinates of finite idèles by
base prime.  Keeping the intermediate index as the literal fiber of upper
height-one primes makes the Galois coordinate formula definitionally match
`finitePlaceTransport`; the equivalence with Milne's absolute-value
completion product is supplied by `HasseNormFinitePlaceBridge`.
-/

namespace Submission.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.COps
open Submission.CField.Ideles
open Submission.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- There are finitely many literal upper primes over a fixed finite base
prime. -/
noncomputable instance finitePrimesAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Finite (FinitePrimesAbove (K := K) (L := L) P) :=
  Finite.of_equiv (UpperPrimeFactors (K := K) (L := L) P)
    (upperPrimesAbove (K := K) (L := L) P)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Contracting upper height-one primes has finite fibers. -/
theorem preimage_singleton
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set.Finite
      ((fun Q : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
        Q.under (NumberField.RingOfIntegers K)) ⁻¹' {P}) := by
  let e : FinitePrimesAbove (K := K) (L := L) P →
      HeightOneSpectrum (NumberField.RingOfIntegers L) := Subtype.val
  have hfinite : Set.Finite (e '' Set.univ) := Set.finite_univ.image e
  refine hfinite.subset ?_
  intro Q hQ
  exact ⟨⟨Q, hQ⟩, Set.mem_univ _, rfl⟩

/-- Contraction of finite upper primes tends to the cofinite filter. -/
noncomputable instance primeTendstoCofinite :
    Filter.TendstoCofinite
      (fun Q : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
        Q.under (NumberField.RingOfIntegers K)) :=
  ⟨Filter.Tendsto.cofinite_of_finite_preimage_singleton
    (preimage_singleton (K := K) (L := L))⟩

/-- Galois conjugation on the literal fiber of upper primes above `P`. -/
@[reducible]
noncomputable def aboveMulAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction Gal(L/K) (FinitePrimesAbove (K := K) (L := L) P) := by
  letI := finitePrimeAction (K := K) (L := L)
  exact
    { smul := fun sigma Q => ⟨sigma • Q.1, by
        rw [finite_prime_smul, Q.2]⟩
      one_smul := fun Q => Subtype.ext (one_smul Gal(L/K) Q.1)
      mul_smul := fun sigma tau Q =>
        Subtype.ext (mul_smul sigma tau Q.1) }

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem primes_above_val
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K)) (Q : FinitePrimesAbove (K := K) (L := L) P) :
    letI := aboveMulAction (K := K) (L := L) P
    (sigma • Q).1 =
      letI := finitePrimeAction (K := K) (L := L)
      sigma • Q.1 :=
  rfl

/-- Coordinate action on the product of prime-adic completed unit groups
above one finite base prime. -/
@[reducible]
noncomputable def aboveUnitsAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction Gal(L/K)
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        (Q.1.adicCompletion L)ˣ) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  exact
    { smul := fun sigma x Q =>
        Units.map
          (finitePlaceTransport (K := K) sigma Q.1).toRingHom.toMonoidHom
          (x (sigma⁻¹ • Q))
      one_smul := fun x => by
        funext Q
        apply Units.ext
        change finitePlaceTransport (K := K) 1 Q.1
            (x ((1 : Gal(L/K))⁻¹ • Q) : _) =
              (x Q : _)
        rw [finite_place_transport]
        rfl
      mul_smul := fun sigma tau x => by
        funext Q
        apply Units.ext
        change finitePlaceTransport (K := K) (sigma * tau) Q.1
            (x ((sigma * tau)⁻¹ • Q) : _) =
          finitePlaceTransport (K := K) sigma Q.1
            (finitePlaceTransport (K := K) tau
              (sigma⁻¹ • Q).1
              (x (tau⁻¹ • sigma⁻¹ • Q) : _))
        have hindex : (sigma * tau)⁻¹ • Q =
            tau⁻¹ • sigma⁻¹ • Q := by
          rw [mul_inv_rev, mul_smul]
        cases hindex
        rw [place_transport_mul]
        rfl
      smul_one := fun sigma => by
        funext Q
        exact map_one (Units.map
          (finitePlaceTransport (K := K) sigma Q.1).toRingHom.toMonoidHom)
      smul_mul := fun sigma x y => by
        funext Q
        exact map_mul (Units.map
          (finitePlaceTransport (K := K) sigma Q.1).toRingHom.toMonoidHom)
          (x (sigma⁻¹ • Q)) (y (sigma⁻¹ • Q)) }

set_option synthInstance.maxHeartbeats 200000 in
-- The resized completion product synthesizes every dependent upper-prime factor.
/-- The resized representation on all prime-adic completion factors above
one finite base prime. -/
noncomputable def resizedAboveRepresentation
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Rep (ULift.{u} ℤ) Gal(L/K) := by
  letI := aboveUnitsAction (K := K) (L := L) P
  exact uliftMulRepresentation
    (G := Gal(L/K))
    (M := ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      (Q.1.adicCompletion L)ˣ)

/-- Product of the local unit subgroups at all upper primes above `P`. -/
abbrev PrimesAboveUnits
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
    IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q.1

set_option maxHeartbeats 1000000 in
-- Preserving the local-unit product unfolds all dependent completion fibers.
set_option synthInstance.maxHeartbeats 200000 in
-- The restricted action synthesizes the transported unit-subgroup instances.
/-- The coordinate action preserves the product of local unit subgroups. -/
@[reducible]
noncomputable def primesUnitsAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction Gal(L/K)
      (PrimesAboveUnits (K := K) (L := L) P) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  letI := aboveUnitsAction (K := K) (L := L) P
  exact
    { smul := fun sigma x Q =>
        ⟨(sigma • (fun Q => (x Q).1)) Q,
          transport_preserves_units sigma Q.1
            (x (sigma⁻¹ • Q)).1 (x (sigma⁻¹ • Q)).2⟩
      one_smul := fun x => by
        funext Q
        apply Subtype.ext
        exact congrFun (one_smul Gal(L/K) (fun Q => (x Q).1)) Q
      mul_smul := fun sigma tau x => by
        funext Q
        apply Subtype.ext
        exact congrFun (mul_smul sigma tau (fun Q => (x Q).1)) Q
      smul_one := fun sigma => by
        funext Q
        apply Subtype.ext
        exact congrFun (smul_one sigma :
          sigma • (1 : ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
            (Q.1.adicCompletion L)ˣ) = 1) Q
      smul_mul := fun sigma x y => by
        funext Q
        apply Subtype.ext
        exact congrFun (smul_mul' sigma (fun Q => (x Q).1)
          (fun Q => (y Q).1)) Q }

set_option synthInstance.maxHeartbeats 200000 in
-- The resized local-unit representation synthesizes its dependent product action.
/-- Resized representation on the product of local units above `P`. -/
noncomputable def resizedPrimesRepresentation
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Rep (ULift.{u} ℤ) Gal(L/K) := by
  letI := primesUnitsAction (K := K) (L := L) P
  exact uliftMulRepresentation
    (G := Gal(L/K))
    (M := PrimesAboveUnits (K := K) (L := L) P)

/-- The finite orbit occurring in `I_{L,S}`: all coordinates are allowed
when `P ∈ S`, and otherwise every coordinate is a local unit. -/
def IdeleStageOrbit
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Subgroup (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      (Q.1.adicCompletion L)ˣ) where
  carrier := {x | ∀ Q, (Sum.inl P : NumberFieldPlace K) ∉ S →
    x Q ∈ IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q.1}
  one_mem' := fun _ _ => Subgroup.one_mem _
  mul_mem' := fun hx hy Q hP => Subgroup.mul_mem _ (hx Q hP) (hy Q hP)
  inv_mem' := fun hx Q hP => Subgroup.inv_mem _ (hx Q hP)

set_option maxHeartbeats 1000000 in
-- The stage action retains the exceptional-set predicate in every coordinate.
set_option synthInstance.maxHeartbeats 200000 in
-- The stage-orbit action synthesizes its restricted dependent product action.
/-- The finite-place orbit action preserves the stage condition. -/
@[reducible]
noncomputable def stageOrbitAction
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction Gal(L/K)
      (IdeleStageOrbit (K := K) (L := L) S P) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  letI := aboveUnitsAction (K := K) (L := L) P
  exact
    { smul := fun sigma x => ⟨sigma • x.1, fun Q hP =>
        transport_preserves_units sigma Q.1
          (x.1 (sigma⁻¹ • Q)) (x.2 (sigma⁻¹ • Q) hP)⟩
      one_smul := fun x => Subtype.ext (one_smul Gal(L/K) x.1)
      mul_smul := fun sigma tau x => Subtype.ext (mul_smul sigma tau x.1)
      smul_one := fun sigma => by
        apply Subtype.ext
        exact (smul_one sigma :
          sigma • (1 : ∀ Q : FinitePrimesAbove (K := K) (L := L) P,
            (Q.1.adicCompletion L)ˣ) = 1)
      smul_mul := fun sigma x y => by
        apply Subtype.ext
        exact (smul_mul' sigma x.1 y.1 :
          sigma • (x.1 * y.1) = (sigma • x.1) * (sigma • y.1)) }

set_option synthInstance.maxHeartbeats 200000 in
-- Resizing one stage orbit synthesizes the inherited subgroup action.
/-- Resized representation of one finite orbit in the stage `I_{L,S}`. -/
noncomputable def stageOrbitRepresentation
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Rep (ULift.{u} ℤ) Gal(L/K) := by
  letI := stageOrbitAction (K := K) (L := L) S P
  exact uliftMulRepresentation
    (G := Gal(L/K))
    (M := IdeleStageOrbit (K := K) (L := L) S P)

/-- At an exceptional base prime, the stage orbit is the unrestricted
completion orbit. -/
noncomputable def stageOrbitFull
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    IdeleStageOrbit (K := K) (L := L) S P ≃*
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        (Q.1.adicCompletion L)ˣ) where
  toFun x := x.1
  invFun x := ⟨x, fun _ hnot => (hnot hP).elim⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Away from the exceptional set, the stage orbit is exactly the product
of local unit subgroups. -/
noncomputable def ideleStageUnits
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    IdeleStageOrbit (K := K) (L := L) S P ≃*
      PrimesAboveUnits (K := K) (L := L) P where
  toFun x Q := ⟨x.1 Q, x.2 Q hP⟩
  invFun x := ⟨fun Q => (x Q).1, fun Q _ => (x Q).2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := by
    funext Q
    exact Subtype.ext rfl
  map_mul' _ _ := rfl

set_option maxHeartbeats 1000000 in
-- The exceptional orbit equivalence unfolds the dependent full completion product.
set_option synthInstance.maxHeartbeats 200000 in
-- The exceptional-orbit isomorphism synthesizes both transported actions.
/-- Representation isomorphism from an exceptional stage orbit to the full
prime-adic completion orbit. -/
noncomputable def stageIsoFull
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    stageOrbitRepresentation (K := K) (L := L) S P ≅
      resizedAboveRepresentation
        (K := K) (L := L) P := by
  apply Rep.mkIso
  let e := stageOrbitFull (K := K) (L := L) S P hP
  refine
    { toLinearEquiv :=
        { toEquiv := e.toAdditive.toEquiv
          map_add' := e.toAdditive.map_add
          map_smul' := fun r x => map_zsmul e.toAdditive r.down x }
      isIntertwining' := fun _ => rfl }

set_option maxHeartbeats 1000000 in
-- The nonexceptional orbit equivalence unfolds the product of local unit subgroups.
set_option synthInstance.maxHeartbeats 200000 in
-- The local-unit orbit isomorphism synthesizes both transported actions.
/-- Representation isomorphism from a nonexceptional stage orbit to the
product of local unit subgroups. -/
noncomputable def resizedStageIso
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    stageOrbitRepresentation (K := K) (L := L) S P ≅
      resizedPrimesRepresentation
        (K := K) (L := L) P := by
  apply Rep.mkIso
  let e := ideleStageUnits
    (K := K) (L := L) S P hP
  refine
    { toLinearEquiv :=
        { toEquiv := e.toAdditive.toEquiv
          map_add' := e.toAdditive.map_add
          map_smul' := fun r x => map_zsmul e.toAdditive r.down x }
      isIntertwining' := fun _ => rfl }

/-- The finite part of `I_{L,S}` as a subgroup of the restricted finite
idèles. -/
def FiniteIdelesPlaces
    (S : Finset (NumberFieldPlace K)) :
    Subgroup (FiniteIdeles (NumberField.RingOfIntegers L) L) where
  carrier := {x | ∀ Q : HeightOneSpectrum (NumberField.RingOfIntegers L),
    (Sum.inl (Q.under (NumberField.RingOfIntegers K)) : NumberFieldPlace K) ∉ S →
      x.1 Q ∈ IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q}
  one_mem' := fun _ _ => Subgroup.one_mem _
  mul_mem' := fun hx hy Q hQ => Subgroup.mul_mem _ (hx Q hQ) (hy Q hQ)
  inv_mem' := fun hx Q hQ => Subgroup.inv_mem _ (hx Q hQ)

set_option maxHeartbeats 1000000 in
-- Regrouping restricted-product coordinates by contraction is elaboration-heavy.
/-- Regroup the finite coordinates of `I_{L,S}` by their contracted base
prime. -/
noncomputable def idelesPiOrbits
    (S : Finset (NumberFieldPlace K)) :
    FiniteIdelesPlaces (K := K) (L := L) S ≃*
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        IdeleStageOrbit (K := K) (L := L) S P) where
  toFun x P := ⟨fun Q => x.1.1 Q.1, fun Q hP => x.2 Q.1 (by simpa [Q.2] using hP)⟩
  invFun y := by
    let f : ∀ Q : HeightOneSpectrum (NumberField.RingOfIntegers L),
        (Q.adicCompletion L)ˣ := fun Q =>
      (y (Q.under (NumberField.RingOfIntegers K))).1
        ⟨Q, rfl⟩
    have hbase : Set.Finite
        {P : HeightOneSpectrum (NumberField.RingOfIntegers K) |
          (Sum.inl P : NumberFieldPlace K) ∈ S} := by
      exact S.finite_toSet.preimage Sum.inl_injective.injOn
    have hupper : Set.Finite
        ((fun Q : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
          Q.under (NumberField.RingOfIntegers K)) ⁻¹'
            {P | (Sum.inl P : NumberFieldPlace K) ∈ S}) :=
      Filter.TendstoCofinite.finite_preimage _ hbase
    let xfin : FiniteIdeles (NumberField.RingOfIntegers L) L :=
      ⟨f, by
        rw [Filter.eventually_cofinite]
        refine hupper.subset ?_
        intro Q hQ
        change ¬f Q ∈ IdeleUnitSubgroup
          (NumberField.RingOfIntegers L) L Q at hQ
        change (Sum.inl (Q.under (NumberField.RingOfIntegers K)) :
          NumberFieldPlace K) ∈ S
        by_contra hnot
        exact hQ ((y (Q.under (NumberField.RingOfIntegers K))).2
          ⟨Q, rfl⟩ hnot)⟩
    exact ⟨xfin, fun Q hQ =>
      (y (Q.under (NumberField.RingOfIntegers K))).2 ⟨Q, rfl⟩ hQ⟩
  left_inv x := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro Q
    rfl
  right_inv y := by
    funext P
    apply Subtype.ext
    funext Q
    rcases Q with ⟨Q, hQ⟩
    cases hQ
    rfl
  map_mul' x y := by
    funext P
    apply Subtype.ext
    funext Q
    rfl

/-- Split `I_{L,S}` into its unrestricted infinite idèle factor and the
finite-idèle subgroup carrying the stage condition. -/
noncomputable def idelesPlacesInfinite
    (S : Finset (NumberFieldPlace K)) :
    idelesAtPlaces (K := K) (L := L) S ≃*
      (InfiniteAdeleRing L)ˣ × FiniteIdelesPlaces (K := K) (L := L) S where
  toFun x := (x.1.1, ⟨x.1.2, x.2⟩)
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Splitting and regrouping the idèle stage synthesizes both product actions.
/-- Split `I_{L,S}` into its unrestricted infinite idèle factor and its
finite stage factor, then regroup the finite coordinates by base prime. -/
noncomputable def idelesPlacesProd
    (S : Finset (NumberFieldPlace K)) :
    idelesAtPlaces (K := K) (L := L) S ≃*
      (InfiniteAdeleRing L)ˣ ×
        (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
          IdeleStageOrbit (K := K) (L := L) S P) :=
  (idelesPlacesInfinite
      (K := K) (L := L) S).trans
    (MulEquiv.prodCongr (MulEquiv.refl ((InfiniteAdeleRing L)ˣ))
      (idelesPiOrbits (K := K) (L := L) S))

set_option synthInstance.maxHeartbeats 200000 in
-- The product action ranges over a dependent family of finite-prime orbits.
/-- Pointwise action on the product of all finite base-prime stage
orbits. -/
@[reducible]
noncomputable def ideleStageAction
    (S : Finset (NumberFieldPlace K)) :
    MulDistribMulAction Gal(L/K)
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        IdeleStageOrbit (K := K) (L := L) S P) := by
  let localAction (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    stageOrbitAction (K := K) (L := L) S P
  letI (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
      MulDistribMulAction Gal(L/K)
        (IdeleStageOrbit (K := K) (L := L) S P) := localAction P
  infer_instance

set_option synthInstance.maxHeartbeats 200000 in
-- The regrouped finite-stage action synthesizes every orbit action.
/-- The product action occurring on the regrouped finite-stage target. -/
@[reducible]
noncomputable def idelesPlacesAction
    (S : Finset (NumberFieldPlace K)) :
    MulDistribMulAction Gal(L/K)
      ((InfiniteAdeleRing L)ˣ ×
        (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
          IdeleStageOrbit (K := K) (L := L) S P)) := by
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := ideleStageAction (K := K) (L := L) S
  infer_instance

omit [FiniteDimensional K L] in
/-- The product decomposition of `I_{L,S}` respects the concrete Galois
action on each infinite and finite coordinate. -/
theorem ideles_places_smul
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K))
    (x : idelesAtPlaces (K := K) (L := L) S) :
    idelesPlacesProd (K := K) (L := L) S
        ((idelesDistribAction (K := K) (L := L) S).smul
          sigma x) =
      (idelesPlacesAction (K := K) (L := L) S).smul sigma
        (idelesPlacesProd
          (K := K) (L := L) S x) := by
  dsimp only [idelesPlacesProd,
    MulEquiv.trans_apply, idelesPlacesInfinite,
    MulEquiv.prodCongr, idelesPiOrbits]
  apply Prod.ext
  · rfl
  · funext P
    apply Subtype.ext
    funext Q
    rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The integral representation synthesizes the dependent product action.
/-- Integral representation on the regrouped finite-stage target. -/
noncomputable def idelesPlacesRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep ℤ Gal(L/K) := by
  letI := idelesPlacesAction (K := K) (L := L) S
  exact Rep.ofMulDistribMulAction Gal(L/K)
    ((InfiniteAdeleRing L)ˣ ×
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        IdeleStageOrbit (K := K) (L := L) S P))

set_option synthInstance.maxHeartbeats 200000 in
-- Equivariance of regrouping synthesizes the source and target product actions.
set_option maxHeartbeats 1000000 in
-- The equivariance proof unfolds the full restricted-product regrouping map.
/-- Regrouping the stage by base prime is equivariant for the concrete
Galois action. -/
noncomputable def idelesRepresentationIso
    (S : Finset (NumberFieldPlace K)) :
    idelesRepresentation (K := K) (L := L) S ≅
      idelesPlacesRepresentation (K := K) (L := L) S := by
  apply Rep.mkIso
  let e := idelesPlacesProd
    (K := K) (L := L) S
  refine
    { toLinearEquiv := e.toAdditive.toIntLinearEquiv
      isIntertwining' := ?_ }
  intro sigma
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  exact ideles_places_smul
    (K := K) (L := L) S sigma x.toMul

/-- Resized representation on the regrouped finite-stage target. -/
noncomputable def resizedIdelesRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep (ULift.{u} ℤ) Gal(L/K) :=
  uliftIntegralRepresentation
    (idelesPlacesRepresentation (K := K) (L := L) S)

/-- Universe-resized version of the stage regrouping isomorphism. -/
noncomputable def resizedRepresentationIso
    (S : Finset (NumberFieldPlace K)) :
    resizedPlacesRepresentation (K := K) (L := L) S ≅
      resizedIdelesRepresentation (K := K) (L := L) S :=
  uliftIntegralIso
    (idelesRepresentationIso (K := K) (L := L) S)

/-- Degree-two cohomology of `I_{L,S}` after regrouping its coordinates by
base prime. -/
noncomputable def resizedIdelesProduct
    (S : Finset (NumberFieldPlace K)) :
    H2 (resizedPlacesRepresentation (K := K) (L := L) S) ≃+
      H2 (resizedIdelesRepresentation
        (K := K) (L := L) S) :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
    (resizedRepresentationIso
      (K := K) (L := L) S)).toLinearEquiv.toAddEquiv

set_option synthInstance.maxHeartbeats 200000 in
-- The integral completion-unit representation synthesizes its orbit action.
/-- Integral form of the finite-prime-orbit representation. -/
noncomputable def primesAboveRepresentation
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Rep ℤ Gal(L/K) := by
  letI := aboveUnitsAction (K := K) (L := L) P
  exact Rep.ofMulDistribMulAction Gal(L/K)
    (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      (Q.1.adicCompletion L)ˣ)

/-- Restrict a finite idèle family to the upper primes above one base
prime. -/
noncomputable def primesAboveMonoid
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IdeleGroup (NumberField.RingOfIntegers L) L →*
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        (Q.1.adicCompletion L)ˣ) where
  toFun x Q := x.2.1 Q.1
  map_one' := rfl
  map_mul' := fun _ _ => rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Evaluation at an orbit synthesizes the concrete and resized actions.
/-- Evaluation of the concrete idèle representation at the finite orbit
above `P` is equivariant. -/
noncomputable def concretePrimesAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (concreteActionData (K := K) (L := L)).representation ⟶
      primesAboveRepresentation (K := K) (L := L) P := by
  apply Rep.ofHom
  refine
    { toLinearMap := (MonoidHom.toAdditive
        (primesAboveMonoid (K := K) (L := L) P)).toIntLinearMap
      isIntertwining' := fun _ => by
        ext x Q
        rfl }

/-- Resized evaluation at the finite orbit above `P`. -/
noncomputable def resizedConcreteAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    resizedConcreteRepresentation K L ⟶
      resizedAboveRepresentation
        (K := K) (L := L) P :=
  uliftIntegralHom (concretePrimesAbove (K := K) (L := L) P)

/-- Reindex the absolute-value completion product directly by the literal
upper primes above `P`. -/
noncomputable def adicPrimesAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (∀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val,
        CompletionFamilyAbove (L := L) (FinitePlace.mk P).val w) ≃+*
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        Q.1.adicCompletion L) :=
  (ringAdicFactors
      (K := K) (L := L) P).trans
    (RingEquiv.piCongrLeft
      (fun Q : FinitePrimesAbove (K := K) (L := L) P =>
        Q.1.adicCompletion L)
      (upperPrimesAbove (K := K) (L := L) P))

/-- Unit-valued coordinate form of the reindexing by literal upper primes. -/
noncomputable def piPrimesAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (∀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val,
        CompletionFamilyAbove (L := L) (FinitePlace.mk P).val w)ˣ ≃*
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        (Q.1.adicCompletion L)ˣ) :=
  (Units.mapEquiv (adicPrimesAbove
    (K := K) (L := L) P).toMulEquiv).trans MulEquiv.piUnits

end

end Submission.CField.HNorm
