import Towers.ClassField.HasseNorm.InfiniteStageLimit

/-!
# Normalized infinite completion places

An absolute value of `L` lying exactly above the normalized absolute value
of an infinite place of `K` is itself the normalized absolute value attached
to a unique infinite place of `L` above that base place.  This removes the
usual positive-power ambiguity and supplies the index correspondence needed
to regroup the infinite idèles by base-field infinite place.
-/

namespace Towers.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A normalized archimedean absolute-value extension is the literal
absolute value underlying an infinite place above the given base place. -/
theorem infinite_normalized_completion
    (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) :
    ∃ w : InfinitePlace L,
      w.comap (algebraMap K L) = v ∧ w.1 = z.1 := by
  have hzNontrivial : z.1.IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := infinite_place_nontrivial v
    have hxMap : algebraMap K L x ≠ 0 := by
      simpa using (algebraMap K L).injective.ne hx0
    refine ⟨algebraMap K L x, hxMap, ?_⟩
    have heq := DFunLike.congr_fun z.2.comp_eq x
    change z.1 (algebraMap K L x) = v.1 x at heq
    exact fun h => hx1 (heq.symm.trans h)
  have hzArch : ¬ IsNonarchimedean z.1 := by
    intro hz
    apply infinite_place_nonarchimedean v
    intro x y
    calc
      v.1 (x + y) = z.1 (algebraMap K L (x + y)) :=
        (DFunLike.congr_fun z.2.comp_eq (x + y)).symm
      _ = z.1 (algebraMap K L x + algebraMap K L y) := by rw [map_add]
      _ ≤ max (z.1 (algebraMap K L x)) (z.1 (algebraMap K L y)) :=
        hz _ _
      _ = max (v.1 x) (v.1 y) := by
        have hx := DFunLike.congr_fun z.2.comp_eq x
        have hy := DFunLike.congr_fun z.2.comp_eq y
        change z.1 (algebraMap K L x) = v.1 x at hx
        change z.1 (algebraMap K L y) = v.1 y at hy
        rw [hx, hy]
  obtain ⟨w, hzw⟩ :=
    infinite_not_nonarchimedean
      z.1 hzNontrivial hzArch
  have hwComap : w.comap (algebraMap K L) = v := by
    apply (InfinitePlace.eq_iff_isEquiv (K := K)).2
    intro x y
    change w.1 (algebraMap K L x) ≤ w.1 (algebraMap K L y) ↔
      v.1 x ≤ v.1 y
    calc
      w.1 (algebraMap K L x) ≤ w.1 (algebraMap K L y) ↔
          z.1 (algebraMap K L x) ≤ z.1 (algebraMap K L y) :=
        (hzw _ _).symm
      _ ↔ v.1 x ≤ v.1 y := by
        have hx := DFunLike.congr_fun z.2.comp_eq x
        have hy := DFunLike.congr_fun z.2.comp_eq y
        change z.1 (algebraMap K L x) = v.1 x at hx
        change z.1 (algebraMap K L y) = v.1 y at hy
        rw [hx, hy]
  obtain ⟨c, hc, hpow⟩ :=
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hzw
  obtain ⟨x, hx0, hx1⟩ := infinite_place_nontrivial v
  have hvx : 0 < v.1 x := v.1.pos hx0
  have hzBase := DFunLike.congr_fun z.2.comp_eq x
  have hwLies := infinite_lies_comap v w hwComap
  have hwBase := DFunLike.congr_fun hwLies.comp_eq x
  change z.1 (algebraMap K L x) = v.1 x at hzBase
  change w.1 (algebraMap K L x) = v.1 x at hwBase
  have hbase : v.1 x ^ c = v.1 x ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    calc
      v.1 x ^ c = z.1 (algebraMap K L x) ^ c := by
        exact congrArg (fun r : ℝ => r ^ c) hzBase.symm
      _ = w.1 (algebraMap K L x) := congrFun hpow _
      _ = v.1 x := hwBase
  have hc1 : c = 1 := (Real.rpow_right_inj hvx hx1).mp hbase
  refine ⟨w, hwComap, ?_⟩
  apply AbsoluteValue.ext
  intro y
  have hy := congrFun hpow y
  simpa [hc1] using hy.symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The normalized extension itself satisfies the predicate defining an
infinite place; only the proof field has to be supplied. -/
theorem normalized_infinite_place
    (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) :
    IsInfinitePlace z.1 := by
  obtain ⟨w, -, hw⟩ :=
    infinite_normalized_completion
      (K := K) (L := L) v z
  exact hw ▸ w.isInfinitePlace

/-- Regard a normalized archimedean extension literally as an infinite
place.  Its underlying absolute value is definitionally the given one. -/
noncomputable def normalizedInfinitePlace
    (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) : InfinitePlace L :=
  ⟨z.1, normalized_infinite_place
    (K := K) (L := L) v z⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The literal infinite place attached to a normalized extension lies
above the prescribed base infinite place. -/
theorem normalized_infinite_comap
    (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) :
    (normalizedInfinitePlace
      (K := K) (L := L) v z).comap (algebraMap K L) = v := by
  obtain ⟨w, hwv, hw⟩ :=
    infinite_normalized_completion
      (K := K) (L := L) v z
  have heq : normalizedInfinitePlace
      (K := K) (L := L) v z = w := Subtype.ext hw.symm
  exact congrArg (fun q : InfinitePlace L =>
    q.comap (algebraMap K L)) heq |>.trans hwv

/-- Normalized absolute-value extensions of `v` are equivalent to the
infinite places of `L` lying above `v`. -/
noncomputable def normalizedPlacesAbove
    (v : InfinitePlace K) :
    CompletionPlacesAbove (L := L) v.1 ≃
      {w : InfinitePlace L // w.comap (algebraMap K L) = v} where
  toFun z :=
    ⟨normalizedInfinitePlace
      (K := K) (L := L) v z,
     normalized_infinite_comap
      (K := K) (L := L) v z⟩
  invFun w :=
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem normalized_places_val
    (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) :
    ((normalizedPlacesAbove
      (K := K) (L := L) v z).1).1 = z.1 :=
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem normalized_above_val
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    (normalizedPlacesAbove
      (K := K) (L := L) v).symm w =
        ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩ :=
  rfl

/-- Globally, upper infinite places are the sigma type of normalized
completion places over lower infinite places. -/
noncomputable def infiniteSigmaNormalized :
    InfinitePlace L ≃
      Σ v : InfinitePlace K, CompletionPlacesAbove (L := L) v.1 :=
  (Equiv.sigmaFiberEquiv
    (fun w : InfinitePlace L => w.comap (algebraMap K L))).symm.trans
      (Equiv.sigmaCongrRight fun v =>
        (normalizedPlacesAbove
          (K := K) (L := L) v).symm)

/-- Regroup the infinite adele ring of `L` by normalized infinite places
of `K`.  This is only a ring reindexing; equivariance is established in the
subsequent completion-product bridge. -/
noncomputable def infiniteAdeleProducts :
    InfiniteAdeleRing L ≃+* (
      (v : InfinitePlace K) →
        (z : CompletionPlacesAbove (L := L) v.1) → z.1.Completion) := by
  let localEquiv (v : InfinitePlace K) :
      ((w : {w : InfinitePlace L //
          w.comap (algebraMap K L) = v}) → w.1.1.Completion) ≃+*
        ((z : CompletionPlacesAbove (L := L) v.1) → z.1.Completion) :=
    RingEquiv.piCongrLeft
      (fun z : CompletionPlacesAbove (L := L) v.1 => z.1.Completion)
      (normalizedPlacesAbove
        (K := K) (L := L) v).symm
  let e :
      ((w : InfinitePlace L) → w.Completion) ≃
        ((v : InfinitePlace K) →
          (z : CompletionPlacesAbove (L := L) v.1) → z.1.Completion) :=
    Equiv.piCongrFiberwise (fun v => (localEquiv v).toEquiv)
  exact
    { toEquiv := e
      map_add' := by
        intro x y
        funext v z
        rfl
      map_mul' := by
        intro x y
        funext v z
        rfl }

/-- Multiplicative regrouping of the infinite idèles by normalized lower
infinite place. -/
noncomputable def infiniteIdelesUnits :
    (InfiniteAdeleRing L)ˣ ≃* (
      (v : InfinitePlace K) →
        ((z : CompletionPlacesAbove (L := L) v.1) →
          z.1.Completion)ˣ) :=
  (Units.mapEquiv
    (infiniteAdeleProducts
      (K := K) (L := L)).toMulEquiv).trans MulEquiv.piUnits

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem infinite_adele_products
    (x : InfiniteAdeleRing L) (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) :
    infiniteAdeleProducts
        (K := K) (L := L) x v z =
      x (normalizedInfinitePlace
        (K := K) (L := L) v z) := by
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem infinite_ideles_units
    (x : (InfiniteAdeleRing L)ˣ) (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) :
    ((infiniteIdelesUnits
      (K := K) (L := L) x v :
        ((u : CompletionPlacesAbove (L := L) v.1) →
          u.1.Completion)ˣ) :
      (u : CompletionPlacesAbove (L := L) v.1) → u.1.Completion) z =
        (x : InfiniteAdeleRing L)
          (normalizedInfinitePlace
            (K := K) (L := L) v z) := by
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The literal normalized-place correspondence respects Galois
conjugation. -/
theorem normalized_infinite_smul
    (v : InfinitePlace K) (sigma : Gal(L/K))
    (z : CompletionPlacesAbove (L := L) v.1) :
    normalizedInfinitePlace
        (K := K) (L := L) v (sigma • z) =
      sigma • normalizedInfinitePlace
        (K := K) (L := L) v z := by
  apply Subtype.ext
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The concrete infinite-place transport agrees with the transport on the
same normalized completion place. -/
theorem number_transport_normalized
    (v : InfinitePlace K) (sigma : Gal(L/K))
    (z : CompletionPlacesAbove (L := L) v.1) :
    numberInfiniteTransport (K := K) sigma
        (normalizedInfinitePlace
          (K := K) (L := L) v z) =
      completionFamilyTransport v.1 sigma z := by
  let w := normalizedInfinitePlace
    (K := K) (L := L) v z
  apply RingEquiv.ext
  intro x
  exact congrFun
    ((dense_range_embedding (sigma⁻¹ • z).1).equalizer
      (number_transport_continuous
        (K := K) sigma w)
      (completionTransport_isometry sigma z.1).continuous
      (funext fun y => by
        change numberInfiniteTransport (K := K) sigma w
            (completionEmbedding (sigma⁻¹ • w).1 y) =
          completionTransport sigma z.1
            (completionEmbedding (sigma⁻¹ • z).1 y)
        rw [number_transport_embedding]
        exact (completion_transport_embedding sigma z.1 y).symm)) x

/-- Pointwise completion-product action on the family indexed by the lower
infinite places. -/
@[reducible]
noncomputable def normalizedUnitsAction :
    MulDistribMulAction Gal(L/K)
      ((v : InfinitePlace K) →
        ((z : CompletionPlacesAbove (L := L) v.1) →
          z.1.Completion)ˣ) := by
  let localAction (v : InfinitePlace K) :=
    unitsDistribAction
      (K := K) (L := L) v.1
  letI (v : InfinitePlace K) :
      MulDistribMulAction Gal(L/K)
        ((z : CompletionPlacesAbove (L := L) v.1) →
          z.1.Completion)ˣ :=
    localAction v
  infer_instance

set_option maxHeartbeats 1000000 in
-- Equivariance of the ring regrouping expands dependent completion transport
-- across every normalized infinite place.
set_option synthInstance.maxHeartbeats 300000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- The ring regrouping intertwines the concrete infinite-idèle action
with the pointwise family of completion-product actions. -/
theorem infinite_ideles_smul
    (sigma : Gal(L/K)) (x : (InfiniteAdeleRing L)ˣ) :
    letI := infiniteIdelesAction (K := K) (L := L)
    letI := normalizedUnitsAction
      (K := K) (L := L)
    infiniteIdelesUnits
        (K := K) (L := L) (sigma • x) =
      sigma •
        infiniteIdelesUnits
          (K := K) (L := L) x := by
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := normalizedUnitsAction
    (K := K) (L := L)
  funext v
  apply Units.ext
  funext z
  change numberInfiniteTransport (K := K) sigma
      (normalizedInfinitePlace
        (K := K) (L := L) v z)
      ((x : InfiniteAdeleRing L)
        (sigma⁻¹ • normalizedInfinitePlace
          (K := K) (L := L) v z)) =
    completionFamilyTransport v.1 sigma z
      ((x : InfiniteAdeleRing L)
        (normalizedInfinitePlace
          (K := K) (L := L) v (sigma⁻¹ • z)))
  have hindex := normalized_infinite_smul
    (K := K) (L := L) v sigma⁻¹ z
  have hx : HEq
      ((x : InfiniteAdeleRing L)
        (sigma⁻¹ • normalizedInfinitePlace
          (K := K) (L := L) v z))
      ((x : InfiniteAdeleRing L)
        (normalizedInfinitePlace
          (K := K) (L := L) v (sigma⁻¹ • z))) := by
    cases hindex
    rfl
  rw [number_transport_normalized
    (K := K) (L := L) v sigma z]
  exact congrArg (completionFamilyTransport v.1 sigma z) (eq_of_heq hx)

set_option maxHeartbeats 1000000 in
-- Constructing the resized family representation resolves the full dependent
-- completion-product action.
set_option synthInstance.maxHeartbeats 300000 in
/-- Resized representation on the pointwise family of the infinite
completion products. -/
noncomputable def resizedProductsRepresentation
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Rep (ULift.{u} ℤ) Gal(L/K) := by
  letI := normalizedUnitsAction
    (K := K) (L := L)
  exact uliftMulRepresentation
    (G := Gal(L/K))
    (M := (v : InfinitePlace K) →
      ((z : CompletionPlacesAbove (L := L) v.1) →
        z.1.Completion)ˣ)

set_option maxHeartbeats 1000000 in
-- Packaging infinite-idèle regrouping as a representation isomorphism
-- requires normalizing both dependent inverse maps and their actions.
set_option synthInstance.maxHeartbeats 300000 in
/-- Regrouping the infinite idèles by lower infinite place is an
equivariant representation isomorphism. -/
noncomputable def resizedIsoProducts :
    resizedInfiniteRepresentation K L ≅
      resizedProductsRepresentation K L := by
  apply Rep.mkIso
  let e := infiniteIdelesUnits
    (K := K) (L := L)
  refine
    { toLinearEquiv :=
        { toEquiv := e.toAdditive.toEquiv
          map_add' := e.toAdditive.map_add
          map_smul' := fun r x => map_zsmul e.toAdditive r.down x }
      isIntertwining' := ?_ }
  intro sigma
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  exact infinite_ideles_smul
    (K := K) (L := L) sigma x.toMul

/-- Evaluation of the pointwise family at one lower infinite place. -/
noncomputable def resizedProductsEvaluation
    (v : InfinitePlace K) :
    resizedProductsRepresentation K L ⟶
      uliftUnitsRepresentation
        (K := K) (L := L) v.1 := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (x.toMul v)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := ?_ }
  intro sigma
  ext x
  rfl

/-- Canonical coordinate map on the degree-two cohomology of the family of
infinite completion products. -/
noncomputable def infiniteProductsPi :
    H2 (resizedProductsRepresentation K L) →+
      (v : InfinitePlace K) →
        H2 (uliftUnitsRepresentation
          (K := K) (L := L) v.1) where
  toFun q v := groupCohomology.map (MonoidHom.id Gal(L/K))
    (resizedProductsEvaluation
      (K := K) (L := L) v) 2 q
  map_zero' := by
    funext v
    exact map_zero _
  map_add' x y := by
    funext v
    exact map_add _ x y

/-- Every family of infinite completion-product degree-two classes is
represented by one cocycle in their pointwise product. -/
theorem resized_products_pi :
    Function.Surjective
      (infiniteProductsPi
        (K := K) (L := L)) := by
  intro q
  have hrepresentative (v : InfinitePlace K) :
      ∃ xV : cocycles₂ (uliftUnitsRepresentation
          (K := K) (L := L) v.1),
        H2π _ xV = q v := by
    induction q v using H2_induction_on with
    | h xV => exact ⟨xV, rfl⟩
  choose x hx using hrepresentative
  let zFun : Gal(L/K) × Gal(L/K) →
      resizedProductsRepresentation K L :=
    fun gh => Additive.ofMul (fun v => (x v gh).toMul)
  have hz : zFun ∈ cocycles₂
      (resizedProductsRepresentation K L) := by
    apply (mem_cocycles₂_iff zFun).2
    intro g h j
    apply Additive.toMul.injective
    funext v
    exact congrArg Additive.toMul
      ((mem_cocycles₂_iff (x v)).1 (x v).2 g h j)
  let z : cocycles₂ (resizedProductsRepresentation
      K L) := ⟨zFun, hz⟩
  refine ⟨H2π _ z, ?_⟩
  funext v
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedProductsEvaluation
        (K := K) (L := L) v) 2 (H2π _ z) = q v
  rw [H2π_comp_map_apply, ← hx v]
  congr 1

/-- The infinite completion-product coordinate map is injective. -/
theorem products_pi_injective :
    Function.Injective
      (infiniteProductsPi
        (K := K) (L := L)) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hcoord : infiniteProductsPi
      (K := K) (L := L) (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  clear hqq'
  have hkernel (r : H2
      (resizedProductsRepresentation K L))
      (hr : infiniteProductsPi
        (K := K) (L := L) r = 0) : r = 0 := by
    induction r using H2_induction_on with
    | h z =>
      have hzero (v : InfinitePlace K) :
          H2π (uliftUnitsRepresentation
              (K := K) (L := L) v.1)
            (mapCocycles₂ (MonoidHom.id Gal(L/K))
              (resizedProductsEvaluation
                (K := K) (L := L) v) z) = 0 := by
        rw [← H2π_comp_map_apply]
        exact congrFun hr v
      have hwitness (v : InfinitePlace K) :
          ∃ aV : Gal(L/K) →
              uliftUnitsRepresentation
                (K := K) (L := L) v.1,
            d₁₂ _ aV = mapCocycles₂ (MonoidHom.id Gal(L/K))
              (resizedProductsEvaluation
                (K := K) (L := L) v) z :=
        (H2π_eq_zero_iff _).1 (hzero v)
      choose a ha using hwitness
      let aProduct : Gal(L/K) →
          resizedProductsRepresentation K L :=
        fun g => Additive.ofMul (fun v => (a v g).toMul)
      apply (H2π_eq_zero_iff z).2
      refine ⟨aProduct, ?_⟩
      funext gh
      apply Additive.toMul.injective
      funext v
      have haV := congrFun (ha v) gh
      change
        (uliftUnitsRepresentation
          (K := K) (L := L) v.1).ρ gh.1 (a v gh.2) -
            a v (gh.1 * gh.2) + a v gh.1 =
          Additive.ofMul ((z gh).toMul v) at haV
      exact congrArg Additive.toMul haV
  exact hkernel (q - q') hcoord

/-- Degree-two cohomology of the pointwise family of infinite completion
products is the product of their degree-two cohomology groups. -/
noncomputable def productsHPi :
    H2 (resizedProductsRepresentation K L) ≃+
      ((v : InfinitePlace K) →
        H2 (uliftUnitsRepresentation
          (K := K) (L := L) v.1)) :=
  AddEquiv.ofBijective
    (infiniteProductsPi (K := K) (L := L))
    ⟨products_pi_injective
      (K := K) (L := L),
     resized_products_pi
      (K := K) (L := L)⟩

/-- The constant infinite-idèle cohomology is the direct sum of the
infinite-place completion-product cohomology groups. -/
noncomputable def resizedDirectSum :
    H2 (resizedInfiniteRepresentation K L) ≃+
      DirectSum (InfinitePlace K)
        (fun v => H2 (resizedPlaceRepresentation
          (K := K) (L := L) (.inr v))) :=
  (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
      (resizedIsoProducts
        (K := K) (L := L))).toLinearEquiv.toAddEquiv.trans
    (productsHPi
      (K := K) (L := L))).trans
        (DirectSum.addEquivProd (fun v : InfinitePlace K =>
          H2 (resizedPlaceRepresentation
            (K := K) (L := L) (.inr v)))).symm

end

end Towers.CField.HNorm
