import Submission.ClassField.LocalReciprocity.LiteralTowerTypes
import Submission.ClassField.LocalReciprocity.UniverseContinuity
import Submission.ClassField.LocalReciprocity.UniverseRestriction
import Submission.ClassField.NormCorrespondence.MaximalAbelianTower
import Submission.ClassField.Reciprocity.UniverseArtinContinuity
import Submission.ClassField.Reciprocity.CompletionArtinHom
import Submission.ClassField.Reciprocity.FiniteProductContinuity
import Submission.ClassField.Reciprocity.FiniteRestrictionTopology
import Submission.ClassField.NormIndex.IdeleTowerLocal
import Submission.ClassField.NormIndex.InfiniteIdeleCompatibility
import Submission.ClassField.KummerNormIndex.PowerIndex
import Submission.ClassField.GrunwaldWang.CompletionNormCompatibility
import Submission.ClassField.HasseNorm.UnramifiedLocal

/-!
# Chapter V, Section 5, Proposition 5.2

This file constructs the finite-layer Artin products from the normalized
local Artin maps and assembles them into the absolute abelian Galois group.
-/

namespace Submission.CField.Recip

open scoped IsMulCommutative
open Filter Ideal IsDedekindDomain NumberField
open CategoryTheory Opposite CategoryTheory.Limits
open FiniteGaloisIntermediateField ProfiniteGrp
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LRecip
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.HNorm
open scoped RestrictedProduct Topology

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

noncomputable local instance layerNumberField
    (L : FASubext K) : NumberField L.1 :=
  NumberField.of_module_finite K L.1

private theorem finiteIndependence
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w q : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    adicArtinUniverse K L P w =
      adicArtinUniverse K L P q :=
  global_universe_independent P w q

private theorem finiteNormalization
    {K : Type u} [Field K] [NumberField K]
    (L : FASubext K) [NumberField L.1]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L.1) P) :
    let w := (Submission.CField.NIndex.placesAboveFactors
      (K := K) (L := L.1) P).symm Q
    LayerLocalArtin L P Q
      (adicArtinUniverse K L.1 P w) :=
  global_artin_universe
    L P Q

/-! A literal-tower form of III.3.3 for abelian upper and lower fields. -/

private theorem universe_restrict_tower
    (F₀ Ω F : Type u)
    [NontriviallyNormedField F₀] [IsUltrametricDist F₀]
    [ValuativeRel F₀] [IsNonarchimedeanLocalField F₀]
    [Valuation.Compatible (NormedField.valuation (K := F₀))]
    [Field Ω] [Algebra F₀ Ω] [FiniteDimensional F₀ Ω]
    [IsGalois F₀ Ω] [IsMulCommutative Gal(Ω/F₀)]
    [Field F] [Algebra F₀ F] [Algebra F Ω]
    [IsScalarTower F₀ F Ω] [FiniteDimensional F₀ F]
    [IsGalois F₀ F] [IsMulCommutative Gal(F/F₀)] :
    (AlgEquiv.restrictNormalHom F).comp
        (abelianArtinUniverse F₀ Ω) =
      abelianArtinUniverse F₀ F := by
  let i : F →ₐ[F₀] Ω := IsScalarTower.toAlgHom F₀ F Ω
  let Ffield : IntermediateField F₀ Ω := i.fieldRange
  let eF : F ≃ₐ[F₀] Ffield :=
    IntermediateField.topEquiv.symm |>.trans
      ((IntermediateField.equivMap (⊤ : IntermediateField F₀ F) i).trans
        (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map i).symm))
  letI : FiniteDimensional F₀ Ffield :=
    Module.Finite.equiv eF.toLinearEquiv
  letI : IsGalois F₀ Ffield := IsGalois.of_algEquiv eF
  letI : IsMulCommutative Gal(Ffield/F₀) := by
    refine ⟨⟨fun sigma tau => eF.autCongr.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (eF.autCongr.symm sigma) (eF.autCongr.symm tau)
  let Ofield : IntermediateField F₀ Ω := ⊤
  let eO : Ω ≃ₐ[F₀] Ofield := IntermediateField.topEquiv.symm
  letI : FiniteDimensional F₀ Ofield :=
    Module.Finite.equiv eO.toLinearEquiv
  letI : IsGalois F₀ Ofield := IsGalois.of_algEquiv eO
  letI : IsMulCommutative Gal(Ofield/F₀) := by
    refine ⟨⟨fun sigma tau => eO.autCongr.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (eO.autCongr.symm sigma) (eO.autCongr.symm tau)
  let Flevel : FiniteGaloisIntermediateField F₀ Ω :=
    { Ffield with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let Olevel : FiniteGaloisIntermediateField F₀ Ω :=
    { Ofield with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let hFO : Flevel ≤ Olevel := by
    change Ffield ≤ Ofield
    exact le_top
  letI : Algebra Ffield Ofield :=
    RingHom.toAlgebra (Subsemiring.inclusion (show Ffield ≤ Ofield by exact le_top))
  let restrictionField : Gal(Ofield/F₀) →* Gal(Ffield/F₀) :=
    galoisRestrictionHom F₀ hFO
  have hrestriction : restrictionField.comp eO.autCongr.toMonoidHom =
      eF.autCongr.toMonoidHom.comp (AlgEquiv.restrictNormalHom F) := by
    apply MonoidHom.ext
    intro sigma
    apply AlgEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := eF.surjective x
    simp only [MonoidHom.comp_apply]
    apply (algebraMap Ffield Ofield).injective
    change algebraMap Ffield Ofield
        ((galoisRestrictionHom F₀ hFO (eO.autCongr sigma)) (eF x)) =
      algebraMap Ffield Ofield
        (eF.autCongr (AlgEquiv.restrictNormalHom F sigma) (eF x))
    have hr := galois_restriction_hom F₀ hFO
      (eO.autCongr sigma) (eF x)
    change algebraMap Ffield Ofield
        ((galoisRestrictionHom F₀ hFO (eO.autCongr sigma)) (eF x)) =
      eO.autCongr sigma (algebraMap Ffield Ofield (eF x)) at hr
    rw [hr]
    apply eO.symm.injective
    simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      eO.symm_apply_apply, eF.symm_apply_apply]
    change sigma (i x) = i ((AlgEquiv.restrictNormalHom F sigma) x)
    exact (AlgEquiv.restrictNormal_commutes sigma F x).symm
  have hintermediate := abelian_universe_restriction
    F₀ Ω hFO
  have htransport := abelian_universe_alg
    F₀ F Ffield eF
  have hambient := abelian_universe_alg
    F₀ Ω Ofield eO
  apply MonoidHom.ext
  intro a
  apply eF.autCongr.injective
  have hi := DFunLike.congr_fun hintermediate a
  have ht := DFunLike.congr_fun htransport a
  have ha := DFunLike.congr_fun hambient a
  have hr := DFunLike.congr_fun hrestriction
    (abelianArtinUniverse F₀ Ω a)
  change eF.autCongr
      (AlgEquiv.restrictNormalHom F
        (abelianArtinUniverse F₀ Ω a)) =
    eF.autCongr (abelianArtinUniverse F₀ F a)
  calc
    _ = restrictionField
        (eO.autCongr (abelianArtinUniverse F₀ Ω a)) := hr.symm
    _ = restrictionField
        (abelianArtinUniverse F₀ Ofield a) :=
      congrArg restrictionField (by
        simpa only [MonoidHom.comp_apply] using ha)
    _ = abelianArtinUniverse F₀ Ffield a := by
      simpa only [MonoidHom.comp_apply] using hi
    _ = eF.autCongr (abelianArtinUniverse F₀ F a) := by
      simpa only [MonoidHom.comp_apply] using ht.symm

/-! The finite product of local factors, specialized to the source and
targets needed in V.5.2.  This lives here so V.5.2 does not depend on the
later idèle-norm tower modules. -/

structure IAProduc
    (K G : Type u) [Field K] [NumberField K] [CommGroup G] where
  finite : RLFam (A := G)
    (fun P : HeightOneSpectrum (OK K) =>
      IdeleUnitSubgroup (OK K) K P)
  infinite : ∀ v : InfinitePlace K, v.1.Completionˣ →* G

namespace IAProduc

variable {G : Type u} [CommGroup G]

noncomputable def infiniteHom (D : IAProduc K G) :
    (InfiniteAdeleRing K)ˣ →* G where
  toFun x := ∏ v : InfinitePlace K, D.infinite v (MulEquiv.piUnits x v)
  map_one' := by
    apply Finset.prod_eq_one
    intro v _
    rw [show MulEquiv.piUnits (1 : (InfiniteAdeleRing K)ˣ) v = 1 by
      exact congrFun (map_one (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) →
          v.1.Completionˣ))) v]
    exact map_one (D.infinite v)
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [show MulEquiv.piUnits (x * y) v =
        MulEquiv.piUnits x v * MulEquiv.piUnits y v by
      exact congrFun (map_mul (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) →
          v.1.Completionˣ)) x y) v]
    exact map_mul (D.infinite v) _ _

set_option maxHeartbeats 1000000 in
-- The restricted-product group structure is dependent on every finite place.
set_option synthInstance.maxHeartbeats 100000 in
noncomputable def artin (D : IAProduc K G) :
    IdeleGroup (OK K) K →* G where
  toFun x := D.infiniteHom x.1 * D.finite.restrictedProductHom _ x.2
  map_one' := by
    change D.infiniteHom 1 * D.finite.restrictedProductHom _ 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' x y := by
    change D.infiniteHom (x.1 * y.1) *
        D.finite.restrictedProductHom _ (x.2 * y.2) = _
    rw [map_mul D.infiniteHom]
    calc
      (D.infiniteHom x.1 * D.infiniteHom y.1) *
          D.finite.restrictedProductHom _ (x.2 * y.2) =
        (D.infiniteHom x.1 * D.infiniteHom y.1) *
          (D.finite.restrictedProductHom _ x.2 *
            D.finite.restrictedProductHom _ y.2) := by
              exact congrArg (fun z ↦
                (D.infiniteHom x.1 * D.infiniteHom y.1) * z)
                ((D.finite.restrictedProductHom _).map_mul x.2 y.2)
      _ = _ := by ac_rfl

@[simp]
theorem artin_apply (D : IAProduc K G)
    (x : IdeleGroup (OK K) K) :
    D.artin x =
      (∏ v : InfinitePlace K,
        D.infinite v (MulEquiv.piUnits x.1 v)) *
      (∏ᶠ P : HeightOneSpectrum (OK K),
        D.finite.localHom P (x.2.1 P)) := rfl

theorem artin_place_embedding
    (D : IAProduc K G)
    (P : HeightOneSpectrum (OK K)) (x : (P.adicCompletion K)ˣ) :
    D.artin (finitePlaceEmbedding (OK K) K P x) =
      D.finite.localHom P x := by
  classical
  change D.infiniteHom 1 *
      D.finite.restrictedProductHom
        (fun Q : HeightOneSpectrum (OK K) =>
          IdeleUnitSubgroup (OK K) K Q)
        (RestrictedProduct.mulSingle
          (fun Q : HeightOneSpectrum (OK K) =>
            IdeleUnitSubgroup (OK K) K Q) P x) = _
  rw [map_one, one_mul]
  exact RLFam.restricted_product_single
    (U := fun Q : HeightOneSpectrum (OK K) =>
      IdeleUnitSubgroup (OK K) K Q) D.finite P x

set_option maxHeartbeats 1000000 in
-- The finite-idèle identity has a dependent restricted-product type.
set_option synthInstance.maxHeartbeats 100000 in
theorem artin_infinite_embedding
    (D : IAProduc K G)
    (v : InfinitePlace K) (x : v.1.Completionˣ) :
    D.artin (infinitePlaceEmbedding (OK K) K v x) = D.infinite v x := by
  classical
  change D.infiniteHom (infiniteLocalEmbedding K v x) *
      D.finite.restrictedProductHom
        (fun P : HeightOneSpectrum (OK K) =>
          IdeleUnitSubgroup (OK K) K P) 1 = _
  rw [map_one, mul_one]
  have hsingle :
      MulEquiv.piUnits (infiniteLocalEmbedding K v x) =
        (Pi.mulSingle v x : (q : InfinitePlace K) → q.1.Completionˣ) :=
    MulEquiv.apply_symm_apply _ _
  change (∏ w : InfinitePlace K,
      D.infinite w (MulEquiv.piUnits (infiniteLocalEmbedding K v x) w)) = _
  rw [hsingle]
  calc
    _ = D.infinite v
        ((Pi.mulSingle v x : (q : InfinitePlace K) → q.1.Completionˣ) v) := by
      apply Fintype.prod_eq_single v
      intro w hw
      rw [Pi.mulSingle_eq_of_ne hw]
      exact map_one (D.infinite w)
    _ = D.infinite v x := by rw [Pi.mulSingle_eq_same]

theorem layerArtinProduct
    (L : FASubext K)
    (D : IAProduc K Gal(L.1/K))
    (hfinite : ∀ (P : HeightOneSpectrum (OK K))
        (Q : UpperPrimeFactors (K := K) (L := L.1) P),
      LayerLocalArtin L P Q (D.finite.localHom P))
    (hinfinite : ∀ (v : InfinitePlace K)
        (w : InfinitePlacesAbove (K := K) (L := L.1) v),
      InfiniteLayerArtin L v w (D.infinite v)) :
    LayerArtinProduct L D.artin := by
  exact ⟨fun P Q => ⟨D.finite.localHom P, hfinite P Q,
      D.artin_place_embedding P⟩,
    fun v w => ⟨D.infinite v, hinfinite v w,
      D.artin_infinite_embedding v⟩⟩

end IAProduc

/-! ### Canonical local factors -/

/-- A fixed upper completion above a finite prime.  The resulting Artin map
is independent of this choice by Lemma V.5.1. -/
noncomputable def finiteCompletion
    (L : FASubext K)
    (P : HeightOneSpectrum (OK K)) :
    CompletionPlacesAbove (L := L.1) (FinitePlace.mk P).val := by
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  exact Classical.choice
    (absolute_value_extension (K := K) (L := L.1)
      (FinitePlace.mk P).val)

/-- The canonical finite-place factor at a finite abelian layer. -/
noncomputable def finiteLocalHom
    (L : FASubext K)
    (P : HeightOneSpectrum (OK K)) :
    (P.adicCompletion K)ˣ →* Gal(L.1/K) :=
  adicArtinUniverse K L.1 P
    (finiteCompletion L P)

/-- A fixed upper infinite place.  Its Artin map is likewise independent of
the choice in an abelian extension. -/
noncomputable def infinitePlace
    (L : FASubext K) (v : InfinitePlace K) :
    InfinitePlacesAbove (K := K) (L := L.1) v :=
  ⟨Classical.choose (infinite_place (L := L.1) v),
    Classical.choose_spec (infinite_place (L := L.1) v)⟩

/-- The canonical archimedean factor at a finite abelian layer. -/
noncomputable def infiniteLocalHom
    (L : FASubext K) (v : InfinitePlace K) :
    v.1.Completionˣ →* Gal(L.1/K) :=
  infiniteGlobalArtin v (infinitePlace L v)

/-! ### Compatibility in a finite global tower -/

set_option maxHeartbeats 8000000 in
-- Finite-place restriction unfolds both completion towers and their Artin transports.
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem local_hom_restriction
    (M L : FASubext K)
    (hML : (M.1 : IntermediateField K (SeparableClosure K)) ≤ L.1)
    (P : HeightOneSpectrum (OK K)) :
    (galoisRestrictionHom K hML).comp
        (finiteLocalHom L P) =
      finiteLocalHom M P := by
  let v := (FinitePlace.mk P).val
  let t := finiteCompletion L P
  letI : Algebra M.1 L.1 :=
    RingHom.toAlgebra (Subsemiring.inclusion hML)
  letI : IsScalarTower K M.1 L.1 :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : IsGalois M.1 L.1 :=
    IsGalois.tower_top_of_isGalois K M.1 L.1
  let uval : AbsoluteValue M.1 ℝ :=
    t.1.comp (algebraMap M.1 L.1).injective
  have huv : AbsoluteValue.LiesOver uval v := by
    constructor
    ext x
    change t.1 (algebraMap M.1 L.1 (algebraMap K M.1 x)) = v x
    rw [← IsScalarTower.algebraMap_apply K M.1 L.1]
    exact DFunLike.congr_fun t.2.comp_eq x
  let u : CompletionPlacesAbove (L := M.1) v := ⟨uval, huv⟩
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver u.1 v) := ⟨u.2⟩
  letI : Fact (AbsoluteValue.LiesOver t.1 v) := ⟨t.2⟩
  letI : Algebra v.Completion u.1.Completion :=
    (completionLies v u.1 u.2).toAlgebra
  have htu : AbsoluteValue.LiesOver t.1 u.1 := by
    constructor
    rfl
  letI : Algebra u.1.Completion t.1.Completion :=
    (completionLies u.1 t.1 htu).toAlgebra
  letI : Algebra v.Completion t.1.Completion :=
    (completionLies v t.1 t.2).toAlgebra
  letI : IsScalarTower v.Completion u.1.Completion t.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (completion_lies_trans v u.1 t.1
      u.2 htu t.2).symm
  letI : FiniteDimensional v.Completion u.1.Completion :=
    placeCompletionDimensional v u
  letI : FiniteDimensional v.Completion t.1.Completion :=
    placeCompletionDimensional v t
  letI : FiniteDimensional u.1.Completion t.1.Completion := by
    exact Module.Finite.of_restrictScalars_finite v.Completion
      u.1.Completion t.1.Completion
  letI : Finite (CompletionPlacesAbove (L := M.1) v) :=
    absolute_extensions_separable v
  letI : Finite (CompletionPlacesAbove (L := L.1) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := M.1) v) :=
    absolute_value_extension (K := K) (L := M.1) v
  letI : Nonempty (CompletionPlacesAbove (L := L.1) v) :=
    absolute_value_extension (K := K) (L := L.1) v
  letI : MulAction.IsPretransitive Gal(M.1/K)
      (CompletionPlacesAbove (L := M.1) v) :=
    completion_above_pretransitive P
  letI : MulAction.IsPretransitive Gal(L.1/K)
      (CompletionPlacesAbove (L := L.1) v) :=
    completion_above_pretransitive P
  letI : IsGalois v.Completion u.1.Completion :=
    placeCompletionGalois v u
  letI : IsGalois v.Completion t.1.Completion :=
    placeCompletionGalois v t
  let decompM := decompositionCompletionExtension v u.1
  let decompL := decompositionCompletionExtension v t.1
  letI : IsMulCommutative Gal(u.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau => decompM.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decompM.symm sigma) (decompM.symm tau)
  letI : IsMulCommutative Gal(t.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau => decompL.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decompL.symm sigma) (decompL.symm tau)
  let localRestriction : Gal(t.1.Completion/v.Completion) →*
      Gal(u.1.Completion/v.Completion) :=
    AlgEquiv.restrictNormalHom u.1.Completion
  have hlocal : localRestriction.comp
        (abelianArtinUniverse v.Completion t.1.Completion) =
      abelianArtinUniverse v.Completion u.1.Completion :=
    universe_restrict_tower
      v.Completion t.1.Completion u.1.Completion
  let intoL : Gal(t.1.Completion/v.Completion) →* Gal(L.1/K) :=
    (absoluteValueDecomposition v t.1).subtype.comp
      decompL.symm.toMonoidHom
  let intoM : Gal(u.1.Completion/v.Completion) →* Gal(M.1/K) :=
    (absoluteValueDecomposition v u.1).subtype.comp
      decompM.symm.toMonoidHom
  let globalRestriction : Gal(L.1/K) →* Gal(M.1/K) :=
    galoisRestrictionHom K hML
  have htarget : globalRestriction.comp intoL =
      intoM.comp localRestriction := by
    apply MonoidHom.ext
    intro sigma
    apply AlgEquiv.ext
    intro x
    apply (completionEmbedding u.1).injective
    let tauL : absoluteValueDecomposition v t.1 := decompL.symm sigma
    let rho : Gal(u.1.Completion/v.Completion) := localRestriction sigma
    let tauM : absoluteValueDecomposition v u.1 := decompM.symm rho
    have hL : decompositionCompletionEquiv v t.1 tauL = sigma :=
      decompL.apply_symm_apply sigma
    have hM : decompositionCompletionEquiv v u.1 tauM = rho :=
      decompM.apply_symm_apply rho
    apply (algebraMap u.1.Completion t.1.Completion).injective
    calc
      algebraMap u.1.Completion t.1.Completion
          (completionEmbedding u.1
            ((globalRestriction (intoL sigma)) x)) =
          completionEmbedding t.1
            (algebraMap M.1 L.1 ((globalRestriction (intoL sigma)) x)) := by
            exact RingHom.congr_fun
              (completion_lies_comp u.1 t.1 htu) _
      _ = completionEmbedding t.1 ((intoL sigma) (algebraMap M.1 L.1 x)) := by
            exact congrArg (completionEmbedding t.1)
              (galois_restriction_hom K hML (intoL sigma) x)
      _ = sigma (completionEmbedding t.1 (algebraMap M.1 L.1 x)) := by
            change completionEmbedding t.1
                (tauL.1 (algebraMap M.1 L.1 x)) = _
            rw [← decomposition_alg_embedding]
            rw [hL]
      _ = sigma (algebraMap u.1.Completion t.1.Completion
          (completionEmbedding u.1 x)) := by
            apply congrArg sigma
            exact (RingHom.congr_fun
              (completion_lies_comp u.1 t.1 htu) x).symm
      _ = algebraMap u.1.Completion t.1.Completion
          (rho (completionEmbedding u.1 x)) := by
            exact (AlgEquiv.restrictNormal_commutes sigma
              u.1.Completion (completionEmbedding u.1 x)).symm
      _ = algebraMap u.1.Completion t.1.Completion
          (completionEmbedding u.1 (tauM.1 x)) := by
            apply congrArg (algebraMap u.1.Completion t.1.Completion)
            rw [← hM]
            exact decomposition_alg_embedding
              v u.1 tauM x
      _ = algebraMap u.1.Completion t.1.Completion
          (completionEmbedding u.1 ((intoM rho) x)) := rfl
  rw [show finiteLocalHom M P =
      adicArtinUniverse K M.1 P u by
    exact finiteIndependence P _ u]
  unfold finiteLocalHom
  rw [artin_universe_completion,
    artin_universe_completion]
  unfold globalArtinUniverse
  let toAbsoluteCompletion : (P.adicCompletion K)ˣ →* v.Completionˣ :=
    Units.map
      (placeCompletionAdic P).symm.toRingHom
  change (globalRestriction.comp
      (intoL.comp ((abelianArtinUniverse
        v.Completion t.1.Completion).comp toAbsoluteCompletion))) =
    intoM.comp ((abelianArtinUniverse
      v.Completion u.1.Completion).comp toAbsoluteCompletion)
  calc
    _ = (globalRestriction.comp intoL).comp
        ((abelianArtinUniverse
          v.Completion t.1.Completion).comp toAbsoluteCompletion) := by
      simp only [MonoidHom.comp_assoc]
    _ = (intoM.comp localRestriction).comp
        ((abelianArtinUniverse
          v.Completion t.1.Completion).comp toAbsoluteCompletion) := by
      rw [htarget]
    _ = intoM.comp
        ((localRestriction.comp
          (abelianArtinUniverse
            v.Completion t.1.Completion)).comp toAbsoluteCompletion) := by
      simp only [MonoidHom.comp_assoc]
    _ = _ := by rw [hlocal]

set_option maxHeartbeats 8000000 in
-- Infinite-place restriction compares dependent completion and Galois transports.
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem infinite_local_restriction
    (M L : FASubext K)
    (hML : (M.1 : IntermediateField K (SeparableClosure K)) ≤ L.1)
    (v : InfinitePlace K) :
    (galoisRestrictionHom K hML).comp
        (infiniteLocalHom L v) =
      infiniteLocalHom M v := by
  let t := infinitePlace L v
  letI : Algebra M.1 L.1 :=
    RingHom.toAlgebra (Subsemiring.inclusion hML)
  letI : IsScalarTower K M.1 L.1 :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : IsGalois M.1 L.1 :=
    IsGalois.tower_top_of_isGalois K M.1 L.1
  let u₀ : InfinitePlace M.1 := t.1.comap (algebraMap M.1 L.1)
  have hu₀ : u₀.comap (algebraMap K M.1) = v := by
    rw [← InfinitePlace.comap_comp]
    change t.1.comap ((algebraMap M.1 L.1).comp (algebraMap K M.1)) = v
    rw [← IsScalarTower.algebraMap_eq K M.1 L.1]
    exact t.2
  let u : InfinitePlacesAbove (K := K) (L := M.1) v := ⟨u₀, hu₀⟩
  let tM : InfinitePlacesAbove (K := M.1) (L := L.1) u.1 := ⟨t.1, rfl⟩
  rw [show infiniteLocalHom M v =
      infiniteGlobalArtin v u by
    exact infinite_artin_independent v _ u]
  unfold infiniteLocalHom
  let Dₗ := absoluteValueDecomposition v.1 t.1.1
  let Dₘ := absoluteValueDecomposition v.1 u.1.1
  let globalRestriction : Gal(L.1/K) →* Gal(M.1/K) :=
    galoisRestrictionHom K hML
  let rD : Dₗ →* Dₘ :=
    { toFun := fun sigma => ⟨globalRestriction sigma.1, by
          intro x
          change t.1.1
              (algebraMap M.1 L.1
                ((sigma.1.restrictScalars K).restrictNormal M.1 x)) =
            t.1.1 (algebraMap M.1 L.1 x)
          rw [AlgEquiv.restrictNormal_commutes]
          exact sigma.2 (algebraMap M.1 L.1 x)⟩
      map_one' := by
        apply Subtype.ext
        exact map_one globalRestriction
      map_mul' := fun sigma tau => by
        apply Subtype.ext
        exact map_mul globalRestriction sigma.1 tau.1 }
  have hDₘstab : Dₘ = MulAction.stabilizer Gal(M.1/K) u.1 := by
    change absoluteValueDecomposition v.1 u.1.1 = _
    rw [absolute_decomposition_stabilizer]
    ext sigma
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      apply InfinitePlace.ext
      exact fun x => DFunLike.congr_fun h x
    · intro h
      exact congrArg (fun z : InfinitePlace M.1 => z.1) h
  have hDₗstab : Dₗ = MulAction.stabilizer Gal(L.1/K) t.1 := by
    change absoluteValueDecomposition v.1 t.1.1 = _
    rw [absolute_decomposition_stabilizer]
    ext sigma
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      apply InfinitePlace.ext
      exact fun x => DFunLike.congr_fun h x
    · intro h
      exact congrArg (fun z : InfinitePlace L.1 => z.1) h
  by_cases huRam : u.1.IsRamified K
  · have htComplex : t.1.IsComplex := by
      rw [← InfinitePlace.not_isReal_iff_isComplex]
      intro htReal
      have huReal := htReal.comap (algebraMap M.1 L.1)
      have huComplex := huRam.isComplex
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr huComplex) huReal
    have htRam : t.1.IsRamified K := by
      rw [InfinitePlace.isRamified_iff]
      refine ⟨htComplex, ?_⟩
      have hvReal := huRam.isReal
      simpa only [IsScalarTower.algebraMap_eq K M.1 L.1,
        InfinitePlace.comap_comp, tM, u, u₀, hu₀] using hvReal
    have hDₘcard : Nat.card Dₘ = 2 := by
      rw [hDₘstab]
      exact InfinitePlace.isRamified_iff_card_stabilizer_eq_two.mp huRam
    have hDₗcard : Nat.card Dₗ = 2 := by
      rw [hDₗstab]
      exact InfinitePlace.isRamified_iff_card_stabilizer_eq_two.mp htRam
    let F := u.1.1.Completion
    let E := t.1.1.Completion
    let huv := infinite_lies_comap v u.1 u.2
    let hut := infinite_lies_comap u.1 tM.1 tM.2
    let hvt := infinite_lies_comap v t.1 t.2
    letI : Fact (AbsoluteValue.LiesOver u.1.1 v.1) := ⟨huv⟩
    letI : Fact (AbsoluteValue.LiesOver t.1.1 u.1.1) := ⟨hut⟩
    letI : Fact (AbsoluteValue.LiesOver t.1.1 v.1) := ⟨hvt⟩
    letI : Algebra v.1.Completion F :=
      (completionLies v.1 u.1.1 huv).toAlgebra
    letI : Algebra F E :=
      (completionLies u.1.1 t.1.1 hut).toAlgebra
    letI : Algebra v.1.Completion E :=
      (completionLies v.1 t.1.1 hvt).toAlgebra
    letI : IsScalarTower v.1.Completion F E := by
      apply IsScalarTower.of_algebraMap_eq'
      exact (completion_lies_trans v.1 u.1.1 t.1.1
        huv hut hvt).symm
    letI : FiniteDimensional v.1.Completion F :=
      infinite_completion_module (K := K) (L := M.1) v u
    letI : FiniteDimensional v.1.Completion E :=
      infinite_completion_module (K := K) (L := L.1) v t
    letI : FiniteDimensional F E :=
      infinite_completion_module (K := M.1) (L := L.1) u.1 tM
    letI : IsGalois v.1.Completion F :=
      infiniteCompletionGalois (K := K) (L := M.1) v u
    letI : IsGalois v.1.Completion E :=
      infiniteCompletionGalois (K := K) (L := L.1) v t
    letI : IsGalois F E :=
      infiniteCompletionGalois (K := M.1) (L := L.1) u.1 tM
    have htUnramM : t.1.IsUnramified M.1 := by
      apply InfinitePlace.isUnramified_iff.mpr
      exact Or.inr (by simpa only [tM] using huRam.isComplex)
    have hrelCard : Nat.card
        (absoluteValueDecomposition u.1.1 t.1.1) = 1 := by
      have hstab : absoluteValueDecomposition u.1.1 t.1.1 =
          MulAction.stabilizer Gal(L.1/M.1) t.1 := by
        rw [absolute_decomposition_stabilizer]
        ext sigma
        rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
        constructor
        · intro h
          apply InfinitePlace.ext
          exact fun x ↦ DFunLike.congr_fun h x
        · intro h
          exact congrArg (fun z : InfinitePlace L.1 ↦ z.1) h
      rw [hstab]
      exact InfinitePlace.isUnramified_iff_card_stabilizer_eq_one.mp htUnramM
    have hdegree : Module.finrank F E = 1 :=
      (Submission.CField.GWang.infiniteDegreeCompatibility
        M.1 L.1 u.1 tM).trans
        hrelCard
    have halgSurj : Function.Surjective (algebraMap F E) := by
      intro z
      have hone : (1 : E) ≠ 0 := by
        intro h
        rcases exists_pair_ne E with ⟨x, y, hxy⟩
        apply hxy
        calc
          x = 1 * x := (one_mul x).symm
          _ = 0 := by rw [h]; exact zero_mul x
          _ = 1 * y := by rw [h]; exact (zero_mul y).symm
          _ = y := one_mul y
      obtain ⟨c, hc⟩ :=
        (finrank_eq_one_iff_of_nonzero' (K := F) (V := E) (1 : E)
          hone).mp hdegree z
      refine ⟨c, ?_⟩
      calc
        algebraMap F E c = algebraMap F E c * 1 :=
          (mul_one (algebraMap F E c)).symm
        _ = z := by simpa only [Algebra.smul_def] using hc
    let decompL := infiniteDecompositionGroup v t.1
    let decompM := infiniteDecompositionGroup v u.1
    let localRestriction : Gal(E/v.1.Completion) →* Gal(F/v.1.Completion) :=
      AlgEquiv.restrictNormalHom F
    have hdecomp (sigma : Dₗ) :
        decompM (rD sigma) = localRestriction (decompL sigma) := by
      apply AlgEquiv.ext
      intro y
      apply (algebraMap F E).injective
      have hfun : (fun z : F => algebraMap F E (decompM (rD sigma) z)) =
          fun z : F => decompL sigma (algebraMap F E z) := by
        apply (dense_range_embedding u.1.1).equalizer
        · exact (completion_lies_isometry u.1.1 t.1.1 hut).continuous.comp
            (decomposition_alg_continuous v.1 u.1.1 _)
        · exact (infinite_alg_isometry
            (K := K) (L := L.1) v t (decompL sigma)).continuous.comp
            (completion_lies_isometry u.1.1 t.1.1 hut).continuous
        · funext x
          simp only [Function.comp_apply]
          change algebraMap F E
              ((decompositionCompletionEquiv v.1 u.1.1 (rD sigma))
                (completionEmbedding u.1.1 x)) =
            decompL sigma
              (algebraMap F E (completionEmbedding u.1.1 x))
          rw [decomposition_alg_embedding]
          calc
            algebraMap F E
                (completionEmbedding u.1.1 ((rD sigma).1 x)) =
              completionEmbedding t.1.1
                (algebraMap M.1 L.1 ((rD sigma).1 x)) :=
              RingHom.congr_fun
                (completion_lies_comp u.1.1 t.1.1 hut) _
            _ = completionEmbedding t.1.1
                (sigma.1 (algebraMap M.1 L.1 x)) := by
              exact congrArg (completionEmbedding t.1.1)
                (galois_restriction_hom K hML sigma.1 x)
            _ = decompL sigma
                (completionEmbedding t.1.1 (algebraMap M.1 L.1 x)) :=
              (decomposition_alg_embedding
                v.1 t.1.1 sigma (algebraMap M.1 L.1 x)).symm
            _ = decompL sigma
                (algebraMap F E (completionEmbedding u.1.1 x)) := by
              exact congrArg (decompL sigma)
                (RingHom.congr_fun
                  (completion_lies_comp u.1.1 t.1.1 hut) x).symm
      exact (congrFun hfun y).trans
        (AlgEquiv.restrictNormal_commutes (decompL sigma) F y).symm
    have hrDInjective : Function.Injective rD := by
      intro sigma tau h
      apply decompL.injective
      apply AlgEquiv.ext
      intro z
      obtain ⟨y, rfl⟩ := halgSurj z
      have hr : localRestriction (decompL sigma) =
          localRestriction (decompL tau) := by
        rw [← hdecomp, ← hdecomp, h]
      calc
        decompL sigma (algebraMap F E y) =
            algebraMap F E (localRestriction (decompL sigma) y) :=
          (AlgEquiv.restrictNormal_commutes (decompL sigma) F y).symm
        _ = algebraMap F E (localRestriction (decompL tau) y) :=
          congrArg (algebraMap F E) (DFunLike.congr_fun hr y)
        _ = decompL tau (algebraMap F E y) :=
          AlgEquiv.restrictNormal_commutes (decompL tau) F y
    have hrDBijective : Function.Bijective rD :=
      (Nat.bijective_iff_injective_and_card rD).mpr
        ⟨hrDInjective, hDₗcard.trans hDₘcard.symm⟩
    let rE : Dₗ ≃* Dₘ := MulEquiv.ofBijective rD hrDBijective
    let Nₗ := (infiniteCompletionNorm (K := K) (L := L.1) v t).range
    let Nₘ := (infiniteCompletionNorm (K := K) (L := M.1) v u).range
    have hNle : Nₗ ≤ Nₘ := by
      rintro x ⟨z, rfl⟩
      refine ⟨infiniteCompletionNorm (K := M.1) (L := L.1) u.1 tM z, ?_⟩
      have htrans := infinite_completion_trans v u tM z
      have htotal :
          (infiniteAboveTower K M.1 L.1 v).symm ⟨u, tM⟩ = t := by
        apply Subtype.ext
        rfl
      cases htotal
      exact htrans.symm
    let q : (v.1.Completionˣ ⧸ Nₗ) →* (v.1.Completionˣ ⧸ Nₘ) :=
      QuotientGroup.map Nₗ Nₘ (MonoidHom.id _) (by simpa using hNle)
    have hqSurj : Function.Surjective q := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Nₘ z
      exact ⟨QuotientGroup.mk' Nₗ x, rfl⟩
    let eL := infinitePlaceArtin v t
    let eM := infinitePlaceArtin v u
    letI : Finite (v.1.Completionˣ ⧸ Nₗ) :=
      Finite.of_injective eL eL.injective
    letI : Finite (v.1.Completionˣ ⧸ Nₘ) :=
      Finite.of_injective eM eM.injective
    have hQLcard : Nat.card (v.1.Completionˣ ⧸ Nₗ) = 2 :=
      (Nat.card_congr eL.toEquiv).trans hDₗcard
    have hQMcard : Nat.card (v.1.Completionˣ ⧸ Nₘ) = 2 :=
      (Nat.card_congr eM.toEquiv).trans hDₘcard
    have hqInj : Function.Injective q :=
      ((Nat.bijective_iff_surjective_and_card q).mpr
        ⟨hqSurj, hQLcard.trans hQMcard.symm⟩).1
    have hNeq : Nₗ = Nₘ := by
      apply le_antisymm hNle
      intro x hx
      have hqone : q (QuotientGroup.mk' Nₗ x) = 1 := by
        change QuotientGroup.mk' Nₘ x = 1
        exact (QuotientGroup.eq_one_iff x).2 hx
      have hone : QuotientGroup.mk' Nₗ x = 1 := by
        apply hqInj
        simpa using hqone
      exact (QuotientGroup.eq_one_iff x).1 hone
    let erestricted : (v.1.Completionˣ ⧸ Nₗ) ≃* Dₘ := eL.trans rE
    have hupper : globalRestriction.comp
        (quotientEquivGlobal Nₗ Dₗ eL) =
      quotientEquivGlobal Nₗ Dₘ erestricted := by
      apply MonoidHom.ext
      intro x
      rfl
    change globalRestriction.comp
        (quotientEquivGlobal Nₗ Dₗ eL) =
      quotientEquivGlobal Nₘ Dₘ eM
    rw [hupper]
    exact quotient_equiv_global
      Nₗ Nₘ Dₘ Dₘ erestricted eM hNeq rfl (Or.inr hDₘcard)
  · have huUnram : u.1.IsUnramified K := by
      exact Classical.byContradiction (fun h => huRam h)
    have hDₘcard : Nat.card Dₘ = 1 := by
      rw [hDₘstab]
      exact InfinitePlace.isUnramified_iff_card_stabilizer_eq_one.mp huUnram
    letI : Subsingleton Dₘ := (Nat.card_eq_one_iff_unique.mp hDₘcard).1
    apply MonoidHom.ext
    intro x
    let upper : Dₗ :=
      (infinitePlaceArtin v t)
        (QuotientGroup.mk'
          (infiniteCompletionNorm (K := K) (L := L.1) v t).range x)
    let lower : Dₘ :=
      (infinitePlaceArtin v u)
        (QuotientGroup.mk'
          (infiniteCompletionNorm (K := K) (L := M.1) v u).range x)
    unfold infiniteGlobalArtin quotientEquivGlobal
    simp only [MonoidHom.comp_apply]
    change (rD upper : Gal(M.1/K)) = (lower : Gal(M.1/K))
    exact congrArg Subtype.val (Subsingleton.elim (rD upper) lower)

/-! ### Finite-place support -/

private def ramifiedPrimes
    (L : FASubext K) :
    Set (HeightOneSpectrum (OK K)) :=
  {P | ∃ Q : Ideal (OK L.1), IsPrime Q ∧ Q ≠ ⊥ ∧
    Q.under (OK K) = P.asIdeal ∧
      Ideal.ramificationIdx P.asIdeal Q ≠ 1}

private theorem ramifiedPrimes_finite
    (L : FASubext K) :
    (ramifiedPrimes L).Finite := by
  let bad : Set (Ideal (OK K)) :=
    {p | ∃ Q : Ideal (OK L.1), IsPrime Q ∧ Q ≠ ⊥ ∧
      Q.under (OK K) = p ∧ Ideal.ramificationIdx p Q ≠ 1}
  have hbad : bad.Finite := by
    exact ramified_base_primes (OK K) (OK L.1)
  have hinj : Function.Injective
      (fun P : HeightOneSpectrum (OK K) ↦ P.asIdeal) := by
    intro P Q h
    exact HeightOneSpectrum.ext_iff.mpr h
  change ((fun P : HeightOneSpectrum (OK K) ↦ P.asIdeal) ⁻¹' bad).Finite
  exact Set.Finite.preimage hinj.injOn hbad

private theorem chosenPrime_unramified
    (L : FASubext K)
    (P : HeightOneSpectrum (OK K))
    (hP : P ∉ ramifiedPrimes L) :
    let w := finiteCompletion L P
    let Q := Submission.CField.NIndex.placeUpperFactor
      (K := K) (L := L.1) P w
    Algebra.IsUnramifiedAt (OK K)
      (upperPrime (K := K) (L := L.1) P Q).asIdeal := by
  let w := finiteCompletion L P
  let Q := Submission.CField.NIndex.placeUpperFactor
    (K := K) (L := L.1) P w
  let q := upperPrime (K := K) (L := L.1) P Q
  letI : q.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L.1) P Q)).symm
  apply (unramified_ramification_idx
    P.asIdeal q.asIdeal q.ne_bot).2
  by_contra hram
  apply hP
  simp only [ramifiedPrimes, Set.mem_setOf_eq]
  exact ⟨q.asIdeal, q.isPrime, q.ne_bot,
    congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L.1) P Q), hram⟩

set_option maxHeartbeats 3000000 in
-- The finite norm-range comparison unfolds two completion models.
set_option synthInstance.maxHeartbeats 100000 in
private theorem local_hom_units
    (L : FASubext K)
    (P : HeightOneSpectrum (OK K))
    (hP : P ∉ ramifiedPrimes L)
    (x : (P.adicCompletion K)ˣ)
    (hx : x ∈ IdeleUnitSubgroup (OK K) K P) :
    finiteLocalHom L P x = 1 := by
  let w := finiteCompletion L P
  let Q := Submission.CField.NIndex.placeUpperFactor
    (K := K) (L := L.1) P w
  let q := upperPrime (K := K) (L := L.1) P Q
  have hQ : Algebra.IsUnramifiedAt (OK K) q.asIdeal :=
    chosenPrime_unramified L P hP
  have hxNorm : x ∈
      (finiteCompletionNorm (K := K) (L := L.1) P Q).range :=
    units_range_unramified
      (K := K) (L := L.1) P Q hQ hx
  let v := (FinitePlace.mk P).val
  letI : Small.{0} v.Completion :=
    absoluteSmallZero K v
  letI : Small.{0} w.1.Completion :=
    absoluteSmallZero L.1 w.1
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : CharZero v.Completion :=
    (RingHom.charZero_iff (algebraMap K v.Completion).injective).mp
      inferInstance
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : Finite (CompletionPlacesAbove (L := L.1) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L.1) v) :=
    absolute_value_extension (K := K) (L := L.1) v
  letI : MulAction.IsPretransitive Gal(L.1/K)
      (CompletionPlacesAbove (L := L.1) v) :=
    completion_above_pretransitive P
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let decomp := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau ↦ decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decomp.symm sigma) (decomp.symm tau)
  have hwq : w.1.IsEquiv
      (FinitePlace.mk (upperPrime (K := K) (L := L.1) P Q)).val := by
    have h :=
      (Submission.CField.NIndex.primeCompletionModel
        K L.1 P Q).isEquiv_upper
    change ((Submission.CField.NIndex.placesAboveFactors
      (K := K) (L := L.1) P).symm Q).1.IsEquiv
        (FinitePlace.mk (upperPrime (K := K) (L := L.1) P Q)).val at h
    rw [show (Submission.CField.NIndex.placesAboveFactors
        (K := K) (L := L.1) P).symm Q = w by
      exact (Submission.CField.NIndex.placesAboveFactors
        (K := K) (L := L.1) P).symm_apply_apply w] at h
    exact h
  have hnormRange :=
    Submission.CField.GWang.completion_norm_range
    (K := K) (L := L.1) P Q w.1 w.2
    hwq
    (inferInstance : Module.Finite v.Completion w.1.Completion)
  have hxAbsolute :
      Units.map (placeCompletionAdic P).symm.toRingHom x ∈
        normSubgroup v.Completion w.1.Completion := by
    change x ∈ (normSubgroup v.Completion w.1.Completion).comap
      (Units.map
        (placeCompletionAdic P).symm.toRingHom)
    rw [hnormRange]
    exact hxNorm
  have hlocalOne : abelianLocalSmall
      v.Completion w.1.Completion
      (Units.map
        (placeCompletionAdic P).symm.toRingHom x) = 1 := by
    rw [← MonoidHom.mem_ker, abelian_small_ker]
    exact hxAbsolute
  unfold finiteLocalHom
  rw [artin_universe_small]
  unfold globalArtinSmall
  simp only [MonoidHom.comp_apply]
  rw [hlocalOne]
  simp only [map_one]

private theorem finiteFactors_eventually
    (L : FASubext K) :
    ∀ᶠ P in cofinite, ∀ x : (P.adicCompletion K)ˣ,
      x ∈ IdeleUnitSubgroup (OK K) K P →
        finiteLocalHom L P x = 1 := by
  rw [eventually_cofinite]
  exact (ramifiedPrimes_finite L).subset (by
    intro P hPbad
    by_contra hP
    apply hPbad
    intro x hx
    exact local_hom_units L P hP x hx)

/-! ### The finite-layer product -/

/-- The literal product of all normalized local Artin symbols at `L/K`. -/
noncomputable def layerProduct
    (L : FASubext K) :
    IAProduc K Gal(L.1/K) where
  finite :=
    { localHom := finiteLocalHom L
      eventually_units := finiteFactors_eventually L }
  infinite := infiniteLocalHom L

private theorem layer_product_local
    (L : FASubext K) :
    LayerArtinProduct L (layerProduct L).artin := by
  apply IAProduc.layerArtinProduct
  · intro P Q
    let wQ := (Submission.CField.NIndex.placesAboveFactors
      (K := K) (L := L.1) P).symm Q
    rw [show (layerProduct L).finite.localHom P =
        adicArtinUniverse K L.1 P wQ by
      exact finiteIndependence P _ wQ]
    exact finiteNormalization L P Q
  · intro v w
    rw [show (layerProduct L).infinite v =
        infiniteGlobalArtin v w by
      exact infinite_artin_independent v _ w]
    exact infinite_artin_local
      L v w

/-! ### Continuity and uniqueness at one finite layer -/

private noncomputable def infiniteBasicSubgroup
    (v : InfinitePlace K) : Subgroup v.1.Completionˣ := by
  classical
  exact if hv : v.IsReal then
      (Units.posSubgroup ℝ).comap
        (Units.map
          (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMonoidHom)
    else ⊤

omit [NumberField K] in
private theorem infinite_basic_open
    (v : InfinitePlace K) :
    IsOpen (infiniteBasicSubgroup (K := K) v :
      Set v.1.Completionˣ) := by
  classical
  rw [infiniteBasicSubgroup]
  split_ifs with hv
  · change IsOpen ((Units.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMonoidHom) ⁻¹'
        (Units.posSubgroup ℝ : Set ℝˣ))
    apply IsOpen.preimage
    · let e : v.1.Completion ≃ₜ* ℝ :=
        { __ := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMulEquiv
          continuous_toFun :=
            (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
          continuous_invFun :=
            (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous }
      exact (Units.mapContinuousMulEquiv e).continuous
    · rw [show (Units.posSubgroup ℝ : Set ℝˣ) =
          {x : ℝˣ | 0 < (x : ℝ)} by
        ext x
        exact Units.mem_posSubgroup (R := ℝ) x]
      exact isOpen_lt continuous_const Units.continuous_val
  · exact isOpen_univ

private theorem real_unit_pos
    (x : ℝˣ) (hx : 0 < (x : ℝ)) {n : ℕ} (hn : n ≠ 0) :
    ∃ y : ℝˣ, y ^ n = x := by
  let r : ℝ := (x : ℝ) ^ ((n : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos hx _
  let y : ℝˣ := Units.mk0 r hr.ne'
  refine ⟨y, ?_⟩
  ext
  exact Real.rpow_inv_natCast_pow hx.le hn

omit [NumberField K] in
private theorem pow_infinite_subgroup
    (v : InfinitePlace K) (x : v.1.Completionˣ)
    (hx : x ∈ infiniteBasicSubgroup (K := K) v)
    (n : ℕ) (hn : 0 < n) :
    ∃ y : v.1.Completionˣ, y ^ n = x := by
  classical
  by_cases hv : v.IsReal
  · rw [infiniteBasicSubgroup, dif_pos hv] at hx
    let e : v.1.Completionˣ ≃* ℝˣ :=
      Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMulEquiv
    have hex : 0 < (e x : ℝ) := hx
    obtain ⟨z, hz⟩ :=
      real_unit_pos (e x) hex hn.ne'
    refine ⟨e.symm z, ?_⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply, hz]
  · rw [infiniteBasicSubgroup, dif_neg hv] at hx
    have hvc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : v.1.Completionˣ ≃* ℂˣ :=
      Units.mapEquiv
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvc).toMulEquiv
    obtain ⟨z, hz⟩ :=
      Submission.CField.KNIndex.complex_monoid_surjective
        n hn (e x)
    refine ⟨e.symm z, ?_⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply]
    exact hz

private theorem continuous_monoid_ker
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (hf : IsOpen (f.ker : Set G)) :
    Continuous f := by
  classical
  have hsingle : ∀ y : H,
      IsOpen ((fun x : G ↦ f x) ⁻¹' ({y} : Set H)) := by
    intro y
    by_cases hy : ∃ a : G, f a = y
    · rcases hy with ⟨a, ha⟩
      have hfiber_eq :
          ((fun x : G ↦ f x) ⁻¹' ({y} : Set H)) =
            (fun x : G ↦ a⁻¹ * x) ⁻¹' (f.ker : Set G) := by
        ext x
        constructor
        · intro hx
          change f x = y at hx
          change f (a⁻¹ * x) = 1
          simp [ha, hx]
        · intro hx
          change f (a⁻¹ * x) = 1 at hx
          have hmul : y⁻¹ * f x = 1 := by
            calc
              y⁻¹ * f x = (f a)⁻¹ * f x := by rw [ha]
              _ = f (a⁻¹ * x) := by simp
              _ = 1 := hx
          exact (inv_mul_eq_one.mp hmul).symm
      have hshift : Continuous (fun x : G ↦ a⁻¹ * x) := by
        fun_prop
      rw [hfiber_eq]
      exact hf.preimage hshift
    · have hfiber_empty :
          ((fun x : G ↦ f x) ⁻¹' ({y} : Set H)) = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hy ⟨x, by simpa using hx⟩).elim
        · intro hx
          exact hx.elim
      rw [hfiber_empty]
      exact isOpen_empty
  rw [continuous_def]
  intro U _
  have hpre_eq :
      ((fun x : G ↦ f x) ⁻¹' U) =
        ⋃ y : U, ((fun x : G ↦ f x) ⁻¹' ({(y : H)} : Set H)) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.2 ⟨⟨f x, hx⟩, by simp⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨y, hy⟩
      have hxy : f x = (y : H) := by simpa using hy
      change f x ∈ U
      rw [hxy]
      exact y.property
  rw [hpre_eq]
  exact isOpen_iUnion (fun y : U ↦ hsingle (y : H))

private theorem local_hom_continuous
    (L : FASubext K)
    (P : HeightOneSpectrum (OK K)) :
    Continuous (finiteLocalHom L P) := by
  unfold finiteLocalHom
  exact artin_universe_continuous L P
    (finiteCompletion L P)

set_option maxHeartbeats 1000000 in
-- The archimedean completion algebra is inferred through a selected place.
set_option synthInstance.maxHeartbeats 100000 in
private theorem infinite_range_open
    (L : FASubext K) (v : InfinitePlace K) :
    IsOpen
      ((infiniteCompletionNorm (K := K) (L := L.1) v
        (infinitePlace L v)).range : Set v.1.Completionˣ) := by
  let w := infinitePlace L v
  let F := v.1.Completion
  let E := w.1.Completion
  letI : Algebra F E :=
    (completionLies v.1 w.1.1
      (infinite_lies_comap v w.1 w.2)).toAlgebra
  letI : Module.Finite F E :=
    infinite_completion_module (K := K) (L := L.1) v w
  apply Subgroup.isOpen_mono
    (H₁ := infiniteBasicSubgroup (K := K) v)
    (H₂ := (infiniteCompletionNorm (K := K) (L := L.1) v w).range)
  · intro x hx
    let n := Module.finrank F E
    have hn : 0 < n := Module.finrank_pos
    obtain ⟨y, hy⟩ :=
      pow_infinite_subgroup
        (K := K) v x hx n hn
    let z : Eˣ := Units.map (algebraMap F E) y
    refine ⟨z, ?_⟩
    apply Units.ext
    change Algebra.norm F (algebraMap F E (y : F)) = (x : F)
    rw [Algebra.norm_algebraMap]
    exact congrArg Units.val hy
  · exact infinite_basic_open (K := K) v

set_option maxHeartbeats 1000000 in
-- Kernel reduction unfolds the archimedean quotient equivalence.
private theorem infinite_local_ker
    (L : FASubext K) (v : InfinitePlace K) :
    (infiniteLocalHom L v).ker =
      (infiniteCompletionNorm (K := K) (L := L.1) v
        (infinitePlace L v)).range := by
  let w := infinitePlace L v
  let N := (infiniteCompletionNorm (K := K) (L := L.1) v w).range
  change (infiniteGlobalArtin v w).ker = N
  unfold infiniteGlobalArtin quotientEquivGlobal
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff x).1
    apply (infinitePlaceArtin v w).injective
    apply Subtype.ext
    simpa using hx
  · intro hx
    have hq : QuotientGroup.mk' N x = 1 :=
      (QuotientGroup.eq_one_iff x).2 hx
    change (absoluteValueDecomposition v.1 w.1.1).subtype
      ((infinitePlaceArtin v w)
        (QuotientGroup.mk' N x)) = 1
    rw [hq]
    simp only [map_one]

private theorem infinite_local_continuous
    (L : FASubext K) (v : InfinitePlace K) :
    Continuous (infiniteLocalHom L v) := by
  apply continuous_monoid_ker
  rw [infinite_local_ker]
  exact infinite_range_open L v

set_option maxHeartbeats 3000000 in
-- Continuity of the dependent finite restricted product needs extra reduction.
private theorem layerProduct_continuous
    (L : FASubext K) :
    Continuous (layerProduct L).artin := by
  let D := layerProduct L
  have hfinite : Continuous (D.finite.restrictedProductHom
      (fun P : HeightOneSpectrum (OK K) ↦
        IdeleUnitSubgroup (OK K) K P)) :=
    D.finite.continuous_restricted_hom _
      (local_hom_continuous L)
  have hinfinite : Continuous D.infiniteHom := by
    apply continuous_finsetProd Finset.univ
    intro v _
    exact (infinite_local_continuous L v).comp
      ((continuous_apply v).comp ContinuousMulEquiv.piUnits.continuous)
  simpa only [D, layerProduct,
    IAProduc.artin] using
    (hinfinite.comp continuous_fst).mul (hfinite.comp continuous_snd)

private theorem continuous_restricted_control
    {I : Type u} {H : I → Type u} [∀ i, CommGroup (H i)]
    (U : ∀ i, Subgroup (H i))
    {A : Type u} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [∀ i, TopologicalSpace (H i)]
    (f : (Πʳ i, [H i, U i]) →* A) (hf : Continuous f) :
    ∃ J : Finset I, ∀ x : ∀ i, U i,
      (∀ i ∈ J, x i = 1) →
        f (RestrictedProduct.structureMap H
          (fun i => (U i : Set (H i))) cofinite x) = 1 := by
  let includeUnits : (∀ i, U i) →* (Πʳ i, [H i, U i]) :=
    { toFun := RestrictedProduct.structureMap H
        (fun i => (U i : Set (H i))) cofinite
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let h : (∀ i, U i) →* A := f.comp includeUnits
  have hh : Continuous h :=
    hf.comp RestrictedProduct.isEmbedding_structureMap.continuous
  have hopen : IsOpen {x : ∀ i, U i | h x = 1} :=
    (isOpen_discrete {1}).preimage hh
  have hone : (1 : ∀ i, U i) ∈ {x : ∀ i, U i | h x = 1} :=
    map_one h
  obtain ⟨J, V, hV, hsub⟩ := (isOpen_pi_iff.mp hopen) 1 hone
  refine ⟨J, fun x hx => ?_⟩
  change f (includeUnits x) = 1
  apply hsub
  intro i hi
  rw [hx i (Finset.mem_coe.mp hi)]
  exact (hV i (Finset.mem_coe.mpr (Finset.mem_coe.mp hi))).2

private theorem restricted_family_continuous
    {I : Type u} {H : I → Type u} [∀ i, CommGroup (H i)]
    (U : ∀ i, Subgroup (H i))
    {A : Type u} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [∀ i, TopologicalSpace (H i)] [DecidableEq I]
    (f : (Πʳ i, [H i, U i]) →* A) (hf : Continuous f) :
    ∃ D : RLFam (A := A) U,
      D.restrictedProductHom U = f ∧
        ∀ i x, D.localHom i x = f (RestrictedProduct.mulSingle U i x) := by
  classical
  obtain ⟨J, hJ⟩ :=
    continuous_restricted_control U f hf
  let localHom : ∀ i, H i →* A := fun i =>
    f.comp
      { toFun := RestrictedProduct.mulSingle U i
        map_one' := RestrictedProduct.mulSingle_one U i
        map_mul' := RestrictedProduct.mulSingle_mul U i }
  have hlocalOutside (i : I) (hiJ : i ∉ J)
      (x : H i) (hx : x ∈ U i) : localHom i x = 1 := by
    let xu : U i := ⟨x, hx⟩
    let z : ∀ j, U j := Pi.mulSingle i xu
    have hzJ : ∀ j ∈ J, z j = 1 := by
      intro j hj
      change (Pi.mulSingle i xu : ∀ k, U k) j = 1
      rw [Pi.mulSingle_eq_of_ne]
      exact fun hji => hiJ (hji ▸ hj)
    have hz := hJ z hzJ
    change f (RestrictedProduct.mulSingle U i x) = 1
    have hzsingle : RestrictedProduct.structureMap H
        (fun j => (U j : Set (H j))) cofinite z =
        RestrictedProduct.mulSingle U i x := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [z, xu]
      · simp [z, xu, hji]
    rwa [hzsingle] at hz
  have heventually : ∀ᶠ i in cofinite,
      ∀ x : H i, x ∈ U i → localHom i x = 1 := by
    filter_upwards [J.finite_toSet.compl_mem_cofinite] with i hiJ
    exact hlocalOutside i (by simpa using hiJ)
  let D : RLFam (A := A) U :=
    { localHom := localHom
      eventually_units := heventually }
  refine ⟨D, ?_, fun _ _ => rfl⟩
  apply MonoidHom.ext
  intro x
  let bad : Set I := {i | x i ∉ U i}
  have hbad : bad.Finite := by
    simpa [bad] using (mem_cofinite.mp x.2)
  let B : Finset I := hbad.toFinset
  let T : Finset I := J ∪ B
  let tail : ∀ i, U i := fun i =>
    if hi : i ∈ T then 1 else
      ⟨x i, by
        have hiB : i ∉ B := fun h => hi (Finset.mem_union_right J h)
        have hibad : i ∉ bad := by simpa [B] using hiB
        simpa [bad] using hibad⟩
  have htailJ : ∀ i ∈ J, tail i = 1 := by
    intro i hi
    simp [tail, T, hi]
  have htail : f (RestrictedProduct.structureMap H
      (fun i => (U i : Set (H i))) cofinite tail) = 1 := hJ tail htailJ
  have hDtail : D.restrictedProductHom U
      (RestrictedProduct.structureMap H
        (fun i => (U i : Set (H i))) cofinite tail) = 1 := by
    change (∏ᶠ i, localHom i (tail i)) = 1
    apply finprod_eq_one_of_forall_eq_one
    intro i
    by_cases hi : i ∈ J
    · rw [htailJ i hi]
      exact map_one (localHom i)
    · exact hlocalOutside i hi (tail i) (tail i).2
  have hprod (i : I) :
      (∏ j ∈ T, RestrictedProduct.mulSingle U j (x j)) i =
        if i ∈ T then x i else 1 := by
    change RestrictedProduct.evalMonoidHom H i
      (∏ j ∈ T, RestrictedProduct.mulSingle U j (x j)) = _
    rw [map_prod]
    by_cases hi : i ∈ T
    · rw [if_pos hi, Finset.prod_eq_single i]
      · change RestrictedProduct.mulSingle U i (x i) i = x i
        exact RestrictedProduct.mulSingle_eq_same U i (x i)
      · intro j hj hji
        exact RestrictedProduct.mulSingle_eq_of_ne U (x j) hji.symm
      · intro hnot
        exact (hnot hi).elim
    · rw [if_neg hi]
      apply Finset.prod_eq_one
      intro j hj
      exact RestrictedProduct.mulSingle_eq_of_ne U (x j)
        (fun hji => hi (hji ▸ hj))
  have hxdecomp :
      x = (∏ i ∈ T, RestrictedProduct.mulSingle U i (x i)) *
        RestrictedProduct.structureMap H
          (fun i => (U i : Set (H i))) cofinite tail := by
    ext i
    change x i =
      (∏ j ∈ T, RestrictedProduct.mulSingle U j (x j)) i *
        (tail i : H i)
    by_cases hi : i ∈ T
    · rw [hprod i, if_pos hi]
      simp [tail, hi]
    · rw [hprod i, if_neg hi]
      simp [tail, hi]
  change D.restrictedProductHom U x = f x
  rw [hxdecomp, map_mul, map_mul, htail, hDtail, mul_one, map_prod, map_prod]
  simp only [mul_one]
  apply Finset.prod_congr rfl
  intro i _
  exact D.restricted_product_single U i (x i)

private theorem artin_continuous
    {A : Type u} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    (f : IdeleGroup (OK K) K →* A) (hf : Continuous f) :
    ∃ D : IAProduc K A,
      D.artin = f ∧
      (∀ P x, D.finite.localHom P x =
        f (finitePlaceEmbedding (OK K) K P x)) ∧
      ∀ v x, D.infinite v x =
        f (infinitePlaceEmbedding (OK K) K v x) := by
  classical
  let finiteInclusion : FiniteIdeles (OK K) K →* IdeleGroup (OK K) K :=
    { toFun := fun x => (1, x)
      map_one' := rfl
      map_mul' := by
        intro x y
        apply Prod.ext
        · change (1 : (InfiniteAdeleRing K)ˣ) = 1 * 1
          simp
        · rfl }
  let ffinite : FiniteIdeles (OK K) K →* A := f.comp finiteInclusion
  have hffinite : Continuous ffinite :=
    hf.comp (continuous_const.prodMk continuous_id)
  letI : DecidableEq (HeightOneSpectrum (OK K)) := Classical.decEq _
  obtain ⟨finite, hfinite, hfinite_coord⟩ :=
    restricted_family_continuous
      (fun P : HeightOneSpectrum (OK K) =>
        IdeleUnitSubgroup (OK K) K P) ffinite hffinite
  let D : IAProduc K A :=
    { finite := finite
      infinite := fun v => f.comp (infinitePlaceEmbedding (OK K) K v) }
  refine ⟨D, ?_, ?_, fun _ _ => rfl⟩
  · apply MonoidHom.ext
    intro a
    rw [D.artin_apply]
    have hfin := DFunLike.congr_fun hfinite a.2
    change (∏ᶠ P, finite.localHom P (a.2.1 P)) = ffinite a.2 at hfin
    rw [hfin]
    have hinfinite :
        (∏ v : InfinitePlace K,
          f (infinitePlaceEmbedding (OK K) K v
            (MulEquiv.piUnits a.1 v))) = f (a.1, 1) := by
      have hidele :
          (∏ v : InfinitePlace K,
            infinitePlaceEmbedding (OK K) K v
              (MulEquiv.piUnits a.1 v)) = (a.1, 1) := by
        apply Prod.ext
        · change (MonoidHom.fst (InfiniteAdeleRing K)ˣ
              (FiniteIdeles (OK K) K))
              (∏ v : InfinitePlace K,
                infinitePlaceEmbedding (OK K) K v
                  (MulEquiv.piUnits a.1 v)) = a.1
          rw [map_prod]
          change (∏ v : InfinitePlace K,
              MulEquiv.piUnits.symm
                (Pi.mulSingle v (MulEquiv.piUnits a.1 v))) = a.1
          rw [← map_prod, Finset.univ_prod_mulSingle]
          exact MulEquiv.symm_apply_apply _ _
        · change (MonoidHom.snd (InfiniteAdeleRing K)ˣ
              (FiniteIdeles (OK K) K))
              (∏ v : InfinitePlace K,
                infinitePlaceEmbedding (OK K) K v
                  (MulEquiv.piUnits a.1 v)) = 1
          rw [map_prod]
          change (∏ _v : InfinitePlace K,
              (1 : FiniteIdeles (OK K) K)) = 1
          simp
      calc
        _ = f (∏ v : InfinitePlace K,
            infinitePlaceEmbedding (OK K) K v
              (MulEquiv.piUnits a.1 v)) := (map_prod f _ Finset.univ).symm
        _ = f (a.1, 1) := congrArg f hidele
    change (∏ v : InfinitePlace K,
        f (infinitePlaceEmbedding (OK K) K v
          (MulEquiv.piUnits a.1 v))) * f (1, a.2) = f a
    rw [hinfinite, ← map_mul]
    apply congrArg f
    apply Prod.ext
    · change a.1 * 1 = a.1
      exact mul_one _
    · change 1 * a.2 = a.2
      exact one_mul _
  · intro P x
    change finite.localHom P x = f _
    rw [hfinite_coord P x]
    rfl

private theorem local_hom_unique
    (L : FASubext K)
    (P : HeightOneSpectrum (OK K))
    (Q : UpperPrimeFactors (K := K) (L := L.1) P)
    (f : (P.adicCompletion K)ˣ →* Gal(L.1/K))
    (hf : LayerLocalArtin L P Q f) :
    f = finiteLocalHom L P := by
  let wQ := (Submission.CField.NIndex.placesAboveFactors
    (K := K) (L := L.1) P).symm Q
  have hcanonical : LayerLocalArtin L P Q
      (finiteLocalHom L P) := by
    rw [show finiteLocalHom L P =
        adicArtinUniverse K L.1 P wQ by
      exact finiteIndependence P _ wQ]
    exact finiteNormalization L P Q
  rcases hf with ⟨wf, hwf, hwfq, ef, _, hfall⟩
  rcases hcanonical with ⟨wc, hwc, hwcq, ec, _, hcall⟩
  exact (hfall wQ).trans (hcall wQ).symm

private theorem infinite_local_unique
    (L : FASubext K)
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L.1) v)
    (f : v.1.Completionˣ →* Gal(L.1/K))
    (hf : InfiniteLayerArtin L v w f) :
    f = infiniteLocalHom L v := by
  rw [infinite_global_artin
      L v w f hf]
  exact infinite_artin_independent v w _

private theorem layerProduct_unique
    (L : FASubext K)
    (f : IdeleGroup (OK K) K →* Gal(L.1/K))
    (hf : Continuous f)
    (hlocal : LayerArtinProduct L f) :
    f = (layerProduct L).artin := by
  obtain ⟨D, hD, hfinite, hinfinite⟩ :=
    artin_continuous f hf
  rw [← hD]
  apply MonoidHom.ext
  intro a
  rw [D.artin_apply, (layerProduct L).artin_apply]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    let w := infinitePlace L v
    obtain ⟨phi, hphi, hcompat⟩ := hlocal.2 v w
    calc
      D.infinite v (MulEquiv.piUnits a.1 v) =
          f (infinitePlaceEmbedding (OK K) K v
            (MulEquiv.piUnits a.1 v)) := hinfinite v _
      _ = phi (MulEquiv.piUnits a.1 v) := hcompat _
      _ = infiniteLocalHom L v
          (MulEquiv.piUnits a.1 v) := by
            rw [infinite_local_unique L v w phi hphi]
  · apply finprod_congr
    intro P
    let w := finiteCompletion L P
    let Q := Submission.CField.NIndex.placeUpperFactor
      (K := K) (L := L.1) P w
    obtain ⟨phi, hphi, hcompat⟩ := hlocal.1 P Q
    calc
      D.finite.localHom P (a.2.1 P) =
          f (finitePlaceEmbedding (OK K) K P (a.2.1 P)) := hfinite P _
      _ = phi (a.2.1 P) := hcompat _
      _ = finiteLocalHom L P (a.2.1 P) := by
        rw [local_hom_unique L P Q phi hphi]

private theorem layerProduct_restriction
    (M L : FASubext K)
    (hML : (M.1 : IntermediateField K (SeparableClosure K)) ≤ L.1) :
    (galoisRestrictionHom K hML).comp
        (layerProduct L).artin =
      (layerProduct M).artin := by
  let r : Gal(L.1/K) →* Gal(M.1/K) := galoisRestrictionHom K hML
  let Dₗ := layerProduct L
  let Dₘ := layerProduct M
  apply MonoidHom.ext
  intro a
  change r (Dₗ.artin a) = Dₘ.artin a
  rw [Dₗ.artin_apply, Dₘ.artin_apply, map_mul]
  have hinfinite :
      r (∏ v : InfinitePlace K,
          Dₗ.infinite v (MulEquiv.piUnits a.1 v)) =
        ∏ v : InfinitePlace K,
          Dₘ.infinite v (MulEquiv.piUnits a.1 v) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro v _
    exact DFunLike.congr_fun
      (infinite_local_restriction M L hML v)
      (MulEquiv.piUnits a.1 v)
  have hfiniteSupport := Dₗ.finite.finite_mulSupport
    (fun P : HeightOneSpectrum (OK K) =>
      IdeleUnitSubgroup (OK K) K P) a.2
  have hfinite :
      r (∏ᶠ P : HeightOneSpectrum (OK K),
          Dₗ.finite.localHom P (a.2.1 P)) =
        ∏ᶠ P : HeightOneSpectrum (OK K),
          Dₘ.finite.localHom P (a.2.1 P) := by
    calc
      _ = ∏ᶠ P : HeightOneSpectrum (OK K),
          r (Dₗ.finite.localHom P (a.2.1 P)) :=
        r.map_finprod hfiniteSupport
      _ = _ := by
        apply finprod_congr
        intro P
        exact DFunLike.congr_fun
          (local_hom_restriction M L hML P) (a.2.1 P)
  rw [hinfinite, hfinite]

/-! ### Inverse-limit assembly of the finite products -/

private structure CFam (K : Type u)
    [Field K] [NumberField K] where
  hom (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    IdeleGroup (OK K) K →* Gal(E/K)
  compatible : ∀ {E F :
      (FiniteGaloisIntermediateField K
        (maximalAbelianIntermediate K))ᵒᵖ}
      (f : E ⟶ F) (a : IdeleGroup (OK K) K),
    (finGaloisGroupFunctor K (maximalAbelianIntermediate K)).map f
        (hom E.unop a) = hom F.unop a

namespace CFam

variable (A : CFam K)

noncomputable def toLimit :
    IdeleGroup (OK K) K →*
      limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K
        (maximalAbelianIntermediate K)) where
  toFun a :=
    ⟨fun E => A.hom E.unop a, by
      intro E F f
      exact A.compatible f a⟩
  map_one' := by
    apply Subtype.ext
    funext E
    exact map_one (A.hom E.unop)
  map_mul' a b := by
    apply Subtype.ext
    funext E
    exact map_mul (A.hom E.unop) a b

noncomputable def maximalAbelian :
    IdeleGroup (OK K) K →* Gal(maximalAbelianIntermediate K/K) :=
  (InfiniteGalois.mulEquivToLimit K
      (maximalAbelianIntermediate K)).symm.toMonoidHom.comp A.toLimit

noncomputable def assemble :
    IdeleGroup (OK K) K →* AbsoluteAbelianGalois K :=
  (abelianGaloisMaximal K).symm.toMonoidHom.comp
    A.maximalAbelian

@[simp]
theorem proj_maximal_abelian
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K))
    (a : IdeleGroup (OK K) K) :
    InfiniteGalois.proj E
        (InfiniteGalois.algEquivToLimit K
          (maximalAbelianIntermediate K)
          (A.maximalAbelian a)) =
      A.hom E a := by
  change InfiniteGalois.proj E
      ((InfiniteGalois.mulEquivToLimit K
        (maximalAbelianIntermediate K))
        ((InfiniteGalois.mulEquivToLimit K
          (maximalAbelianIntermediate K)).symm (A.toLimit a))) = _
  exact congrArg (InfiniteGalois.proj E)
    ((InfiniteGalois.mulEquivToLimit K
      (maximalAbelianIntermediate K)).apply_symm_apply (A.toLimit a))

@[simp]
theorem abelian_maximal_assemble
    (a : IdeleGroup (OK K) K) :
    abelianGaloisMaximal K (A.assemble a) =
      A.maximalAbelian a := by
  exact (abelianGaloisMaximal K).apply_symm_apply _

@[simp]
theorem proj_assemble
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K))
    (a : IdeleGroup (OK K) K) :
    InfiniteGalois.proj E
        (InfiniteGalois.algEquivToLimit K
          (maximalAbelianIntermediate K)
          (abelianGaloisMaximal K (A.assemble a))) =
      A.hom E a := by
  rw [A.abelian_maximal_assemble,
    A.proj_maximal_abelian]

theorem abelian_restriction_assemble
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K))
    (a : IdeleGroup (OK K) K) :
    localAbelianRestriction (maximalAbelianSubextension K E)
        (A.assemble a) =
      (maximalAbelianLevel K E).autCongr (A.hom E a) := by
  rw [abelian_restriction_subextension]
  exact congrArg (maximalAbelianLevel K E).autCongr
    (A.proj_assemble E a)

theorem assemble_point_unique
    (a : IdeleGroup (OK K) K)
    (sigma : AbsoluteAbelianGalois K)
    (hsigma : ∀ E : FiniteGaloisIntermediateField K
        (maximalAbelianIntermediate K),
      localAbelianRestriction (maximalAbelianSubextension K E) sigma =
        (maximalAbelianLevel K E).autCongr (A.hom E a)) :
    sigma = A.assemble a := by
  apply (abelianGaloisMaximal K).injective
  apply (InfiniteGalois.mulEquivToLimit K
    (maximalAbelianIntermediate K)).injective
  apply Subtype.ext
  funext E
  have hs := hsigma E.unop
  rw [abelian_restriction_subextension] at hs
  change InfiniteGalois.proj E.unop
      (InfiniteGalois.algEquivToLimit K
        (maximalAbelianIntermediate K)
        (abelianGaloisMaximal K sigma)) =
    InfiniteGalois.proj E.unop
      (InfiniteGalois.algEquivToLimit K
        (maximalAbelianIntermediate K)
        (abelianGaloisMaximal K (A.assemble a)))
  have hs' :=
    (maximalAbelianLevel K E.unop).autCongr.injective hs
  change InfiniteGalois.proj E.unop
      (InfiniteGalois.algEquivToLimit K
        (maximalAbelianIntermediate K)
        (abelianGaloisMaximal K sigma)) =
    A.hom E.unop a at hs'
  rw [hs', A.proj_assemble]

end CFam

noncomputable def compatibleFamily :
    CFam K where
  hom E :=
    (maximalAbelianLevel K E).autCongr.symm.toMonoidHom.comp
      (layerProduct
        (maximalAbelianSubextension K E)).artin
  compatible := by
    intro E F f a
    let hFE : F.unop ≤ E.unop := CategoryTheory.leOfHom f.unop
    have hf : f = (CategoryTheory.homOfLE hFE).op := Subsingleton.elim _ _
    rw [hf]
    change galoisRestrictionHom K hFE
        ((maximalAbelianLevel K E.unop).autCongr.symm
          ((layerProduct
            (maximalAbelianSubextension K E.unop)).artin a)) =
      (maximalAbelianLevel K F.unop).autCongr.symm
        ((layerProduct
          (maximalAbelianSubextension K F.unop)).artin a)
    apply (maximalAbelianLevel K F.unop).autCongr.injective
    have hnat := DFunLike.congr_fun
      (maximal_restriction_natural
        (K := K) hFE)
      ((maximalAbelianLevel K E.unop).autCongr.symm
        ((layerProduct
          (maximalAbelianSubextension K E.unop)).artin a))
    change galoisRestrictionHom K
        (maximal_subextension_mono hFE)
        ((maximalAbelianLevel K E.unop).autCongr
          ((maximalAbelianLevel K E.unop).autCongr.symm
            ((layerProduct
              (maximalAbelianSubextension K E.unop)).artin a))) =
      (maximalAbelianLevel K F.unop).autCongr
        (galoisRestrictionHom K hFE
          ((maximalAbelianLevel K E.unop).autCongr.symm
            ((layerProduct
              (maximalAbelianSubextension K E.unop)).artin a))) at hnat
    rw [MulEquiv.apply_symm_apply] at hnat
    rw [← hnat, MulEquiv.apply_symm_apply]
    exact DFunLike.congr_fun
      (layerProduct_restriction
        (maximalAbelianSubextension K F.unop)
        (maximalAbelianSubextension K E.unop)
        (maximal_subextension_mono hFE)) a

private theorem compatibleFamily_restriction
    (L : FASubext K) (a : IdeleGroup (OK K) K) :
    localAbelianRestriction L
        ((compatibleFamily (K := K)).assemble a) =
      (layerProduct L).artin a := by
  obtain ⟨E, hE⟩ := maximal_abelian_subextension K L
  subst L
  rw [(compatibleFamily (K := K)).abelian_restriction_assemble E a]
  exact (maximalAbelianLevel K E).autCongr.apply_symm_apply _

set_option maxHeartbeats 1000000 in
-- Expanding the compatible family at an arbitrary finite lift is reduction-heavy.
private theorem pointwiseInverseLimit
    (a : IdeleGroup (OK K) K) :
    ∃! sigma : AbsoluteAbelianGalois K,
      ∀ L : FASubext K,
        localAbelianRestriction L sigma =
          (layerProduct L).artin a := by
  let A := compatibleFamily (K := K)
  refine ⟨A.assemble a,
    (fun L ↦ compatibleFamily_restriction L a),
    fun sigma hsigma => ?_⟩
  apply A.assemble_point_unique a sigma
  intro E
  let L := maximalAbelianSubextension K E
  have hs := hsigma L
  change localAbelianRestriction L sigma =
    (maximalAbelianLevel K E).autCongr (A.hom E a)
  rw [hs]
  change (layerProduct L).artin a =
    (maximalAbelianLevel K E).autCongr
      ((maximalAbelianLevel K E).autCongr.symm
        ((layerProduct L).artin a))
  exact (maximalAbelianLevel K E).autCongr.apply_symm_apply _ |>.symm

/-- The concrete finite local Artin products, with continuity, uniqueness,
and their inverse-limit compatibility packaged for Proposition V.5.2. -/
noncomputable def layerArtinSystem :
    LASystem (K := K) where
  layerMap L := (layerProduct L).artin
  layer_local_product := layer_product_local
  layer_unique := layerProduct_unique
  layer_continuous := layerProduct_continuous
  pointwise_inverseLimit := pointwiseInverseLimit

/-- **Proposition V.5.2.** There is a unique continuous global Artin
homomorphism whose finite restrictions agree with all local Artin maps. -/
theorem global_artin_unique : GlobalArtinProposition (K := K) :=
  restriction_topology_system K
    (layerArtinSystem (K := K))

end

end Submission.CField.Recip
