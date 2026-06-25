import Submission.ClassField.BrauerLocalization.RestrictedProductZero
import Submission.ClassField.UnramifiedCohom.NormInteger
import Submission.ClassField.HasseNorm.UnramifiedH2

/-!
# Tate degree minus one for the restricted idèle product

This file supplies the denominator in Proposition VII.2.7.  The
representation-level decompositions used for Tate degree zero work in
degree one as well.  The only extra arithmetic input is Proposition III.1.1:
the first cohomology of the integer units in an unramified local extension
vanishes.
-/

namespace Submission.CField.BLoc

open CategoryTheory CategoryTheory.Limits Representation
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.COps
open Submission.CField.Shifting
open Submission.CField.UCohom
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HNorm
open groupCohomology

attribute [local instance] Units.mulDistribMulActionRight

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance negOneNumberFieldPlaceDecidableEq :
    DecidableEq (NumberFieldPlace K) :=
  Classical.decEq _

local instance negOneFinitePlaceNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance negOneFinitePlaceCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

local instance negOneCompletionPlacesAboveFinite
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Finite (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  absolute_extensions_separable (FinitePlace.mk P).val

local instance negOneCompletionPlacesAboveNonempty
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nonempty (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  absolute_value_extension
    (K := K) (L := L) (FinitePlace.mk P).val

local instance negOneCompletionPlacesAbovePretransitive
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  completion_above_pretransitive P

local instance negOneCompletionPlaceLiesOverFact
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :
    Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩

local instance negOneFinitePlaceCompletionNontriviallyNormed
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NontriviallyNormedField (FinitePlace.mk P).val.Completion :=
  placeNontriviallyNormed P

local instance negOneCompletionPlaceNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Fact w.1.IsNontrivial :=
  ⟨absolute_extension_nontrivial (FinitePlace.mk P).val w⟩

local instance negOneCompletionPlaceUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    IsUltrametricDist w.1.Completion :=
  absoluteUltrametricDist w.1
    (absolute_extension_nonarchimedean (FinitePlace.mk P).val w)

/-! ## Equivariant transport in degree one -/

/-- Simultaneously relabel the acting group and the multiplicative
coefficient group. -/
noncomputable def ulift1Equivariant
    {G H M N : Type u} [Group G] [Group H]
    [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction H N]
    (eG : G ≃* H) (eM : M ≃* N)
    (heq : ∀ g : G, ∀ x : M, eM (g • x) = eG g • eM x) :
    H1 (uliftMulRepresentation (G := G) (M := M)) ≃+
      H1 (uliftMulRepresentation (G := H) (M := N)) := by
  let eRep : uliftMulRepresentation (G := G) (M := M) ≅
      Rep.res eG.toMonoidHom
        (uliftMulRepresentation (G := H) (M := N)) := by
    apply Rep.mkIso
    refine
      { toLinearEquiv :=
          { toEquiv := eM.toAdditive.toEquiv
            map_add' := eM.toAdditive.map_add
            map_smul' := fun r x ↦ map_zsmul eM.toAdditive r.down x }
        isIntertwining' := ?_ }
    intro g
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    exact heq g x.toMul
  exact (((groupCohomology.functor (ULift.{u} ℤ) G 1).mapIso eRep) ≪≫
    (cohomologyMulIso eG
      (uliftMulRepresentation (G := H) (M := N)) 1).symm).toLinearEquiv.toAddEquiv

private theorem isMulCocycle₁_of_mem_cocycles₁_ulift
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (f : G → Additive M)
    (hf : f ∈ cocycles₁ (uliftMulRepresentation (G := G) (M := M))) :
    IsMulCocycle₁ (Additive.toMul ∘ f) :=
  (mem_cocycles₁_iff
    (A := uliftMulRepresentation (G := G) (M := M)) f).1 hf

private def coboundariesMulCoboundary₁_ulift
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    {f : G → M} (hf : IsMulCoboundary₁ f) :
    coboundaries₁ (uliftMulRepresentation (G := G) (M := M)) :=
  ⟨Additive.ofMul ∘ f, hf.choose, funext hf.choose_spec⟩

private abbrev valuationInteger
    (F : Type u) [NontriviallyNormedField F] [ValuativeRel F] :=
  Valuation.integer (ValuativeRel.valuation F)

set_option maxHeartbeats 4000000 in
-- The degree-one integral-model argument expands the full unramified Galois
-- action and its unit-valued cocycle calculation.
set_option synthInstance.maxHeartbeats 500000 in
/-- Universe-polymorphic degree-one part of Proposition III.1.1, stated
for an arbitrary finite formally unramified integral model. -/
theorem integral_model_subsingleton
    (F E U : Type u)
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E]
    [CommRing U] [Algebra (valuationInteger F) U]
    [Algebra U E]
    [IsScalarTower (valuationInteger F) U E]
    [IsIntegralClosure U (valuationInteger F) E]
    [Module.Finite (valuationInteger F) U]
    [Algebra.FormallyUnramified (valuationInteger F) U]
    [IsLocalRing U]
    [IsLocalHom (algebraMap (valuationInteger F) U)]
    [MulSemiringAction Gal(E/F) U] [SMulDistribClass Gal(E/F) U E] :
    Subsingleton
      (H1 (uliftMulRepresentation (G := Gal(E/F)) (M := Uˣ))) := by
  letI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField F E
  letI : NormedAlgebra F E := spectralNorm.normedAlgebra F E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra F
  letI : ValuativeRel E := FLExt.valuativeRel F E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField F E
  letI : (NormedField.valuation (K := F)).HasExtension
      (NormedField.valuation (K := E)) := spectralValuationExtension F E
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : Algebra (valuationInteger F) N :=
    valuativeSpectralAlgebra F E
  letI : IsScalarTower (valuationInteger F) N E :=
    valuativeSpectralTower F E
  let eNorm := valuativeSpectralInteger F E U
  let eOut := valuativeIntegerNorm E
  let eRing : U ≃+* Valuation.integer (ValuativeRel.valuation E) :=
    eNorm.toRingEquiv.trans eOut.symm
  have eRing_coe (x : U) :
      ((eRing x : Valuation.integer (ValuativeRel.valuation E)) : E) =
        algebraMap U E x := by
    change ((eOut.symm (eNorm x) :
      Valuation.integer (ValuativeRel.valuation E)) : E) =
        algebraMap U E x
    change ((eNorm x : N) : E) = algebraMap U E x
    exact valuative_spectral_integer F E U x
  constructor
  intro a b
  suffices hz : ∀ z : H1
      (uliftMulRepresentation (G := Gal(E/F)) (M := Uˣ)), z = 0 by
    exact (hz a).trans (hz b).symm
  intro z
  exact H1_induction_on z fun x ↦ (H1π_eq_zero_iff _).2 <| by
    let fU : Gal(E/F) → Uˣ := Additive.toMul ∘ x
    have hfU : IsMulCocycle₁ fU :=
      isMulCocycle₁_of_mem_cocycles₁_ulift _ x.2
    let j : Uˣ →* Eˣ := Units.map (algebraMap U E).toMonoidHom
    let fE : Gal(E/F) → Eˣ := fun g ↦ j (fU g)
    have hfE : IsMulCocycle₁ fE := by
      intro g h
      dsimp [fE]
      rw [hfU g h, map_mul]
      congr 1
      apply Units.ext
      exact algebraMap.coe_smul' (B := U) (C := E) g (fU h)
    obtain ⟨beta, hbeta⟩ :=
      isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units fE hfE
    obtain ⟨tAdd, ht⟩ := local_order_surjective F
      (-localUnitOrder E (Additive.ofMul beta))
    let t : Fˣ := tAdd.toMul
    let q : Eˣ := Units.map (algebraMap F E).toMonoidHom t
    let alpha : Eˣ := q * beta
    have halphaOrder :
        localUnitOrder E (Additive.ofMul alpha) = 0 := by
      change localUnitOrder E (Additive.ofMul (q * beta)) = 0
      rw [show Additive.ofMul (q * beta) =
            Additive.ofMul q + Additive.ofMul beta by rfl,
        map_add,
        show localUnitOrder E (Additive.ofMul q) =
            localUnitOrder F (Additive.ofMul t) by
          exact algebra_integral_model
            F E U t]
      change localUnitOrder F tAdd +
          localUnitOrder E (Additive.ofMul beta) = 0
      rw [ht]
      exact neg_add_cancel _
    have halphaUnit : alpha ∈ localUnitSubgroup E := by
      rw [local_subgroup]
      apply le_antisymm
      · have hle : localUnitOrder E (0 : Additive Eˣ) ≤
            localUnitOrder E (Additive.ofMul alpha) := by
          simp [halphaOrder]
        have h := (local_order_valuation E
          (1 : Eˣ) alpha).1 hle
        simpa using h
      · have hle : localUnitOrder E (Additive.ofMul alpha) ≤
            localUnitOrder E (0 : Additive Eˣ) := by
          simp [halphaOrder]
        have h := (local_order_valuation E
          alpha (1 : Eˣ)).1 hle
        simpa using h
    let epsilonSpectral :
        (Valuation.integer (ValuativeRel.valuation E))ˣ :=
      localInteger E ⟨alpha, halphaUnit⟩
    let epsilon : Uˣ :=
      Units.map eRing.symm.toMonoidHom epsilonSpectral
    have hj_epsilon : j epsilon = alpha := by
      apply Units.ext
      change algebraMap U E (eRing.symm epsilonSpectral.val) = (alpha : E)
      rw [← eRing_coe]
      rw [eRing.apply_symm_apply]
      rfl
    refine (coboundariesMulCoboundary₁_ulift ?_).2
    refine ⟨epsilon, fun g ↦ ?_⟩
    have hj : Function.Injective j := by
      intro p q hpq
      apply Units.ext
      apply IsIntegralClosure.algebraMap_injective U
        (valuationInteger F) E
      exact congrArg Units.val hpq
    have hj_smul (g : Gal(E/F)) (v : Uˣ) :
        j (g • v) = g • j v := by
      apply Units.ext
      exact algebraMap.coe_smul' (B := U) (C := E) g (v : U)
    apply hj
    rw [map_div, hj_smul, hj_epsilon]
    have htfix : g • q = q := by
      apply Units.ext
      simp [q]
    have hgbeta : g • beta = fE g * beta := by
      calc
        g • beta = (g • beta / beta) * beta := by simp
        _ = fE g * beta := by rw [hbeta g]
    have halpha_smul : g • alpha = fE g * alpha := by
      calc
        g • alpha = g • (q * beta) := rfl
        _ = (g • q) * (g • beta) := by
          simp only [AlgEquiv.smul_units_def, map_mul]
        _ = q * (fE g * beta) := by rw [htfix, hgbeta]
        _ = fE g * (q * beta) := by ac_rfl
        _ = fE g * alpha := rfl
    rw [halpha_smul]
    simp only [mul_div_cancel_right]
    rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- The completion integral model and its transported Galois action are instance-heavy.
set_option maxHeartbeats 6000000 in
/-- At an unramified finite prime, the first cohomology of the units in the
completed valuation ring is trivial. -/
theorem integer_subsingleton_unramified
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal) :
    let v := (FinitePlace.mk P).val
    let w := aboveCompletionPlace (K := K) (L := L) P Q
    let F := v.Completion
    let E := w.1.Completion
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : NontriviallyNormedField F :=
      placeNontriviallyNormed P
    letI : IsUltrametricDist F := placeUltrametricDist P
    letI : ValuativeRel F := placeValuativeRel P
    letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
    letI : IsNonarchimedeanLocalField F :=
      placeNonarchimedeanField P
    letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional F E :=
      Submission.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois F E := placeCompletionGalois v w
    letI : MulSemiringAction Gal(E/F) (completionIntegerRing w.1) :=
      integerRingAction
        (K := K) (L := L) P Q
    Subsingleton
      (H1 (uliftMulRepresentation (G := Gal(E/F))
        (M := (completionIntegerRing w.1)ˣ))) := by
  dsimp only
  let v := (FinitePlace.mk P).val
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  let F := v.Completion
  let E := w.1.Completion
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : Fact w.1.IsNontrivial := ⟨hw⟩
  letI : NontriviallyNormedField F :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist F := placeUltrametricDist P
  letI : IsUltrametricDist E :=
    absoluteUltrametricDist w.1 hwna
  letI : ValuativeRel F := placeValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    placeNonarchimedeanField P
  let A := Valuation.integer (ValuativeRel.valuation F)
  let A' := completionIntegerRing v
  let B := completionIntegerRing w.1
  letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
  let hFinite : FiniteDimensional F E :=
    Submission.NumberTheory.Milne.placeCompletionDimensional v w
  letI : FiniteDimensional F E := hFinite
  letI : IsGalois F E := placeCompletionGalois v w
  let hSeparable : Algebra.IsSeparable F E := IsGalois.to_isSeparable
  letI : Algebra A' B := completionIntegerLies v w.1 w.2
  let eA : A ≃+* A' := valuativeIntegerNorm F
  letI : Algebra A B :=
    ((algebraMap A' B).comp eA.toRingHom).toAlgebra
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra A E := Algebra.ofSubring A
  letI : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsDiscreteValuationRing A' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (centeredIntegerAdic v
        (absolute_value_nontrivial P)
        (fun x y ↦ (FinitePlace.mk P).add_le x y)).symm
  letI : Module.Finite A' B :=
    completion_integer_module v w.1 w.2 hFinite hSeparable
  letI : Module.Finite A B := by
    apply Module.Finite.of_equiv_equiv eA.symm (RingEquiv.refl B)
    ext x
    rfl
  have hcenter :
      nonarchimedeanHeightSpectrum w.1 hw hwna = Q.1 :=
    (upper_place_factor
        (K := K) (L := L) P w).symm.trans
      (above_place_center (K := K) (L := L) P Q)
  have hUnramifiedA' : Algebra.FormallyUnramified A' B := by
    have hQcenter : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K)
        (nonarchimedeanHeightSpectrum w.1 hw hwna).asIdeal :=
      hcenter.symm ▸ hQ
    exact completion_formally_unramified
      P w.1 w.2 hw hwna hQcenter hFinite hSeparable
  letI : Algebra.FormallyUnramified A' B := hUnramifiedA'
  letI : IsLocalHom (algebraMap A' B) :=
    completion_integer_lies v w.1 w.2
  letI : IsLocalHom eA.toRingHom :=
    IsLocalHom.of_surjective eA.toRingHom eA.surjective
  letI : IsLocalHom (algebraMap A B) := by
    change IsLocalHom ((algebraMap A' B).comp eA.toRingHom)
    infer_instance
  letI : Algebra.FormallyUnramified A B := by
    apply Algebra.FormallyUnramified.of_map_maximalIdeal
    calc
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
          ((IsLocalRing.maximalIdeal A).map eA.toRingHom).map
            (algebraMap A' B) := by rw [Ideal.map_map]; rfl
      _ = (IsLocalRing.maximalIdeal A').map (algebraMap A' B) := by
        congr 1
        exact IsLocalRing.map_ringEquiv_maximalIdeal eA
      _ = IsLocalRing.maximalIdeal B :=
        Algebra.FormallyUnramified.map_maximalIdeal
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  letI : IsFractionRing B E :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isFractionRing
  letI : IsIntegrallyClosed B :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isIntegrallyClosed
  letI : IsIntegralClosure B A E :=
    IsIntegralClosure.of_isIntegrallyClosed B A E
  letI : MulSemiringAction Gal(E/F) B :=
    integerRingAction
      (K := K) (L := L) P Q
  letI : SMulDistribClass Gal(E/F) B E := ⟨by
    intro g b x
    change g ((b : E) * x) = (g (b : E)) * g x
    exact map_mul g (b : E) x⟩
  exact integral_model_subsingleton F E B

/-! ## Degree-one versions of the existing decomposition maps -/

/-- Degree-one cohomology commutes with the arbitrary product of finite
stage orbit representations. -/
noncomputable def stage1Pi
    (S : Finset (NumberFieldPlace K)) :
    H1 (resizedStageRepresentation
      (K := K) (L := L) S) ≃+
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        H1 (stageOrbitRepresentation
          (K := K) (L := L) S P)) := by
  let A := fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
    stageOrbitRepresentation (K := K) (L := L) S P
  let e₁ := ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 1).mapIso
    (stageIsoCategorical
      (K := K) (L := L) S)).toLinearEquiv.toAddEquiv
  let e₂ := (groupProductIso
    (ULift.{u} ℤ) Gal(L/K) A 1).toLinearEquiv.toAddEquiv
  let e₃ := moduleCatPi (fun P ↦ H1 (A P))
  exact e₁.trans (e₂.trans e₃)

/-- At an exceptional finite prime, the degree-one stage factor is the
unrestricted completion orbit. -/
noncomputable def resizedStageFull
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    H1 (stageOrbitRepresentation
      (K := K) (L := L) S P) ≃+
      H1 (resizedAboveRepresentation
        (K := K) (L := L) P) :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 1).mapIso
    (stageIsoFull
      (K := K) (L := L) S P hP)).toLinearEquiv.toAddEquiv

/-- At a nonexceptional finite prime, the degree-one stage factor is the
product of the upper integer-unit groups. -/
noncomputable def resizedStageUnits
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    H1 (stageOrbitRepresentation
      (K := K) (L := L) S P) ≃+
      H1 (resizedPrimesRepresentation
        (K := K) (L := L) P) :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 1).mapIso
    (resizedStageIso
      (K := K) (L := L) S P hP)).toLinearEquiv.toAddEquiv

/-- Restricted Shapiro in degree one for the product of local units above
one finite base prime. -/
noncomputable def resizedPrimesAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    H1 (resizedPrimesRepresentation
        (K := K) (L := L) P) ≃+
      H1 (resizedUnitsRepresentation
        (K := K) (L := L) P Q) :=
  (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 1).mapIso
      (aboveInducedIso
        (K := K) (L := L) P Q)) ≪≫
    shapiro
      (primeAboveStabilizer (K := K) (L := L) P Q)
      (resizedUnitsRepresentation
        (K := K) (L := L) P Q) 1).toLinearEquiv.toAddEquiv

set_option synthInstance.maxHeartbeats 1000000 in
-- The two concrete local-unit actions and their completion models elaborate together.
set_option maxHeartbeats 6000000 in
/-- The chosen upper local-unit factor has trivial first cohomology at an
unramified prime. -/
theorem resized_1_subsingleton
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal) :
    Subsingleton
      (H1 (resizedUnitsRepresentation
        (K := K) (L := L) P Q)) := by
  letI := unitsStabilizerAction (K := K) (L := L) P Q
  let v := (FinitePlace.mk P).val
  let w := aboveCompletionPlace (K := K) (L := L) P Q
  let F := v.Completion
  let E := w.1.Completion
  let B := completionIntegerRing w.1
  letI : Algebra F E := (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional F E :=
    Submission.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois F E := placeCompletionGalois v w
  letI : MulSemiringAction Gal(E/F) B :=
    integerRingAction
      (K := K) (L := L) P Q
  letI : MulDistribMulAction Gal(E/F) Bˣ :=
    integerUnitsAction
      (K := K) (L := L) P Q
  let eG := aboveStabilizerGal
    (K := K) (L := L) P Q
  let eM := unitsCompletionInteger
    (K := K) (L := L) P Q
  let e := ulift1Equivariant eG eM
    (units_integer_equivariant
      (K := K) (L := L) P Q)
  letI : Subsingleton
      (H1 (uliftMulRepresentation (G := Gal(E/F)) (M := Bˣ))) :=
    integer_subsingleton_unramified
      (K := K) (L := L) P Q hQ
  exact e.injective.subsingleton

/-- Restricted Shapiro transports the chosen-factor vanishing to the
whole product of upper local-unit factors. -/
theorem above_subsingleton_unramified
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal) :
    Subsingleton
      (H1 (resizedPrimesRepresentation
        (K := K) (L := L) P)) := by
  letI : Subsingleton
      (H1 (resizedUnitsRepresentation
        (K := K) (L := L) P Q)) :=
    resized_1_subsingleton
      (K := K) (L := L) P Q hQ
  exact (resizedPrimesAbove
    (K := K) (L := L) P Q).injective.subsingleton

/-- Every nonexceptional finite-stage orbit has trivial first cohomology
when all primes outside the stage are unramified. -/
theorem resized_subsingleton_outside
    (S : Finset (NumberFieldPlace K))
    (hunramified :
      ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Sum.inl P : NumberFieldPlace K) ∉ S →
          ∀ Q : UpperPrimeFactors (K := K) (L := L) P,
            Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
              (upperPrime (K := K) (L := L) P Q).asIdeal)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    Subsingleton
      (H1 (stageOrbitRepresentation
        (K := K) (L := L) S P)) := by
  let w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val :=
    Classical.choice
      (absolute_value_extension
        (K := K) (L := L) (FinitePlace.mk P).val)
  let Q₀ : UpperPrimeFactors (K := K) (L := L) P :=
    placeUpperFactor (K := K) (L := L) P w
  let Q : FinitePrimesAbove (K := K) (L := L) P :=
    upperPrimesAbove (K := K) (L := L) P Q₀
  have hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal := by
    simpa only [Q, upper_primes_above] using
      hunramified P hP Q₀
  letI : Subsingleton
      (H1 (resizedPrimesRepresentation
        (K := K) (L := L) P)) :=
    above_subsingleton_unramified
      (K := K) (L := L) P Q hQ
  exact (resizedStageUnits
    (K := K) (L := L) S P hP).injective.subsingleton

/-- Delete the cohomologically trivial degree-one coordinates outside the
finite exceptional set. -/
noncomputable def stage1Exceptional
    (S : Finset (NumberFieldPlace K))
    (houtside :
      ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Sum.inl P : NumberFieldPlace K) ∉ S →
          Subsingleton
            (H1 (stageOrbitRepresentation
              (K := K) (L := L) S P))) :
    (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        H1 (stageOrbitRepresentation
          (K := K) (L := L) S P)) ≃+
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          (Sum.inl P : NumberFieldPlace K) ∈ S},
        H1 (resizedAboveRepresentation
          (K := K) (L := L) P.1)) where
  toFun x P :=
    resizedStageFull
      (K := K) (L := L) S P.1 P.2 (x P.1)
  invFun x P := if hP : (Sum.inl P : NumberFieldPlace K) ∈ S then
    (resizedStageFull
      (K := K) (L := L) S P hP).symm (x ⟨P, hP⟩)
  else
    0
  left_inv x := by
    funext P
    by_cases hP : (Sum.inl P : NumberFieldPlace K) ∈ S
    · change (if hP' : (Sum.inl P : NumberFieldPlace K) ∈ S then
          (resizedStageFull
            (K := K) (L := L) S P hP').symm
            ((resizedStageFull
              (K := K) (L := L) S P hP') (x P))
        else 0) = x P
      simp only [dif_pos hP, AddEquiv.symm_apply_apply]
    · letI := houtside P hP
      exact Subsingleton.elim _ _
  right_inv x := by
    funext P
    change (resizedStageFull
      (K := K) (L := L) S P.1 P.2)
        (if hP' : (Sum.inl P.1 : NumberFieldPlace K) ∈ S then
          (resizedStageFull
            (K := K) (L := L) S P.1 hP').symm (x ⟨P.1, hP'⟩)
        else 0) = x P
    simp only [dif_pos P.2, AddEquiv.apply_symm_apply]
  map_add' x y := by
    funext P
    exact (resizedStageFull
      (K := K) (L := L) S P.1 P.2).map_add (x P.1) (y P.1)

/-- An unrestricted finite completion orbit is Shapiro-equivalent in
degree one to the chosen completion. -/
noncomputable def h1Chosen
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    H1 (resizedAboveRepresentation
      (K := K) (L := L) P) ≃+
      H1 (uliftIntegralRepresentation
        (placeUnitsRepresentation (FinitePlace.mk P).val w)) := by
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  exact
    ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 1).mapIso
      (resizedIsoOrbit
        (K := K) (L := L) P).symm).toLinearEquiv.toAddEquiv |>.trans
          (uliftShapiroIso
            (K := K) (L := L) (FinitePlace.mk P).val w 1).toLinearEquiv.toAddEquiv

/-- The finite part of an admissible stage has degree-one cohomology equal
to the product of its unrestricted exceptional completion orbits. -/
noncomputable def stageHExceptional
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S) :
    H1 (resizedStageRepresentation
      (K := K) (L := L) S) ≃+
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          (Sum.inl P : NumberFieldPlace K) ∈ S},
        H1 (resizedAboveRepresentation
          (K := K) (L := L) P.1)) :=
  (stage1Pi
    (K := K) (L := L) S).trans
      (stage1Exceptional
        (K := K) (L := L) S
        (fun P hP ↦
          resized_subsingleton_outside
            (K := K) (L := L) S
            (unramified_outside S hS) P hP))

/-- The finite factor of an admissible stage is the product of the chosen
local degree-one groups at its finite members. -/
noncomputable def stage1Chosen
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    H1 (resizedStageRepresentation
      (K := K) (L := L) S) ≃+
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          (Sum.inl P : NumberFieldPlace K) ∈ S},
        H1 (uliftIntegralRepresentation
          (placeUnitsRepresentation (FinitePlace.mk P.1).val
            (w ⟨Sum.inl P.1, P.2⟩)))) :=
  (stageHExceptional S hS).trans <|
    AddEquiv.piCongrRight fun P ↦
      h1Chosen P.1
        (w ⟨Sum.inl P.1, P.2⟩)

/-- The resized degree-one cohomology of any chosen completion is trivial
by local Hilbert 90. -/
theorem resized_h_subsingleton
    (v : NumberFieldPlace K)
    (w : CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute v)) :
    Subsingleton
      (H1 (uliftIntegralRepresentation
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute v) w))) := by
  let H := CompletionPlaceStabilizer
    (coinvariantsInvariantsAbsolute v) w
  let e : H1 (uliftIntegralRepresentation
      (placeUnitsRepresentation
        (coinvariantsInvariantsAbsolute v) w)) ≃+
      H1 (hasseUnitsRepresentation
        (coinvariantsInvariantsAbsolute v) w) :=
    ((groupCohomology.functor (ULift.{u} ℤ) H 1).mapIso
      (uliftIsoHasse
        (K := K) (L := L)
        (coinvariantsInvariantsAbsolute v)
        w)).toLinearEquiv.toAddEquiv
  constructor
  intro x y
  apply e.injective
  exact (units_h_1 v w (e x)).trans
    (units_h_1 v w (e y)).symm

private abbrev infiniteCompletionFamily (v : InfinitePlace K) :=
  uliftUnitsRepresentation
    (K := K) (L := L) v.1

set_option synthInstance.maxHeartbeats 300000 in
-- Resolving the categorical product of all infinite completion-orbit
-- representations requires a deeper module-instance search.
/-- Evaluation from the categorical product of infinite completion orbits
to the concrete pointwise product representation. -/
noncomputable def categoricalProductsPointwise :
    (∏ᶜ fun v : InfinitePlace K ↦ infiniteCompletionFamily
        (K := K) (L := L) v) ⟶
      resizedProductsRepresentation K L := by
  letI repModule (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) X := X.hV2
  let A := fun v : InfinitePlace K ↦
    infiniteCompletionFamily (K := K) (L := L) v
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
-- The inverse concrete-product equivalence creates deeply nested dependent
-- representation instances.
/-- The preceding evaluation map is bijective on carriers. -/
theorem categorical_products_pointwise :
    Function.Bijective
      (categoricalProductsPointwise
        (K := K) (L := L)) := by
  letI repModule (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) X := X.hV2
  let A := fun v : InfinitePlace K ↦
    infiniteCompletionFamily (K := K) (L := L) v
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
-- Packaging the pointwise product as a categorical representation requires
-- elaborating the full dependent product action.
/-- The pointwise infinite completion product is the corresponding
categorical product of representations. -/
noncomputable def productsIsoCategorical :
    resizedProductsRepresentation K L ≅
      (∏ᶜ fun v : InfinitePlace K ↦ infiniteCompletionFamily
        (K := K) (L := L) v) := by
  letI repModule (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) X := X.hV2
  exact (Rep.mkIso
    ((categoricalProductsPointwise
      (K := K) (L := L)).hom.ofBijective
        (categorical_products_pointwise
          (K := K) (L := L)))).symm

set_option synthInstance.maxHeartbeats 400000 in
-- Applying degree-one cohomology to the categorical product equivalence
-- requires a larger dependent module-instance search.
/-- Degree-one cohomology of the infinite pointwise product is the
pointwise product of degree-one cohomology. -/
noncomputable def resizedProductsPi :
    H1 (resizedProductsRepresentation K L) ≃+
      (∀ v : InfinitePlace K,
        H1 (uliftUnitsRepresentation
          (K := K) (L := L) v.1)) := by
  let A := fun v : InfinitePlace K ↦
    infiniteCompletionFamily (K := K) (L := L) v
  let e₁ := ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 1).mapIso
    (productsIsoCategorical
      (K := K) (L := L))).toLinearEquiv.toAddEquiv
  let e₂ := (groupProductIso
    (ULift.{u} ℤ) Gal(L/K) A 1).toLinearEquiv.toAddEquiv
  let e₃ := moduleCatPi (fun v ↦ H1 (A v))
  exact e₁.trans (e₂.trans e₃)

/-- The infinite idèle factor is the product of the chosen local
degree-one groups. -/
noncomputable def infiniteIdelesChosen
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    H1 (resizedInfiniteRepresentation K L) ≃+
      (∀ v : InfinitePlace K,
        H1 (uliftIntegralRepresentation
          (placeUnitsRepresentation v.1
            (w ⟨Sum.inr v, hS.1 v⟩)))) := by
  refine (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 1).mapIso
    (resizedIsoProducts
      (K := K) (L := L))).toLinearEquiv.toAddEquiv.trans
      (resizedProductsPi
        (K := K) (L := L))).trans ?_
  apply AddEquiv.piCongrRight
  intro v
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v.1) :=
    places_above_pretransitive v
  exact (uliftShapiroIso
    (K := K) (L := L) v.1
      (w ⟨Sum.inr v, hS.1 v⟩) 1).toLinearEquiv.toAddEquiv

/-- The infinite factor of an admissible restricted idèle stage has
trivial first cohomology. -/
theorem infinite_ideles_subsingleton
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    Subsingleton (H1 (resizedInfiniteRepresentation K L)) := by
  letI (v : InfinitePlace K) : Subsingleton
      (H1 (uliftIntegralRepresentation
        (placeUnitsRepresentation v.1
          (w ⟨Sum.inr v, hS.1 v⟩)))) :=
    resized_h_subsingleton
      (K := K) (L := L) (Sum.inr v) (w ⟨Sum.inr v, hS.1 v⟩)
  exact (infiniteIdelesChosen
    (K := K) (L := L) S hS w).injective.subsingleton

/-- The finite factor of an admissible restricted idèle stage has trivial
first cohomology. -/
theorem stage_1_subsingleton
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    Subsingleton
      (H1 (resizedStageRepresentation
        (K := K) (L := L) S)) := by
  letI (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ S}) : Subsingleton
      (H1 (uliftIntegralRepresentation
        (placeUnitsRepresentation (FinitePlace.mk P.1).val
          (w ⟨Sum.inl P.1, P.2⟩)))) :=
    resized_h_subsingleton
      (K := K) (L := L) (Sum.inl P.1) (w ⟨Sum.inl P.1, P.2⟩)
  exact (stage1Chosen
    (K := K) (L := L) S hS w).injective.subsingleton

/-- First cohomology of the regrouped product stage is trivial when it is
trivial on its infinite and finite factors. -/
theorem resized_ideles_subsingleton
    (S : Finset (NumberFieldPlace K))
    (hInfinite : Subsingleton
      (H1 (resizedInfiniteRepresentation K L)))
    (hFinite : Subsingleton
      (H1 (resizedStageRepresentation
        (K := K) (L := L) S))) :
    Subsingleton
      (H1 (resizedIdelesRepresentation
        (K := K) (L := L) S)) := by
  letI := hInfinite
  letI := hFinite
  constructor
  intro q q'
  suffices hz : ∀ r : H1 (resizedIdelesRepresentation
      (K := K) (L := L) S), r = 0 by
    exact (hz q).trans (hz q').symm
  intro r
  induction r using H1_induction_on with
  | h x =>
      have hInfiniteClass :
          H1π (resizedInfiniteRepresentation K L)
            (mapCocycles₁ (MonoidHom.id Gal(L/K))
              (resizedPlacesInfinite
                (K := K) (L := L) S) x) = 0 :=
        Subsingleton.elim _ _
      have hFiniteClass :
          H1π (resizedStageRepresentation
              (K := K) (L := L) S)
            (mapCocycles₁ (MonoidHom.id Gal(L/K))
              (resizedIdelesFinite
                (K := K) (L := L) S) x) = 0 :=
        Subsingleton.elim _ _
      obtain ⟨a, ha⟩ := (H1π_eq_zero_iff _).1 hInfiniteClass
      obtain ⟨b, hb⟩ := (H1π_eq_zero_iff _).1 hFiniteClass
      apply (H1π_eq_zero_iff x).2
      let c : resizedIdelesRepresentation
          (K := K) (L := L) S :=
        Additive.ofMul (a.toMul, b.toMul)
      refine ⟨c, ?_⟩
      funext g
      apply Additive.toMul.injective
      apply Prod.ext
      · have ha' := congrFun ha g
        change (resizedInfiniteRepresentation K L).ρ g a - a =
          Additive.ofMul (x g).toMul.1 at ha'
        exact congrArg Additive.toMul ha'
      · have hb' := congrFun hb g
        change (resizedStageRepresentation
            (K := K) (L := L) S).ρ g b - b =
          Additive.ofMul (x g).toMul.2 at hb'
        exact congrArg Additive.toMul hb'

/-- The resized first cohomology of the literal restricted idèle stage is
trivial. -/
theorem ideles_1_subsingleton
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    Subsingleton
      (H1 (resizedPlacesRepresentation
        (K := K) (L := L) S)) := by
  letI : Subsingleton (H1 (resizedInfiniteRepresentation K L)) :=
    infinite_ideles_subsingleton
      (K := K) (L := L) S hS w
  letI : Subsingleton
      (H1 (resizedStageRepresentation
        (K := K) (L := L) S)) :=
    stage_1_subsingleton
      (K := K) (L := L) S hS w
  letI : Subsingleton
      (H1 (resizedIdelesRepresentation
        (K := K) (L := L) S)) :=
    resized_ideles_subsingleton
      (K := K) (L := L) S inferInstance inferInstance
  let e : H1 (resizedPlacesRepresentation
      (K := K) (L := L) S) ≃+
      H1 (resizedIdelesRepresentation
        (K := K) (L := L) S) :=
    ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 1).mapIso
      (resizedRepresentationIso
        (K := K) (L := L) S)).toLinearEquiv.toAddEquiv
  exact e.injective.subsingleton

set_option synthInstance.maxHeartbeats 500000 in
-- Cyclic periodicity and the restricted-stage representation elaborate together.
set_option maxHeartbeats 4000000 in
/-- The denominator in the Herbrand quotient of an admissible restricted
idèle stage is trivial. -/
theorem ideles_places_subsingleton
    [IsCyclic Gal(L/K)]
    (S : Finset (NumberFieldPlace K))
    (hS : AdmissiblePlaceSet (K := K) (L := L) S)
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    Subsingleton
      (tateNegOne
        (idelesRepresentation (K := K) (L := L) S)) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let A := idelesRepresentation (K := K) (L := L) S
  let e : tateNegOne A ≃+
      H1 (resizedPlacesRepresentation
        (K := K) (L := L) S) :=
    (tateULift A).trans
      (tateCohomologyNeg
        (resizedPlacesRepresentation (K := K) (L := L) S)
        g hg).toAddEquiv
  letI : Subsingleton
      (H1 (resizedPlacesRepresentation
        (K := K) (L := L) S)) :=
    ideles_1_subsingleton
      (K := K) (L := L) S hS w
  exact e.injective.subsingleton

set_option synthInstance.maxHeartbeats 500000 in
-- The dependent local cardinalities and both global Tate groups elaborate together.
set_option maxHeartbeats 6000000 in
/-- The complete restricted-product assembly required by Proposition
VII.2.7. -/
theorem herbrandAssemblyBridge :
    HerbrandAssemblyBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  intro S hS w hlocal
  letI (v : S) : Fintype (CompletionPlaceStabilizer
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) :=
    Fintype.ofFinite _
  have hlocalZero : ∀ v : S,
      Finite (tateZero
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))) ∧
      Nat.card (tateZero
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))) =
        Nat.card (CompletionPlaceStabilizer
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) := by
    intro v
    let A := placeUnitsRepresentation
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)
    obtain ⟨hfiniteZero, hfiniteNeg, hquotient⟩ := hlocal v
    letI : Finite (tateZero A) := hfiniteZero
    letI : Subsingleton (tateNegOne A) :=
      tate_neg_subsingleton
        (v : NumberFieldPlace K) (w v)
    letI : Finite (tateNegOne A) := inferInstance
    have hcardNeg : Nat.card (tateNegOne A) = 1 :=
      Nat.card_unique
    have hcardZeroQ : (Nat.card (tateZero A) : ℚ) =
        Nat.card (CompletionPlaceStabilizer
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) := by
      change (Nat.card (tateZero A) : ℚ) /
          Nat.card (tateNegOne A) = _ at hquotient
      rw [hcardNeg, Nat.cast_one, div_one] at hquotient
      exact hquotient
    exact ⟨hfiniteZero, by exact_mod_cast hcardZeroQ⟩
  obtain ⟨hfiniteZero, hcardZero⟩ :=
    ideles_places_cardinality
      (K := K) (L := L) S hS w hlocalZero
  let A := idelesRepresentation (K := K) (L := L) S
  letI : Finite (tateZero A) := hfiniteZero
  letI : Subsingleton (tateNegOne A) :=
    ideles_places_subsingleton
      (K := K) (L := L) S hS w
  letI : Finite (tateNegOne A) := inferInstance
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hcardNeg : Nat.card (tateNegOne A) = 1 :=
    Nat.card_unique
  rw [hcardZero, hcardNeg, Nat.cast_one, div_one]
  norm_cast

/-- Finite spectral base change now supplies Proposition VII.2.7 without
an additional restricted-product assembly hypothesis. -/
theorem restricted_spectral_change
    (hbaseChange : FiniteSpectralChange.{u}) :
    LocalHerbrandFormula.{u} :=
  spectral_change_assembly
    hbaseChange herbrandAssemblyBridge

/-- **Proposition VII.2.7.** The Herbrand quotient of the restricted
idèle group is the product of the local completion degrees. -/
theorem restrictedHerbrandFormula :
    LocalHerbrandFormula.{u} :=
  coinvariants_invariants_assembly
    localHerbrandBridge herbrandAssemblyBridge

end

end Submission.CField.BLoc
