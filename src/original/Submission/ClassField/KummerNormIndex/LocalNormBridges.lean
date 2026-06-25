import Submission.ClassField.HasseNorm.IdeleOpenness
import Submission.ClassField.HasseNorm.LocalComparison
import Submission.ClassField.Reciprocity.CompletionArtinHom

open scoped IsMulCommutative

/-!
# The local norm inputs in Lemma VII.6.4

This file supplies the two local bridges used by the restricted-product
assembly of Lemma VII.6.4.  At a place in `S`, local reciprocity identifies
the local norm quotient with a decomposition subgroup of the global Galois
group, so the exponent-`p` hypothesis kills every `p`th power in that
quotient.  Away from `S ∪ T`, unramified unit-norm surjectivity supplies the
required unit-preserving lift.
-/

namespace Submission.CField.KNIndex

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LRecip
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.ICohomo
open Submission.CField.GWang
open Submission.CField.HNorm

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Conjugating both the base and extension fields transports a Galois
automorphism. -/
private def transportGal
    {F₁ E₁ F₂ E₂ : Type*}
    [Field F₁] [Field E₁] [Field F₂] [Field E₂]
    [Algebra F₁ E₁] [Algebra F₂ E₂]
    (f : F₁ ≃+* F₂) (g : E₁ ≃+* E₂)
    (h : (algebraMap F₂ E₂).comp f.toRingHom =
      g.toRingHom.comp (algebraMap F₁ E₁))
    (sigma : Gal(E₁/F₁)) : Gal(E₂/F₂) := by
  let c : E₂ ≃+* E₂ := g.symm.trans (sigma.toRingEquiv.trans g)
  exact AlgEquiv.ofRingEquiv (f := c) fun x => by
    change g (sigma (g.symm (algebraMap F₂ E₂ x))) =
      algebraMap F₂ E₂ x
    have hsquare := DFunLike.congr_fun h (f.symm x)
    have hpreimage : g.symm (algebraMap F₂ E₂ x) =
        algebraMap F₁ E₁ (f.symm x) := by
      apply g.injective
      rw [g.apply_symm_apply]
      simpa using hsquare
    rw [hpreimage, sigma.commutes]
    simpa using hsquare.symm

/-- The Galois groups of two extensions identified by a commutative square
of field equivalences are multiplicatively equivalent. -/
private def galMulEquiv
    {F₁ E₁ F₂ E₂ : Type*}
    [Field F₁] [Field E₁] [Field F₂] [Field E₂]
    [Algebra F₁ E₁] [Algebra F₂ E₂]
    (f : F₁ ≃+* F₂) (g : E₁ ≃+* E₂)
    (h : (algebraMap F₂ E₂).comp f.toRingHom =
      g.toRingHom.comp (algebraMap F₁ E₁)) :
    Gal(E₁/F₁) ≃* Gal(E₂/F₂) where
  toFun := transportGal f g h
  invFun := transportGal f.symm g.symm (by
    apply RingHom.ext
    intro x
    apply g.injective
    simpa using (DFunLike.congr_fun h (f.symm x)).symm)
  left_inv sigma := by
    ext x
    change g.symm (g (sigma (g.symm (g x)))) = sigma x
    simp
  right_inv sigma := by
    ext x
    change g (g.symm (sigma (g (g.symm x)))) = sigma x
    simp
  map_mul' sigma tau := by
    ext x
    change g ((sigma * tau) (g.symm x)) =
      g (sigma (g.symm (g (tau (g.symm x)))))
    simp

/-- A number field has a Type-0 model, since a finite rational basis embeds
it into a finite power of `ℚ`. -/
private theorem number_small_zero
    (F : Type u) [Field F] [NumberField F] : Small.{0} F := by
  let b := Module.finBasis ℚ F
  exact small_of_injective b.repr.injective

/-- The valued copy of a small field is small. -/
private theorem abs_small_zero
    (F : Type u) [Field F] [Small.{0} F]
    (v : AbsoluteValue F ℝ) : Small.{0} (WithAbs v) :=
  small_of_injective (WithAbs.equiv v).injective

/-- Uniform completion preserves Type-0 smallness. -/
private theorem uniform_small_zero
    (X : Type u) [Small.{0} X] [UniformSpace X] :
    Small.{0} (UniformSpace.Completion X) := by
  let eSet : Set X ≃ Set (Shrink.{0} X) :=
    Equiv.Set.congr (equivShrink X)
  let eSetSet : Set (Set X) ≃ Set (Set (Shrink.{0} X)) :=
    Equiv.Set.congr eSet
  letI : Small.{0} (Set (Set X)) :=
    small_of_injective eSetSet.injective
  letI : Small.{0} (Filter X) := by
    apply small_of_injective (f := fun f : Filter X ↦ f.sets)
    intro f g h
    apply Filter.ext
    intro s
    change f.sets = g.sets at h
    change s ∈ f.sets ↔ s ∈ g.sets
    rw [h]
  letI : Small.{0} (CauchyFilter X) :=
    small_of_injective Subtype.val_injective
  change Small.{0} (Quotient (inseparableSetoid (CauchyFilter X)))
  exact small_of_surjective Quotient.mk_surjective

set_option maxHeartbeats 2000000 in
-- The transported norm subgroup includes several dependent algebra norms.
set_option synthInstance.maxHeartbeats 500000 in
-- Shrink transport and reconstruction of the local-field topology elaborate together.
/-- The universe-polymorphic consequence of finite local reciprocity used
below.  The Type-0 reciprocity theorem is applied to `Shrink` models; the
last part of the proof transports its norm subgroup back to `F`. -/
private theorem pow_subgroup_small
    (p : ℕ) (F E : Type u)
    [Small.{0} F] [Small.{0} E]
    [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsMulCommutative Gal(E/F)]
    (hexponent : ∀ sigma : Gal(E/F), sigma ^ p = 1)
    (x : Fˣ) : x ^ p ∈ normSubgroup F E := by
  let eF : (Shrink.{0} F) ≃+* F := Shrink.ringEquiv F
  let eE : (Shrink.{0} E) ≃+* E := Shrink.ringEquiv E
  letI : NormedField (Shrink.{0} F) :=
    NormedField.induced (Shrink.{0} F) F eF.toRingHom eF.injective
  letI : NontriviallyNormedField (Shrink.{0} F) :=
    { (inferInstance : NormedField (Shrink.{0} F)) with
      non_trivial := by
        obtain ⟨y, hy⟩ := NontriviallyNormedField.non_trivial (α := F)
        refine ⟨eF.symm y, ?_⟩
        change 1 < ‖eF (eF.symm y)‖
        simpa using hy }
  letI : CharZero (Shrink.{0} F) := eF.toRingHom.charZero
  letI : IsUltrametricDist (Shrink.{0} F) := by
    constructor
    intro a b c
    change dist (eF a) (eF c) ≤
      max (dist (eF a) (eF b)) (dist (eF b) (eF c))
    exact dist_triangle_max (eF a) (eF b) (eF c)
  letI : Algebra (Shrink.{0} F) F := eF.toRingHom.toAlgebra
  let eFAlg : (Shrink.{0} F) ≃ₐ[(Shrink.{0} F)] F :=
    AlgEquiv.ofRingEquiv (f := eF) (fun _ ↦ rfl)
  letI : Module.Finite (Shrink.{0} F) F :=
    Module.Finite.equiv eFAlg.toLinearEquiv
  letI : Algebra (Shrink.{0} F) E :=
    ((algebraMap F E).comp eF.toRingHom).toAlgebra
  letI : IsScalarTower (Shrink.{0} F) F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite (Shrink.{0} F) E := Module.Finite.trans F E
  letI : Algebra (Shrink.{0} F) (Shrink.{0} E) := inferInstance
  let eEAlg : (Shrink.{0} E) ≃ₐ[(Shrink.{0} F)] E := Shrink.algEquiv (Shrink.{0} F) E
  letI : Module.Finite (Shrink.{0} F) (Shrink.{0} E) :=
    Module.Finite.equiv eEAlg.toLinearEquiv.symm
  letI : ValuativeRel (Shrink.{0} F) :=
    ValuativeRel.ofValuation (NormedField.valuation (K := (Shrink.{0} F)))
  letI : Valuation.Compatible (NormedField.valuation (K := (Shrink.{0} F))) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := (Shrink.{0} F)))
  haveI htop : IsValuativeTopology (Shrink.{0} F) := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : Shrink.{0} F) ↔
        ∃ gamma : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := Shrink.{0} F)))ˣ,
          {y | (NormedField.valuation (K := Shrink.{0} F)).restrict y <
            gamma.1} ⊆ s from
      (NormedField.toValued
        (K := Shrink.{0} F)).is_topological_valuation s]
    simpa using
      (NormedField.valuation
        (K := Shrink.{0} F)).exists_setOf_restrict_le_iff 0 s
  haveI hcompact : LocallyCompactSpace (Shrink.{0} F) :=
    (Shrink.homeomorph F).symm.isOpenEmbedding.locallyCompactSpace
  haveI hvaluationNontrivial :
      (NormedField.valuation (K := (Shrink.{0} F))).IsNontrivial := by
    constructor
    obtain ⟨y, hy⟩ :=
      NontriviallyNormedField.non_trivial (α := (Shrink.{0} F))
    refine ⟨y, ?_, ?_⟩
    · have hy0 : y ≠ 0 := by
        intro h
        subst y
        have hnorm_zero : ‖(0 : (Shrink.{0} F))‖ = 0 := norm_zero
        rw [hnorm_zero] at hy
        exact (not_lt_of_ge zero_le_one) hy
      intro h
      apply hy0
      change ‖y‖₊ = 0 at h
      exact nnnorm_eq_zero.mp h
    · intro h
      change ‖y‖₊ = 1 at h
      have hnorm : ‖y‖ = 1 := by
        have hc := congrArg (fun r : NNReal ↦ (r : ℝ)) h
        change (↑‖y‖₊ : ℝ) = (↑(1 : NNReal) : ℝ)
        exact hc
      exact (ne_of_gt hy) hnorm
  haveI hnontrivial : ValuativeRel.IsNontrivial (Shrink.{0} F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := (Shrink.{0} F)))).mpr inferInstance
  haveI hlocal : IsNonarchimedeanLocalField (Shrink.{0} F) :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hcompact
      toIsNontrivial := hnontrivial }
  have hsquare : (algebraMap (Shrink.{0} F) (Shrink.{0} E)).comp eF.symm.toRingHom =
      eE.symm.toRingHom.comp (algebraMap F E) := by
    apply RingHom.ext
    intro y
    change algebraMap (Shrink.{0} F) (Shrink.{0} E) (eF.symm y) =
      eE.symm (algebraMap F E y)
    calc
      _ = eE.symm (eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) (eF.symm y))) :=
        (eE.symm_apply_apply _).symm
      _ = eE.symm (algebraMap F E y) := by
        congr 1
        calc
          eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) (eF.symm y)) =
              algebraMap (Shrink.{0} F) E (eF.symm y) := eEAlg.commutes _
          _ = algebraMap F E y := by
            change algebraMap F E (eF (eF.symm y)) = _
            rw [eF.apply_symm_apply]
  letI : IsGalois (Shrink.{0} F) (Shrink.{0} E) := IsGalois.of_equiv_equiv
    (F := F) (E := E) (M := (Shrink.{0} F)) (N := (Shrink.{0} E))
    (f := eF.symm) (g := eE.symm) hsquare
  let galEquiv : Gal((Shrink.{0} E)/(Shrink.{0} F)) ≃* Gal(E/F) :=
    galMulEquiv eF eE (by
      apply RingHom.ext
      intro y
      change algebraMap F E (eF y) = eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) y)
      exact (eEAlg.commutes y).symm)
  letI : IsMulCommutative Gal((Shrink.{0} E)/(Shrink.{0} F)) := by
    refine ⟨⟨fun sigma tau ↦ galEquiv.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm (galEquiv sigma) (galEquiv tau)
  have hexponent0 : ∀ sigma : Gal((Shrink.{0} E)/(Shrink.{0} F)), sigma ^ p = 1 := by
    intro sigma
    apply galEquiv.injective
    simpa only [map_pow, map_one] using hexponent (galEquiv sigma)
  have he : (algebraMap F E).comp eF.toRingHom =
      eE.toRingHom.comp (algebraMap (Shrink.{0} F) (Shrink.{0} E)) := by
    apply RingHom.ext
    intro y
    change algebraMap F E (eF y) = eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) y)
    exact (eEAlg.commutes y).symm
  have hnorm :
      (normSubgroup (Shrink.{0} F) (Shrink.{0} E)).comap (Units.map eF.symm.toRingHom) =
        normSubgroup F E := by
    ext y
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨Units.map eE.toRingHom z, ?_⟩
      apply Units.ext
      change Algebra.norm F (eE (z : (Shrink.{0} E))) = (y : F)
      have hn := Algebra.norm_eq_of_equiv_equiv eF eE he (z : (Shrink.{0} E))
      change Algebra.norm (Shrink.{0} F) (z : (Shrink.{0} E)) =
        eF.symm (Algebra.norm F (eE (z : (Shrink.{0} E)))) at hn
      have hz' := congrArg Units.val hz
      change Algebra.norm (Shrink.{0} F) (z : (Shrink.{0} E)) = eF.symm (y : F) at hz'
      apply eF.symm.injective
      rw [← hn, ← hz']
    · rintro ⟨z, hz⟩
      refine ⟨Units.map eE.symm.toRingHom z, ?_⟩
      apply Units.ext
      change Algebra.norm (Shrink.{0} F) (eE.symm (z : E)) = eF.symm (y : F)
      have hn := Algebra.norm_eq_of_equiv_equiv eF eE he
        (eE.symm (z : E))
      rw [eE.apply_symm_apply] at hn
      have hz' := congrArg Units.val hz
      change Algebra.norm F (z : E) = (y : F) at hz'
      rw [hn, hz']
  rw [← hnorm]
  change Units.map eF.symm.toRingHom (x ^ p) ∈ normSubgroup (Shrink.{0} F) (Shrink.{0} E)
  apply (QuotientGroup.eq_one_iff _).1
  let artin := @abelianLocalArtin
    (Shrink.{0} F) (Shrink.{0} E)
    inferInstance inferInstance hlocal inferInstance inferInstance
    inferInstance inferInstance inferInstance
  apply artin.injective
  let x0 : (Shrink.{0} F)ˣ := Units.map eF.symm.toRingHom x
  change artin (QuotientGroup.mk' (normSubgroup (Shrink.{0} F) (Shrink.{0} E))
      (Units.map eF.symm.toRingHom (x ^ p))) = artin 1
  calc
    _ = artin (QuotientGroup.mk' (normSubgroup (Shrink.{0} F) (Shrink.{0} E)) (x0 ^ p)) := by
      rw [map_pow]
    _ = (artin (QuotientGroup.mk' (normSubgroup (Shrink.{0} F) (Shrink.{0} E)) x0)) ^ p := by
      rw [map_pow, map_pow]
    _ = 1 := hexponent0 _
    _ = artin 1 := (map_one artin).symm

/-- Membership in one archimedean completed norm range gives a lift
supported at that upper place. -/
private theorem infinite_lift_range
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (x : v.Completionˣ)
    (hx : x ∈ (infiniteCompletionNorm (K := K) (L := L) v w).range) :
    InfiniteNormLift K L v x := by
  classical
  obtain ⟨y, hy⟩ := hx
  let z : ∀ q : InfinitePlace L, q.Completionˣ :=
    Pi.mulSingle (M := fun q : InfinitePlace L ↦ q.Completionˣ) w.1 y
  refine ⟨z, ?_, ?_⟩
  · intro q hq
    apply Pi.mulSingle_eq_of_ne
      (M := fun q : InfinitePlace L ↦ q.Completionˣ)
    intro hqw
    apply hq
    rw [hqw, w.2]
  · rw [Finset.prod_eq_single w]
    · change infiniteCompletionNorm (K := K) (L := L) v w (z w.1) = x
      rw [show z w.1 = y from Pi.mulSingle_eq_same
        (M := fun q : InfinitePlace L ↦ q.Completionˣ) w.1 y]
      exact hy
    · intro q _ hq
      have hUpper : q.1 ≠ w.1 := by
        intro h
        exact hq (Subtype.ext h)
      change infiniteCompletionNorm (K := K) (L := L) v q (z q.1) = 1
      rw [show z q.1 = 1 from Pi.mulSingle_eq_of_ne
        (M := fun q : InfinitePlace L ↦ q.Completionˣ) hUpper y]
      exact map_one _
    · intro hw
      exact (hw (by simp)).elim

set_option synthInstance.maxHeartbeats 500000 in
-- Completion Galois groups and their reciprocity maps elaborate simultaneously.
set_option maxHeartbeats 4000000 in
-- The finite and infinite local cases are assembled in one bridge.
/-- Exponent `p` in the global abelian Galois group makes every local
`p`th power a norm, at finite and infinite places alike. -/
theorem powerLocalBridge : PowerLocalBridge.{u} := by
  classical
  intro p K L _ _ _ _ _ _ _ hexponent
  constructor
  · intro P x hx
    obtain ⟨y, rfl⟩ := hx
    let Q := chosenPrimeFactor (K := K) (L := L) P
    let v := (FinitePlace.mk P).val
    let model := hasseCompletionModel K L P Q
    let w := model.place
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : NontriviallyNormedField v.Completion :=
      placeNontriviallyNormed P
    letI : CharZero v.Completion :=
      charZero_of_injective_ringHom (completionEmbedding v).injective
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
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Finite (CompletionPlacesAbove (L := L) v) :=
      absolute_extensions_separable v
    letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
      absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) v) :=
      completion_above_pretransitive P
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    let e := decompositionCompletionExtension v w.1
    letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
      refine ⟨⟨fun sigma tau ↦ e.symm.injective ?_⟩⟩
      simpa only [map_mul] using mul_comm (e.symm sigma) (e.symm tau)
    have hlocalExponent :
        ∀ sigma : Gal(w.1.Completion/v.Completion), sigma ^ p = 1 := by
      intro sigma
      apply e.symm.injective
      apply Subtype.ext
      simpa only [map_pow, map_one] using
        hexponent ((e.symm sigma : absoluteValueDecomposition v w.1) :
          Gal(L/K))
    letI : Small.{0} K := number_small_zero K
    letI : Small.{0} L := number_small_zero L
    letI : Small.{0} (WithAbs v) := abs_small_zero K v
    letI : Small.{0} (WithAbs w.1) := abs_small_zero L w.1
    letI : Small.{0} v.Completion := uniform_small_zero _
    letI : Small.{0} w.1.Completion := uniform_small_zero _
    let eK := placeCompletionAdic P
    let eUnits : (P.adicCompletion K)ˣ ≃* v.Completionˣ :=
      Units.mapEquiv eK.symm.toMulEquiv
    have hnorm : (eUnits y) ^ p ∈
        normSubgroup v.Completion w.1.Completion :=
      pow_subgroup_small p v.Completion w.1.Completion
        hlocalExponent (eUnits y)
    have hrange := completion_norm_range
      (K := K) (L := L) P Q w.1 w.2 model.isEquiv_upper
        (inferInstance : Module.Finite v.Completion w.1.Completion)
    have hcompletion : y ^ p ∈
        (finiteCompletionNorm (K := K) (L := L) P Q).range := by
      rw [← hrange]
      change (Units.map eK.symm.toRingHom y) ^ p ∈
        normSubgroup v.Completion w.1.Completion at hnorm
      change Units.map eK.symm.toRingHom (y ^ p) ∈
        normSubgroup v.Completion w.1.Completion
      rw [map_pow]
      exact hnorm
    exact lift_completion_range
      (K := K) (L := L) P Q (y ^ p) hcompletion
  · intro v x hx
    obtain ⟨y, rfl⟩ := hx
    let w := chosenUpperPlace (K := K) (L := L) v
    let N := (infiniteCompletionNorm (K := K) (L := L) v w).range
    let D := absoluteValueDecomposition v.1 w.1.1
    let artin : (v.1.Completionˣ ⧸ N) ≃* D :=
      infinitePlaceArtin v w
    have hquotient : QuotientGroup.mk' N (y ^ p) = 1 := by
      apply artin.injective
      apply Subtype.ext
      simpa only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one] using
        hexponent ((artin (QuotientGroup.mk' N y) : D) : Gal(L/K))
    have hcompletion : y ^ p ∈ N :=
      (QuotientGroup.eq_one_iff (y ^ p)).mp hquotient
    exact infinite_lift_range
      v w (y ^ p) hcompletion

/-- At an unramified finite prime every local unit has a norm lift made of
upper local units. -/
theorem unramifiedUnitBridge :
    UnramifiedUnitBridge.{u} := by
  intro K L _ _ _ _ _ _ P hUpper x hx
  let Q := chosenPrimeFactor (K := K) (L := L) P
  exact norm_lift_unramified
    (K := K) (L := L) P Q (hUpper Q) x hx

/-- **Lemma VII.6.4.** -/
theorem localBridgesStatement : (∀ (p : ℕ) (K L : Type u)
      [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L],
      (∀ sigma : Gal(L/K), sigma ^ p = 1) →
      ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
        (∀ v : InfinitePlace K,
          (Sum.inr v : NumberFieldPlace K) ∈ S) →
        SelectedLocallyTrivial K L T →
        (∀ Q : FinitePrime L,
          (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
            Algebra.IsUnramifiedAt (OK K) Q.asIdeal) →
        ideleSubgroup K p S T ≤
          ideleNormSubgroup (K := K) (L := L)) :=
  lift_local_cases
    powerLocalBridge unramifiedUnitBridge

end

end Submission.CField.KNIndex
