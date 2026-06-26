import Towers.ClassField.NormCorrespondence.ExistenceConsequences
import Towers.ClassField.LocalExistence.ValuationClassification
import Towers.NumberTheory.Locals.RamificationGroups
import Towers.FieldTheory.ConductorNineCleanup

/-!
# Local reciprocity and integral inertia

This file supplies the normalization bridge needed by the conductor-nine
cleanup.  Its first step is the valuation-theoretic classification of norm
groups containing all local units: local reciprocity identifies their
extensions with the canonical unramified extensions.
-/

noncomputable section

namespace Towers
namespace TBluepr

open ValuativeRel
open Towers.CField.LFTheory
open Towers.CField.LExist
open Towers.CField.LBrauer
open Towers.NumberTheory.Milne

universe u v

/-- The spectral norm is invariant under a base-field algebra equivalence,
including when the source and target are presented as different types. -/
theorem spectral_alg_equiv
    (K : Type u) [NormedField K]
    (E F : Type*) [Field E] [Field F] [Algebra K E] [Algebra K F]
    (e : E ≃ₐ[K] F) (x : E) :
    spectralNorm K E x = spectralNorm K F (e x) := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

/-- Finiteness and formal unramifiedness of spectral valuation integers are
invariant under a base-field algebra equivalence. -/
theorem spectral_integer_formally
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (E F : Type*) [Field E] [Field F] [Algebra K E] [Algebra K F]
    [FiniteDimensional K E] [FiniteDimensional K F]
    (e : E ≃ₐ[K] F) :
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := E)) :=
      spectralValuationExtension K E
    letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
    letI : NontriviallyNormedField F :=
      FLExt.nontriviallyNormedField K F
    letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
    letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := F)) :=
      spectralValuationExtension K F
    let A := Valuation.integer (ValuativeRel.valuation K)
    let OE := Valuation.integer (NormedField.valuation (K := E))
    let OF := Valuation.integer (NormedField.valuation (K := F))
    letI : Algebra A OE := valuativeSpectralAlgebra K E
    letI : Algebra A OF := valuativeSpectralAlgebra K F
    (Module.Finite A OE ∧ Algebra.FormallyUnramified A OE) →
      Module.Finite A OF ∧ Algebra.FormallyUnramified A OF := by
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    spectralValuationExtension K E
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := F)) :=
    spectralValuationExtension K F
  let A := Valuation.integer (ValuativeRel.valuation K)
  let OE := Valuation.integer (NormedField.valuation (K := E))
  let OF := Valuation.integer (NormedField.valuation (K := F))
  letI : Algebra A OE := valuativeSpectralAlgebra K E
  letI : Algebra A OF := valuativeSpectralAlgebra K F
  let eIntRing : OE ≃+* OF := e.toRingEquiv.restrict OE OF (by
    intro x
    change spectralNorm K E x ≤ 1 ↔ spectralNorm K F (e x) ≤ 1
    rw [spectral_alg_equiv K E F e x])
  let eInt : OE ≃ₐ[A] OF := AlgEquiv.ofRingEquiv (f := eIntRing) (by
    intro a
    apply Subtype.ext
    change e (algebraMap K E (a : K)) = algebraMap K F (a : K)
    exact e.commutes (a : K))
  change (Module.Finite A OE ∧ Algebra.FormallyUnramified A OE) →
    Module.Finite A OF ∧ Algebra.FormallyUnramified A OF
  intro h
  letI : Module.Finite A OE := h.1
  letI : Algebra.FormallyUnramified A OE := h.2
  exact ⟨Module.Finite.equiv eInt.toLinearEquiv,
    Algebra.FormallyUnramified.of_equiv eInt⟩

/-- A finite-index local norm group containing all valuation units is an
order-congruence subgroup. -/
theorem mod_ker_units
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (hrec : LocalReciprocityLaw K)
    (E : FASubext K)
    (hU : localUnitSubgroup K ≤ E.normGroup) :
    ∃ n : ℕ, n ≠ 0 ∧
      E.normGroup = (localOrderMod K n).ker := by
  let ord : Additive Kˣ →+ ℤ := localUnitOrder K
  let N : AddSubgroup (Additive Kˣ) := E.normGroup.toAddSubgroup
  have hker : ord.ker ≤ N := by
    intro x hx
    change x.toMul ∈ E.normGroup
    apply hU
    rw [local_order_zero]
    exact hx
  letI : E.normGroup.FiniteIndex :=
    E.normgr_finin_local K hrec
  letI : N.FiniteIndex := by
    refine ⟨?_⟩
    rw [show N.index = E.normGroup.index by
      exact Subgroup.index_toAddSubgroup]
    exact Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨n, hn, hN⟩ :=
    comap_zmultiples_ker
      ord (local_order_surjective K) N hker
  letI : NeZero n := ⟨hn⟩
  refine ⟨n, hn, ?_⟩
  ext x
  change Additive.ofMul x ∈ N ↔
    Additive.ofMul x ∈
      Subgroup.toAddSubgroup (localOrderMod K n).ker
  rw [hN]
  change localUnitOrder K (Additive.ofMul x) ∈
      AddSubgroup.zmultiples (n : ℤ) ↔ _
  rw [Int.mem_zmultiples_iff]
  change (n : ℤ) ∣ localUnitOrder K (Additive.ofMul x) ↔
    x ∈ (localOrderMod K n).ker
  rw [mod_ker_dvd]

/-- Under local reciprocity, a finite abelian subextension whose norm group
contains all local units is the canonical unramified extension of its
degree. -/
theorem abelian_subextension_unramified
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (hrec : LocalReciprocityLaw K)
    (E : FASubext K)
    (hU : localUnitSubgroup K ≤ E.normGroup) :
    E.IsUnramified K := by
  obtain ⟨n, hn, hnorm⟩ :=
    mod_ker_units
      K hrec E hU
  letI : NeZero n := ⟨hn⟩
  have hnorm' : E.normGroup =
      (canonicalUnramifiedSubextension K n).normGroup := by
    rw [hnorm,
      unramified_subextension_ker]
  let hNorm := norm_correspondence_reciprocity hrec
  have hE : E = canonicalUnramifiedSubextension K n := by
    apply hNorm.normGroup_bijective.1
    exact Subtype.ext hnorm'
  rw [hE]
  exact unramified_subextension K n

set_option maxHeartbeats 2000000 in
-- The proof constructs the integral stage explicitly inside the ambient extension.
/-- A finite intermediate field which is algebra-equivalent to an intrinsically
unramified local extension is fixed by ambient integral inertia. -/
theorem spectral_intermediate_fixed
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (L : Type v) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (E : IntermediateField K L)
    [FiniteDimensional K E]
    (F : Type*) [Field F] [Algebra K F] [FiniteDimensional K F]
    (e : E ≃ₐ[K] F)
    (hunr :
      letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
      letI : NontriviallyNormedField F :=
        FLExt.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : (NormedField.valuation (K := K)).HasExtension
          (NormedField.valuation (K := F)) := spectralValuationExtension K F
      let A := Valuation.integer (NormedField.valuation (K := K))
      let OF := Valuation.integer (NormedField.valuation (K := F))
      Module.Finite A OF ∧ Algebra.FormallyUnramified A OF) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      FLExt.nonarchimedeanLocalField K L
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    let A := Valuation.integer (NormedField.valuation (K := K))
    let B := Valuation.integer (NormedField.valuation (K := L))
    letI : IsIntegralClosure B A L :=
      FLExt.spectral_integer_closure K L
    letI : MulSemiringAction Gal(L/K) B :=
      IsIntegralClosure.MulSemiringAction A K L B
    E ≤ inertiaFixedField (K := K) (L := L) (IsLocalRing.maximalIdeal B) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  let A := Valuation.integer (NormedField.valuation (K := K))
  let B := Valuation.integer (NormedField.valuation (K := L))
  letI : Algebra B L := B.subtype.toAlgebra
  letI : IsFractionRing A K :=
    (Valuation.integer.integers
      (NormedField.valuation (K := K))).isFractionRing
  letI : IsFractionRing B L :=
    (Valuation.integer.integers
      (NormedField.valuation (K := L))).isFractionRing
  letI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure B A L :=
    FLExt.spectral_integer_closure K L
  letI : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  letI : IsNoetherianRing B :=
    isNoetherianRing_of_ringEquiv
      (Valuation.integer (ValuativeRel.valuation L))
      (RingEquiv.subringCongr (valuative_integer_norm L))
  letI : SMulDistribClass Gal(L/K) B L := by infer_instance
  letI : Algebra.IsIntegral A B :=
    IsIntegralClosure.isIntegral_algebra A L
  letI : IsGaloisGroup Gal(L/K) A B :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) A B K L
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := F)) := spectralValuationExtension K F
  let OF := Valuation.integer (NormedField.valuation (K := F))
  letI : Algebra OF F := OF.subtype.toAlgebra
  letI : IsFractionRing OF F :=
    (Valuation.integer.integers
      (NormedField.valuation (K := F))).isFractionRing
  let f : OF →ₐ[A] B :=
    { toFun := fun x => ⟨E.val (e.symm x), by
          change spectralNorm K L (E.val (e.symm x)) ≤ 1
          calc
            _ = spectralNorm K E (e.symm x) := by
              simpa using
                (spectralNorm.eq_of_tower (K := K) (L := L)
                  (e.symm x)).symm
            _ = spectralNorm K F x := by
              simpa using spectral_alg_equiv K E F e (e.symm x)
            _ ≤ 1 := by
              have hx := x.property
              change spectralNorm K F (x : F) ≤ 1 at hx
              exact hx⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp
      commutes' := fun a => by
        apply Subtype.ext
        change E.val (e.symm (algebraMap K F (a : K))) =
          algebraMap K L (a : K)
        rw [e.symm.commutes]
        rfl }
  let U : Subalgebra A B := f.range
  let eOU : OF ≃ₐ[A] U := AlgEquiv.ofInjective f (by
    intro x y hxy
    have hL : E.val (e.symm (x : F)) = E.val (e.symm (y : F)) := by
      exact congrArg (fun z : B => (z : L)) hxy
    have hE : e.symm (x : F) = e.symm (y : F) := E.val.injective hL
    have hF : (x : F) = (y : F) := e.symm.injective hE
    apply Subtype.ext
    exact hF)
  have hOF := hunr
  change Module.Finite A OF ∧ Algebra.FormallyUnramified A OF at hOF
  letI : Algebra.FormallyUnramified A OF := hOF.2
  letI : Algebra.FormallyUnramified A U :=
    Algebra.FormallyUnramified.of_equiv eOU
  have hfrac : fractionFieldSubalgebra A B K L U = E := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨u, hu, rfl⟩
      rcases hu with ⟨x, rfl⟩
      exact (e.symm x).property
    · intro x hx
      let xE : E := ⟨x, hx⟩
      let yF : F := e xE
      obtain ⟨a, b, _hb, hab⟩ := IsFractionRing.div_surjective OF yF
      have haU : f a ∈ U := ⟨a, rfl⟩
      have hbU : f b ∈ U := ⟨b, rfl⟩
      let F0 := fractionFieldSubalgebra A B K L U
      have haF : algebraMap B L (f a) ∈ F0 :=
        IntermediateField.subset_adjoin K
          ((algebraMap B L) '' (U : Set B)) ⟨f a, haU, rfl⟩
      have hbF : algebraMap B L (f b) ∈ F0 :=
        IntermediateField.subset_adjoin K
          ((algebraMap B L) '' (U : Set B)) ⟨f b, hbU, rfl⟩
      have hdiv : algebraMap B L (f a) / algebraMap B L (f b) = x := by
        dsimp [f]
        have hab' : (a : F) / (b : F) = e xE := by simpa using hab
        calc
          E.val (e.symm (a : F)) / E.val (e.symm (b : F)) =
              E.val (e.symm (a : F) / e.symm (b : F)) :=
            (map_div₀ E.val (e.symm (a : F)) (e.symm (b : F))).symm
          _ = E.val (e.symm ((a : F) / (b : F))) :=
            congrArg E.val (map_div₀ e.symm (a : F) (b : F)).symm
          _ = E.val (e.symm (e xE)) := by rw [hab']
          _ = x := congrArg Subtype.val (e.symm_apply_apply xE)
      rw [← hdiv]
      exact F0.div_mem haF hbF
  rw [← hfrac]
  exact fraction_subalgebra_fixed
    (A := A) (B := B) (K := K) (L := L) U

set_option synthInstance.maxHeartbeats 500000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option maxHeartbeats 3000000 in
-- Fixed fields and local norm correspondence generate a large instance telescope.
/-- Local reciprocity sends the full valuation-unit subgroup onto the
integral inertia subgroup of every finite abelian local extension. -/
theorem reciprocity_inertia_integral
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (hrec : LocalReciprocityLaw K)
    (L : FASubext K) :
    letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
    letI : NontriviallyNormedField L.1 :=
      FLExt.nontriviallyNormedField K L.1
    letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
    letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
    letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
    letI : IsNonarchimedeanLocalField L.1 :=
      FLExt.nonarchimedeanLocalField K L.1
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L.1)) :=
      spectralValuationExtension K L.1
    let A := Valuation.integer (NormedField.valuation (K := K))
    let B := Valuation.integer (NormedField.valuation (K := L.1))
    letI : IsIntegralClosure B A L.1 :=
      FLExt.spectral_integer_closure K L.1
    letI : MulSemiringAction Gal(L.1/K) B :=
      IsIntegralClosure.MulSemiringAction A K L.1 B
    reciprocityInertiaSubgroup K hrec.choose L =
      (IsLocalRing.maximalIdeal B).inertia Gal(L.1/K) := by
  let recMap := hrec.choose
  have hrecMap : IsReciprocityMap K recMap := hrec.choose_spec.1
  letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
  letI : NontriviallyNormedField L.1 :=
    FLExt.nontriviallyNormedField K L.1
  letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
  letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
  letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
  letI : IsNonarchimedeanLocalField L.1 :=
    FLExt.nonarchimedeanLocalField K L.1
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L.1)) :=
    spectralValuationExtension K L.1
  let A := Valuation.integer (NormedField.valuation (K := K))
  let B := Valuation.integer (NormedField.valuation (K := L.1))
  letI : IsIntegralClosure B A L.1 :=
    FLExt.spectral_integer_closure K L.1
  letI : MulSemiringAction Gal(L.1/K) B :=
    IsIntegralClosure.MulSemiringAction A K L.1 B
  let H := reciprocityInertiaSubgroup K recMap L
  letI : H.Normal := by dsimp [H]; infer_instance
  letI : CommGroup Gal(L.1/K) :=
    { (inferInstance : Group Gal(L.1/K)) with
      mul_comm := mul_comm' }
  let E0 : IntermediateField K L.1 := IntermediateField.fixedField H
  letI : FiniteDimensional K E0 :=
    Module.Finite.of_injective E0.val.toLinearMap Subtype.val_injective
  letI : IsGalois K E0 := IsGalois.of_fixedField_normal_subgroup H
  let qAut : Gal(L.1/K) ⧸ H ≃* Gal(E0/K) :=
    IsGalois.normalAutEquivQuotient H
  letI : IsMulCommutative Gal(E0/K) := by
    refine ⟨⟨fun sigma tau => ?_⟩⟩
    apply qAut.symm.injective
    simpa only [map_mul] using mul_comm (qAut.symm sigma) (qAut.symm tau)
  letI : CommGroup Gal(E0/K) :=
    { (inferInstance : Group Gal(E0/K)) with
      mul_comm := mul_comm' }
  let Efield : IntermediateField K (SeparableClosure K) :=
    IntermediateField.lift E0
  let e : E0 ≃ₐ[K] Efield := IntermediateField.liftAlgEquiv E0
  letI : Module.Finite K Efield := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K Efield := IsGalois.of_algEquiv e
  let Efg : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := Efield
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let eAut : Gal(E0/K) ≃* Gal(Efg/K) := e.autCongr
  letI : IsMulCommutative Gal(Efg/K) := by
    refine ⟨⟨fun sigma tau => ?_⟩⟩
    apply eAut.symm.injective
    simpa only [map_mul] using mul_comm (eAut.symm sigma) (eAut.symm tau)
  let E : FASubext K :=
    { finiteIntermediateField := Efg }
  have hU : localUnitSubgroup K ≤ E.normGroup := by
    intro u hu
    rw [← reciprocity_hom_ker recMap hrecMap.2 E]
    have hrestriction :
        finiteReciprocityHom recMap E u = 1 ↔
          finiteReciprocityHom recMap L u ∈ H := by
      obtain ⟨sigma, hsigma⟩ :=
        QuotientGroup.mk'_surjective
          (Subgroup.topologicalClosure
            (commutator (LocalAbsoluteGalois K)))
          (recMap u)
      change localAbelianRestriction E (recMap u) = 1 ↔
        localAbelianRestriction L (recMap u) ∈ H
      rw [← hsigma]
      change localAbelianRestriction E (localAbelianizationMap K sigma) = 1 ↔
        localAbelianRestriction L (localAbelianizationMap K sigma) ∈ H
      rw [abelian_restriction_quotient,
        abelian_restriction_quotient]
      change (AlgEquiv.restrictNormalHom E.intermediateField sigma = 1) ↔
        AlgEquiv.restrictNormalHom
          L.finiteIntermediateField.toIntermediateField sigma ∈ H
      rw [← MonoidHom.mem_ker,
        IntermediateField.restrictNormalHom_ker]
      change sigma ∈ Efield.fixingSubgroup ↔ _
      rw [fixing_lift_restrict L E0 sigma,
        IntermediateField.fixingSubgroup_fixedField]
    apply hrestriction.mpr
    exact ⟨u, hu, rfl⟩
  have hEunr : E.IsUnramified K :=
    abelian_subextension_unramified
      K hrec E hU
  have hfield : E0 ≤ inertiaFixedField (K := K) (L := L.1)
      (IsLocalRing.maximalIdeal B) :=
    spectral_intermediate_fixed
      K L.1 E0 Efield e hEunr
  have hIle : (IsLocalRing.maximalIdeal B).inertia Gal(L.1/K) ≤ H := by
    have hfix := IntermediateField.fixingSubgroup_antitone hfield
    simpa [E0, inertiaFixedField,
      IntermediateField.fixingSubgroup_fixedField] using hfix
  have hHle : H ≤
      (IsLocalRing.maximalIdeal B).inertia Gal(L.1/K) := by
    dsimp [H, recMap]
    exact reciprocity_subgroup_integral
      K hrec.choose hrec.choose_spec.1 L
  exact le_antisymm hHle hIle

set_option synthInstance.maxHeartbeats 500000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option maxHeartbeats 2000000 in
-- Inverting finite reciprocity expands the fixed-field norm correspondence.
/-- Every integral-inertia element in a finite abelian local extension is
the Artin symbol of a valuation unit. -/
theorem reciprocity_integral_inertia
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (hrec : LocalReciprocityLaw K)
    (L : FASubext K) :
    letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
    letI : NontriviallyNormedField L.1 :=
      FLExt.nontriviallyNormedField K L.1
    letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
    letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
    letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
    letI : IsNonarchimedeanLocalField L.1 :=
      FLExt.nonarchimedeanLocalField K L.1
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L.1)) :=
      spectralValuationExtension K L.1
    let A := Valuation.integer (NormedField.valuation (K := K))
    let B := Valuation.integer (NormedField.valuation (K := L.1))
    letI : IsIntegralClosure B A L.1 :=
      FLExt.spectral_integer_closure K L.1
    letI : MulSemiringAction Gal(L.1/K) B :=
      IsIntegralClosure.MulSemiringAction A K L.1 B
    ∀ sigma : (IsLocalRing.maximalIdeal B).inertia Gal(L.1/K),
      ∃ u : localUnitSubgroup K,
        finiteReciprocityHom hrec.choose L u = sigma.1 := by
  dsimp only
  letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
  letI : NontriviallyNormedField L.1 :=
    FLExt.nontriviallyNormedField K L.1
  letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
  letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
  letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
  letI : IsNonarchimedeanLocalField L.1 :=
    FLExt.nonarchimedeanLocalField K L.1
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L.1)) :=
    spectralValuationExtension K L.1
  let A := Valuation.integer (NormedField.valuation (K := K))
  let B := Valuation.integer (NormedField.valuation (K := L.1))
  letI : IsIntegralClosure B A L.1 :=
    FLExt.spectral_integer_closure K L.1
  letI : MulSemiringAction Gal(L.1/K) B :=
    IsIntegralClosure.MulSemiringAction A K L.1 B
  intro sigma
  have hsigma : sigma.1 ∈
      reciprocityInertiaSubgroup K hrec.choose L := by
    have heq : reciprocityInertiaSubgroup K hrec.choose L =
        (IsLocalRing.maximalIdeal B).inertia Gal(L.1/K) :=
      reciprocity_inertia_integral K hrec L
    exact heq.symm ▸ sigma.property
  rcases hsigma with ⟨u, hu, heq⟩
  exact ⟨⟨u, hu⟩, heq⟩

/-- If a cyclic quotient is obtained by dividing out a subgroup whose image
is central, then the image of the whole group is commutative. -/
theorem monoid_commutative_center
    {G : Type u} [Group G] {E : Type v} [Group E]
    (I : Subgroup G) [I.Normal] [IsCyclic (G ⧸ I)]
    (f : G →* E)
    (hI : ∀ i : I, f i.1 ∈ Subgroup.center E) :
    ∀ x y : f.range, x * y = y * x := by
  obtain ⟨qgen, hqgen⟩ :=
    (IsCyclic.exists_generator : ∃ qgen : G ⧸ I,
      ∀ x : G ⧸ I, x ∈ Subgroup.zpowers qgen)
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective I qgen
  intro x y
  obtain ⟨gx, hgxval⟩ := x.property
  obtain ⟨gy, hgyval⟩ := y.property
  obtain ⟨m, hm⟩ :=
    Subgroup.mem_zpowers_iff.mp (hqgen (QuotientGroup.mk' I gx))
  obtain ⟨n, hn⟩ :=
    Subgroup.mem_zpowers_iff.mp (hqgen (QuotientGroup.mk' I gy))
  let ix : I := ⟨gx * (t ^ m)⁻¹, by
    rw [← QuotientGroup.ker_mk' I, MonoidHom.mem_ker,
      map_mul, map_inv, map_zpow, ht, hm, mul_inv_cancel]⟩
  let iy : I := ⟨gy * (t ^ n)⁻¹, by
    rw [← QuotientGroup.ker_mk' I, MonoidHom.mem_ker,
      map_mul, map_inv, map_zpow, ht, hn, mul_inv_cancel]⟩
  have hgx : gx = ix.1 * t ^ m := by
    dsimp [ix]
    group
  have hgy : gy = iy.1 * t ^ n := by
    dsimp [iy]
    group
  have hfgx : f gx = f ix.1 * f t ^ m := by
    rw [hgx, map_mul, map_zpow]
  have hfgy : f gy = f iy.1 * f t ^ n := by
    rw [hgy, map_mul, map_zpow]
  have hix (z : E) : Commute (f ix.1) z :=
    (Subgroup.mem_center_iff.mp (hI ix) z).symm
  have hiy (z : E) : Commute (f iy.1) z :=
    (Subgroup.mem_center_iff.mp (hI iy) z).symm
  have hpow : Commute (f t ^ m) (f t ^ n) :=
    (Commute.refl (f t)).zpow_zpow m n
  apply Subtype.ext
  change (x : E) * (y : E) = (y : E) * (x : E)
  rw [← hgxval, ← hgyval, hfgx, hfgy]
  exact (((hix (f iy.1)).mul_left ((hiy (f t ^ m)).symm)).mul_right
    ((hix (f t ^ n)).mul_left hpow)).eq

set_option maxHeartbeats 3000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The spectral integral model creates a large quotient instance tower.
/-- The quotient of a finite local Galois group by integral inertia is
cyclic.  This is the residue-field Frobenius quotient, expressed using the
spectral integral model used by the local-reciprocity bridge. -/
theorem integral_inertia_cyclic
    (K F : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] :
    letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
    letI : NontriviallyNormedField F :=
      FLExt.nontriviallyNormedField K F
    letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
    letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel F := FLExt.valuativeRel K F
    letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
    letI : IsNonarchimedeanLocalField F :=
      FLExt.nonarchimedeanLocalField K F
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := F)) := spectralValuationExtension K F
    let A := Valuation.integer (NormedField.valuation (K := K))
    let B := Valuation.integer (NormedField.valuation (K := F))
    letI : IsIntegralClosure B A F :=
      FLExt.spectral_integer_closure K F
    letI : MulSemiringAction Gal(F/K) B :=
      IsIntegralClosure.MulSemiringAction A K F B
    let I := (IsLocalRing.maximalIdeal B).inertia Gal(F/K)
    ∀ hnormal : I.Normal,
      letI : I.Normal := hnormal
      IsCyclic (Gal(F/K) ⧸ I) := by
  dsimp only
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := FLExt.valuativeRel K F
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField K F
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := F)) := spectralValuationExtension K F
  let A := Valuation.integer (NormedField.valuation (K := K))
  let B := Valuation.integer (NormedField.valuation (K := F))
  letI : IsFractionRing B F :=
    (Valuation.integer.integers
      (NormedField.valuation (K := F))).isFractionRing
  letI : IsScalarTower A K F := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure B A F :=
    FLExt.spectral_integer_closure K F
  letI : MulSemiringAction Gal(F/K) B :=
    IsIntegralClosure.MulSemiringAction A K F B
  let p := IsLocalRing.maximalIdeal A
  let P := IsLocalRing.maximalIdeal B
  let I := P.inertia Gal(F/K)
  intro hnormal
  letI : I.Normal := hnormal
  have hAF : Valuation.integer (ValuativeRel.valuation K) = A := by
    ext x
    simp only [A, Valuation.mem_integer_iff]
    rw [← (ValuativeRel.valuation K).vle_one_iff,
      ← (NormedField.valuation (K := K)).vle_one_iff]
  letI : IsDiscreteValuationRing A := by
    rw [← hAF]
    exact discrete_valuation_ring K
  letI : Module.Finite A B := IsIntegralClosure.finite A K F B
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).2 <| by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective A K
      apply (algebraMap K F).injective
      rw [← IsScalarTower.algebraMap_apply A K F a,
        ← IsScalarTower.algebraMap_apply A K F b,
        IsScalarTower.algebraMap_apply A B F a,
        IsScalarTower.algebraMap_apply A B F b]
      exact congrArg (algebraMap B F) hab
  letI : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  have hBF : Valuation.integer (ValuativeRel.valuation F) = B := by
    ext x
    simp only [B, Valuation.mem_integer_iff]
    rw [← (ValuativeRel.valuation F).vle_one_iff,
      ← (NormedField.valuation (K := F)).vle_one_iff]
  letI : IsDiscreteValuationRing B := by
    rw [← hBF]
    exact discrete_valuation_ring F
  letI : HenselianLocalRing B := by
    rw [← hBF]
    exact integer_henselian_ring F
  letI : IsGaloisGroup Gal(F/K) A B :=
    IsGaloisGroup.of_isFractionRing Gal(F/K) A B K F
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  letI : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  letI : P.LiesOver p := by
    exact (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm
  let e : Gal(F/K) ⧸ I ≃*
      (B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P) :=
    inertiaResidueGalois (G := Gal(F/K)) p hp
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  letI : Finite (A ⧸ p) := by
    letI : Finite (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation K))) :=
      local_field_residue K
    exact Finite.of_equiv
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation K)))
      (IsLocalRing.ResidueField.mapEquiv
        (valuativeIntegerNorm K)).toEquiv
  letI : Fintype (A ⧸ p) := Fintype.ofFinite _
  letI : Module.Finite (A ⧸ p) (B ⧸ P) := by infer_instance
  letI : Finite (B ⧸ P) := Module.finite_of_finite (A ⧸ p)
  letI : Fintype (B ⧸ P) := Fintype.ofFinite _
  have hcyclicResidue : IsCyclic ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) :=
    Towers.galois_group_cyclic
      (k := A ⧸ p) (K := B ⧸ P)
  exact e.isCyclic.mpr hcyclicResidue

set_option maxHeartbeats 3000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- The quotient field, lifted local layer, and both integral models are dependent.
/-- Local reciprocity simultaneously parametrizes any two characters of a
finite local Galois group as soon as their joint image is abelian. -/
theorem joint_parametrization_range
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (hrec : LocalReciprocityLaw K)
    (W : Type u) [Field W] [Algebra K W]
    [FiniteDimensional K W] [IsGalois K W]
    {R : Type*} [Group R] {A : Type*} [Group A]
    {B : Type*} [Group B]
    (restriction : Gal(W/K) →* R) (lift : Gal(W/K) →* A)
    (target : A →* B)
    (hcomm : ∀ x y : (restriction.prod lift).range, x * y = y * x) :
    letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
    letI : NontriviallyNormedField W :=
      FLExt.nontriviallyNormedField K W
    letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
    letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel W := FLExt.valuativeRel K W
    letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
    letI : IsNonarchimedeanLocalField W :=
      FLExt.nonarchimedeanLocalField K W
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := W)) := spectralValuationExtension K W
    let AK := Valuation.integer (NormedField.valuation (K := K))
    let BW := Valuation.integer (NormedField.valuation (K := W))
    letI : IsIntegralClosure BW AK W :=
      FLExt.spectral_integer_closure K W
    letI : MulSemiringAction Gal(W/K) BW :=
      IsIntegralClosure.MulSemiringAction AK K W BW
    let I := (IsLocalRing.maximalIdeal BW).inertia Gal(W/K)
    (∀ i : I, target (lift i.1) = 1) →
      ∃ unitRestriction : localUnitSubgroup K →* R,
        ∃ unitLift : localUnitSubgroup K →* A,
          (∀ unit : localUnitSubgroup K,
            (unitRestriction unit, unitLift unit) ∈
              (restriction.prod lift).range) ∧
            (∀ unit : localUnitSubgroup K, target (unitLift unit) = 1) ∧
              ∀ sigma : I,
                ∃ unit : localUnitSubgroup K,
                  unitRestriction unit = restriction sigma.1 ∧
                    unitLift unit = lift sigma.1 := by
  letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
  letI : NontriviallyNormedField W :=
    FLExt.nontriviallyNormedField K W
  letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
  letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel W := FLExt.valuativeRel K W
  letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
  letI : IsNonarchimedeanLocalField W :=
    FLExt.nonarchimedeanLocalField K W
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := W)) := spectralValuationExtension K W
  let AK := Valuation.integer (NormedField.valuation (K := K))
  let BW := Valuation.integer (NormedField.valuation (K := W))
  letI : IsIntegralClosure BW AK W :=
    FLExt.spectral_integer_closure K W
  letI : MulSemiringAction Gal(W/K) BW :=
    IsIntegralClosure.MulSemiringAction AK K W BW
  let I := (IsLocalRing.maximalIdeal BW).inertia Gal(W/K)
  let joint := restriction.prod lift
  let H := joint.ker
  letI : H.Normal := by dsimp [H]; infer_instance
  let E0 : IntermediateField K W := IntermediateField.fixedField H
  letI : FiniteDimensional K E0 :=
    Module.Finite.of_injective E0.val.toLinearMap Subtype.val_injective
  letI : IsGalois K E0 := IsGalois.of_fixedField_normal_subgroup H
  let qAut : Gal(W/K) ⧸ H ≃* Gal(E0/K) :=
    IsGalois.normalAutEquivQuotient H
  let qRange : Gal(W/K) ⧸ H ≃* joint.range :=
    QuotientGroup.quotientKerEquivRange joint
  let jAut : Gal(E0/K) ≃* joint.range := qAut.symm.trans qRange
  letI : IsMulCommutative Gal(E0/K) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply jAut.injective
    simpa only [map_mul] using hcomm (jAut x) (jAut y)
  letI : CommGroup Gal(E0/K) :=
    { (inferInstance : Group Gal(E0/K)) with
      mul_comm := mul_comm' }
  let i : E0 →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let Efield : IntermediateField K (SeparableClosure K) := i.fieldRange
  let e : E0 ≃ₐ[K] Efield := AlgEquiv.ofInjectiveField i
  letI : Module.Finite K Efield := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K Efield := IsGalois.of_algEquiv e
  let Efg : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := Efield
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let eAut : Gal(E0/K) ≃* Gal(Efg/K) := e.autCongr
  letI : IsMulCommutative Gal(Efg/K) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eAut.symm.injective
    simpa only [map_mul] using mul_comm (eAut.symm x) (eAut.symm y)
  letI : CommGroup Gal(Efg/K) :=
    { (inferInstance : Group Gal(Efg/K)) with
      mul_comm := mul_comm' }
  let E : FASubext K :=
    { finiteIntermediateField := Efg }
  let jointRangeE : Gal(Efg/K) →* joint.range :=
    jAut.toMonoidHom.comp eAut.symm.toMonoidHom
  let jointE : Gal(Efg/K) →* R × A :=
    ((restriction.prod lift).range.subtype).comp jointRangeE
  let unitJoint : localUnitSubgroup K →* R × A :=
    jointE.comp ((finiteReciprocityHom hrec.choose E).comp
      (localUnitSubgroup K).subtype)
  have hjoint_apply (sigma : Gal(W/K)) :
      jointE (eAut (AlgEquiv.restrictNormalHom E0 sigma)) = joint sigma := by
    let tau0 : Gal(E0/K) := AlgEquiv.restrictNormalHom E0 sigma
    change ((restriction.prod lift).range.subtype)
      (jAut (eAut.symm (eAut tau0))) = joint sigma
    rw [eAut.symm_apply_apply]
    have hqAut : qAut.symm tau0 = QuotientGroup.mk' H sigma := by
      apply qAut.injective
      rw [qAut.apply_symm_apply]
      rfl
    rw [show jAut tau0 = qRange (QuotientGroup.mk' H sigma) by
      change qRange (qAut.symm tau0) = _
      rw [hqAut]]
    rfl
  refine fun hkill => ⟨(MonoidHom.fst R A).comp unitJoint,
    (MonoidHom.snd R A).comp unitJoint, ?_, ?_, ?_⟩
  · intro unit
    change unitJoint unit ∈ joint.range
    exact (jointRangeE
      (finiteReciprocityHom hrec.choose E unit)).property
  · intro unit
    let baseE : Gal(Efg/K) →* B :=
      target.comp ((MonoidHom.snd R A).comp jointE)
    let J := baseE.ker
    letI : J.Normal := by dsimp [J]; infer_instance
    let F0 : IntermediateField K Efield := IntermediateField.fixedField J
    letI : FiniteDimensional K F0 :=
      Module.Finite.of_injective F0.val.toLinearMap Subtype.val_injective
    letI : IsGalois K F0 := IsGalois.of_fixedField_normal_subgroup J
    let Ffield : IntermediateField K (SeparableClosure K) :=
      IntermediateField.lift F0
    let eF : F0 ≃ₐ[K] Ffield := IntermediateField.liftAlgEquiv F0
    letI : Module.Finite K Ffield := Module.Finite.equiv eF.toLinearEquiv
    letI : IsGalois K Ffield := IsGalois.of_algEquiv eF
    let Ffg : FiniteGaloisIntermediateField K (SeparableClosure K) :=
      { toIntermediateField := Ffield
        finiteDimensional := inferInstance
        isGalois := inferInstance }
    let eFAut : Gal(F0/K) ≃* Gal(Ffg/K) := eF.autCongr
    let qF : Gal(Efield/K) ⧸ J ≃* Gal(F0/K) :=
      IsGalois.normalAutEquivQuotient J
    letI : IsMulCommutative Gal(Ffg/K) := by
      refine ⟨⟨fun x y => ?_⟩⟩
      apply eFAut.symm.injective
      apply qF.symm.injective
      simpa only [map_mul] using mul_comm (qF.symm (eFAut.symm x))
        (qF.symm (eFAut.symm y))
    let F : FASubext K :=
      { finiteIntermediateField := Ffg }
    let iFW : F0 →ₐ[K] W :=
      E0.val.comp (e.symm.toAlgHom.comp F0.val)
    let FW : IntermediateField K W := iFW.fieldRange
    let eFW : F0 ≃ₐ[K] FW := AlgEquiv.ofInjectiveField iFW
    have hFWfixed : FW ≤ IntermediateField.fixedField I := by
      rintro _ ⟨x, rfl⟩
      rw [IntermediateField.mem_fixedField_iff]
      intro sigma _hsigma
      have htauJ : eAut (AlgEquiv.restrictNormalHom E0 sigma) ∈ J := by
        change target
          (((MonoidHom.snd R A) (jointE
            (eAut (AlgEquiv.restrictNormalHom E0 sigma))))) = 1
        rw [hjoint_apply]
        exact hkill ⟨sigma, _hsigma⟩
      have hxfix := x.property
        ⟨eAut (AlgEquiv.restrictNormalHom E0 sigma), htauJ⟩
      have hxfixE : AlgEquiv.restrictNormalHom E0 sigma (e.symm x) =
          e.symm x := by
        apply e.injective
        simpa [eAut] using hxfix
      have hxfixW := congrArg E0.val hxfixE
      change sigma (E0.val (e.symm (x : Efield))) =
        E0.val (e.symm (x : Efield))
      exact (AlgEquiv.restrictNormalHom_apply E0 sigma
        (e.symm (x : Efield))).symm.trans hxfixW
    let fixedI : IntermediateField K W := IntermediateField.fixedField I
    let AV := Valuation.integer (ValuativeRel.valuation K)
    letI : Algebra AV BW := valuativeSpectralAlgebra K W
    letI : Algebra BW W := BW.subtype.toAlgebra
    letI : IsFractionRing BW W :=
      (Valuation.integer.integers
        (NormedField.valuation (K := W))).isFractionRing
    letI : IsScalarTower AV BW W :=
      valuativeSpectralTower K W
    letI : IsScalarTower AV K W := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsIntegralClosure BW AV W :=
      spectral_integer_valuative K W
    letI : SMulDistribClass Gal(W/K) BW W :=
      ⟨fun g b x => by
        change g ((b : W) * x) = (g • b : BW) * g x
        rw [map_mul]
        congr 1
        exact (algebraMap_galRestrictHom_apply AV K W BW g b).symm⟩
    have hUfixed : localUnitSubgroup K ≤ normSubgroup K fixedI :=
      inertia_fixed_norm K W
    letI : Algebra FW fixedI :=
      (IntermediateField.inclusion hFWfixed).toAlgebra
    letI : IsScalarTower K FW fixedI := IsScalarTower.of_algebraMap_eq' rfl
    letI : Module.Finite FW fixedI := Module.Finite.right K FW fixedI
    have hUFW : localUnitSubgroup K ≤ normSubgroup K FW := by
      intro u hu
      apply norm_subgroup_tower K fixedI FW
      exact hUfixed hu
    let eFFW : Ffield ≃ₐ[K] FW := eF.symm.trans eFW
    have hUF : localUnitSubgroup K ≤ F.normGroup := by
      intro u hu
      change (u : Kˣ) ∈ normSubgroup K Ffield
      rw [norm_alg_equiv K Ffield FW eFFW]
      exact hUFW hu
    have hrecF : finiteReciprocityHom hrec.choose F (unit : Kˣ) = 1 := by
      rw [← MonoidHom.mem_ker,
        reciprocity_hom_ker hrec.choose hrec.choose_spec.1.2 F]
      exact hUF unit.property
    obtain ⟨sigmaAbs, hsigmaAbs⟩ :=
      QuotientGroup.mk'_surjective
        (Subgroup.topologicalClosure
          (commutator (LocalAbsoluteGalois K)))
        (hrec.choose (unit : Kˣ))
    have hrecE : finiteReciprocityHom hrec.choose E (unit : Kˣ) =
        AlgEquiv.restrictNormalHom Efield sigmaAbs := by
      change localAbelianRestriction E (hrec.choose (unit : Kˣ)) = _
      rw [← hsigmaAbs]
      change localAbelianRestriction E (localAbelianizationMap K sigmaAbs) = _
      exact abelian_restriction_quotient E sigmaAbs
    have hrecF' : finiteReciprocityHom hrec.choose F (unit : Kˣ) =
        AlgEquiv.restrictNormalHom Ffield sigmaAbs := by
      change localAbelianRestriction F (hrec.choose (unit : Kˣ)) = _
      rw [← hsigmaAbs]
      change localAbelianRestriction F (localAbelianizationMap K sigmaAbs) = _
      exact abelian_restriction_quotient F sigmaAbs
    have hsigmaJ : AlgEquiv.restrictNormalHom Efield sigmaAbs ∈ J := by
      rw [← IntermediateField.fixingSubgroup_fixedField J]
      apply (fixing_lift_restrict E F0 sigmaAbs).mp
      rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]
      rw [← hrecF', hrecF]
    change baseE (finiteReciprocityHom hrec.choose E (unit : Kˣ)) = 1
    rw [hrecE]
    exact hsigmaJ
  intro sigma
  let tau0 : Gal(E0/K) := AlgEquiv.restrictNormalHom E0 sigma.1
  let tauE : Gal(Efg/K) := eAut tau0
  letI : Algebra.IsAlgebraic K Efield := Algebra.IsAlgebraic.of_finite K Efield
  letI : NontriviallyNormedField Efield :=
    FLExt.nontriviallyNormedField K Efield
  letI : NormedAlgebra K Efield := spectralNorm.normedAlgebra K Efield
  letI : IsUltrametricDist Efield := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := Efield)) := spectralValuationExtension K Efield
  let BE := Valuation.integer (NormedField.valuation (K := Efield))
  letI : IsIntegralClosure BE AK Efield :=
    FLExt.spectral_integer_closure K Efield
  letI : MulSemiringAction Gal(Efield/K) BE :=
    IsIntegralClosure.MulSemiringAction AK K Efield BE
  have htauE : tauE ∈ (IsLocalRing.maximalIdeal BE).inertia Gal(Efield/K) := by
    intro x
    dsimp only [BE]
    apply (Valuation.mem_maximalIdeal_iff Efield
      (NormedField.valuation (K := Efield))).2
    rw [NormedField.valuation_apply]
    change ‖((tauE • x - x : BE) : Efield)‖₊ < 1
    have hcoe : ((tauE • x - x : BE) : Efield) =
        tauE (x : Efield) - x := by
      change ((tauE • x : BE) : Efield) - (x : Efield) = _
      exact congrArg (fun z : Efield ↦ z - (x : Efield))
        (algebraMap.coe_smul' (B := BE) (C := Efield) tauE x)
    rw [hcoe]
    let y : E0 := e.symm (x : Efield)
    have hyInt : spectralNorm K W (E0.val y) ≤ 1 := by
      calc
        _ = spectralNorm K E0 y := by
          simpa using (spectralNorm.eq_of_tower (K := K) (L := W) y).symm
        _ = spectralNorm K Efield (e y) :=
          spectral_alg_equiv K E0 Efield e y
        _ = spectralNorm K Efield (x : Efield) := by rw [e.apply_symm_apply]
        _ ≤ 1 := by
          have hx := x.property
          change spectralNorm K Efield (x : Efield) ≤ 1 at hx
          exact hx
    let yW : BW := ⟨E0.val y, hyInt⟩
    have hamb := sigma.property yW
    have hamb' :=
      (NormedField.valuation (K := W)).mem_maximalIdeal_iff.mp hamb
    rw [NormedField.valuation_apply] at hamb'
    have hcoeW : (((sigma.1 • yW - yW : BW) : W)) =
        sigma.1 (E0.val y) - E0.val y := by
      change ((sigma.1 • yW : BW) : W) - (yW : W) = _
      exact congrArg (fun z : W ↦ z - (yW : W))
        (algebraMap.coe_smul' (B := BW) (C := W) sigma.1 yW)
    rw [hcoeW] at hamb'
    have hambReal : spectralNorm K W
        (sigma.1 (E0.val y) - E0.val y) < 1 := by
      exact_mod_cast hamb'
    have hreal : spectralNorm K Efield (tauE (x : Efield) - x) < 1 := by
      calc
        spectralNorm K Efield (tauE (x : Efield) - x) =
            spectralNorm K E0 (tau0 y - y) := by
          rw [spectral_alg_equiv K E0 Efield e]
          congr 2
          simp [tauE, tau0, eAut, y]
        _ = spectralNorm K W (E0.val (tau0 y - y)) :=
          spectralNorm.eq_of_tower (K := K) (L := W) (tau0 y - y)
        _ = spectralNorm K W
            (sigma.1 (E0.val y) - E0.val y) := by
          congr 2
          simp [tau0, AlgEquiv.restrictNormalHom_apply]
        _ < 1 := hambReal
    exact_mod_cast hreal
  obtain ⟨unit, hunit⟩ :=
    reciprocity_integral_inertia
      K hrec E ⟨tauE, htauE⟩
  refine ⟨unit, ?_⟩
  have hjoint : jointE tauE = joint sigma.1 := hjoint_apply sigma.1
  have hpair : unitJoint unit = joint sigma.1 := by
    change jointE (finiteReciprocityHom hrec.choose E unit) = joint sigma.1
    rw [hunit, hjoint]
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

set_option maxHeartbeats 3000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- This compatibility wrapper retains the original API while the strengthened
-- theorem above also exposes that every pair lies in the joint range.
theorem local_joint_parametrization
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (hrec : LocalReciprocityLaw K)
    (W : Type u) [Field W] [Algebra K W]
    [FiniteDimensional K W] [IsGalois K W]
    {R : Type*} [Group R] {A : Type*} [Group A]
    (restriction : Gal(W/K) →* R) (lift : Gal(W/K) →* A)
    (hcomm : ∀ x y : (restriction.prod lift).range, x * y = y * x) :
    letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
    letI : NontriviallyNormedField W :=
      FLExt.nontriviallyNormedField K W
    letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
    letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel W := FLExt.valuativeRel K W
    letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
    letI : IsNonarchimedeanLocalField W :=
      FLExt.nonarchimedeanLocalField K W
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := W)) := spectralValuationExtension K W
    let AK := Valuation.integer (NormedField.valuation (K := K))
    let BW := Valuation.integer (NormedField.valuation (K := W))
    letI : IsIntegralClosure BW AK W :=
      FLExt.spectral_integer_closure K W
    letI : MulSemiringAction Gal(W/K) BW :=
      IsIntegralClosure.MulSemiringAction AK K W BW
    ∃ unitRestriction : localUnitSubgroup K →* R,
      ∃ unitLift : localUnitSubgroup K →* A,
        ∀ sigma : (IsLocalRing.maximalIdeal BW).inertia Gal(W/K),
          ∃ unit : localUnitSubgroup K,
            unitRestriction unit = restriction sigma.1 ∧
              unitLift unit = lift sigma.1 := by
  obtain ⟨unitRestriction, unitLift, _hrange, _hkernel, hparam⟩ :=
    joint_parametrization_range
      K hrec W restriction lift (1 : A →* A) hcomm (by simp)
  exact ⟨unitRestriction, unitLift, hparam⟩

set_option maxHeartbeats 3000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Kernel-valued parametrization unfolds the fixed field and joint range.
/-- Kernel-valued form of joint local parametrization.  If a quotient map
kills the lift on integral inertia, local reciprocity produces the lift
coordinate directly in that quotient kernel. -/
theorem joint_parametrization_kernel
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (hrec : LocalReciprocityLaw K)
    (W : Type u) [Field W] [Algebra K W]
    [FiniteDimensional K W] [IsGalois K W]
    {R : Type*} [Group R] {A B : Type*} [Group A] [Group B]
    (restriction : Gal(W/K) →* R) (lift : Gal(W/K) →* A)
    (target : A →* B)
    (hcomm : ∀ x y : (restriction.prod lift).range, x * y = y * x) :
    letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
    letI : NontriviallyNormedField W :=
      FLExt.nontriviallyNormedField K W
    letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
    letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel W := FLExt.valuativeRel K W
    letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
    letI : IsNonarchimedeanLocalField W :=
      FLExt.nonarchimedeanLocalField K W
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := W)) := spectralValuationExtension K W
    let AK := Valuation.integer (NormedField.valuation (K := K))
    let BW := Valuation.integer (NormedField.valuation (K := W))
    letI : IsIntegralClosure BW AK W :=
      FLExt.spectral_integer_closure K W
    letI : MulSemiringAction Gal(W/K) BW :=
      IsIntegralClosure.MulSemiringAction AK K W BW
    let I := (IsLocalRing.maximalIdeal BW).inertia Gal(W/K)
    ∀ (hkill : ∀ i : I, target (lift i.1) = 1),
      ∃ unitRestriction : localUnitSubgroup K →* R,
        ∃ unitLift : localUnitSubgroup K →* target.ker,
          ∀ sigma : I,
            ∃ unit : localUnitSubgroup K,
              unitRestriction unit = restriction sigma.1 ∧
                unitLift unit =
                  ⟨lift sigma.1, hkill sigma⟩ := by
  dsimp only
  intro hkill
  obtain ⟨unitRestriction, unitLift, _hrange, hunitKernel, hparam⟩ :=
    joint_parametrization_range
      K hrec W restriction lift target hcomm hkill
  let unitLiftKernel : localUnitSubgroup K →* target.ker :=
    unitLift.codRestrict target.ker (fun unit => hunitKernel unit)
  refine ⟨unitRestriction, unitLiftKernel, ?_⟩
  intro sigma
  obtain ⟨unit, hrestriction, hlift⟩ := hparam sigma
  refine ⟨unit, hrestriction, ?_⟩
  apply Subtype.ext
  exact hlift

set_option maxHeartbeats 3000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Comparing integral models synthesizes both Galois actions and closures.
/-- The integral inertia subgroup does not depend on the chosen integral
closure model, provided the Galois actions on the two models are compatible. -/
theorem spectral_inertia_model
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (W : Type u) [Field W] [Algebra K W]
    [FiniteDimensional K W] [IsGalois K W]
    (C : Type*) [CommRing C] [IsLocalRing C]
    [Algebra (Valuation.integer (NormedField.valuation (K := K))) C]
    [Algebra C W]
    [IsScalarTower (Valuation.integer
      (NormedField.valuation (K := K))) C W]
    [IsIntegralClosure C
      (Valuation.integer (NormedField.valuation (K := K))) W]
    [MulSemiringAction Gal(W/K) C]
    (hCaction : ∀ (tau : Gal(W/K)) (x : C),
      algebraMap C W (tau • x) = tau (algebraMap C W x)) :
    letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
    letI : NontriviallyNormedField W :=
      FLExt.nontriviallyNormedField K W
    letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
    letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel W := FLExt.valuativeRel K W
    letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
    letI : IsNonarchimedeanLocalField W :=
      FLExt.nonarchimedeanLocalField K W
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := W)) := spectralValuationExtension K W
    let AK := Valuation.integer (NormedField.valuation (K := K))
    let BW := Valuation.integer (NormedField.valuation (K := W))
    letI : IsIntegralClosure BW AK W :=
      FLExt.spectral_integer_closure K W
    letI : MulSemiringAction Gal(W/K) BW :=
      IsIntegralClosure.MulSemiringAction AK K W BW
    (IsLocalRing.maximalIdeal BW).inertia Gal(W/K) =
      (IsLocalRing.maximalIdeal C).inertia Gal(W/K) := by
  dsimp only
  letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
  letI : NontriviallyNormedField W :=
    FLExt.nontriviallyNormedField K W
  letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
  letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel W := FLExt.valuativeRel K W
  letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
  letI : IsNonarchimedeanLocalField W :=
    FLExt.nonarchimedeanLocalField K W
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := W)) := spectralValuationExtension K W
  let AK := Valuation.integer (NormedField.valuation (K := K))
  let BW := Valuation.integer (NormedField.valuation (K := W))
  letI : IsIntegralClosure BW AK W :=
    FLExt.spectral_integer_closure K W
  letI : MulSemiringAction Gal(W/K) BW :=
    IsIntegralClosure.MulSemiringAction AK K W BW
  let eC : BW ≃ₐ[AK] C := IsIntegralClosure.equiv AK BW W C
  have heC (x : BW) : algebraMap C W (eC x) =
      algebraMap BW W x :=
    IsIntegralClosure.algebraMap_equiv AK BW W C x
  have heCsmul (tau : Gal(W/K)) (x : BW) :
      eC (tau • x) = tau • eC x := by
    apply (IsIntegralClosure.algebraMap_injective C AK W)
    rw [heC]
    rw [hCaction]
    rw [heC]
    exact algebraMap_galRestrictHom_apply AK K W BW tau x
  apply SetLike.ext'
  ext tau
  exact local_ring_inertia
    (MulEquiv.refl _) eC.toRingEquiv heCsmul tau

set_option maxHeartbeats 6000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- The joint-range proof expands spectral inertia and quotient structures.
/-- Centrality on spectral integral inertia makes the joint
restriction-and-lift image commutative. -/
theorem joint_commutative_center
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (W : Type u) [Field W] [Algebra K W]
    [FiniteDimensional K W] [IsGalois K W]
    {R : Type*} [Group R] [IsMulCommutative R]
    {A : Type*} [Group A]
    (restriction : Gal(W/K) →* R) (lift : Gal(W/K) →* A) :
    letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
    letI : NontriviallyNormedField W :=
      FLExt.nontriviallyNormedField K W
    letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
    letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel W := FLExt.valuativeRel K W
    letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
    letI : IsNonarchimedeanLocalField W :=
      FLExt.nonarchimedeanLocalField K W
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := W)) := spectralValuationExtension K W
    let AK := Valuation.integer (NormedField.valuation (K := K))
    let BW := Valuation.integer (NormedField.valuation (K := W))
    letI : IsIntegralClosure BW AK W :=
      FLExt.spectral_integer_closure K W
    letI : MulSemiringAction Gal(W/K) BW :=
      IsIntegralClosure.MulSemiringAction AK K W BW
    let I := (IsLocalRing.maximalIdeal BW).inertia Gal(W/K)
    (∀ i : I, lift i.1 ∈ Subgroup.center A) →
      ∀ x y : (restriction.prod lift).range, x * y = y * x := by
  dsimp only
  letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
  letI : NontriviallyNormedField W :=
    FLExt.nontriviallyNormedField K W
  letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
  letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel W := FLExt.valuativeRel K W
  letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
  letI : IsNonarchimedeanLocalField W :=
    FLExt.nonarchimedeanLocalField K W
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := W)) := spectralValuationExtension K W
  let AK := Valuation.integer (NormedField.valuation (K := K))
  let BW := Valuation.integer (NormedField.valuation (K := W))
  letI : IsIntegralClosure BW AK W :=
    FLExt.spectral_integer_closure K W
  letI : MulSemiringAction Gal(W/K) BW :=
    IsIntegralClosure.MulSemiringAction AK K W BW
  let I := (IsLocalRing.maximalIdeal BW).inertia Gal(W/K)
  intro hcenter
  have hnormal : I.Normal := by
    dsimp [I]
    apply inertia_forall_smul
    intro tau
    rw [Ideal.pointwise_smul_eq_comap]
    exact IsLocalRing.eq_maximalIdeal inferInstance
  letI : I.Normal := hnormal
  have hcyclic : IsCyclic (Gal(W/K) ⧸ I) :=
    integral_inertia_cyclic K W hnormal
  letI : IsCyclic (Gal(W/K) ⧸ I) := hcyclic
  apply monoid_commutative_center
    I (restriction.prod lift)
  intro i
  rw [Subgroup.mem_center_iff]
  intro z
  apply Prod.ext
  · exact mul_comm' _ _
  · exact Subgroup.mem_center_iff.mp (hcenter i) z.2

set_option maxHeartbeats 6000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Transport from an arbitrary integral model builds both local field towers.
/-- Kernel-valued local parametrization expressed using any local integral
model of the finite extension.  The spectral integral model is constructed
internally and transported to the supplied model by uniqueness of integral
closure. -/
theorem joint_parametrization_model
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (hrec : LocalReciprocityLaw K)
    (W : Type u) [Field W] [Algebra K W]
    [FiniteDimensional K W] [IsGalois K W]
    (C : Type*) [CommRing C] [IsLocalRing C]
    [Algebra (Valuation.integer (NormedField.valuation (K := K))) C]
    [Algebra C W]
    [MulSemiringAction Gal(W/K) C]
    {R : Type*} [Group R] [IsMulCommutative R]
    {A B : Type*} [Group A] [Group B]
    (restriction : Gal(W/K) →* R) (lift : Gal(W/K) →* A)
    (target : A →* B)
    (hCscalar : IsScalarTower
      (Valuation.integer (NormedField.valuation (K := K))) C W)
    (hCclosure : IsIntegralClosure C
      (Valuation.integer (NormedField.valuation (K := K))) W)
    (hCaction : ∀ (tau : Gal(W/K)) (x : C),
      algebraMap C W (tau • x) = tau (algebraMap C W x)) :
    let IC := (IsLocalRing.maximalIdeal C).inertia Gal(W/K)
    (∀ i : IC, target (lift i.1) = 1) →
      (∀ i : IC, lift i.1 ∈ Subgroup.center A) →
        ∃ unitRestriction : localUnitSubgroup K →* R,
          ∃ unitLift : localUnitSubgroup K →* target.ker,
            ∀ sigma : IC,
              ∃ unit : localUnitSubgroup K,
                unitRestriction unit = restriction sigma.1 ∧
                  (unitLift unit : A) = lift sigma.1 := by
  dsimp only
  intro hkillC hcenterC
  letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
  letI : NontriviallyNormedField W :=
    FLExt.nontriviallyNormedField K W
  letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
  letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel W := FLExt.valuativeRel K W
  letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
  letI : IsNonarchimedeanLocalField W :=
    FLExt.nonarchimedeanLocalField K W
  letI : IsScalarTower
      (Valuation.integer (NormedField.valuation (K := K))) C W := hCscalar
  letI : IsIntegralClosure C
      (Valuation.integer (NormedField.valuation (K := K))) W := hCclosure
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := W)) := spectralValuationExtension K W
  let AK := Valuation.integer (NormedField.valuation (K := K))
  let BW := Valuation.integer (NormedField.valuation (K := W))
  letI : IsIntegralClosure BW AK W :=
    FLExt.spectral_integer_closure K W
  letI : MulSemiringAction Gal(W/K) BW :=
    IsIntegralClosure.MulSemiringAction AK K W BW
  let I := (IsLocalRing.maximalIdeal BW).inertia Gal(W/K)
  have hIeq : I =
      (IsLocalRing.maximalIdeal C).inertia Gal(W/K) :=
    spectral_inertia_model K W C hCaction
  have hkill : ∀ i : I, target (lift i.1) = 1 := by
    intro i
    exact hkillC ⟨i.1, hIeq ▸ i.2⟩
  have hcenter : ∀ i : I, lift i.1 ∈ Subgroup.center A := by
    intro i
    exact hcenterC ⟨i.1, hIeq ▸ i.2⟩
  have hcomm : ∀ x y : (restriction.prod lift).range,
      x * y = y * x :=
    joint_commutative_center
      K W restriction lift hcenter
  obtain ⟨unitRestriction, unitLift, hparam⟩ :=
    joint_parametrization_kernel
      K hrec W restriction lift target hcomm hkill
  refine ⟨unitRestriction, unitLift, ?_⟩
  intro sigma
  let sigmaI : I := ⟨sigma.1, hIeq.symm ▸ sigma.2⟩
  obtain ⟨unit, hrestriction, hlift⟩ := hparam sigmaI
  refine ⟨unit, hrestriction, ?_⟩
  exact congrArg Subtype.val hlift

set_option maxHeartbeats 3000000 in
-- This packages the central-inertia/cyclic-residue criterion used at `3`.
/-- A commutative restriction character and a lift whose inertia image is
central are jointly parametrized by local units when the residue quotient is
cyclic. -/
theorem joint_parametrization_inertia
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (hrec : LocalReciprocityLaw K)
    (W : Type u) [Field W] [Algebra K W]
    [FiniteDimensional K W] [IsGalois K W]
    {R : Type*} [Group R] [IsMulCommutative R]
    {A : Type*} [Group A]
    (restriction : Gal(W/K) →* R) (lift : Gal(W/K) →* A) :
    letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
    letI : NontriviallyNormedField W :=
      FLExt.nontriviallyNormedField K W
    letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
    letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel W := FLExt.valuativeRel K W
    letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
    letI : IsNonarchimedeanLocalField W :=
      FLExt.nonarchimedeanLocalField K W
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := W)) := spectralValuationExtension K W
    let AK := Valuation.integer (NormedField.valuation (K := K))
    let BW := Valuation.integer (NormedField.valuation (K := W))
    letI : IsIntegralClosure BW AK W :=
      FLExt.spectral_integer_closure K W
    letI : MulSemiringAction Gal(W/K) BW :=
      IsIntegralClosure.MulSemiringAction AK K W BW
    let I := (IsLocalRing.maximalIdeal BW).inertia Gal(W/K)
    ∀ (hnormal : Subgroup.Normal I),
      letI : Subgroup.Normal I := hnormal
      IsCyclic (Gal(W/K) ⧸ I) →
      (∀ i : I, lift i.1 ∈ Subgroup.center A) →
      ∃ unitRestriction : localUnitSubgroup K →* R,
        ∃ unitLift : localUnitSubgroup K →* A,
          ∀ sigma : I, ∃ unit : localUnitSubgroup K,
            unitRestriction unit = restriction sigma.1 ∧
              unitLift unit = lift sigma.1 := by
  dsimp only
  letI : Algebra.IsAlgebraic K W := Algebra.IsAlgebraic.of_finite K W
  letI : NontriviallyNormedField W :=
    FLExt.nontriviallyNormedField K W
  letI : NormedAlgebra K W := spectralNorm.normedAlgebra K W
  letI : IsUltrametricDist W := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel W := FLExt.valuativeRel K W
  letI : Valuation.Compatible (NormedField.valuation (K := W)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := W))
  letI : IsNonarchimedeanLocalField W :=
    FLExt.nonarchimedeanLocalField K W
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := W)) := spectralValuationExtension K W
  let AK := Valuation.integer (NormedField.valuation (K := K))
  let BW := Valuation.integer (NormedField.valuation (K := W))
  letI : IsIntegralClosure BW AK W :=
    FLExt.spectral_integer_closure K W
  letI : MulSemiringAction Gal(W/K) BW :=
    IsIntegralClosure.MulSemiringAction AK K W BW
  let I := (IsLocalRing.maximalIdeal BW).inertia Gal(W/K)
  intro hnormal
  letI : Subgroup.Normal I := hnormal
  intro hcyclic hcenter
  letI : IsCyclic (Gal(W/K) ⧸ I) := hcyclic
  apply local_joint_parametrization K hrec W restriction lift
  apply monoid_commutative_center
    I (restriction.prod lift)
  intro i
  rw [Subgroup.mem_center_iff]
  intro z
  apply Prod.ext
  · exact mul_comm' z.1 (restriction i.1)
  · exact Subgroup.mem_center_iff.mp (hcenter i) z.2

end TBluepr
end Towers
