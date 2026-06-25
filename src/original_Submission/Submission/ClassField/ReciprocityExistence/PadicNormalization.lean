import Submission.ClassField.ReciprocityExistence.PadicCompletionModel
import Submission.ClassField.LocalReciprocity.MixedCupTransport
import Submission.ClassField.LocalReciprocity.CyclotomicComparison
import Submission.ClassField.LocalReciprocity.PadicRootNormalization
import Submission.ClassField.LocalReciprocity.AmbientCompatibility
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

namespace Submission.CField.RExist

open scoped IsMulCommutative
open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LTate
open Submission.CField.LRecip
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.ICohomo

noncomputable section

theorem action_primitive_root
    (p n : ℕ) [Fact p.Prime]
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E]
    (u : ℤ_[p]ˣ) (mu : E) (hmu : IsPrimitiveRoot mu (p ^ (n + 1))) :
    padicCyclotomicAction p (n + 1)
        (padicCyclotomic_irreducible p n) (L := E) u mu =
      mu ^ ((padicUnitReduction p (n + 1) u⁻¹ :
        ZMod (p ^ (n + 1))).val) := by
  let sigma := padicCyclotomicAction p (n + 1)
    (padicCyclotomic_irreducible p n) (L := E) u
  let hzeta := IsCyclotomicExtension.zeta_spec (p ^ (n + 1)) ℚ_[p] E
  have hsigma : hzeta.autToPow ℚ_[p] sigma =
      padicUnitReduction p (n + 1) u⁻¹ := by
    let e := IsCyclotomicExtension.autEquivPow E
      (padicCyclotomic_irreducible p n)
    change e (e.symm (padicUnitReduction p (n + 1) u⁻¹)) = _
    exact e.apply_symm_apply _
  have hpow : hmu.autToPow ℚ_[p] sigma =
      padicUnitReduction p (n + 1) u⁻¹ := by
    calc
      hmu.autToPow ℚ_[p] sigma =
          modularCyclotomicCharacter E hmu.card_rootsOfUnity sigma :=
        hmu.autToPow_eq_modularCyclotomicCharacter
          (p ^ (n + 1)) ℚ_[p] sigma
      _ = modularCyclotomicCharacter E hzeta.card_rootsOfUnity sigma := by
        congr
      _ = hzeta.autToPow ℚ_[p] sigma :=
        (hzeta.autToPow_eq_modularCyclotomicCharacter
          (p ^ (n + 1)) ℚ_[p] sigma).symm
      _ = padicUnitReduction p (n + 1) u⁻¹ := hsigma
  change sigma mu = _
  calc
    sigma mu = mu ^ ((hmu.autToPow ℚ_[p] sigma :
        ZMod (p ^ (n + 1))).val) :=
      (hmu.autToPow_spec ℚ_[p] sigma).symm
    _ = _ := by rw [hpow]

local instance (p : ℕ) [Fact p.Prime] : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))

local instance (p : ℕ) [Fact p.Prime] :
    Valuation.Compatible (NormedField.valuation (K := ℚ_[p])) :=
  Valuation.Compatible.ofValuation _

local instance (p : ℕ) [Fact p.Prime] :
    IsNonarchimedeanLocalField ℚ_[p] := by
  haveI htop : IsValuativeTopology ℚ_[p] := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : ℚ_[p]) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := ℚ_[p])))ˣ,
          {x | (NormedField.valuation (K := ℚ_[p])).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := ℚ_[p])).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := ℚ_[p]))
        |>.exists_setOf_restrict_le_iff 0 s
  haveI hnontrivial : ValuativeRel.IsNontrivial ℚ_[p] :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := ℚ_[p]))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }

set_option maxHeartbeats 3000000 in
-- Canonical normalization unfolds both the cyclotomic completion and local Artin transports.
set_option synthInstance.maxHeartbeats 500000 in
-- The same comparison synthesizes the local-field and completed Galois instances together.
theorem canonical_padic_normalization
    (p n : ℕ) [Fact p.Prime]
    (hunit : PadicArtinNormalization p)
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    canonicalPadicArtin p (n + 1) L w =
      padicCyclotomicArtin p (n + 1) L := by
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
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
    Valuation.Compatible.ofValuation _
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Algebra ℚ v.Completion := (completionEmbedding v).toAlgebra
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := ℚ) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/ℚ) W :=
    completion_above_pretransitive P
  letI : IsMulCommutative Gal(L/ℚ) :=
    IsCyclotomicExtension.isMulCommutative {p ^ (n + 1)} ℚ L
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let e := rationalAbsoluteCompletion p
  letI : Algebra ℚ_[p] v.Completion := e.symm.toRingHom.toAlgebra
  letI : Algebra ℚ_[p] w.1.Completion :=
    (rationalQpAlgebra p L w).toAlgebra
  letI : IsScalarTower ℚ_[p] v.Completion w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hfinrank : Module.finrank ℚ_[p] w.1.Completion =
      p ^ n * (p - 1) :=
    cyclotomic_finrank_padic p n L w
  letI : FiniteDimensional ℚ_[p] w.1.Completion :=
    FiniteDimensional.of_finrank_pos (by
      rw [hfinrank]
      exact Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos n)
        (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
  letI : IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] w.1.Completion :=
    cyclotomic_completion_extension p n L w
  letI : IsGalois ℚ_[p] w.1.Completion :=
    IsCyclotomicExtension.isGalois {p ^ (n + 1)} ℚ_[p] w.1.Completion
  let decomp := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau => decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm (decomp.symm sigma) (decomp.symm tau)
  letI : IsMulCommutative Gal(w.1.Completion/ℚ_[p]) :=
    IsCyclotomicExtension.isMulCommutative {p ^ (n + 1)} ℚ_[p]
      w.1.Completion
  let eAlg : v.Completion ≃ₐ[ℚ_[p]] ℚ_[p] :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv)
      (fun x => e.apply_symm_apply x)
  letI : FiniteDimensional ℚ_[p] v.Completion :=
    FiniteDimensional.of_surjective eAlg.symm.toLinearEquiv.toLinearMap
      eAlg.symm.surjective
  let hnorm : ∀ x : ℚ_[p], ‖eAlg.symm x‖ = ‖x‖ := by
    intro x
    have h := (rational_absolute_isometry p).dist_eq
      (e.symm x) 0
    simpa [eAlg, e, dist_zero] using h.symm
  let i : w.1.Completion ≃+* w.1.Completion := RingEquiv.refl _
  let hbase : ∀ a : ℚ_[p],
      i (algebraMap ℚ_[p] w.1.Completion a) =
        algebraMap v.Completion w.1.Completion
          (algebraMap ℚ_[p] v.Completion a) := fun _ => rfl
  let g := mixedUniverseGal eAlg i hbase
  have htransport :
      g.toMonoidHom.comp
          (abelianArtinUniverse ℚ_[p] w.1.Completion) =
        (abelianArtinUniverse
          v.Completion w.1.Completion).comp
            (Units.map (algebraMap ℚ_[p] v.Completion).toMonoidHom) :=
    abelian_artin_universe
    ℚ_[p] w.1.Completion v.Completion w.1.Completion eAlg hnorm
      i hbase
  apply MonoidHom.ext
  intro a
  obtain ⟨aUnit, m, haUnit, ha⟩ :=
    unit_uniformizer_zpow
      (Padic.mulValuation (p := p)) (p : ℚ_[p])
        (padic_prime_uniformizer p) a
  let valuationUnit :
      (Padic.mulValuation (p := p)).valuationSubring.unitGroup :=
    ⟨aUnit, (Valuation.mem_unitGroup_iff ℚ_[p]
      (Padic.mulValuation (p := p)) aUnit).mpr haUnit⟩
  let u : ℤ_[p]ˣ := padicValuationInt p valuationUnit
  have hunitCoe :
      ((((padicValuationInt p).symm u :
          (Padic.mulValuation (p := p)).valuationSubring.unitGroup) :
          ℚ_[p]ˣ)) = aUnit := by
    change ((((padicValuationInt p).symm
      (padicValuationInt p valuationUnit) :
        (Padic.mulValuation (p := p)).valuationSubring.unitGroup) :
        ℚ_[p]ˣ)) = aUnit
    rw [(padicValuationInt p).symm_apply_apply]
  have ha' : a =
      (((padicValuationInt p).symm u :
          (Padic.mulValuation (p := p)).valuationSubring.unitGroup) :
          ℚ_[p]ˣ) *
        (Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero) ^ m := by
    rw [hunitCoe]
    exact ha
  let x : ℚ_[p]ˣ := Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  let xV : v.Completionˣ :=
    Units.map (algebraMap ℚ_[p] v.Completion).toMonoidHom x
  let tau : Gal(w.1.Completion/ℚ_[p]) :=
    padicCyclotomicAction p (n + 1)
      (padicCyclotomic_irreducible p n) (L := w.1.Completion) u
  have hQp : abelianArtinUniverse ℚ_[p] w.1.Completion x =
      tau := by
    rw [← abelian_local_universe]
    exact abelian_artin_normalization
      p hunit n u w.1.Completion
  have hlocal : abelianArtinUniverse
      v.Completion w.1.Completion xV = g tau := by
    have ht := DFunLike.congr_fun htransport x
    change g (abelianArtinUniverse ℚ_[p] w.1.Completion x) =
      abelianArtinUniverse v.Completion w.1.Completion xV at ht
    rw [hQp] at ht
    exact ht.symm
  let varpi : ℚ_[p]ˣ :=
    Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero
  have hQpVarpi :
      abelianArtinUniverse ℚ_[p] w.1.Completion varpi = 1 := by
    rw [← abelian_local_universe]
    exact abelian_cyclotomic_uniformizer
      p n w.1.Completion
  have hQpA :
      abelianArtinUniverse ℚ_[p] w.1.Completion a = tau := by
    rw [ha', map_mul, map_zpow, hQpVarpi, one_zpow, mul_one]
    exact hQp
  let aV : v.Completionˣ :=
    Units.map (algebraMap ℚ_[p] v.Completion).toMonoidHom a
  have hlocalA : abelianArtinUniverse
      v.Completion w.1.Completion aV = g tau := by
    have ht := DFunLike.congr_fun htransport a
    change g (abelianArtinUniverse ℚ_[p] w.1.Completion a) =
      abelianArtinUniverse v.Completion w.1.Completion aV at ht
    rw [hQpA] at ht
    exact ht.symm
  let rho : Gal(w.1.Completion/v.Completion) := g tau
  let sigma : Gal(L/ℚ) :=
    padicCyclotomicAction p (n + 1)
      (Polynomial.cyclotomic.irreducible_rat
        (pow_pos (Fact.out : p.Prime).pos (n + 1))) (L := L) u
  let delta : absoluteValueDecomposition v w.1 := decomp.symm rho
  have hglobal : (delta : Gal(L/ℚ)) = sigma := by
    apply AlgEquiv.coe_algHom_injective
    apply ((IsCyclotomicExtension.zeta_spec
      (p ^ (n + 1)) ℚ L).powerBasis ℚ).algHom_ext
    apply (completionEmbedding w.1).injective
    let zeta := IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ L
    let completedZeta := cyclotomicCompletedZeta p n L w
    let exponent :=
      (padicUnitReduction p (n + 1) u⁻¹ : ZMod (p ^ (n + 1))).val
    calc
      completionEmbedding w.1 (delta.1 zeta) =
          decompositionCompletionEquiv v w.1 delta
            (completionEmbedding w.1 zeta) := by
        rw [decomposition_alg_embedding]
      _ = decomp delta (completionEmbedding w.1 zeta) := rfl
      _ = rho (completionEmbedding w.1 zeta) := by
        rw [show decomp delta = rho from decomp.apply_symm_apply rho]
      _ = g tau (completionEmbedding w.1 zeta) := rfl
      _ = tau (completionEmbedding w.1 zeta) := by
        exact gal_zero_universe eAlg.symm.toRingEquiv i
          (mixed_universe_square eAlg i hbase) tau
            (completionEmbedding w.1 zeta)
      _ = completedZeta ^ exponent := by
        exact action_primitive_root p n w.1.Completion u
          completedZeta
          (completed_zeta_primitive p n L w)
      _ = completionEmbedding w.1 (zeta ^ exponent) := by
        rw [map_pow]
        rfl
      _ = completionEmbedding w.1 (sigma zeta) := by
        congr 1
        symm
        exact padic_action_zeta p (n + 1)
          (Polynomial.cyclotomic.irreducible_rat
            (pow_pos (Fact.out : p.Prime).pos (n + 1))) u
  have hintoGlobal :
      ((absoluteValueDecomposition v w.1).subtype.comp
        decomp.symm.toMonoidHom) rho = sigma := by
    exact hglobal
  have hcanonicalUnit :
      ((absoluteValueDecomposition v w.1).subtype.comp
        decomp.symm.toMonoidHom)
          (abelianArtinUniverse
            v.Completion w.1.Completion xV) = sigma := by
    rw [hlocal]
    exact hintoGlobal
  have hcanonicalA :
      ((absoluteValueDecomposition v w.1).subtype.comp
        decomp.symm.toMonoidHom)
          (abelianArtinUniverse
            v.Completion w.1.Completion aV) = sigma := by
    rw [hlocalA]
    exact hintoGlobal
  have hexplicit :
      padicCyclotomicArtin p (n + 1) L a = sigma := by
    rw [ha']
    exact padic_artin_zpow
      p (n + 1) L u m
  have hsource :
      Units.map
          (placeCompletionAdic P).symm.toRingHom
          ((rationalUnitsEquiv p).symm a) = aV := by
    apply Units.ext
    rfl
  change ((absoluteValueDecomposition v w.1).subtype.comp
      decomp.symm.toMonoidHom)
        (abelianArtinUniverse v.Completion w.1.Completion
          (Units.map
            (placeCompletionAdic P).symm.toRingHom
            ((rationalUnitsEquiv p).symm a))) =
      padicCyclotomicArtin p (n + 1) L a
  rw [hsource, hcanonicalA, hexplicit]

/-- The root-field unit formula, uniformly in p, gives the full canonical
normalization, including the degree-one conductors. -/
theorem canonical_normalization_unit
    (hunit : ∀ (p : ℕ) [Fact p.Prime],
      PadicArtinNormalization p) :
    CanonicalPadicNormalization := by
  apply canonical_normalization_positive
  intro p r _ _ L _ _ _ w hr _
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  letI : IsGalois ℚ L :=
    IsCyclotomicExtension.isGalois {p ^ (n + 1)} ℚ L
  exact canonical_padic_normalization
    p n (hunit p) L w

/-- The canonical `p`-adic factor in Example VII.8.2 has the explicit
inverse-unit Lubin--Tate normalization, with no remaining hypothesis. -/
theorem canonicalPadicNormalization :
    CanonicalPadicNormalization :=
  canonical_normalization_unit
    (fun p _ ↦ padicArtinNormalization p)

end
end Submission.CField.RExist
