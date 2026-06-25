import Towers.ClassField.LocalReciprocity.PadicRootCore
import Towers.ClassField.LocalReciprocity.ArtinTowerCompatibility
import Towers.ClassField.LocalReciprocity.LiteralTowerTypes

open Towers.CField.LFTheory
open Towers.CField.UCohom
open Towers.CField.LRecip
open Towers.CField.LBrauer

namespace Towers.CField.LRecip.PNProof

open scoped IsMulCommutative
open Towers.CField.LTate
open Towers.CField.FGroups
open Towers.CField.LBrauer

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

local instance : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))

local instance : Valuation.Compatible
    (NormedField.valuation (K := ℚ_[p])) :=
  Valuation.Compatible.ofValuation _

local instance : IsNonarchimedeanLocalField ℚ_[p] := by
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

set_option maxHeartbeats 5000000 in
-- The mixed-universe Artin transport elaborates several spectral-norm structures at once.
set_option synthInstance.maxHeartbeats 500000 in
/-- The same relative normalization after presenting the basic field as an
actual intermediate field of the compositum. -/
theorem abelian_comparison_uniformizer
    (n : ℕ) (u : ℤ_[p]ˣ)
    (varpi : (basicWittField p k n u)ˣ)
    (hvarpi : localUnitOrder (basicWittField p k n u)
      (Additive.ofMul varpi) = 1) :
    let FM := wittFieldComparison p k n u
    letI : Algebra.IsAlgebraic ℚ_[p] FM :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] FM
    letI : SeminormedRing FM := spectralNorm.seminormedRing ℚ_[p] FM
    let hN : NontriviallyNormedField FM :=
      FLExt.nontriviallyNormedField ℚ_[p] FM
    letI : NontriviallyNormedField FM := hN
    let hNF : NormedField FM := hN.toNormedField
    letI : NormedField FM := hNF
    let hMetric : MetricSpace FM := hNF.toMetricSpace
    letI : MetricSpace FM := hMetric
    let hPseudo : PseudoMetricSpace FM := hMetric.toPseudoMetricSpace
    letI : PseudoMetricSpace FM := hPseudo
    letI : Dist FM := hPseudo.toDist
    let hUniform : UniformSpace FM := hPseudo.toUniformSpace
    letI : UniformSpace FM := hUniform
    letI : TopologicalSpace FM := hUniform.toTopologicalSpace
    letI : NormedAlgebra ℚ_[p] FM := spectralNorm.normedAlgebra ℚ_[p] FM
    letI : IsUltrametricDist FM := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    letI : ValuativeRel FM := FLExt.valuativeRel ℚ_[p] FM
    letI : IsNonarchimedeanLocalField FM :=
      FLExt.nonarchimedeanLocalField ℚ_[p] FM
    abelianArtinHom FM
        (comparisonWittField p k n u)
        (Units.map
          (basicWittComparison p k n u).toRingEquiv.toMonoidHom
          varpi) =
      comparisonWittBasic p k n u := by
  dsimp only
  let F := basicWittField p k n u
  let M := comparisonWittField p k n u
  let FM := wittFieldComparison p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] FM :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] FM
  letI : SeminormedRing FM := spectralNorm.seminormedRing ℚ_[p] FM
  let hN : NontriviallyNormedField FM :=
    FLExt.nontriviallyNormedField ℚ_[p] FM
  letI : NontriviallyNormedField FM := hN
  let hNF : NormedField FM := hN.toNormedField
  letI : NormedField FM := hNF
  let hMetric : MetricSpace FM := hNF.toMetricSpace
  letI : MetricSpace FM := hMetric
  let hPseudo : PseudoMetricSpace FM := hMetric.toPseudoMetricSpace
  letI : PseudoMetricSpace FM := hPseudo
  letI : Dist FM := hPseudo.toDist
  let hUniform : UniformSpace FM := hPseudo.toUniformSpace
  letI : UniformSpace FM := hUniform
  letI : TopologicalSpace FM := hUniform.toTopologicalSpace
  letI : NormedAlgebra ℚ_[p] FM := spectralNorm.normedAlgebra ℚ_[p] FM
  letI : IsUltrametricDist FM := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let eF : F ≃ₐ[ℚ_[p]] wittFieldComparison p k n u :=
    basicWittComparison p k n u
  letI : ValuativeRel FM := FLExt.valuativeRel ℚ_[p] FM
  letI : Valuation.Compatible
      (NormedField.valuation (K := FM)) :=
    Valuation.Compatible.ofValuation _
  letI : IsNonarchimedeanLocalField FM :=
    FLExt.nonarchimedeanLocalField ℚ_[p] FM
  letI : Algebra F (wittFieldComparison p k n u) :=
    eF.toAlgHom.toAlgebra
  let eBase : wittFieldComparison p k n u ≃ₐ[F] F :=
    { eF.symm.toRingEquiv with
      commutes' := fun x ↦ eF.symm_apply_apply x }
  letI : FiniteDimensional F (wittFieldComparison p k n u) :=
    Module.Finite.equiv eBase.symm.toLinearEquiv
  let i : M ≃+* M := RingEquiv.refl M
  have hbase (a : F) :
      i (algebraMap F M a) =
        algebraMap (wittFieldComparison p k n u) M
          (algebraMap F (wittFieldComparison p k n u) a) := by
    rfl
  letI : IsScalarTower F (wittFieldComparison p k n u) M :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hnorm (x : F) : ‖eBase.symm x‖ = ‖x‖ := by
    change ‖eF x‖ = ‖x‖
    change spectralNorm ℚ_[p] FM (eF x) = ‖x‖
    rw [← spectral_alg_local ℚ_[p] F FM eF]
    exact (NormedAlgebra.norm_eq_spectralNorm ℚ_[p] x).symm
  let g : Gal(M/F) ≃* Gal(M/wittFieldComparison p k n u) :=
    mixedUniverseGal eBase i hbase
  have hnat :=
    abelian_artin_universe
      F M (wittFieldComparison p k n u) M eBase hnorm i hbase
  rw [← abelian_local_universe F M,
    ← abelian_local_universe
      (wittFieldComparison p k n u) M] at hnat
  have hnatVarpi := DFunLike.congr_fun hnat varpi
  have hrel := abelian_witt_uniformizer
    p k n u varpi hvarpi
  have hg : g (comparisonRelativeFrobenius p k n u) =
      comparisonWittBasic p k n u := by
    apply AlgEquiv.ext
    intro x
    rfl
  change abelianArtinHom (wittFieldComparison p k n u) M
      (Units.map eF.toRingEquiv.toMonoidHom varpi) = _
  rw [← hg, ← hrel]
  exact hnatVarpi.symm


end

open Towers.CField.LFTheory
open Towers.CField.UCohom
open Towers.CField.LRecip
open Towers.CField.LBrauer

open Towers.CField.LTate
open Towers.CField.FGroups
open Towers.CField.LBrauer
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

local instance : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
local instance : Valuation.Compatible (NormedField.valuation (K := ℚ_[p])) :=
  Valuation.Compatible.ofValuation _
local instance : IsNonarchimedeanLocalField ℚ_[p] := by
  haveI htop : IsValuativeTopology ℚ_[p] := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : ℚ_[p]) ↔ ∃ γ : (MonoidWithZeroHom.ValueGroup₀
        (NormedField.valuation (K := ℚ_[p])))ˣ,
      {x | (NormedField.valuation (K := ℚ_[p])).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := ℚ_[p])).is_topological_valuation s]
    simpa using (NormedField.valuation (K := ℚ_[p])).exists_setOf_restrict_le_iff 0 s
  haveI hnontrivial : ValuativeRel.IsNontrivial ℚ_[p] :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := ℚ_[p]))).mpr inferInstance
  exact { toIsValuativeTopology := htop
          toLocallyCompactSpace := inferInstance
          toIsNontrivial := hnontrivial }

theorem intermediate_cast_val
    {K M : Type} [Field K] [Field M] [Algebra K M]
    {S T : IntermediateField K M} (h : S = T) (x : Sˣ) :
    (((_root_.cast (congrArg (fun J : IntermediateField K M ↦ Jˣ) h) x : Tˣ) : T) : M) =
      ((x : S) : M) := by
  subst T
  rfl

theorem intermediate_gal_cast
    {K M : Type} [Field K] [Field M] [Algebra K M]
    {S T : IntermediateField K M} (h : S = T) (sigma : Gal(M/S)) (x : M) :
    (_root_.cast (congrArg (fun J : IntermediateField K M ↦ Gal(M/J)) h) sigma) x =
      sigma x := by
  subst T
  rfl

set_option maxHeartbeats 5000000 in
-- Constructing the spectral local Artin map synthesizes the full local-field structure on `E`.
set_option synthInstance.maxHeartbeats 500000 in
noncomputable def spectralIntermediateArtin
    (n : ℕ) (u : ℤ_[p]ˣ)
    (E : IntermediateField ℚ_[p] (comparisonWittField p k n u)) :
    Eˣ →* Abelianization Gal(comparisonWittField p k n u/E) := by
  let M := comparisonWittField p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : SeminormedRing E := spectralNorm.seminormedRing ℚ_[p] E
  let hN : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField ℚ_[p] E
  letI : NontriviallyNormedField E := hN
  let hNF : NormedField E := hN.toNormedField
  letI : NormedField E := hNF
  let hMetric : MetricSpace E := hNF.toMetricSpace
  letI : MetricSpace E := hMetric
  let hPseudo : PseudoMetricSpace E := hMetric.toPseudoMetricSpace
  letI : PseudoMetricSpace E := hPseudo
  letI : Dist E := hPseudo.toDist
  let hUniform : UniformSpace E := hPseudo.toUniformSpace
  letI : UniformSpace E := hUniform
  letI : TopologicalSpace E := hUniform.toTopologicalSpace
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : ValuativeRel E := FLExt.valuativeRel ℚ_[p] E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation _
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField ℚ_[p] E
  letI : FiniteDimensional E M := FiniteDimensional.right ℚ_[p] E M
  letI : IsGalois E M := IsGalois.tower_top_of_isGalois ℚ_[p] E M
  exact localArtinHom E M

theorem spectral_intermediate_transport
    (n : ℕ) (u : ℤ_[p]ˣ)
    (E₁ E₂ : IntermediateField ℚ_[p] (comparisonWittField p k n u))
    (h : E₁ = E₂) (x : E₁ˣ) (sigma : Gal(comparisonWittField p k n u/E₁))
    (hx : spectralIntermediateArtin p k n u E₁ x =
      Abelianization.of sigma) :
    spectralIntermediateArtin p k n u E₂
        (_root_.cast (congrArg (fun J : IntermediateField ℚ_[p]
          (comparisonWittField p k n u) ↦ Jˣ) h) x) =
      Abelianization.of
        (_root_.cast (congrArg (fun J : IntermediateField ℚ_[p]
          (comparisonWittField p k n u) ↦
            Gal(comparisonWittField p k n u/J)) h) sigma) := by
  subst E₂
  exact hx

set_option maxHeartbeats 50000000 in
-- The fixed-field norm square and its spectral transports require deep normalization.
set_option synthInstance.maxHeartbeats 500000 in
/-- Norm functoriality carries the relative arithmetic Frobenius to the
same explicit automorphism in the Galois group over `Q_p`. -/
theorem artin_comparison_uniformizer
    (n : ℕ) (u : ℤ_[p]ˣ)
    (varpi : (basicWittField p k n u)ˣ)
    (hvarpi : localUnitOrder (basicWittField p k n u)
      (Additive.ofMul varpi) = 1) :
    localArtinHom ℚ_[p] (comparisonWittField p k n u)
        (normOnUnits ℚ_[p] (basicWittField p k n u) varpi) =
      Abelianization.of (comparisonWittFrobenius p k n u) := by
  let F := basicWittField p k n u
  let M := comparisonWittField p k n u
  let FM := wittFieldComparison p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] FM :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] FM
  letI : SeminormedRing FM := spectralNorm.seminormedRing ℚ_[p] FM
  let hN : NontriviallyNormedField FM :=
    FLExt.nontriviallyNormedField ℚ_[p] FM
  letI : NontriviallyNormedField FM := hN
  let hNF : NormedField FM := hN.toNormedField
  letI : NormedField FM := hNF
  let hMetric : MetricSpace FM := hNF.toMetricSpace
  letI : MetricSpace FM := hMetric
  let hPseudo : PseudoMetricSpace FM := hMetric.toPseudoMetricSpace
  letI : PseudoMetricSpace FM := hPseudo
  letI : Dist FM := hPseudo.toDist
  let hUniform : UniformSpace FM := hPseudo.toUniformSpace
  letI : UniformSpace FM := hUniform
  letI : TopologicalSpace FM := hUniform.toTopologicalSpace
  letI : NormedAlgebra ℚ_[p] FM := spectralNorm.normedAlgebra ℚ_[p] FM
  letI : IsUltrametricDist FM := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : ValuativeRel FM := FLExt.valuativeRel ℚ_[p] FM
  letI : Valuation.Compatible
      (NormedField.valuation (K := FM)) :=
    Valuation.Compatible.ofValuation _
  letI : IsNonarchimedeanLocalField FM := by
    exact FLExt.nonarchimedeanLocalField ℚ_[p] FM
  let eF : F ≃ₐ[ℚ_[p]] FM :=
    basicWittComparison p k n u
  let xFM : FMˣ := Units.map eF.toRingEquiv.toMonoidHom varpi
  let sigmaFM : Gal(M/FM) :=
    comparisonWittBasic p k n u
  letI : FiniteDimensional ℚ_[p] FM := Module.Finite.equiv eF.toLinearEquiv
  letI : IsGalois ℚ_[p] FM := IsGalois.of_algEquiv eF
  letI : FiniteDimensional FM M := FiniteDimensional.right ℚ_[p] FM M
  letI : IsGalois FM M := IsGalois.tower_top_of_isGalois ℚ_[p] FM M
  letI : IsMulCommutative Gal(M/FM) :=
    witt_comparison_commutative p k n u
  have hrel : abelianArtinHom FM M xFM = sigmaFM := by
    exact abelian_comparison_uniformizer
      p k n u varpi hvarpi
  let H : Subgroup Gal(M/ℚ_[p]) := FM.fixingSubgroup
  have hfixed : IntermediateField.fixedField H = FM := by
    exact IsGalois.fixedField_fixingSubgroup FM
  let E := IntermediateField.fixedField H
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : SeminormedRing E := spectralNorm.seminormedRing ℚ_[p] E
  let hNE : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField ℚ_[p] E
  letI : NontriviallyNormedField E := hNE
  let hNFE : NormedField E := hNE.toNormedField
  letI : NormedField E := hNFE
  let hMetricE : MetricSpace E := hNFE.toMetricSpace
  letI : MetricSpace E := hMetricE
  let hPseudoE : PseudoMetricSpace E := hMetricE.toPseudoMetricSpace
  letI : PseudoMetricSpace E := hPseudoE
  letI : Dist E := hPseudoE.toDist
  let hUniformE : UniformSpace E := hPseudoE.toUniformSpace
  letI : UniformSpace E := hUniformE
  letI : TopologicalSpace E := hUniformE.toTopologicalSpace
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : ValuativeRel E := FLExt.valuativeRel ℚ_[p] E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation _
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField ℚ_[p] E
  let xFixed : Eˣ :=
    _root_.cast (congrArg (fun J : IntermediateField ℚ_[p] M ↦ Jˣ)
      hfixed.symm) xFM
  let sigmaFixed : Gal(M/E) :=
    _root_.cast (congrArg (fun J : IntermediateField ℚ_[p] M ↦ Gal(M/J))
      hfixed.symm) sigmaFM
  have hsquare := (artinTowerCompatibility ℚ_[p] M H).1
  unfold NormSquare at hsquare
  have hsquarex := DFunLike.congr_fun hsquare xFixed
  have hArtinAbFM : localArtinHom FM M xFM =
      Abelianization.of sigmaFM := by
    rw [← hrel]
    change localArtinHom FM M xFM =
      Abelianization.equivOfComm
        (Abelianization.equivOfComm.symm (localArtinHom FM M xFM))
    exact (Abelianization.equivOfComm.apply_symm_apply _).symm
  change spectralIntermediateArtin p k n u FM xFM =
    Abelianization.of sigmaFM at hArtinAbFM
  have hArtinAbFixed : spectralIntermediateArtin p k n u E xFixed =
      Abelianization.of sigmaFixed := by
    exact spectral_intermediate_transport
      p k n u FM E hfixed.symm xFM sigmaFM hArtinAbFM
  have hfixedArtin : fixedArtinHom ℚ_[p] M H xFixed =
      Abelianization.of
        ((IntermediateField.subgroupEquivAlgEquiv H).symm sigmaFixed) := by
    change (IntermediateField.subgroupEquivAlgEquiv H).symm.abelianizationCongr
        (spectralIntermediateArtin p k n u E xFixed) = _
    rw [hArtinAbFixed]
    rfl
  change abelianizedSubgroupInclusion H
      (fixedArtinHom ℚ_[p] M H xFixed) =
    localArtinHom ℚ_[p] M
      (normOnUnits ℚ_[p] E xFixed) at hsquarex
  rw [hfixedArtin] at hsquarex
  have hnorm : normOnUnits ℚ_[p] FM xFM =
      normOnUnits ℚ_[p] F varpi := by
    apply Units.ext
    change Algebra.norm ℚ_[p] (eF (varpi : F)) =
      Algebra.norm ℚ_[p] (varpi : F)
    let he : (algebraMap ℚ_[p] FM).comp (RingEquiv.refl ℚ_[p]).toRingHom =
        eF.toRingEquiv.toRingHom.comp (algebraMap ℚ_[p] F) := by
      apply RingHom.ext
      intro a
      exact (eF.commutes a).symm
    simpa using (Algebra.norm_eq_of_equiv_equiv
      (RingEquiv.refl ℚ_[p]) eF.toRingEquiv he (varpi : F)).symm
  have hnormFixed :
      normOnUnits ℚ_[p] E xFixed =
        normOnUnits ℚ_[p] FM xFM := by
    apply Units.ext
    let eFixed : E ≃ₐ[ℚ_[p]] FM :=
      IntermediateField.equivOfEq hfixed
    have hex : eFixed xFixed = xFM := by
      apply Subtype.ext
      change (((xFixed : E) : M)) = ((xFM : FM) : M)
      exact intermediate_cast_val hfixed.symm xFM
    let he : (algebraMap ℚ_[p] FM).comp (RingEquiv.refl ℚ_[p]).toRingHom =
        eFixed.toRingEquiv.toRingHom.comp (algebraMap ℚ_[p] E) := by
      apply RingHom.ext
      intro a
      exact (eFixed.commutes a).symm
    change Algebra.norm ℚ_[p] (xFixed : E) =
      Algebra.norm ℚ_[p] (xFM : FM)
    have hn := Algebra.norm_eq_of_equiv_equiv
      (RingEquiv.refl ℚ_[p]) eFixed.toRingEquiv he (xFixed : _)
    calc
      Algebra.norm ℚ_[p] (xFixed : E) =
          Algebra.norm ℚ_[p] (eFixed xFixed) := by simpa using hn
      _ = Algebra.norm ℚ_[p] (xFM : FM) := congrArg _ hex
  rw [hnormFixed, hnorm] at hsquarex
  have hinclusion : abelianizedSubgroupInclusion H
      (Abelianization.of
        ((IntermediateField.subgroupEquivAlgEquiv H).symm sigmaFixed)) =
      Abelianization.of (sigmaFixed.restrictScalars ℚ_[p]) := by
    rfl
  rw [hinclusion] at hsquarex
  have hsigma : sigmaFixed.restrictScalars ℚ_[p] =
      comparisonWittFrobenius p k n u := by
    have hsigmaFM : sigmaFM.restrictScalars ℚ_[p] =
        comparisonWittFrobenius p k n u := by
      rfl
    apply AlgEquiv.ext
    intro x
    dsimp only [sigmaFixed, E]
    change (_root_.cast (congrArg
      (fun J : IntermediateField ℚ_[p] M ↦ Gal(M/J)) hfixed.symm) sigmaFM) x = _
    rw [intermediate_gal_cast hfixed.symm sigmaFM x]
    exact DFunLike.congr_fun hsigmaFM x
  rw [hsigma] at hsquarex
  exact hsquarex.symm

theorem comparison_witt_uniformizer
    (n : ℕ) (u : ℤ_[p]ˣ) :
    localArtinHom ℚ_[p] (comparisonWittField p k n u)
        (padicUniformizerUnit p u) =
      Abelianization.of (comparisonWittFrobenius p k n u) := by
  rw [← units_comparison_prime p k n u]
  exact artin_comparison_uniformizer
    p k n u (basicComparisonPrime p k n u)
      (basic_comparison_order p k n u)

set_option synthInstance.maxHeartbeats 500000 in
-- Transporting commutativity through the cyclotomic root-field equivalence is instance-heavy.
noncomputable instance cyclotomic_witt_commutative
    (n : ℕ) :
    IsMulCommutative Gal(cyclotomicWittField p k n/ℚ_[p]) := by
  let Z := (cyclotomicLubinDatum p).RootField ℚ_[p] n
  let E := cyclotomicWittField p k n
  let eZ : Z ≃ₐ[ℚ_[p]] E :=
    AlgEquiv.ofInjectiveField (cyclotomicAlgHom p k n)
  refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
  apply eZ.autCongr.symm.injective
  simpa only [map_mul] using
    mul_comm (eZ.autCongr.symm sigma) (eZ.autCongr.symm tau)

set_option maxHeartbeats 5000000 in
-- Restriction compares two transported cyclotomic Artin maps through a compositum.
set_option synthInstance.maxHeartbeats 500000 in
theorem abelian_witt_restriction
    (n : ℕ) (u : ℤ_[p]ˣ) :
    abelianArtinHom ℚ_[p] (cyclotomicWittField p k n)
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) =
      (comparisonWittFrobenius p k n u).restrictNormal
        (cyclotomicWittField p k n) := by
  let D := padicLubinDatum p
  let R := D.RootField ℚ_[p] n
  let Z := (cyclotomicLubinDatum p).RootField ℚ_[p] n
  let E := cyclotomicWittField p k n
  let M := comparisonWittField p k n u
  let eZ : Z ≃ₐ[ℚ_[p]] E := AlgEquiv.ofInjectiveField (cyclotomicAlgHom p k n)
  let e₀ : R ≃ₐ[ℚ_[p]] Z :=
    padicIntegerAlg p n
  let e : R ≃ₐ[ℚ_[p]] E := e₀.trans eZ
  letI : IsMulCommutative Gal(E/ℚ_[p]) := by
    refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
    apply eZ.autCongr.symm.injective
    simpa only [map_mul] using
      mul_comm (eZ.autCongr.symm sigma) (eZ.autCongr.symm tau)
  let punit : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p])
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let xunit : ℚ_[p]ˣ := Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  have hM := comparison_witt_uniformizer p k n u
  have htower := abelianized_restrict_normal ℚ_[p] M E
  have htowerValue := DFunLike.congr_fun htower (padicUniformizerUnit p u)
  have hRestr : abelianArtinHom ℚ_[p] E
      (padicUniformizerUnit p u) =
      (comparisonWittFrobenius p k n u).restrictNormal E := by
    change Abelianization.lift (AlgEquiv.restrictNormalHom E)
        (localArtinHom ℚ_[p] M (padicUniformizerUnit p u)) =
      abelianArtinHom ℚ_[p] E
        (padicUniformizerUnit p u) at htowerValue
    rw [hM] at htowerValue
    simpa using htowerValue.symm
  have hEp : abelianArtinHom ℚ_[p] E punit = 1 := by
    have htransport := DFunLike.congr_fun
      (abelian_artin_alg ℚ_[p] R E e) punit
    change e.autCongr (abelianArtinHom ℚ_[p] R punit) =
      abelianArtinHom ℚ_[p] E punit at htransport
    rw [abelian_artin_uniformizer]
      at htransport
    change e.autCongr 1 = abelianArtinHom ℚ_[p] E punit at htransport
    rw [map_one] at htransport
    exact htransport.symm
  have hfactor : padicUniformizerUnit p u = punit * xunit := by
    apply Units.ext
    rfl
  rw [hfactor, map_mul, hEp, one_mul] at hRestr
  exact hRestr

set_option maxHeartbeats 3000000 in
-- Extensionality for the transported root-field automorphisms unfolds the explicit Witt root.
set_option synthInstance.maxHeartbeats 500000 in
theorem comparison_witt_restrict
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let E := cyclotomicWittField p k n
    let e := (padicIntegerAlg p n).trans
      (AlgEquiv.ofInjectiveField (cyclotomicAlgHom p k n))
    let q := padicIntInteger p (n + 1) u⁻¹
    (comparisonWittFrobenius p k n u).restrictNormal E =
      e.autCongr
        (padicIntegerCyclotomic p n q) := by
  let D := padicLubinDatum p
  let R := D.RootField ℚ_[p] n
  let Z := (cyclotomicLubinDatum p).RootField ℚ_[p] n
  let E := cyclotomicWittField p k n
  let eZ : Z ≃ₐ[ℚ_[p]] E := AlgEquiv.ofInjectiveField (cyclotomicAlgHom p k n)
  let e₀ : R ≃ₐ[ℚ_[p]] Z :=
    padicIntegerAlg p n
  let e : R ≃ₐ[ℚ_[p]] E := e₀.trans eZ
  let q := padicIntInteger p (n + 1) u⁻¹
  let orbit := padicIntegerCyclotomic p n q
  let lhs : Z →+* E :=
    ((comparisonWittFrobenius p k n u).restrictNormal E).toRingEquiv.toRingHom.comp
      eZ.toRingEquiv.toRingHom
  let rhs : Z →+* E :=
    (e.autCongr orbit).toRingEquiv.toRingHom.comp eZ.toRingEquiv.toRingHom
  have hhom : lhs = rhs := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      change ((comparisonWittFrobenius p k n u).restrictNormal E)
          (eZ (algebraMap ℚ_[p] Z a)) =
        (e.autCongr orbit) (eZ (algebraMap ℚ_[p] Z a))
      rw [eZ.commutes]
      simp
    · dsimp only [lhs, rhs, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe]
      change ((comparisonWittFrobenius p k n u).restrictNormal E)
          (eZ ((cyclotomicLubinDatum p).root ℚ_[p] n)) =
        (e.autCongr orbit)
          (eZ ((cyclotomicLubinDatum p).root ℚ_[p] n))
      apply Subtype.ext
      have hrestrict (y : E) :
          ((((comparisonWittFrobenius p k n u).restrictNormal E) y : E) :
              FractionRing (PadicWittRing p k n)) =
            (((comparisonWittFrobenius p k n u)
              (cyclotomicWittComparison p k n u y) :
                comparisonWittField p k n u) :
              FractionRing (PadicWittRing p k n)) := by
        have h := AlgEquiv.restrictNormal_commutes
          (comparisonWittFrobenius p k n u) E y
        exact congrArg Subtype.val h
      rw [hrestrict, comparison_frobenius_coe]
      have hroot :
          (((cyclotomicWittComparison p k n u
              (eZ ((cyclotomicLubinDatum p).root ℚ_[p] n)) :
                comparisonWittField p k n u) :
              FractionRing (PadicWittRing p k n))) =
            algebraMap (PadicWittRing p k n)
              (FractionRing (PadicWittRing p k n))
              (cyclotomicWittRoot p k n) := by
        change cyclotomicAlgHom p k n
            ((cyclotomicLubinDatum p).root ℚ_[p] n) = _
        exact padic_cyclotomic_fraction p k n
      rw [hroot]
      change padicFrobeniusFraction p k n u
          (algebraMap (PadicWittRing p k n)
            (FractionRing (PadicWittRing p k n))
            (cyclotomicWittRoot p k n)) =
        ((e.autCongr orbit) (eZ ((cyclotomicLubinDatum p).root ℚ_[p] n)) :
          E)
      rw [frobenius_fraction_root]
      have heRoot :
          eZ ((cyclotomicLubinDatum p).root ℚ_[p] n) =
            e (D.root ℚ_[p] n) := by
        change eZ ((cyclotomicLubinDatum p).root ℚ_[p] n) =
          eZ (e₀ (D.root ℚ_[p] n))
        rw [padic_integer_alg]
      rw [heRoot, AlgEquiv.autCongr_apply]
      change algebraMap (PadicWittRing p k n)
          (FractionRing (PadicWittRing p k n))
          (padicWittValue p k n u⁻¹) =
        e (orbit (e.symm (e (D.root ℚ_[p] n))))
      rw [e.symm_apply_apply]
      rw [padic_integer_cyclotomic]
      simp only [map_sub, map_pow, map_add, map_one]
      change algebraMap (PadicWittRing p k n)
          (FractionRing (PadicWittRing p k n))
          (padicWittValue p k n u⁻¹) =
        (1 + ((e (D.root ℚ_[p] n) : E) :
            FractionRing (PadicWittRing p k n))) ^
              ((padicZMod p (n + 1) q :
                ZMod (p ^ (n + 1))).val) - 1
      have heNormRoot :
          ((e (D.root ℚ_[p] n) : E) :
              FractionRing (PadicWittRing p k n)) =
            algebraMap (PadicWittRing p k n)
              (FractionRing (PadicWittRing p k n))
              (cyclotomicWittRoot p k n) := by
        change cyclotomicAlgHom p k n (e₀ (D.root ℚ_[p] n)) = _
        rw [padic_integer_alg]
        exact padic_cyclotomic_fraction p k n
      rw [heNormRoot]
      exact padic_witt_pow p k n u⁻¹
  apply AlgEquiv.ext
  intro x
  obtain ⟨z, rfl⟩ := eZ.surjective x
  exact DFunLike.congr_fun hhom z

include k

set_option maxHeartbeats 5000000 in
-- The final normalization combines Artin transport, restriction, and the explicit orbit formula.
set_option synthInstance.maxHeartbeats 500000 in
/-- The previously postulated orientation statement is a theorem: the
cohomological finite Artin map on cyclotomic units is the inverse of the
direct Lubin--Tate orbit. -/
theorem padicArtinNormalization :
    PadicArtinNormalization p := by
  intro n u
  let D := padicLubinDatum p
  let R := D.RootField ℚ_[p] n
  let Z := (cyclotomicLubinDatum p).RootField ℚ_[p] n
  let E := cyclotomicWittField p k n
  let eZ : Z ≃ₐ[ℚ_[p]] E :=
    AlgEquiv.ofInjectiveField (cyclotomicAlgHom p k n)
  letI : FiniteDimensional ℚ_[p] E :=
    Module.Finite.equiv eZ.toLinearEquiv
  letI : IsGalois ℚ_[p] E := IsGalois.of_algEquiv eZ
  let e := (padicIntegerAlg p n).trans
    eZ
  let x : ℚ_[p]ˣ := Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  let q := padicIntInteger p (n + 1) u⁻¹
  let orbit := padicIntegerCyclotomic p n q
  letI : IsMulCommutative Gal(E/ℚ_[p]) :=
    cyclotomic_witt_commutative p k n
  have htransport := DFunLike.congr_fun
    (abelian_artin_alg ℚ_[p] R E e) x
  have hE := abelian_witt_restriction
    p k n u
  have haction := comparison_witt_restrict
    p k n u
  apply e.autCongr.injective
  calc
    e.autCongr (abelianArtinHom ℚ_[p] R x) =
        abelianArtinHom ℚ_[p] E x := htransport
    _ = (comparisonWittFrobenius p k n u).restrictNormal E := hE
    _ = e.autCongr orbit := haction



end
end Towers.CField.LRecip.PNProof

namespace Towers.CField.LRecip

open Towers.CField.LTate

noncomputable section

/-- The cyclotomic root-field unit normalization, with the auxiliary
algebraically closed residue field discharged canonically. -/
theorem padicArtinNormalization
    (p : ℕ) [Fact p.Prime] :
    PadicArtinNormalization p := by
  let k := AlgebraicClosure (ZMod p)
  exact PNProof.padicArtinNormalization p k

/-- The canonical finite local fundamental cocycle has the required cyclic
product on every cyclotomic Lubin--Tate unit orbit. -/
theorem fundamentalCocycleCalculation
    (p : ℕ) [Fact p.Prime] :
    PadicCocycleCalculation p := by
  apply fundamental_calculation_residue p
  exact (artin_normalization_residue p).mp
    (padicArtinNormalization p)

end

end Towers.CField.LRecip
