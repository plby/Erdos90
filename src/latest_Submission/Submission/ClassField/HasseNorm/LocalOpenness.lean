import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.Analysis.Normed.Field.TransferInstance
import Mathlib.Analysis.Normed.Module.Shrink
import Mathlib.Analysis.Normed.Ring.TransferInstance
import Mathlib.Topology.Instances.Shrink
import Submission.ClassField.Ideles.PrincipalUnitsSubgroup

/-!
# Openness of norm groups for arbitrary finite local extensions

Proposition V.4.12(b) does not require the extension to be Galois.  Embed a
finite extension in its normal closure.  Norm transitivity puts the norm
group of the normal closure inside the original norm group, and the former
is open by CFT I.1.3 and the finite local norm-residue theorem.  A subgroup
containing an open subgroup is open.
-/

namespace Submission.CField.HNorm

open Submission.CField.LFTheory
open Submission.CField.NCorr
open Submission.CField.LRecip
open Submission.CField.Ideles
open IntermediateField

noncomputable section

universe u v

variable (K : Type) [NontriviallyNormedField K] [CharZero K]
  [IsUltrametricDist K]

local instance finiteLocalNormOpenValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance finiteLocalNormOpenValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

/-- **Proposition V.4.12(b), openness clause.**  The norm subgroup of an
arbitrary finite extension of a characteristic-zero nonarchimedean local
field is open. -/
theorem normSubgroupOpen
    (L : Type)
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] :
    NormSubgroupOpen K L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : IsAlgClosure K (AlgebraicClosure L) := inferInstance
  letI : IsGalois K (AlgebraicClosure L) :=
    IsAlgClosure.isGalois K (AlgebraicClosure L)
  let M := normalClosure K L (AlgebraicClosure L)
  letI : IsGalois K M :=
    IsGalois.normalClosure K L (AlgebraicClosure L)
  letI : FiniteDimensional K M :=
    normalClosure.is_finiteDimensional K L (AlgebraicClosure L)
  letI : FiniteDimensional L M :=
    FiniteDimensional.right K L M
  letI : Finite (Kˣ ⧸ normSubgroup K M) :=
    Finite.of_injective (localArtinEquiv K M)
      (localArtinEquiv K M).injective
  letI : (normSubgroup K M).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have hopen : IsOpen (normSubgroup K M : Set Kˣ) :=
    norm_subgroup K M
  have hle : normSubgroup K M ≤ normSubgroup K L :=
    norm_subgroup_tower K M L
  exact Subgroup.isOpen_mono hle hopen

local instance finiteLocalNormOpenValuativeRelPoly
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F] :
    ValuativeRel F :=
  ValuativeRel.ofValuation (NormedField.valuation (K := F))

set_option maxHeartbeats 1000000 in
-- Transporting local norm openness through Type-0 shrink models requires a
-- large topology and field-equivalence calculation.
set_option synthInstance.maxHeartbeats 300000 in
-- Constructing the valuative topology on the shrink model requires deeper
-- valuation-instance search.
/-- The Type-0 local norm theorem applied after replacing small fields by
isomorphic Type-0 models.  The conclusion is transported back along the
induced homeomorphism of unit groups. -/
lemma subgroup_open_small
    (K : Type u) [Small.{0} K]
    [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
    [IsNonarchimedeanLocalField K]
    (L : Type v) [Small.{0} L]
    [Field L] [Algebra K L] [Module.Finite K L] :
    IsOpen (normSubgroup K L : Set Kˣ) := by
  let L0 := Shrink.{0} L
  let eK : (Shrink.{0} K) ≃+* K := Shrink.ringEquiv K
  let eL : L0 ≃+* L := Shrink.ringEquiv L
  letI : NormedField (Shrink.{0} K) :=
    NormedField.induced (Shrink.{0} K) K eK.toRingHom eK.injective
  letI : NontriviallyNormedField (Shrink.{0} K) :=
    { (inferInstance : NormedField (Shrink.{0} K)) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
        refine ⟨eK.symm x, ?_⟩
        change 1 < ‖eK (eK.symm x)‖
        simpa using hx }
  letI : CharZero (Shrink.{0} K) := eK.toRingHom.charZero
  letI : IsUltrametricDist (Shrink.{0} K) := by
    constructor
    intro x y z
    change dist (eK x) (eK z) ≤
      max (dist (eK x) (eK y)) (dist (eK y) (eK z))
    exact dist_triangle_max (eK x) (eK y) (eK z)
  letI : Algebra (Shrink.{0} K) K := eK.toRingHom.toAlgebra
  let eKAlg : (Shrink.{0} K) ≃ₐ[(Shrink.{0} K)] K :=
    AlgEquiv.ofRingEquiv (f := eK) (fun _ ↦ rfl)
  letI : Module.Finite (Shrink.{0} K) K := Module.Finite.equiv eKAlg.toLinearEquiv
  letI : Algebra (Shrink.{0} K) L :=
    ((algebraMap K L).comp eK.toRingHom).toAlgebra
  letI : IsScalarTower (Shrink.{0} K) K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite (Shrink.{0} K) L := Module.Finite.trans K L
  letI : Algebra (Shrink.{0} K) L0 := inferInstance
  let eLAlg : L0 ≃ₐ[(Shrink.{0} K)] L := Shrink.algEquiv (Shrink.{0} K) L
  letI : Module.Finite (Shrink.{0} K) L0 :=
    Module.Finite.equiv eLAlg.toLinearEquiv.symm
  letI : ValuativeRel (Shrink.{0} K) :=
    finiteLocalNormOpenValuativeRel (K := (Shrink.{0} K))
  letI : Valuation.Compatible (NormedField.valuation (K := (Shrink.{0} K))) :=
    finiteLocalNormOpenValuationCompatible (K := (Shrink.{0} K))
  haveI htop : IsValuativeTopology (Shrink.{0} K) := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : (Shrink.{0} K)) ↔
          ∃ γ : (MonoidWithZeroHom.ValueGroup₀
              (NormedField.valuation (K := (Shrink.{0} K))))ˣ,
            {x | (NormedField.valuation (K := (Shrink.{0} K))).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := (Shrink.{0} K))).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := (Shrink.{0} K))).exists_setOf_restrict_le_iff 0 s
  letI hcompact : LocallyCompactSpace (Shrink.{0} K) :=
    (Shrink.homeomorph K).symm.isOpenEmbedding.locallyCompactSpace
  haveI hvaluationNontrivial :
      (NormedField.valuation (K := (Shrink.{0} K))).IsNontrivial := by
    constructor
    obtain ⟨x, hx⟩ :=
      NontriviallyNormedField.non_trivial (α := (Shrink.{0} K))
    refine ⟨x, ?_, ?_⟩
    · have hx0 : x ≠ 0 := by
        intro h
        subst x
        have hnorm_zero : ‖(0 : Shrink.{0} K)‖ = 0 := norm_zero
        rw [hnorm_zero] at hx
        exact (not_lt_of_ge zero_le_one) hx
      intro h
      apply hx0
      change ‖x‖₊ = 0 at h
      exact nnnorm_eq_zero.mp h
    · intro h
      change ‖x‖₊ = 1 at h
      have hnorm : ‖x‖ = 1 := by
        have hc := congrArg (fun r : NNReal ↦ (r : ℝ)) h
        change (↑‖x‖₊ : ℝ) = (↑(1 : NNReal) : ℝ)
        exact hc
      exact (ne_of_gt hx) hnorm
  haveI hnontrivial : ValuativeRel.IsNontrivial (Shrink.{0} K) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := (Shrink.{0} K)))).mpr inferInstance
  letI hlocal : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hcompact
      toIsNontrivial := hnontrivial }
  have hopen : IsOpen (normSubgroup (Shrink.{0} K) L0 : Set (Shrink.{0} K)ˣ) :=
    @normSubgroupOpen (Shrink.{0} K) inferInstance inferInstance
      inferInstance L0 hlocal inferInstance inferInstance inferInstance
  have he : (algebraMap K L).comp eK.toRingHom =
      eL.toRingHom.comp (algebraMap (Shrink.{0} K) L0) := by
    ext x
    exact (eLAlg.commutes x).symm
  have hnorm :
      (normSubgroup (Shrink.{0} K) L0).comap (Units.map eK.symm.toRingHom) =
        normSubgroup K L := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Units.map eL.toRingHom y, ?_⟩
      apply Units.ext
      change Algebra.norm K (eL (y : L0)) = (x : K)
      have hn := Algebra.norm_eq_of_equiv_equiv eK eL he (y : L0)
      change Algebra.norm (Shrink.{0} K) (y : L0) =
        eK.symm (Algebra.norm K (eL (y : L0))) at hn
      have hy' := congrArg Units.val hy
      change Algebra.norm (Shrink.{0} K) (y : L0) = eK.symm (x : K) at hy'
      apply eK.symm.injective
      rw [← hn, ← hy']
    · rintro ⟨y, hy⟩
      refine ⟨Units.map eL.symm.toRingHom y, ?_⟩
      apply Units.ext
      change Algebra.norm (Shrink.{0} K) (eL.symm (y : L)) = eK.symm (x : K)
      have hn := Algebra.norm_eq_of_equiv_equiv eK eL he
        (eL.symm (y : L))
      rw [eL.apply_symm_apply] at hn
      have hy' := congrArg Units.val hy
      change Algebra.norm K (y : L) = (x : K) at hy'
      rw [hn, hy']
  rw [← hnorm]
  let eKC : (Shrink.{0} K) ≃ₜ* K :=
    { __ := eK.toMulEquiv
      continuous_toFun := (Shrink.homeomorph K).symm.continuous
      continuous_invFun := (Shrink.homeomorph K).continuous }
  exact hopen.preimage (Units.mapContinuousMulEquiv eKC.symm).continuous

/-- The principal-unit conclusion of Proposition V.4.12(b), now without a
Galois hypothesis. -/
theorem principal_unit_norm
    (L : Type)
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] :
    ∃ m : ℕ,
      principalUnitField K m ≤ normSubgroup K L :=
  norm_open K L
    (normSubgroupOpen K L)

end

end Submission.CField.HNorm
