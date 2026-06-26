import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Convex
import Submission.NumberTheory.Units.SUnits
import Submission.ClassField.NormCorrespondence.PrincipalUnitQuotients
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure
import Submission.ClassField.Ideles.ModulusUnitSubgroup
import Submission.ClassField.Ideles.FinitePlaceCompletion
import Submission.ClassField.HasseNorm.UnramifiedLocal
import Submission.ClassField.HasseNorm.InfiniteBasicSubgroup

/-!
# Modulus-unit subgroups form a basis of open idèle subgroups

This is the second topological input in Corollary V.4.13.  The positive
component at every real place is the identity component of the
archimedean idèles, hence lies in every open subgroup.  On the everywhere
unit finite idèles, the restricted-product topology is the product topology;
a basic neighborhood restricts only finitely many coordinates, and deep ray
unit subgroups fit inside those finitely many neighborhoods.
-/

namespace Submission.CField.HNorm

open Filter Ideal IsDedekindDomain NumberField Set
open IsLocalRing ValuativeRel
open Topology
open Submission.NumberTheory.Milne
open Submission.CField.NCorr
open Submission.CField.LBrauer
open Submission.CField.RCGroups
open Submission.CField.Ideles
open scoped RestrictedProduct Topology

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

variable {K : Type u} [Field K] [NumberField K]

private theorem connected_pos_units :
    IsConnected (Units.posSubgroup ℝ : Set ℝˣ) := by
  let X := {x : ℝ // 0 < x}
  let f : X → ℝˣ := fun x ↦ Units.mk0 x.1 x.2.ne'
  letI : ConnectedSpace X := Subtype.connectedSpace isConnected_Ioi
  have hf : Continuous f := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    · exact (continuous_subtype_val.inv₀ fun x ↦ x.2.ne')
  have hrange : Set.range f = (Units.posSubgroup ℝ : Set ℝˣ) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hu
      refine ⟨⟨(u : ℝ), hu⟩, ?_⟩
      exact Units.ext rfl
  rw [← hrange]
  exact isConnected_range hf

private theorem connected_complex_units :
    IsConnected (Set.univ : Set ℂˣ) := by
  exact isConnected_univ

omit [NumberField K] in
/-- Each local factor used in the archimedean basic subgroup is connected. -/
theorem infinite_basic_connected
    (v : InfinitePlace K) :
    IsConnected (infiniteBasicSubgroup (K := K) v :
      Set v.Completionˣ) := by
  classical
  rw [infiniteBasicSubgroup]
  split_ifs with hv
  · let e : v.Completion ≃ₜ* ℝ :=
      { __ := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMulEquiv
        continuous_toFun :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
        continuous_invFun :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous }
    let eu : v.Completionˣ ≃ₜ* ℝˣ := Units.mapContinuousMulEquiv e
    exact eu.toHomeomorph.isConnected_preimage.mpr connected_pos_units
  · have hvc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : v.Completion ≃ₜ* ℂ :=
      { __ := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvc).toMulEquiv
        continuous_toFun :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hvc).continuous
        continuous_invFun :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hvc).symm.continuous }
    let eu : v.Completionˣ ≃ₜ* ℂˣ := Units.mapContinuousMulEquiv e
    simpa only [preimage_univ] using
      eu.toHomeomorph.isConnected_preimage.mpr connected_complex_units

omit [NumberField K] in
/-- The full archimedean basic subgroup is connected and contains one. -/
theorem infinite_idele_connected :
    IsConnected (infiniteIdeleSubgroup (K := K) :
      Set (InfiniteAdeleRing K)ˣ) := by
  let s : Set ((v : InfinitePlace K) → v.Completionˣ) :=
    Set.univ.pi fun v ↦
      (infiniteBasicSubgroup (K := K) v : Set v.Completionˣ)
  have hs : IsConnected s := by
    constructor
    · refine ⟨fun v ↦ 1, ?_⟩
      intro v _
      exact (infiniteBasicSubgroup (K := K) v).one_mem
    · exact isPreconnected_univ_pi fun v ↦
        (infinite_basic_connected (K := K) v).isPreconnected
  have hpre := ContinuousMulEquiv.piUnits.toHomeomorph.isConnected_preimage.mpr hs
  convert hpre using 1
  ext a
  have hleft :
      a ∈ infiniteIdeleSubgroup (K := K) ↔
        ∀ v, MulEquiv.piUnits a v ∈
          infiniteBasicSubgroup (K := K) v := Iff.rfl
  apply hleft.trans
  change (∀ v, MulEquiv.piUnits a v ∈
      infiniteBasicSubgroup (K := K) v) ↔
    MulEquiv.piUnits a ∈ s
  simp only [s, Set.mem_pi, Set.mem_univ, true_implies]
  rfl

set_option synthInstance.maxHeartbeats 300000 in
-- Resolving the prime-adic integer-ring equivalence and its unit topology
-- requires a deeper instance search.
set_option maxHeartbeats 2000000 in
-- Comparing the two ray subgroups unfolds their dependent completion maps.
set_option maxRecDepth 100000 in
/-- The ray subgroup defined using the prime-adic integer ring is the usual
principal-unit subgroup of the completed field. -/
theorem ray_principal_field
    (P : FinitePrime K) (m : ℕ) :
    let F := P.adicCompletion K
    letI : NontriviallyNormedField F :=
      adicNontriviallyNormed P
    letI : CharZero F :=
      (RingHom.charZero_iff (algebraMap K F).injective).mp inferInstance
    letI : IsUltrametricDist F := by infer_instance
    letI : ValuativeRel F := adicValuativeRel P
    letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
    letI : IsNonarchimedeanLocalField F :=
      adicNonarchimedeanField P
    rayLocalSubgroup (K := K) P m =
      principalUnitField F m := by
  dsimp only
  let F := P.adicCompletion K
  let C := P.adicCompletionIntegers K
  letI : NontriviallyNormedField F :=
    adicNontriviallyNormed P
  letI : CharZero F :=
    (RingHom.charZero_iff (algebraMap K F).injective).mp inferInstance
  letI : IsUltrametricDist F := by infer_instance
  letI : ValuativeRel F := adicValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    adicNonarchimedeanField P
  let A := 𝒪[F]
  let eA : A ≃+* C :=
    (valuativeIntegerNorm F).trans
      (normedIntegerIntegers P)
  let eU : Aˣ ≃* Cˣ := Units.mapEquiv eA.toMulEquiv
  let jA : Aˣ →* Fˣ := Units.map A.subtype
  let jC : Cˣ →* Fˣ :=
    C.unitGroup.subtype.comp C.unitGroupMulEquiv.symm.toMonoidHom
  have hprincipal (u : Cˣ) :
      eU.symm u ∈ principalUnitSubgroup A m ↔
        u ∈ principalUnitSubgroup C m := by
    have heu : eA (eU.symm u : A) = (u : C) := by
      exact congrArg Units.val (eU.apply_symm_apply u)
    change ((eU.symm u : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ m) ↔
      ((u : C) - 1 ∈ IsLocalRing.maximalIdeal C ^ m)
    rw [← Ideal.apply_mem_of_equiv_iff (f := eA)]
    simp only [map_sub, map_one, Ideal.map_pow,
      IsLocalRing.map_ringEquiv_maximalIdeal, heu]
  have hj (u : Cˣ) : jA (eU.symm u) = jC u := by
    apply Units.ext
    rfl
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨eU.symm u, (hprincipal u).2 hu, ?_⟩
    exact hj u
  · rintro ⟨u, hu, rfl⟩
    refine ⟨eU u, (hprincipal (eU u)).1 ?_, ?_⟩
    · simpa only [eU, MulEquiv.symm_apply_apply] using hu
    · simpa only [eU, MulEquiv.apply_symm_apply] using (hj (eU u)).symm

set_option synthInstance.maxHeartbeats 300000 in
-- The neighborhood argument resolves valuation and unit-topology instances
-- for a dependent finite completion.
set_option maxHeartbeats 2000000 in
-- Extracting a ray level from an arbitrary unit neighborhood uses several
-- transported topological group equivalences.
/-- Every neighborhood of one in a finite completion contains a positive
level ray subgroup. -/
theorem positive_ray_subset
    (P : FinitePrime K) (V : Set (P.adicCompletion K)ˣ)
    (hV : V ∈ 𝓝 (1 : (P.adicCompletion K)ˣ)) :
    ∃ m : ℕ, 0 < m ∧
      (rayLocalSubgroup (K := K) P m :
        Set (P.adicCompletion K)ˣ) ⊆ V := by
  let F := P.adicCompletion K
  letI : NontriviallyNormedField F :=
    adicNontriviallyNormed P
  letI : CharZero F :=
    (RingHom.charZero_iff (algebraMap K F).injective).mp inferInstance
  letI : IsUltrametricDist F := by infer_instance
  letI : ValuativeRel F := adicValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    adicNonarchimedeanField P
  let A := 𝒪[F]
  let j : Aˣ →* Fˣ := Units.map A.subtype
  have hj : Continuous j := continuous_subtype_val.units_map _
  have hpre : j ⁻¹' V ∈ 𝓝 (1 : Aˣ) := by
    exact hj.continuousAt hV
  obtain ⟨m, -, hm⟩ := (principal_unit_basis F).mem_iff.mp hpre
  refine ⟨m + 1, Nat.zero_lt_succ m, ?_⟩
  rw [ray_principal_field
    (K := K) P (m + 1)]
  rintro x ⟨u, hu, rfl⟩
  apply hm
  change (u : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ m
  exact Ideal.pow_le_pow_right (Nat.le_succ m) hu

private theorem idele_unit_open
    (P : FinitePrime K) :
    IsOpen (IdeleUnitSubgroup (OK K) K P :
      Set (P.adicCompletion K)ˣ) := by
  apply Submonoid.isOpen_units
  change IsOpen (P.adicCompletionIntegers K : Set (P.adicCompletion K))
  exact Valued.isOpen_valuationSubring _

set_option synthInstance.maxHeartbeats 300000 in
-- The global cofinality proof combines all finite completion topology
-- instances and the archimedean connected factor.
set_option maxHeartbeats 3000000 in
-- Assembling a global modulus from finitely many local neighborhoods requires
-- a large restricted-product openness calculation.
/-- Milne's `W_m` form a cofinal family among the open subgroups of the
idèle group. -/
theorem modulusSubgroupsCofinal :
    ModulusSubgroupsCofinal (K := K) := by
  classical
  intro H hH
  let localUnits : FinitePrime K → Type u := fun P ↦
    IdeleUnitSubgroup (OK K) K P
  let finiteUnitMap : (∀ P, localUnits P) →
      FiniteIdeles (OK K) K :=
    RestrictedProduct.structureMap
      (fun P : FinitePrime K ↦ (P.adicCompletion K)ˣ)
      (fun P : FinitePrime K ↦
        (IdeleUnitSubgroup (OK K) K P :
          Set (P.adicCompletion K)ˣ)) Filter.cofinite
  have hfiniteUnitMap : Continuous finiteUnitMap := by
    exact (RestrictedProduct.isOpenEmbedding_structureMap
      (R := fun P : FinitePrime K ↦ (P.adicCompletion K)ˣ)
      (A := fun P : FinitePrime K ↦
        (IdeleUnitSubgroup (OK K) K P :
          Set (P.adicCompletion K)ˣ))
      (fun P ↦ idele_unit_open (K := K) P)).continuous
  let finiteOnly : (∀ P, localUnits P) → IdeleGroup (OK K) K :=
    fun u ↦ (1, finiteUnitMap u)
  have hfiniteOnly : Continuous finiteOnly :=
    continuous_const.prodMk hfiniteUnitMap
  have hpre : finiteOnly ⁻¹' (H : Set (IdeleGroup (OK K) K)) ∈
      𝓝 (1 : ∀ P, localUnits P) := by
    apply (hH.preimage hfiniteOnly).mem_nhds
    change (1, finiteUnitMap 1) ∈ H
    have hmapOne : finiteUnitMap 1 = 1 := by
      apply RestrictedProduct.ext
      intro P
      rfl
    rw [hmapOne]
    exact H.one_mem
  rw [nhds_pi, Filter.mem_pi'] at hpre
  obtain ⟨I, t, ht, htSub⟩ := hpre
  have hlocal : ∀ (P : FinitePrime K), P ∈ I →
      ∃ m : ℕ, 0 < m ∧
        (rayLocalSubgroup (K := K) P m :
          Set (P.adicCompletion K)ˣ) ⊆
            Subtype.val '' t P := by
    intro P hPI
    have himage : Subtype.val '' t P ∈
        𝓝 (1 : (P.adicCompletion K)ˣ) := by
      let emb : localUnits P → (P.adicCompletion K)ˣ := Subtype.val
      have hemb : IsOpenEmbedding emb :=
        (idele_unit_open (K := K) P).isOpenEmbedding_subtypeVal
      have hmap : Filter.map emb (𝓝 (1 : localUnits P)) =
          𝓝 (1 : (P.adicCompletion K)ˣ) := by
        simpa only [emb] using
          hemb.map_nhds_eq (1 : localUnits P)
      rw [← hmap]
      rw [Filter.mem_map]
      exact Filter.mem_of_superset (ht P)
        (Set.subset_preimage_image Subtype.val (t P))
    exact positive_ray_subset
      (K := K) P (Subtype.val '' t P) himage
  choose level hlevelPos hlevel using hlocal
  let exponent : FinitePrime K → ℕ := fun P ↦
    if hP : P ∈ I then level P hP else 0
  have hexponentSupport : ∀ P, exponent P ≠ 0 → P ∈ I := by
    intro P hP
    by_contra hPI
    exact hP (by simp only [exponent, dif_neg hPI])
  let finitePart : FinitePrime K →₀ ℕ :=
    Finsupp.onFinset I exponent hexponentSupport
  let m : Modulus K :=
    { finite := finitePart
      infinite := Finset.univ }
  refine ⟨m, ?_⟩
  intro a ha
  rw [idele_modulus_subgroup] at ha
  have haModulus := ha.1
  have haFiniteUnits := ha.2
  have haInfinite : a.1 ∈ infiniteIdeleSubgroup (K := K) := by
    intro v
    by_cases hv : v.IsReal
    · let w : RealInfinitePlace K := ⟨v, hv⟩
      have hw := haModulus.2 w (by simp only [m, Finset.mem_univ])
      simpa only [infiniteBasicSubgroup, dif_pos hv,
        positiveRealSubgroup] using hw
    · rw [infiniteBasicSubgroup, dif_neg hv]
      exact Subgroup.mem_top _
  have haInfiniteH : (a.1, 1) ∈ H := by
    let S : Subgroup (infiniteIdeleSubgroup (K := K)) :=
      { carrier := {x | ((x : (InfiniteAdeleRing K)ˣ), 1) ∈ H}
        one_mem' := by
          simpa only [Subgroup.coe_one] using H.one_mem
        mul_mem' := by
          intro x y hx hy
          simpa only [Subgroup.coe_mul, Prod.mk_mul_mk, mul_one] using
            H.mul_mem hx hy
        inv_mem' := by
          intro x hx
          simpa only [Subgroup.coe_inv, Prod.inv_mk, inv_one] using
            H.inv_mem hx }
    have hSopen : IsOpen (S : Set (infiniteIdeleSubgroup (K := K))) := by
      change IsOpen
        ((fun x : infiniteIdeleSubgroup (K := K) =>
            (((x : (InfiniteAdeleRing K)ˣ), 1) :
              IdeleGroup (OK K) K)) ⁻¹'
          (H : Set (IdeleGroup (OK K) K)))
      exact hH.preimage (continuous_subtype_val.prodMk continuous_const)
    have hSclosed : IsClosed (S : Set (infiniteIdeleSubgroup (K := K))) :=
      S.isClosed_of_isOpen hSopen
    haveI : PreconnectedSpace (infiniteIdeleSubgroup (K := K)) :=
      Subtype.preconnectedSpace (infinite_idele_connected (K := K)).isPreconnected
    have hStop : (S : Set (infiniteIdeleSubgroup (K := K))) = Set.univ :=
      IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨1, S.one_mem⟩
    have haS : (⟨a.1, haInfinite⟩ :
        infiniteIdeleSubgroup (K := K)) ∈ (S : Set _) := by
      rw [hStop]
      exact Set.mem_univ _
    exact haS
  let b : ∀ P, localUnits P := fun P ↦
    ⟨a.2.1 P, haFiniteUnits P⟩
  have hb : b ∈ (I : Set (FinitePrime K)).pi t := by
    intro P hPI
    have hfiniteValue : m.finite P = level P hPI := by
      have hPI' : P ∈ I := hPI
      simp only [m, finitePart, Finsupp.onFinset_apply, exponent,
        dif_pos hPI']
    have hsupport : P ∈ m.finiteSupport := by
      rw [Modulus.finite_support_iff, hfiniteValue]
      exact (hlevelPos P hPI).ne'
    have hray := haModulus.1 P hsupport
    rw [hfiniteValue] at hray
    obtain ⟨u, hu, hua⟩ := hlevel P hPI hray
    have hub : u = b P := Subtype.ext hua
    rwa [← hub]
  have haFiniteH : (1, a.2) ∈ H := by
    have hbH := htSub hb
    change finiteOnly b ∈ H at hbH
    have hmap : finiteUnitMap b = a.2 := by
      apply RestrictedProduct.ext
      intro P
      rfl
    simpa only [finiteOnly, hmap] using hbH
  rw [show a = (a.1, 1) * (1, a.2) by
    apply Prod.ext
    · change a.1 = a.1 * 1
      exact (mul_one a.1).symm
    · change a.2 = 1 * a.2
      exact (one_mul a.2).symm]
  exact H.mul_mem haInfiniteH haFiniteH

end

end Submission.CField.HNorm
