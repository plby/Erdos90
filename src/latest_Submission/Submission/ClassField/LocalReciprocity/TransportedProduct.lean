import Submission.ClassField.LocalReciprocity.CyclicCase
import Submission.ClassField.LocalReciprocity.NormCompatibility
import Submission.ClassField.LocalReciprocity.TatePairing
import Submission.ClassField.CrossedProducts.MultiplicativeHComparison

/-!
# Proposition III.3.6

The local Artin symbol and the cup-product pairing with a rational
character are adjoint:

`chi (Artin(a)) = inv_K (a ∪ δ chi)`.
-/

namespace Submission.CField.LRecip

open CategoryTheory MonoidalCategory Rep
open scoped MonoidalCategory IsMulCommutative
open Submission.CField.LFTheory
open Submission.CField.COps
open Submission.CField.COps.CPBuild
open Submission.CField.COps.CPFuncto
open Submission.CField.LClass
open Submission.CField.CProduca
open Submission.CField.LBrauer
open Submission.CField.RExist

noncomputable section

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

local instance (priority := 10000) repIntModule36
    {J : Type} [Group J] (A : Rep.{0} ℤ J) : Module ℤ A := A.hV2

/-- On a finite cyclic group, cupping the cyclic product of a cocycle with
the normalized generator character recovers the class of that cocycle. -/
private theorem transported_cup_boundary
    {J M : Type} [CommGroup J] [Fintype J]
    [CommGroup M] [MulDistribMulAction J M]
    (g : J) (hg : ∀ x : J, x ∈ Subgroup.zpowers g)
    (hn : 1 < Nat.card J)
    (c : NMCocycl₂ (G := J) (M := M)) :
    let n := Nat.card J
    let _ : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
    let e : Multiplicative (ZMod n) ≃* J :=
      zmodMulEquivOfGenerator hg rfl
    let piJ := NMCocycl₂.cyclicProductInvariant c g
    let piAdd :
        (Rep.ofMulDistribMulAction J M).ρ.invariants :=
      ⟨Additive.ofMul piJ.1,
        fun j => congrArg Additive.ofMul (piJ.2 j)⟩
    transportedCyclicBoundary n J M e piAdd =
      multiplicative2Additive (MHTwo.mk c) := by
  dsimp only
  let n := Nat.card J
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  let e : Multiplicative (ZMod n) ≃* J :=
    zmodMulEquivOfGenerator hg rfl
  let piJ := NMCocycl₂.cyclicProductInvariant c g
  let pi : GroupH2.pulledInvariants (M := M) e :=
    (GroupH2.invariantsMulEquiv e).symm piJ
  let piAdd : (Rep.ofMulDistribMulAction J M).ρ.invariants :=
    ⟨Additive.ofMul piJ.1,
      fun j => congrArg Additive.ofMul (piJ.2 j)⟩
  have hcup := transported_boundary_carry
    n J M e pi
  have hcup' : transportedCyclicBoundary n J M e piAdd =
      multiplicative2Additive
        (transportedMultiplicativeCarry n J M e pi) := by
    simpa [piAdd, pi, piJ] using hcup
  let cyc := GroupH2.mulInvariantsMod
    (M := M) e hn
  have hcarryUniverse :=
    universe_transported_carry hn e pi
  have hcarry : cyc (transportedMultiplicativeCarry n J M e pi) =
      QuotientGroup.mk' (FMAct.norm J M).range piJ := by
    simpa [cyc, transportedMultiplicativeCarry,
      universeTransportedCarry, pi, piJ] using
        hcarryUniverse
  have hc := cyclic_invariants_mk hn e c
  have hc' : cyc (MHTwo.mk c) =
      QuotientGroup.mk' (FMAct.norm J M).range piJ := by
    simpa [cyc, piJ, e] using hc
  have hclass : transportedMultiplicativeCarry n J M e pi =
      MHTwo.mk c := by
    apply cyc.injective
    rw [hcarry, hc']
  rw [hcup', hclass]

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance fullValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance fullValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- The base unit and the cyclic product at its Artin symbol represent the
same invariant class modulo the group norm. -/
private theorem base_invariant_cyclic
    (a : Kˣ) (g : Gal(L/K))
    (hg : Abelianization.of g = localArtinHom K L a) :
    let piG : FMAct.invariants Gal(L/K) Lˣ :=
      ⟨Units.map (algebraMap K L).toMonoidHom a,
        multiplicative_base_fixed K L a⟩
    QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range piG =
      QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
        (localCyclicInvariant K L g) := by
  dsimp only
  let piG : FMAct.invariants Gal(L/K) Lˣ :=
    ⟨Units.map (algebraMap K L).toMonoidHom a,
      multiplicative_base_fixed K L a⟩
  have hnorm : localNormResidue K L (Abelianization.of g) =
      QuotientGroup.mk' (normSubgroup K L) a :=
    by
      rw [hg]
      exact (localNormResidue K L).apply_symm_apply _
  have hparameter := local_cyclic_product K L g
  let invNorm := galoisInvariantsMod K L
  apply invNorm.injective
  calc
    invNorm (QuotientGroup.mk'
        (FMAct.norm Gal(L/K) Lˣ).range piG) =
        QuotientGroup.mk' (normSubgroup K L) a :=
      galois_invariants_algebra K L a
    _ = localNormResidue K L (Abelianization.of g) :=
      hnorm.symm
    _ = invNorm (QuotientGroup.mk'
        (FMAct.norm Gal(L/K) Lˣ).range
          (localCyclicInvariant K L g)) := by
      rw [← hparameter]
      exact invNorm.apply_symm_apply _ |>.symm

private def additiveInvariantMultiplicative
    {J M : Type} [Group J] [CommGroup M] [MulDistribMulAction J M]
    (p : FMAct.invariants J M) :
    (Rep.ofMulDistribMulAction J M).ρ.invariants :=
  ⟨Additive.ofMul p.1, fun j => congrArg Additive.ofMul (p.2 j)⟩

/-- Degree-zero cup product depends only on the invariant coefficient
modulo the finite group norm. -/
private theorem cup_invariant_mod
    {J M : Type} [Group J] [Fintype J]
    [CommGroup M] [MulDistribMulAction J M]
    (p q : FMAct.invariants J M)
    (hpq : QuotientGroup.mk' (FMAct.norm J M).range p =
      QuotientGroup.mk' (FMAct.norm J M).range q)
    (y : groupCohomology (Rep.trivial ℤ J ℤ) 2) :
    cupCohomology (Rep.ofMulDistribMulAction J M)
        (Rep.trivial ℤ J ℤ) 0 2
        (transportedCyclic0 J M
          (additiveInvariantMultiplicative p)) y =
      cupCohomology (Rep.ofMulDistribMulAction J M)
        (Rep.trivial ℤ J ℤ) 0 2
        (transportedCyclic0 J M
          (additiveInvariantMultiplicative q)) y := by
  let C := Rep.ofMulDistribMulAction J M
  have hdiv : p / q ∈ (FMAct.norm J M).range :=
    QuotientGroup.eq_iff_div_mem.mp hpq
  obtain ⟨x, hx⟩ := hdiv
  let d : FMAct.invariants J M := p / q
  let r : C.ρ.invariants :=
    additiveInvariantMultiplicative d
  have hinv : additiveInvariantMultiplicative p =
      additiveInvariantMultiplicative q + r := by
    apply Subtype.ext
    change Additive.ofMul p.1 = Additive.ofMul (q.1 * d.1)
    congr 1
    simp [d]
  have hrnorm : r =
      ⟨C.ρ.norm (Additive.ofMul x),
        fun j => C.ρ.self_norm_apply j (Additive.ofMul x)⟩ := by
    apply Subtype.ext
    dsimp only [r, C, additiveInvariantMultiplicative]
    apply Additive.toMul.injective
    change d.1 = Additive.toMul
      ((Representation.ofMulDistribMulAction J M).norm
        (Additive.ofMul x))
    rw [Representation.norm_ofMulDistribMulAction_eq]
    exact (congrArg Subtype.val hx).symm
  have hh0 : transportedCyclic0 J M
        (additiveInvariantMultiplicative p) =
      transportedCyclic0 J M
          (additiveInvariantMultiplicative q) +
        transportedCyclic0 J M r := by
    simp only [transportedCyclic0, ← map_add]
    rw [← hinv]
  rw [hh0]
  rw [(cupCohomology C (Rep.trivial ℤ J ℤ) 0 2).map_add]
  rw [LinearMap.add_apply]
  have hzero := cup_cohomology_invariant C
    (Additive.ofMul x) y
  change cupCohomology C (Rep.trivial ℤ J ℤ) 0 2
      (transportedCyclic0 J M
        (additiveInvariantMultiplicative q)) y +
    cupCohomology C (Rep.trivial ℤ J ℤ) 0 2
      (transportedCyclic0 J M r) y = _
  rw [show cupCohomology C (Rep.trivial ℤ J ℤ) 0 2
      (transportedCyclic0 J M r) y = 0 by
    rw [hrnorm]
    simpa [transportedCyclic0, C] using hzero, add_zero]

/-- The degree-zero corestriction of the subgroup cyclic product is the
ambient cyclic product. -/
private theorem corestriction_cyclic_0
    {J M : Type} [Group J] [Fintype J]
    [CommGroup M] [MulDistribMulAction J M]
    (c : NMCocycl₂ (G := J) (M := M))
    (H : Subgroup J) [Fintype H] [H.FiniteIndex]
    (S : H.LeftTransversal) (h : H) :
    let cH := NMCocycl₂.restrict H.subtype
      (by intro t x; rfl) c
    let pH := NMCocycl₂.cyclicProductInvariant cH h
    let pJ := NMCocycl₂.cyclicProductInvariant c (h : J)
    corestriction (Rep.ofMulDistribMulAction J M) H 0
        (transportedCyclic0 H M
          (additiveInvariantMultiplicative pH)) =
      transportedCyclic0 J M
        (additiveInvariantMultiplicative pJ) := by
  dsimp only
  let C := Rep.ofMulDistribMulAction J M
  let cH := NMCocycl₂.restrict H.subtype
    (by intro t x; rfl) c
  let pH := NMCocycl₂.cyclicProductInvariant cH h
  let pJ := NMCocycl₂.cyclicProductInvariant c (h : J)
  let pHAdd := additiveInvariantMultiplicative pH
  let pJAdd := additiveInvariantMultiplicative pJ
  let mH := (groupCohomology.cocyclesIso₀
    (Rep.res H.subtype C)).inv pHAdd
  have hcor := corestriction_0_transversal C H S mH
  have hprod := NMCocycl₂.cyclic_transversal_norm
    c H S h
  have htrans :
      (⟨transversalNorm C H S pHAdd.1,
        transversal_norm_invariants C H pHAdd.1 pHAdd.2 S⟩ :
          C.ρ.invariants) = pJAdd := by
    apply Subtype.ext
    apply Additive.toMul.injective
    change (∏ q : J ⧸ H, (S.2.leftQuotientEquiv q : J) •
        ∏ t : H, c (t, h)) = NMCocycl₂.cyclicProduct c h
    exact hprod.symm
  change corestriction C H 0
      (groupCohomology.π (Rep.res H.subtype C) 0 mH) =
    groupCohomology.π C 0
      ((groupCohomology.cocyclesIso₀ C).inv pJAdd)
  rw [← htrans]
  simpa [mH, pHAdd] using hcor

private theorem invariant_h_zsmul
    (z : ℤ)
    (x : groupCohomology.H2
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) :
    invariantH2 K L (z • x) =
      z • invariantH2 K L x := by
  let f : groupCohomology.H2
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) →+
      LocalInvariant := {
    toFun := invariantH2 K L
    map_zero' := by simp [invariantH2]
    map_add' := invariant_h_add K L }
  exact map_zsmul f z x

private theorem invariant_h_nsmul
    (m : ℕ)
    (x : groupCohomology.H2
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) :
    invariantH2 K L (m • x) =
      m • invariantH2 K L x := by
  simpa using invariant_h_zsmul K L (m : ℤ) x

private theorem invariant_fundamental_class :
    invariantH2 K L
        (multiplicative2Additive
          (multiplicativeFundamentalClass K L)) =
      ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) := by
  unfold invariantH2
  have hcomparison :
      (multiplicativeHCohomology
        (G := Gal(L/K)) (M := Lˣ)).symm
          (Multiplicative.ofAdd (multiplicative2Additive
            (multiplicativeFundamentalClass K L))) =
        multiplicativeFundamentalClass K L :=
    (multiplicativeHCohomology
      (G := Gal(L/K)) (M := Lˣ)).symm_apply_apply _
  rw [hcomparison, invariant_torsion_coe,
    h_brauer_fundamental,
    relative_fundamental_coe,
    canonical_carry_brauer]
  rfl

private theorem characterBoundary_zsmul
    {J : Type} [Group J] [Fintype J]
    (z : ℤ) (chi : RationalCharacter J) :
    characterBoundary J (z • chi) = z • characterBoundary J chi := by
  let f : RationalCharacter J →+
      groupCohomology (Rep.trivial ℤ J ℤ) 2 := {
    toFun := characterBoundary J
    map_zero' := characterBoundary_zero J
    map_add' := characterBoundary_add J }
  exact map_zsmul f z chi

/-- Proposition III.3.6 before assuming that the ambient Galois group is
abelian.  Its natural target is the abelianization, and a character of that
target is inflated along the quotient map in the cup product. -/
theorem abelianization
    (a : Kˣ) (chi : RationalCharacter (Abelianization Gal(L/K))) :
    chi (Additive.ofMul (localArtinHom K L a)) =
      characterCupInvariant K L a
        (chi.comp Abelianization.of.toAdditive) := by
  let gbar := localArtinHom K L a
  by_cases hg1 : gbar = 1
  · have hq : QuotientGroup.mk' (normSubgroup K L) a = 1 := by
      have h := congrArg (localNormResidue K L) hg1
      simpa [gbar, local_artin_hom] using h
    have ha : a ∈ normSubgroup K L :=
      (QuotientGroup.eq_one_iff a).mp hq
    obtain ⟨x, rfl⟩ := ha
    have hartin : localArtinHom K L (normOnUnits K L x) = 1 := by
      simpa [gbar] using hg1
    rw [hartin]
    change chi 0 = characterCupInvariant K L (normOnUnits K L x)
      (chi.comp Abelianization.of.toAdditive)
    rw [map_zero, character_cup_units]
  · obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      (commutator Gal(L/K)) gbar
    change Abelianization.of g = gbar at hg
    have hg_ne : g ≠ 1 := by
      intro h
      apply hg1
      rw [← hg, h, map_one]
    let H : Subgroup Gal(L/K) := Subgroup.zpowers g
    letI : CommGroup H := inferInstance
    letI : Fintype H := Fintype.ofFinite H
    let h : H := ⟨g, Subgroup.mem_zpowers g⟩
    have hgen : ∀ x : H, x ∈ Subgroup.zpowers h := by
      intro x
      obtain ⟨z, hz⟩ := x.2
      exact ⟨z, Subtype.ext hz⟩
    have hn : 1 < Nat.card H := by
      rw [show Nat.card H = Nat.card (Subgroup.zpowers g) by rfl,
        Nat.card_zpowers]
      have hpos := orderOf_pos g
      have hne : orderOf g ≠ 1 := by
        simpa [orderOf_eq_one_iff] using hg_ne
      omega
    let n := Nat.card H
    letI : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
    let e : Multiplicative (ZMod n) ≃* H :=
      zmodMulEquivOfGenerator hgen rfl
    let psi : RationalCharacter H :=
      multiplicativeRationalCharacter H h hgen
    let chiG : RationalCharacter Gal(L/K) :=
      chi.comp Abelianization.of.toAdditive
    let chiH : RationalCharacter H := chiG.comp H.subtype.toAdditive
    obtain ⟨j, hchi⟩ :=
      rational_zsmul_generator h hgen chiH
    let C := Rep.ofMulDistribMulAction Gal(L/K) Lˣ
    let CH := Rep.ofMulDistribMulAction H Lˣ
    let c := localFundamentalCocycle K L
    let cH := NMCocycl₂.restrict H.subtype
      (by intro t x; rfl) c
    let pH := NMCocycl₂.cyclicProductInvariant cH h
    let pG := NMCocycl₂.cyclicProductInvariant c g
    let pHAdd := additiveInvariantMultiplicative pH
    let pGAdd := additiveInvariantMultiplicative pG
    let zH := cupCohomology CH (Rep.trivial ℤ H ℤ) 0 2
      (transportedCyclic0 H Lˣ pHAdd)
      (characterBoundary H psi)
    let gamma := multiplicative2Additive
      (multiplicativeFundamentalClass K L)
    let gammaH := multiplicative2Additive (MHTwo.mk cH)
    have hpsi : psi = transportedStandardCharacter n H e := by
      rfl
    have hcyclic : groupCohomology.map (MonoidHom.id H)
        (ρ_ CH).hom 2 zH = gammaH := by
      simpa [n, e, psi, hpsi, cH, pH, pHAdd, zH, CH, gammaH] using
        (transported_cup_boundary h hgen hn cH)
    have hresGamma : restriction C H 2 gamma = gammaH := by
      have hgamma : gamma = multiplicative2Additive
          (MHTwo.mk c) := by
        exact congrArg multiplicative2Additive
          (mk_fundamental_cocycle K L).symm
      have hres := multiplicative_2_restriction H.subtype
        (by intro t x; rfl)
        (MHTwo.mk c)
      rw [MHTwo.restrictionHom_mk] at hres
      have hcoeff : multiplicativeRestrictionRep H.subtype
          (by intro t x; rfl) = 𝟙 (Rep.res H.subtype C) := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        rfl
      rw [hgamma]
      simpa [gammaH, cH, additive2Restriction, hcoeff,
        restriction, C, CH] using hres.symm
    let rawGamma := groupCohomology.map (MonoidHom.id Gal(L/K))
      (ρ_ C).inv 2 gamma
    have hcyclicRaw : zH = groupCohomology.map (MonoidHom.id H)
        (ρ_ CH).inv 2 gammaH := by
      let eCH := (groupCohomology.functor ℤ H 2).mapIso (ρ_ CH)
      change zH = eCH.inv gammaH
      change eCH.hom zH = gammaH at hcyclic
      calc
        zH = eCH.inv (eCH.hom zH) := (eCH.hom_inv_id_apply zH).symm
        _ = eCH.inv gammaH := congrArg eCH.inv hcyclic
    have hresRaw : restriction (C ⊗ Rep.trivial ℤ Gal(L/K) ℤ :
          Rep ℤ Gal(L/K)) H 2 rawGamma =
        groupCohomology.map (MonoidHom.id H) (ρ_ CH).inv 2
          (restriction C H 2 gamma) := by
      let rawC := (C ⊗ Rep.trivial ℤ Gal(L/K) ℤ :
        Rep ℤ Gal(L/K))
      have hcomp₁ := groupCohomology.map_comp
        (A := C) (B := rawC) (C := Rep.res H.subtype rawC)
        (MonoidHom.id Gal(L/K)) H.subtype (ρ_ C).inv
        (𝟙 (Rep.res H.subtype rawC)) 2
      have happ₁ := congrArg (fun f => f gamma) hcomp₁
      have hcomp₂ := groupCohomology.map_comp
        (A := C) (B := Rep.res H.subtype C)
        (C := (CH ⊗ Rep.trivial ℤ H ℤ : Rep ℤ H))
        H.subtype (MonoidHom.id H) (𝟙 (Rep.res H.subtype C))
        (ρ_ CH).inv 2
      have happ₂ := congrArg (fun f => f gamma) hcomp₂
      calc
        restriction rawC H 2 rawGamma =
            groupCohomology.map H.subtype
              ((Rep.resFunctor H.subtype).map (ρ_ C).inv) 2 gamma := by
          simpa [rawGamma, restriction, rawC] using happ₁.symm
        _ = groupCohomology.map (MonoidHom.id H) (ρ_ CH).inv 2
            (restriction C H 2 gamma) := by
          simpa [restriction, C, CH, rawC] using happ₂
    have hzH : zH = restriction
        (C ⊗ Rep.trivial ℤ Gal(L/K) ℤ : Rep ℤ Gal(L/K)) H 2
          rawGamma := by
      rw [hcyclicRaw, hresRaw, hresGamma]
      rfl
    let S : H.LeftTransversal :=
      ⟨Set.range (fun q : Gal(L/K) ⧸ H => q.out),
        Subgroup.isComplement_range_left Quotient.out_eq'⟩
    have hcorH0 := corestriction_cyclic_0 c H S h
    have hresBoundary := restriction_characterBoundary H chiG
    have hproj := cup_corestriction_projection H C
      (Rep.trivial ℤ Gal(L/K) ℤ) 0 2
      (transportedCyclic0 H Lˣ pHAdd)
      (characterBoundary Gal(L/K) chiG)
    have hsubCup : cupCohomology CH (Rep.trivial ℤ H ℤ) 0 2
        (transportedCyclic0 H Lˣ pHAdd)
        (restriction (Rep.trivial ℤ Gal(L/K) ℤ) H 2
          (characterBoundary Gal(L/K) chiG)) = j • zH := by
      rw [hresBoundary]
      have hb : characterBoundary H chiH =
          j • characterBoundary H psi := by
        rw [hchi]
        change characterBoundary H (j • psi) =
          j • characterBoundary H psi
        exact characterBoundary_zsmul j psi
      rw [hb]
      exact map_zsmul _ j (characterBoundary H psi)
    have hambientP : cupCohomology C
        (Rep.trivial ℤ Gal(L/K) ℤ) 0 2
        (transportedCyclic0 Gal(L/K) Lˣ pGAdd)
        (characterBoundary Gal(L/K) chiG) =
      j • (H.index • rawGamma) := by
      rw [← hcorH0]
      rw [← hproj]
      have hsubCup' : cupCohomology (Rep.res H.subtype C)
          (Rep.res H.subtype (Rep.trivial ℤ Gal(L/K) ℤ)) 0 2
          (transportedCyclic0 H Lˣ pHAdd)
          (restriction (Rep.trivial ℤ Gal(L/K) ℤ) H 2
            (characterBoundary Gal(L/K) chiG)) = j • zH := by
        simpa [C, CH] using hsubCup
      rw [hsubCup']
      rw [show corestriction
          (C ⊗ Rep.trivial ℤ Gal(L/K) ℤ : Rep ℤ Gal(L/K)) H (0 + 2)
            (j • zH) = j • corestriction
              (C ⊗ Rep.trivial ℤ Gal(L/K) ℤ : Rep ℤ Gal(L/K)) H (0 + 2)
                zH by exact map_zsmul _ j zH]
      rw [hzH]
      have hcorres := congrArg (fun f => f rawGamma)
        (restriction_corestriction_degrees
          (C ⊗ Rep.trivial ℤ Gal(L/K) ℤ : Rep ℤ Gal(L/K)) H 2)
      simp only [ConcreteCategory.comp_apply] at hcorres
      have hcorres' : corestriction
          (C ⊗ Rep.trivial ℤ Gal(L/K) ℤ : Rep ℤ Gal(L/K)) H 2
            (restriction
              (C ⊗ Rep.trivial ℤ Gal(L/K) ℤ : Rep ℤ Gal(L/K)) H 2
                rawGamma) = H.index • rawGamma := by
        simpa [ModuleCat.hom_nsmul, Pi.smul_apply] using hcorres
      rw [hcorres']
    have hquot := base_invariant_cyclic K L a g
      (hg.trans rfl)
    have hbaseCup := cup_invariant_mod
      (⟨Units.map (algebraMap K L).toMonoidHom a,
        multiplicative_base_fixed K L a⟩ :
          FMAct.invariants Gal(L/K) Lˣ)
      pG (by
        simpa [pG, c, local_cyclic_invariant] using hquot)
      (characterBoundary Gal(L/K) chiG)
    have hraw : cupCohomology C
        (Rep.trivial ℤ Gal(L/K) ℤ) 0 2
        (baseH0 K L a) (characterBoundary Gal(L/K) chiG) =
      j • (H.index • rawGamma) := by
      rw [show baseH0 K L a =
          transportedCyclic0 Gal(L/K) Lˣ
            (additiveInvariantMultiplicative
              (⟨Units.map (algebraMap K L).toMonoidHom a,
                multiplicative_base_fixed K L a⟩ :
                FMAct.invariants Gal(L/K) Lˣ)) by rfl,
        hbaseCup, hambientP]
    have hclass : cupCharacterBoundary K L a chiG =
        j • (H.index • gamma) := by
      rw [cupCharacterBoundary, hraw, map_zsmul, map_nsmul]
      change j • (H.index •
        groupCohomology.map (MonoidHom.id Gal(L/K))
          (ρ_ C).hom 2 rawGamma) = _
      rw [show groupCohomology.map (MonoidHom.id Gal(L/K))
          (ρ_ C).hom 2 rawGamma = gamma by
        let eC := (groupCohomology.functor ℤ Gal(L/K) 2).mapIso (ρ_ C)
        change eC.hom (eC.inv gamma) = gamma
        exact eC.inv_hom_id_apply gamma]
    unfold characterCupInvariant
    rw [hclass, invariant_h_zsmul,
      invariant_h_nsmul,
      invariant_fundamental_class]
    have heval : chi (Additive.ofMul (localArtinHom K L a)) =
        chiH (Additive.ofMul h) := by
      change chi (Additive.ofMul gbar) = chi (Additive.ofMul (Abelianization.of g))
      rw [hg]
    rw [heval, hchi]
    change j • psi (Additive.ofMul h) = _
    change j • psi (Additive.ofMul h) =
      j • (H.index •
        ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant))
    congr 1
    dsimp only [psi]
    calc
      multiplicativeRationalCharacter H h hgen
          (Additive.ofMul h) =
          (((Nat.card H : ℚ)⁻¹ : ℚ) : LocalInvariant) :=
        multiplicative_rational_character H h hgen
      _ = H.index •
          ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) := by
        have hcard : Nat.card Gal(L/K) = H.index * Nat.card H := by
          simpa [Nat.card_eq_fintype_card, Nat.mul_comm] using
            (Subgroup.card_mul_index H).symm
        have hrank : Nat.card Gal(L/K) = Module.finrank K L := by
          simpa using IsGalois.card_aut_eq_finrank K L
        rw [← hrank, hcard]
        change (((Nat.card H : ℚ)⁻¹ : ℚ) : LocalInvariant) =
          ((((H.index : ℚ) *
            (1 / ((H.index * Nat.card H : ℕ) : ℚ))) : ℚ) :
            LocalInvariant)
        congr 1
        have hi : (H.index : ℚ) ≠ 0 := by
          exact_mod_cast Subgroup.FiniteIndex.index_ne_zero (H := H)
        have hnq : (Nat.card H : ℚ) ≠ 0 := by positivity
        push_cast
        field_simp

/-- **Proposition III.3.6.**  For an abelian extension, identify the
abelianization with the Galois group in the preceding theorem. -/
theorem transportedCupBoundary
    [IsMulCommutative Gal(L/K)]
    (a : Kˣ) (chi : RationalCharacter Gal(L/K)) :
    CharacterFormula K L a chi := by
  letI : CommGroup Gal(L/K) := inferInstance
  let e : Gal(L/K) ≃* Abelianization Gal(L/K) :=
    Abelianization.equivOfComm
  let chiAb : RationalCharacter (Abelianization Gal(L/K)) :=
    chi.comp e.symm.toAdditive
  have h := abelianization K L a chiAb
  have hchi : chiAb.comp Abelianization.of.toAdditive = chi := by
    ext g
    change chi (Additive.ofMul (e.symm (Abelianization.of g))) =
      chi (Additive.ofMul g)
    rw [show e.symm (Abelianization.of g) = g by
      apply e.injective
      simp [e]]
  unfold CharacterFormula
  rw [← hchi]
  rw [← h]
  rfl

end

end Submission.CField.LRecip
