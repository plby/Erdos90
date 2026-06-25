import Submission.ClassField.LocalReciprocity.TateGenerator
import Submission.ClassField.LocalBrauer.CanonicalFrobeniusRestriction

/-!
# Frobenius carry classes and the finite local fundamental class

This file identifies the carry cocycle formed with arithmetic Frobenius with
the cardinality-normalized local fundamental class.  It also records the
cohomology and norm-quotient comparisons needed by Lemma III.3.7.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca
open scoped BigOperators

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- Frobenius-normalized cyclic coordinates commute with reduction along
every inclusion of canonical unramified levels. -/
theorem level_z_compatible
    {n m : ℕ} [NeZero n] [NeZero m] (hnm : n ∣ m)
    (z : Multiplicative (ZMod m)) :
    galoisRestrictionHom K
        (unramified_level K (NeZero.pos n) (NeZero.pos m) hnm)
        (levelZMod K m z) =
      levelZMod K n
        (CCarry.indexReduction hnm z) := by
  let oneM : Multiplicative (ZMod m) := Multiplicative.ofAdd 1
  have hz : z ∈ Subgroup.zpowers oneM := by
    refine ⟨(z.toAdd.val : ℤ), ?_⟩
    change oneM ^ (z.toAdd.val : ℤ) = z
    rw [zpow_natCast]
    apply Multiplicative.toAdd.injective
    simp [oneM]
  obtain ⟨i, hi⟩ := hz
  rw [← hi]
  simp only [map_zpow]
  rw [level_frobenius_z,
    arithmetic_frobenius_restrict K hnm,
    ← level_frobenius_z K n]
  apply congrArg (fun x ↦ x ^ i)
  apply congrArg (levelZMod K n)
  apply Multiplicative.toAdd.injective
  rw [CCarry.reduction_toAdd]
  exact (ZMod.cast_one hnm).symm

set_option maxHeartbeats 3000000 in
-- Comparing carry classes through a factorial overlevel is elaboration-heavy.
/-- The absolute invariant of the carry class formed with arithmetic
Frobenius is `1 / n`, at every canonical unramified level. -/
theorem canonical_carry_frobenius
    (n : ℕ) [NeZero n] :
    carryBrauerInvariant K
        ((CProduc.relativeBrauerClass K
          (canonicalUnramifiedLevel K n)
          (galoisCarryCocycle K
            (levelZMod K n)
            (canonicalLocalUniformizer K)) :
              relativeBrauerGroup K (canonicalUnramifiedLevel K n)) :
          BrauerGroup K) =
      Multiplicative.ofAdd
        ((1 : ℚ) / (n : ℚ) : LocalInvariant) := by
  let r := n
  let m := invariantLevelDegree r
  letI : NeZero m := ⟨(invariant_level_pos r).ne'⟩
  have hnm : n ∣ m := by
    dsimp [m, r, invariantLevelDegree]
    apply Nat.dvd_factorial (NeZero.pos n)
    omega
  let F := canonicalUnramifiedLevel K n
  let E := canonicalUnramifiedLevel K m
  let hFE : F ≤ E :=
    unramified_level K (NeZero.pos n) (NeZero.pos m) hnm
  let eR := levelZMod K n
  let eS := levelZMod K m
  let cR := galoisCarryCocycle K eR (canonicalLocalUniformizer K)
  let cS := galoisCarryCocycle K eS (canonicalLocalUniformizer K)
  letI : Fact (F ≤ E) := ⟨hFE⟩
  have hinfl : inflationHom K hFE (MHTwo.mk cR) =
      MHTwo.mk cS ^ (m / n) := by
    exact (inflation_concrete_cocycle K cR).trans
      (inflation_carry_cocycle K hnm hFE eR eS
        (level_z_compatible K hnm)
        (canonicalLocalUniformizer K))
  have hrel := congrArg (CProduc.hRelativeBrauer K E) hinfl
  rw [relative_brauer_inflation, map_pow] at hrel
  have habs := congrArg Subtype.val hrel
  have habs' :
      ((CProduc.hRelativeBrauer K F
          (MHTwo.mk cR) : relativeBrauerGroup K F) : BrauerGroup K) =
        (((CProduc.hRelativeBrauer K E
          (MHTwo.mk cS) : relativeBrauerGroup K E) ^ (m / n) :
            relativeBrauerGroup K E) : BrauerGroup K) := by
    simpa [relativeBrauerInclusion] using habs
  change carryBrauerInvariant K
      (((CProduc.hRelativeBrauer K F)
        (MHTwo.mk cR) : relativeBrauerGroup K F) : BrauerGroup K) = _
  rw [habs']
  apply Multiplicative.toAdd.injective
  have hupper := canonical_carry_coe K r (m / n)
  change
    (carryBrauerInvariant K
      ((((CProduc.hRelativeBrauer K E)
        (MHTwo.mk cS)) ^ (m / n) : relativeBrauerGroup K E) :
          BrauerGroup K)).toAdd = _
  have heqUpper :
      (((CProduc.hRelativeBrauer K E)
        (MHTwo.mk cS) : relativeBrauerGroup K E) : BrauerGroup K) =
        canonicalCarryBrauer K r := by
    rfl
  change (carryBrauerInvariant K
      (((((CProduc.hRelativeBrauer K E)
        (MHTwo.mk cS) : relativeBrauerGroup K E) :
          BrauerGroup K)) ^ (m / n))).toAdd = _
  rw [heqUpper, hupper]
  change (((m / n : ℕ) : ℚ) / (m : ℚ) : LocalInvariant) =
    ((1 : ℚ) / (n : ℚ) : LocalInvariant)
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  refine ⟨0, ?_⟩
  symm
  simp only [zero_smul]
  change ((m / n : ℕ) : ℚ) / (m : ℚ) - 1 / (n : ℚ) = 0
  have hmul : n * (m / n) = m := Nat.mul_div_cancel' hnm
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne m
  apply sub_eq_zero.mpr
  apply (div_eq_div_iff hm0 hn0).2
  norm_num
  exact_mod_cast (by simpa [Nat.mul_comm] using hmul)

/-- Cohomologous cocycles have the same cyclic product modulo the finite
group norm. -/
theorem product_mod_cohomologous
    {G M : Type} [Group G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M]
    {c d : NMCocycl₂ (G := G) (M := M)}
    (hcd : MHTwo.IsCohomologous c d) (g : G)
    (pc pd : FMAct.invariants G M)
    (hpc : pc.1 = ∏ h : G, c (h, g))
    (hpd : pd.1 = ∏ h : G, d (h, g)) :
    QuotientGroup.mk' (FMAct.norm G M).range pc =
      QuotientGroup.mk' (FMAct.norm G M).range pd := by
  change (pc : FMAct.invariantsModNorm G M) = pd
  rw [QuotientGroup.eq_iff_div_mem]
  obtain ⟨x, hx⟩ := hcd
  refine ⟨x g, ?_⟩
  apply Subtype.ext
  symm
  change pc.1 / pd.1 = ∏ h : G, h • x g
  rw [hpc, hpd, ← Finset.prod_div_distrib]
  calc
    ∏ h : G, c (h, g) / d (h, g) =
        ∏ h : G, (h • x g / x (h * g)) * x h := by
      apply Finset.prod_congr rfl
      intro h _
      exact (hx h g).symm
    _ = (∏ h : G, h • x g) *
        (∏ h : G, x (h * g))⁻¹ * (∏ h : G, x h) := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_inv_distrib]
    _ = ∏ h : G, h • x g := by
      have hr : (∏ h : G, x (h * g)) = ∏ h : G, x h :=
        Fintype.prod_equiv (Equiv.mulRight g) _ _ (fun _ ↦ rfl)
      rw [hr]
      simp

set_option maxHeartbeats 3000000 in
-- Transporting the full cyclic product through the Galois equivalence is expensive.
/-- Proposition III.1.9 in the transported Frobenius coordinate: the cyclic
product of the carry factor set is the base uniformizer. -/
theorem carry_cocycle_frobenius
    (n : ℕ) [NeZero n] (hn : 1 < n) :
    ∏ σ : Gal(canonicalUnramifiedLevel K n/K),
      galoisCarryCocycle K
          (levelZMod K n)
          (canonicalLocalUniformizer K)
        (σ, canonicalArithmeticFrobenius K n) =
      Units.map (algebraMap K (canonicalUnramifiedLevel K n))
        (canonicalLocalUniformizer K) := by
  let L := canonicalUnramifiedLevel K n
  let e := levelZMod K n
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Lˣ :=
    GroupH2.pulledAction e
  let pi := cyclicBaseInvariant K e (canonicalLocalUniformizer K)
  let c := galoisCarryCocycle K e (canonicalLocalUniformizer K)
  let s : Multiplicative (ZMod n) := Multiplicative.ofAdd 1
  have hp := CyclicH2.parameter_factorSet (n := n) hn pi.1 pi.2
  have hs : e s = canonicalArithmeticFrobenius K n := by
    exact level_frobenius_z K n
  rw [← hs]
  calc
    ∏ σ : Gal(L/K), c (σ, e s) =
      ∏ z : Multiplicative (ZMod n), c (e z, e s) :=
        (Fintype.prod_equiv e.toEquiv _ _ (fun _ ↦ rfl)).symm
    _ = ∏ z : Multiplicative (ZMod n),
        CCarry.factorSet pi.1 pi.2 (z, s) := by
      apply Finset.prod_congr rfl
      intro z _
      dsimp only [c, galoisCarryCocycle]
      rw [MHTrans.cocycleMap_apply]
      rw [e.symm_apply_apply, e.symm_apply_apply]
      rfl
    _ = CyclicH2.parameter (CCarry.factorSet pi.1 pi.2) := rfl
    _ = pi.1 := hp
    _ = Units.map (algebraMap K L) (canonicalLocalUniformizer K) := rfl

end

end Submission.CField.LBrauer


namespace Submission.CField.CProduca

open groupCohomology

noncomputable section

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- Convert the chosen normalized additive representative back to a
normalized multiplicative cocycle. -/
noncomputable def normalizedCocycleAdditive
    (φ : cocycles₂ (Rep.ofMulDistribMulAction G M))
    (hφ : φ (1, 1) = 0) : NMCocycl₂ (G := G) (M := M) := by
  let f : G × G → M := Additive.toMul ∘ φ
  have hf : IsMulCocycle₂ f :=
    isMulCocycle₂_of_mem_cocycles₂ (G := G) (M := M) φ φ.property
  have hf0 : f (1, 1) = 1 := congrArg Additive.toMul hφ
  exact {
    toFun := f
    isMulCocycle₂ := hf
    map_one_fst := fun g ↦ by
      rw [map_one_fst_of_isMulCocycle₂ hf]
      exact hf0
    map_one_snd := fun g ↦ by
      rw [map_one_snd_of_isMulCocycle₂ hf, hf0]
      simp }

@[simp]
theorem normalized_cocycle_additive
    (φ : cocycles₂ (Rep.ofMulDistribMulAction G M))
    (hφ : φ (1, 1) = 0) :
    (normalizedCocycleAdditive φ hφ).toAdditiveH2 =
      H2π (Rep.ofMulDistribMulAction G M) φ := by
  rfl

theorem mk_normalized_cocycle
    (gamma : H2 (Rep.ofMulDistribMulAction G M))
    (c : NMCocycl₂ (G := G) (M := M))
    (hc : c.toAdditiveH2 = gamma) :
    MHTwo.mk
        (normalizedCocycleAdditive
          (Shifting.normalizedCocycleClass
            (Rep.ofMulDistribMulAction G M) gamma)
          (Shifting.normalized_cocycle_class
            (Rep.ofMulDistribMulAction G M) gamma)) =
      MHTwo.mk c := by
  apply (multiplicativeHCohomology
    (G := G) (M := M)).injective
  change Multiplicative.ofAdd
      ((normalizedCocycleAdditive
        (Shifting.normalizedCocycleClass
          (Rep.ofMulDistribMulAction G M) gamma)
        (Shifting.normalized_cocycle_class
          (Rep.ofMulDistribMulAction G M) gamma)).toAdditiveH2) =
    Multiplicative.ofAdd c.toAdditiveH2
  apply Multiplicative.ofAdd.injective
  rw [normalized_cocycle_additive,
    Shifting.normalized_cocycle_represents, hc]

end

end Submission.CField.CProduca


namespace Submission.CField.LRecip

open Submission.CField.LClass
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance frobeniusCarryValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance frobeniusCarryValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

attribute [local instance] Units.mulDistribMulActionRight

/-- Evaluation of the representation-theoretic Tate-zero quotient on an
invariant representative. -/
theorem tate_invariants_mk
    (G M : Type) [Group G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M]
    (x : (Rep.ofMulDistribMulAction G M).ρ.invariants) :
    tateCohomologyInvariants G M
        (Submodule.Quotient.mk x) =
      Additive.ofMul
        (QuotientGroup.mk' (FMAct.norm G M).range
          ⟨x.1.toMul, fun g ↦ congrArg Additive.toMul (x.2 g)⟩) := by
  rfl

set_option maxHeartbeats 3000000 in
-- The relative-Brauer and cohomology equivalences create a large elaboration term.
set_option synthInstance.maxHeartbeats 200000 in
-- Typeclass search traverses the finite local-field cohomology instances here.
/-- The Frobenius carry cocycle represents the cardinality-normalized
categorical local fundamental class. -/
theorem frobenius_carry_fundamental
    (n : ℕ) [NeZero n]
    (hcard : Nat.card
      (relativeBrauerGroup K (canonicalUnramifiedLevel K n)) = n) :
    (galoisCarryCocycle K
      (levelZMod K n)
      (canonicalLocalUniformizer K)).toAdditiveH2 =
      cohomologyFundamentalCardinality K
        (canonicalUnramifiedLevel K n) (by
          simpa [unramified_level_finrank K n] using hcard) := by
  let L := canonicalUnramifiedLevel K n
  letI : NeZero (Module.finrank K L) :=
    ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  let c := galoisCarryCocycle K
    (levelZMod K n)
    (canonicalLocalUniformizer K)
  let hcard' : Nat.card (relativeBrauerGroup K L) = Module.finrank K L := by
    simpa [L, unramified_level_finrank K n] using hcard
  apply (cohomology_fundamental_cardinality
    K L hcard' c.toAdditiveH2).2
  apply Additive.toMul.injective
  change (((multiplicativeHCohomology
      (G := Gal(L/K)) (M := Lˣ)).symm.trans
        ((CProduc.hRelativeBrauer K L).trans
          (relativeTorsionCardinality
            K L hcard')))
      (Multiplicative.ofAdd c.toAdditiveH2)) =
        invariantDivTorsion (Module.finrank K L)
  rw [show Multiplicative.ofAdd c.toAdditiveH2 =
      multiplicativeHCohomology
        (MHTwo.mk c) by rfl,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
  apply Subtype.ext
  change carryBrauerInvariant K
      ((CProduc.hRelativeBrauer K L
        (MHTwo.mk c) : relativeBrauerGroup K L) : BrauerGroup K) = _
  rw [div_torsion_coe]
  calc
    _ = Multiplicative.ofAdd
        ((1 : ℚ) / (n : ℚ) : LocalInvariant) :=
      canonical_carry_frobenius K n
    _ = Multiplicative.ofAdd
        ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) := by
      rw [unramified_level_finrank K n]

end

end Submission.CField.LRecip
