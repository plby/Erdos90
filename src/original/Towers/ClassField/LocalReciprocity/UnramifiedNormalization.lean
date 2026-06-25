import Towers.ClassField.NormCorrespondence.UnramifiedNormGroups
import Towers.ClassField.LocalReciprocity.DualityConclusion
import Towers.ClassField.LocalReciprocity.FrobeniusCarry
import Towers.ClassField.LocalReciprocity.LocalUnitsRep
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedFrobenius

/-!
# Milne, Class Field Theory, Lemma III.3.7: unramified normalization

The normalized-order quotient and the Frobenius-normalized cyclic coordinate
give the unramified reciprocity equivalence directly.  This proves the full
formula on every canonical finite unramified level.

The final comparison computes the negative Tate shift on the cyclic generator.
The first connecting morphism contributes the standard inverse in the
identification `H₁(G, ℤ) ≃ Gᵃᵇ`; the norm in Tate's splitting module then
produces exactly the carry-factor product of Proposition III.1.9.
-/

namespace Towers.CField.LRecip

open Towers.CField.LFTheory
open Towers.CField.TCohomo
open Towers.CField.Shifting
open Towers.CField.LClass
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open AddSubgroup CategoryTheory CategoryTheory.Limits Rep Representation
open scoped BigOperators IsMulCommutative

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance unramifiedNormalizationValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance unramifiedNormalizationValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

/-- The Frobenius-normalized reciprocity equivalence on the canonical
unramified extension of degree `n`.  It is normalized valuation modulo `n`,
followed by the cyclic coordinate sending `1` to arithmetic Frobenius. -/
noncomputable def frobeniusNormalizedArtin
    (n : ℕ) [NeZero n] :
    (Kˣ ⧸ normSubgroup K (canonicalUnramifiedLevel K n)) ≃*
      Gal(canonicalUnramifiedLevel K n/K) :=
  (QuotientGroup.quotientMulEquivOfEq
      (unramified_level_ker K n)).trans
    ((QuotientGroup.quotientKerEquivOfSurjective
      (localOrderMod K n)
      (local_mod_surjective K n)).trans
        (levelZMod K n))

/-- **Lemma III.3.7 on the canonical unramified level.**  The normalized
unramified Artin map sends the class of `a` to arithmetic Frobenius raised to
the normalized order of `a`. -/
theorem frobenius_normalized_artin
    (n : ℕ) [NeZero n] (a : Kˣ) :
    frobeniusNormalizedArtin K n
        (QuotientGroup.mk'
          (normSubgroup K (canonicalUnramifiedLevel K n)) a) =
      canonicalArithmeticFrobenius K n ^
        localUnitOrder K (Additive.ofMul a) := by
  rw [frobeniusNormalizedArtin]
  change levelZMod K n
      (Multiplicative.ofAdd
        (localUnitOrder K (Additive.ofMul a) : ZMod n)) = _
  exact level_z_cast K n _

/-- The corresponding homomorphism on field units has the exact source-level
formula, before passing to the norm quotient. -/
noncomputable def frobeniusNormalizedUnramified
    (n : ℕ) [NeZero n] :
    Kˣ →* Gal(canonicalUnramifiedLevel K n/K) :=
  (frobeniusNormalizedArtin K n).toMonoidHom.comp
    (QuotientGroup.mk'
      (normSubgroup K (canonicalUnramifiedLevel K n)))

@[simp]
theorem frobenius_normalized_unramified
    (n : ℕ) [NeZero n] (a : Kˣ) :
    frobeniusNormalizedUnramified K n a =
      canonicalArithmeticFrobenius K n ^
        localUnitOrder K (Additive.ofMul a) :=
  frobenius_normalized_artin K n a

/-- In particular, every normalized prime element maps to arithmetic
Frobenius. -/
theorem frobenius_normalized_uniformizer
    (n : ℕ) [NeZero n] (varpi : Kˣ)
    (hvarpi : localUnitOrder K (Additive.ofMul varpi) = 1) :
    frobeniusNormalizedUnramified K n varpi =
      canonicalArithmeticFrobenius K n := by
  rw [frobenius_normalized_unramified, hvarpi, zpow_one]

set_option synthInstance.maxHeartbeats 200000 in
-- Identifying the Artin kernel synthesizes the finite unramified Galois tower.
/-- The normalized unramified Artin homomorphism has exactly the norm group
as kernel. -/
theorem frobenius_normalized_ker
    (n : ℕ) [NeZero n] :
    (frobeniusNormalizedUnramified K n).ker =
      normSubgroup K (canonicalUnramifiedLevel K n) := by
  let eG := levelZMod K n
  letI : CommGroup Gal(canonicalUnramifiedLevel K n/K) :=
    eG.symm.toMonoidHom.commGroupOfInjective eG.symm.injective
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff x).1
    apply (frobeniusNormalizedArtin K n).injective
    simpa [frobeniusNormalizedUnramified] using hx
  · intro hx
    have hq : QuotientGroup.mk'
        (normSubgroup K (canonicalUnramifiedLevel K n)) x = 1 :=
      (QuotientGroup.eq_one_iff x).2 hx
    change frobeniusNormalizedArtin K n
      (QuotientGroup.mk'
        (normSubgroup K (canonicalUnramifiedLevel K n)) x) = 1
    rw [hq, map_one]

end

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance comparisonValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance comparisonValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

set_option maxHeartbeats 5000000 in
-- Expanding both exceptional Tate connecting maps produces a large proof term.
set_option synthInstance.maxHeartbeats 500000 in
-- The assembled local-field, fixed-field, and cohomology instances are deep.
/-- The canonical negative Tate shift sends arithmetic Frobenius to the
class of the canonical uniformizer. -/
theorem norm_residue_frobenius
    (n : ℕ) [NeZero n] (hn : 1 < n) :
    localResidueEquiv K (canonicalUnramifiedLevel K n)
        (Additive.ofMul
          (Abelianization.of (canonicalArithmeticFrobenius K n))) =
      Additive.ofMul
        (QuotientGroup.mk'
          (normSubgroup K (canonicalUnramifiedLevel K n))
          (canonicalLocalUniformizer K)) := by
  let L := canonicalUnramifiedLevel K n
  let G := Gal(L/K)
  let C := Rep.ofMulDistribMulAction G Lˣ
  let g : G := canonicalArithmeticFrobenius K n
  let hbase := h_card_finrank K L
  let hfixed := cardinalityFixedFields K L
  let hrelative :=
    relative_brauer_cardinality K L hbase
  let gamma := cohomologyFundamentalCardinality K L hrelative
  let hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma :=
    zmultiples_fundamental_cardinality K L hbase
  let hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1) :=
    fun H ↦ hilbert_90_zero (K := K) (L := L) H
  let hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H :=
    h_fixed_cardinality K L hfixed
  let hcardG : Nat.card (groupCohomology C 2) = Nat.card G := by
    calc
      Nat.card (groupCohomology C 2) = Module.finrank K L := hbase
      _ = Nat.card G := (IsGalois.card_aut_eq_finrank K L).symm
  let hcardFinite : Nat.card (groupCohomology C 2) = Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using hcardG
  let hC1self : IsZero (groupCohomology C 1) :=
    cohomology_res_top C 1 (hC1 ⊤)
  let hboundary : ∀ H : Subgroup G,
      IsIso (groupCohomology.δ
        ((splitting_sequence_short C
          (normalizedCocycleClass C gamma)
          (normalized_cocycle_class C gamma)).map_of_exact
            (Rep.resFunctor H.subtype)) 1 2 rfl) :=
    fun H ↦ splitting_boundary_iso C gamma hgamma hcardG hcardH H
  let φ := normalizedCocycleClass C gamma
  let hφ := normalized_cocycle_class C gamma
  let x₁ := splittingParameterInvariant φ hφ g
  have hsource :
      (homology1Abelianization G).symm
          (-Additive.ofMul (Abelianization.of g)) =
        groupHomology.H1π (Rep.trivial ℤ G ℤ)
          ((groupHomology.cycles₁IsoOfIsTrivial
            (Rep.trivial ℤ G ℤ)).inv (Finsupp.single g⁻¹ 1)) := by
    apply (homology1Abelianization G).injective
    rw [AddEquiv.apply_symm_apply]
    change -Additive.ofMul (Abelianization.of g) =
      (TensorProduct.rid ℤ (Additive (Abelianization G)))
        ((groupHomology.H1AddEquivOfIsTrivial
          (Rep.trivial ℤ G ℤ))
            (groupHomology.H1π (Rep.trivial ℤ G ℤ)
              ((groupHomology.cycles₁IsoOfIsTrivial
                (Rep.trivial ℤ G ℤ)).inv
                  (Finsupp.single g⁻¹ 1))))
    rw [groupHomology.H1AddEquivOfIsTrivial_single]
    simp
  have hshift :
      (shiftHCardinality K L hbase hfixed).negTwo
          ((homology1Abelianization G).symm
            (-Additive.ofMul (Abelianization.of g))) =
        Submodule.Quotient.mk x₁ := by
    rw [hsource]
    simpa only [shiftHCardinality,
      restrictedShiftStatement, cohomologyResTop] using
      (neg_generator_inv gamma hgamma hcardFinite hC1self
        hC1 hboundary g)
  let c := galoisCarryCocycle K
    (levelZMod K n)
    (canonicalLocalUniformizer K)
  have hcardRel : Nat.card (relativeBrauerGroup K L) = n := by
    exact hrelative.trans (unramified_level_finrank K n)
  have hc : c.toAdditiveH2 = gamma := by
    simpa [c, gamma, L] using
      (frobenius_carry_fundamental K n hcardRel)
  let cφ := normalizedCocycleAdditive φ hφ
  have hcoh : MHTwo.IsCohomologous cφ c := by
    rw [← MHTwo.mk_eq_iff]
    exact mk_normalized_cocycle gamma c hc
  let pc : FMAct.invariants G Lˣ :=
    ⟨x₁.1.toMul, fun σ ↦ congrArg Additive.toMul (x₁.2 σ)⟩
  let pd : FMAct.invariants G Lˣ :=
    ⟨Units.map (algebraMap K L) (canonicalLocalUniformizer K), by
      intro σ
      apply Units.ext
      exact σ.commutes (canonicalLocalUniformizer K)⟩
  have hpc : pc.1 = ∏ σ : G, cφ (σ, g) := by
    change Additive.toMul (x₁.1 : Additive Lˣ) =
      ∏ σ : G, Additive.toMul (show Additive Lˣ from φ (σ, g))
    rw [splitting_parameter_coe]
    rfl
  have hpd : pd.1 = ∏ σ : G, c (σ, g) := by
    exact (carry_cocycle_frobenius K n hn).symm
  have hquot := product_mod_cohomologous
    hcoh g pc pd hpc hpd
  have htate :
      tateCohomologyInvariants G Lˣ
          (Submodule.Quotient.mk x₁) =
        Additive.ofMul
          (QuotientGroup.mk' (FMAct.norm G Lˣ).range pd) := by
    rw [tate_invariants_mk]
    exact congrArg Additive.ofMul hquot
  rw [localResidueEquiv, residueHCardinality,
    AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
    AddEquiv.neg_apply, hshift]
  change galoisTateQuotient K L
      (Submodule.Quotient.mk x₁) = _
  rw [galoisTateQuotient, AddEquiv.trans_apply, htate]
  simpa [pd, L] using congrArg Additive.ofMul
    (galois_invariants_algebra K L
      (canonicalLocalUniformizer K))

local instance canonicalUnramifiedGalIsMulCommutative
    (n : ℕ) [NeZero n] :
    IsMulCommutative Gal(canonicalUnramifiedLevel K n/K) := by
  let eG := levelZMod K n
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  apply eG.symm.injective
  simpa only [map_mul] using mul_comm (eG.symm σ) (eG.symm τ)

/-- **Lemma III.3.7.** On every canonical finite unramified level, the
explicit Frobenius-normalized reciprocity equivalence is the finite local
Artin equivalence obtained from Tate's two-degree shift. -/
theorem frobenius_normalized_abelian
    (n : ℕ) [NeZero n] :
    frobeniusNormalizedArtin K n =
      abelianLocalArtin K
        (canonicalUnramifiedLevel K n) := by
  by_cases hnOne : n = 1
  · have hcard : Nat.card Gal(canonicalUnramifiedLevel K n/K) = 1 := by
      have hcardN : Nat.card Gal(canonicalUnramifiedLevel K n/K) = n := by
        rw [IsGalois.card_aut_eq_finrank,
          unramified_level_finrank K n]
      exact hcardN.trans hnOne
    letI : Subsingleton Gal(canonicalUnramifiedLevel K n/K) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    apply MulEquiv.ext
    intro q
    exact Subsingleton.elim _ _
  · have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hn : 1 < n := by omega
    let qvarpi := QuotientGroup.mk'
      (normSubgroup K (canonicalUnramifiedLevel K n))
      (canonicalLocalUniformizer K)
    let frobenius := canonicalArithmeticFrobenius K n
    have hexplicit :
        frobeniusNormalizedArtin K n qvarpi =
          frobenius := by
      change frobeniusNormalizedUnramified K n
          (canonicalLocalUniformizer K) =
        canonicalArithmeticFrobenius K n
      exact frobenius_normalized_uniformizer K n
        (canonicalLocalUniformizer K) (canonical_uniformizer_order K)
    have hnorm :
        localResidueEquiv K (canonicalUnramifiedLevel K n)
            (Additive.ofMul (Abelianization.of frobenius)) =
          Additive.ofMul qvarpi := by
      simpa [qvarpi, frobenius] using
        (norm_residue_frobenius K n hn)
    have hinverse :
        (localResidueEquiv K
            (canonicalUnramifiedLevel K n)).symm
            (Additive.ofMul qvarpi) =
          Additive.ofMul (Abelianization.of frobenius) := by
      exact ((localResidueEquiv K
        (canonicalUnramifiedLevel K n)).eq_symm_apply.mpr hnorm).symm
    have hcanonical :
        abelianLocalArtin K
            (canonicalUnramifiedLevel K n) qvarpi =
          frobenius := by
      change Additive.toMul
          ((Abelianization.equivOfComm
              (H := Gal(canonicalUnramifiedLevel K n/K))).symm.toAdditive
            ((localResidueEquiv K
              (canonicalUnramifiedLevel K n)).symm
                (Additive.ofMul qvarpi))) =
        frobenius
      rw [hinverse]
      exact (Abelianization.equivOfComm
        (H := Gal(canonicalUnramifiedLevel K n/K))).symm_apply_apply frobenius
    apply MulEquiv.ext
    intro q
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      (zpowers_arithmetic_frobenius K n
        (frobeniusNormalizedArtin K n q))
    have hq : q = qvarpi ^ i := by
      apply (frobeniusNormalizedArtin K n).injective
      rw [map_zpow, hexplicit]
      exact hi.symm
    rw [hq, map_zpow, map_zpow, hexplicit, hcanonical]

end

end Towers.CField.LRecip
