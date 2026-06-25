import Submission.ClassField.LocalReciprocity.ResidueMulEquiv
import Submission.ClassField.LocalReciprocity.CocycleNaturality
import Submission.ClassField.LocalReciprocity.FrobeniusCarry
import Submission.ClassField.LocalClass.Inflation

/-!
# The local norm-residue map as a cyclic cocycle product

The exceptional degree-minus-two component of Tate's shift admits a useful
elementwise description.  If `c` is the normalized multiplicative cocycle
chosen for the local fundamental class, then the image of `g` is represented
in Tate degree zero by `∏ s, c(s,g)`.  This is the common computational input
for the two naturality squares in Lemma III.3.2.
-/

namespace Submission.CField.LRecip

open AddSubgroup CategoryTheory CategoryTheory.Limits Rep
open Submission.CField.LFTheory
open Submission.CField.TCohomo
open Submission.CField.Shifting
open Submission.CField.LClass
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance formulaValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance formulaValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

private abbrev localRep :=
  Rep.ofMulDistribMulAction Gal(L/K) Lˣ

/-- The normalized additive cocycle selected by Tate's construction for the
cardinality-normalized finite local fundamental class. -/
noncomputable def finiteFundamentalCocycle :
    groupCohomology.cocycles₂ (localRep K L) :=
  let hbase := h_card_finrank K L
  let hrelative :=
    relative_brauer_cardinality K L hbase
  normalizedCocycleClass (localRep K L)
    (cohomologyFundamentalCardinality K L hrelative)

/-- The chosen local fundamental cocycle is normalized at `(1,1)`. -/
theorem fundamental_cocycle_normalized :
    finiteFundamentalCocycle K L (1, 1) = 0 := by
  exact normalized_cocycle_class _ _

/-- Multiplicative form of the chosen normalized local fundamental cocycle. -/
noncomputable def localFundamentalCocycle :
    NMCocycl₂ (G := Gal(L/K)) (M := Lˣ) :=
  normalizedCocycleAdditive
    (finiteFundamentalCocycle K L)
    (fundamental_cocycle_normalized K L)

/-- The chosen normalized multiplicative cocycle represents the intrinsic
finite local fundamental class. -/
theorem mk_fundamental_cocycle :
    MHTwo.mk (localFundamentalCocycle K L) =
      multiplicativeFundamentalClass K L := by
  apply (multiplicativeHCohomology
    (G := Gal(L/K)) (M := Lˣ)).injective
  change Multiplicative.ofAdd
      (groupCohomology.H2π (localRep K L)
        (finiteFundamentalCocycle K L)) =
    Multiplicative.ofAdd (hFundamentalClass K L)
  apply Multiplicative.ofAdd.injective
  rw [show groupCohomology.H2π (localRep K L)
      (finiteFundamentalCocycle K L) =
      cohomologyFundamentalCardinality K L
        (relative_brauer_cardinality K L
          (h_card_finrank K L)) by
        exact normalized_cocycle_represents _ _]
  exact (fundamental_class_cardinality K L).symm

/-- The invariant cyclic product representing the image of `g` in Tate
degree zero. -/
noncomputable def localCyclicInvariant (g : Gal(L/K)) :
    FMAct.invariants Gal(L/K) Lˣ :=
  let hbase := h_card_finrank K L
  let hrelative :=
    relative_brauer_cardinality K L hbase
  let gamma :=
    cohomologyFundamentalCardinality K L hrelative
  let φ := normalizedCocycleClass (localRep K L) gamma
  let hφ := normalized_cocycle_class (localRep K L) gamma
  let x := splittingParameterInvariant φ hφ g
  ⟨x.1.toMul, fun σ ↦ congrArg Additive.toMul (x.2 σ)⟩

theorem cyclic_invariant_coe (g : Gal(L/K)) :
    (localCyclicInvariant K L g).1 =
      NMCocycl₂.cyclicProduct
        (localFundamentalCocycle K L) g := by
  change Additive.toMul
      ((splittingParameterInvariant
        (finiteFundamentalCocycle K L)
        (fundamental_cocycle_normalized K L) g).1 : Additive Lˣ) = _
  rw [splitting_parameter_coe]
  rfl

theorem local_cyclic_invariant (g : Gal(L/K)) :
    localCyclicInvariant K L g =
      NMCocycl₂.cyclicProductInvariant
        (localFundamentalCocycle K L) g := by
  apply Subtype.ext
  exact cyclic_invariant_coe K L g

set_option maxHeartbeats 5000000 in
-- Expanding the Tate shift and normalizing its transported cocycle produces
-- a large finite-product expression.
set_option synthInstance.maxHeartbeats 500000 in
/-- Elementwise cyclic-product formula for Theorem III.3.1 in degree `-2`.
The result is stated before converting Galois invariants back to base-field
units, which is the form best suited to subgroup calculations. -/
theorem local_cyclic_product (g : Gal(L/K)) :
    (galoisInvariantsMod K L).symm
        (localNormResidue K L (Abelianization.of g)) =
      QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
        (localCyclicInvariant K L g) := by
  let G := Gal(L/K)
  let C := localRep K L
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
  have htate :
      tateCohomologyInvariants G Lˣ
          (Submodule.Quotient.mk x₁) =
        Additive.ofMul
          (QuotientGroup.mk' (FMAct.norm G Lˣ).range
            (localCyclicInvariant K L g)) := by
    rfl
  apply (galoisInvariantsMod K L).injective
  rw [(galoisInvariantsMod K L).apply_symm_apply]
  apply Additive.ofMul.injective
  change localResidueEquiv K L
      (Additive.ofMul (Abelianization.of g)) = _
  rw [localResidueEquiv, residueHCardinality,
    AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
    AddEquiv.neg_apply, hshift]
  change galoisTateQuotient K L
      (Submodule.Quotient.mk x₁) = _
  rw [galoisTateQuotient, AddEquiv.trans_apply]
  rw [htate]
  rfl

/-- The same degree-minus-two formula after converting Galois invariants
back to the base-field norm quotient. -/
theorem residue_cyclic_product
    (g : Gal(L/K)) :
    localNormResidue K L (Abelianization.of g) =
      galoisInvariantsMod K L
        (QuotientGroup.mk'
          (FMAct.norm Gal(L/K) Lˣ).range
          (localCyclicInvariant K L g)) := by
  rw [← local_cyclic_product K L g]
  exact
    (galoisInvariantsMod K L).apply_symm_apply _ |>.symm

/-- Fully explicit cocycle-product form of the finite norm-residue map. -/
theorem fundamental_cyclic_product
    (g : Gal(L/K)) :
    localNormResidue K L (Abelianization.of g) =
      galoisInvariantsMod K L
        (QuotientGroup.mk'
          (FMAct.norm Gal(L/K) Lˣ).range
          (NMCocycl₂.cyclicProductInvariant
            (localFundamentalCocycle K L) g)) := by
  rw [← local_cyclic_invariant K L g]
  exact residue_cyclic_product K L g

end

end Submission.CField.LRecip
