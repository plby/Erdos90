import Towers.ClassField.LocalClass.FundamentalClassCompatibility
import Towers.ClassField.LocalClass.CardinalityCanonicalSplitting
import Towers.ClassField.LocalClass.FiniteGaloisExtensions
import Towers.ClassField.LocalClass.LocalInvariantCorestriction
import Towers.ClassField.BrauerGroups.BaseChangeTower
import Towers.ClassField.CrossedProducts.IsMulCoboundary
import Towers.ClassField.CrossedProducts.Multiplicative2Comparison

/-!
# Lemma III.2.7: inflation of the local fundamental class

This file proves formula (33) for an abstract tower of finite Galois local
extensions.  Inflation is defined, as in `Corollary316.inflationHom`, by
inclusion of relative Brauer groups and the crossed-product classification.
Unlike `Corollary316.inflationHom`, the construction here does not require
the fields to have first been embedded in a chosen separable closure.

The restriction and corestriction formulas (31) and (32) require two pieces
which are not presently available together in the repository: the full
cross-base local invariant formula on arbitrary Brauer classes, and a Brauer
corestriction comparison.  The invariant-theoretic deductions from those
compatibilities are already formalized in `FundamentalClassCompatibility`.
-/

namespace Towers.CField.LClass

noncomputable section

open CategoryTheory Rep
open Towers.CField.COps
open BGroups CProduca LBrauer

attribute [local instance] Units.mulDistribMulActionRight

universe u

/-- Formula (32), once formula (31) has identified the restricted class,
for the actual categorical restriction and corestriction maps.  This is the
formal `Cor ∘ Res = [G:H]` deduction; the missing arithmetic input is exactly
the identification supplied by (31). -/
theorem cohomology_corestriction_restriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) [H.FiniteIndex]
    (uG : groupCohomology A 2)
    (uH : groupCohomology (res H.subtype A) 2)
    (hrestriction : restriction A H 2 uG = uH) :
    corestriction A H 2 uH = H.index • uG := by
  rw [← hrestriction]
  have h := congrArg (fun f ↦ f uG)
    (restriction_corestriction_degrees A H 2)
  simpa using h

section AlgebraicTower

variable (K E L : Type u)
  [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]

/-- Inclusion `Br(E/K) → Br(L/K)` for an abstract field tower. -/
def relativeTowerInclusion :
    relativeBrauerGroup K E →* relativeBrauerGroup K L where
  toFun x := ⟨x.1, by
    rw [relative_brauer_group, ← base_change_tower K E L,
      (relative_brauer_group K E x.1).1 x.2, map_one]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem tower_inclusion_coe
    (x : relativeBrauerGroup K E) :
    ((relativeTowerInclusion K E L x : relativeBrauerGroup K L) :
        BrauerGroup K) = x :=
  rfl

variable [FiniteDimensional K E] [IsGalois K E]
  [FiniteDimensional K L] [IsGalois K L]

/-- Inflation in multiplicative `H²` for an abstract finite Galois tower,
characterized by inclusion of the corresponding relative Brauer groups. -/
def galoisHInflation :
    MHTwo Gal(E/K) Eˣ →* MHTwo Gal(L/K) Lˣ :=
  (CProduc.hRelativeBrauer K L).symm.toMonoidHom.comp
    ((relativeTowerInclusion K E L).comp
      (CProduc.hRelativeBrauer K E).toMonoidHom)

@[simp]
theorem h_brauer_inflation
    (x : MHTwo Gal(E/K) Eˣ) :
    CProduc.hRelativeBrauer K L
        (galoisHInflation K E L x) =
      relativeTowerInclusion K E L
        (CProduc.hRelativeBrauer K E x) := by
  simp [galoisHInflation]

end AlgebraicTower

section LocalTower

variable (K E L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance inflationValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance inflationValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [FiniteDimensional K L] [IsGalois K L] [IsGalois K E]

local instance inflationDegreeNeZero (F : Type)
    [Field F] [Algebra K F] [FiniteDimensional K F] :
    NeZero (Module.finrank K F) :=
  ⟨Module.finrank_pos.ne'⟩

/-- The local fundamental class, first in its intrinsic relative-Brauer
form: it is the class of invariant `1 / [F : K]`. -/
def relativeFundamentalClass (F : Type)
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] :
    relativeBrauerGroup K F :=
  ⟨canonicalBrauerClass K (Module.finrank K F),
    brauer_relative_galois K F⟩

@[simp]
theorem relative_fundamental_coe (F : Type)
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] :
    (relativeFundamentalClass K F : BrauerGroup K) =
      canonicalBrauerClass K (Module.finrank K F) :=
  rfl

/-- The intrinsic canonical-degree class is the cardinality-based relative
fundamental class used after Lemma III.2.6. -/
theorem relative_fundamental_cardinality (F : Type)
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] :
    relativeFundamentalClass K F =
      relativeFundamentalCardinality K F
        (relative_brauer_class
          K F (brauer_relative_galois K F)) := by
  apply (relative_class_cardinality K F _ _).2
  exact canonical_carry_brauer
    K (Module.finrank K F)

/-- The same fundamental class in normalized multiplicative `H²`. -/
def multiplicativeFundamentalClass (F : Type)
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] :
    MHTwo Gal(F/K) Fˣ :=
  (CProduc.hRelativeBrauer K F).symm
    (relativeFundamentalClass K F)

@[simp]
theorem h_brauer_fundamental (F : Type)
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] :
    CProduc.hRelativeBrauer K F
        (multiplicativeFundamentalClass K F) =
      relativeFundamentalClass K F :=
  (CProduc.hRelativeBrauer K F).apply_symm_apply _

/-- The local fundamental class in Mathlib's categorical additive `H²`. -/
def hFundamentalClass (F : Type)
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] :
    groupCohomology.H2
      (Rep.ofMulDistribMulAction Gal(F/K) Fˣ) :=
  (multiplicativeHCohomology
    (multiplicativeFundamentalClass K F)).toAdd

/-- The intrinsic categorical class agrees with the class constructed from
the cardinality equivalence in Lemma III.2.6. -/
theorem fundamental_class_cardinality (F : Type)
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] :
    hFundamentalClass K F =
      cohomologyFundamentalCardinality K F
        (relative_brauer_class
          K F (brauer_relative_galois K F)) := by
  let hcanonical :=
    brauer_relative_galois K F
  let hcard :=
    relative_brauer_class
      K F hcanonical
  apply (cohomology_fundamental_cardinality
    K F hcard _).2
  apply Additive.toMul.injective
  change
    (((multiplicativeHCohomology
        (G := Gal(F/K)) (M := Fˣ)).symm.trans
      ((CProduc.hRelativeBrauer K F).trans
        (relativeTorsionCardinality
          K F hcard)))
      (multiplicativeHCohomology
        ((CProduc.hRelativeBrauer K F).symm
          (relativeFundamentalClass K F)))) =
      invariantDivTorsion (Module.finrank K F)
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    relative_fundamental_cardinality]
  exact (relativeTorsionCardinality
    K F hcard).apply_symm_apply
      (invariantDivTorsion (Module.finrank K F))

/-- The additive categorical form of inflation. -/
def hInflationAdd :
    letI : FiniteDimensional K E := FiniteDimensional.left K E L
    groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(E/K) Eˣ) →+
      groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) := by
  letI : FiniteDimensional K E := FiniteDimensional.left K E L
  exact
    ((multiplicativeHCohomology
        (G := Gal(L/K)) (M := Lˣ)).toMonoidHom.comp
      ((galoisHInflation K E L).comp
        (multiplicativeHCohomology
          (G := Gal(E/K)) (M := Eˣ)).symm.toMonoidHom)).toAdditive

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem h_inflation_add
    [FiniteDimensional K E]
    (x : groupCohomology.H2
      (Rep.ofMulDistribMulAction Gal(E/K) Eˣ)) :
    hInflationAdd K E L x =
      (multiplicativeHCohomology
        (galoisHInflation K E L
          ((multiplicativeHCohomology
            (G := Gal(E/K)) (M := Eˣ)).symm
              (Multiplicative.ofAdd x)))).toAdd :=
  rfl

/-- Formula (33) in relative-Brauer form. -/
theorem tower_inclusion_fundamental :
    letI : FiniteDimensional K E := FiniteDimensional.left K E L
    letI : FiniteDimensional E L := FiniteDimensional.right K E L
    relativeTowerInclusion K E L
        (relativeFundamentalClass K E) =
      (relativeFundamentalClass K L) ^ Module.finrank E L := by
  letI : FiniteDimensional K E := FiniteDimensional.left K E L
  letI : FiniteDimensional E L := FiniteDimensional.right K E L
  letI : NeZero (Module.finrank E L) := ⟨Module.finrank_pos.ne'⟩
  apply Subtype.ext
  apply (carryBrauerInvariant K).injective
  change carryBrauerInvariant K
      (canonicalBrauerClass K (Module.finrank K E)) =
    carryBrauerInvariant K
      ((canonicalBrauerClass K (Module.finrank K L)) ^
        Module.finrank E L)
  rw [map_pow,
    canonical_carry_brauer,
    canonical_carry_brauer]
  apply Multiplicative.ext
  change ((1 : ℚ) / (Module.finrank K E : ℚ) : LocalInvariant) =
    Module.finrank E L •
      ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant)
  rw [← Module.finrank_mul_finrank K E L, Nat.mul_comm]
  exact (invariant_nsmul_div
    (Module.finrank E L) (Module.finrank K E)).symm

/-- **Lemma III.2.7, formula (33).** If `E/K` is Galois, inflation sends
`u_{E/K}` to `[L:E] u_{L/K}` (written multiplicatively as a power). -/
theorem h_inflation_fundamental :
    letI : FiniteDimensional K E := FiniteDimensional.left K E L
    letI : FiniteDimensional E L := FiniteDimensional.right K E L
    galoisHInflation K E L
        (multiplicativeFundamentalClass K E) =
      (multiplicativeFundamentalClass K L) ^
        Module.finrank E L := by
  letI : FiniteDimensional K E := FiniteDimensional.left K E L
  letI : FiniteDimensional E L := FiniteDimensional.right K E L
  apply (CProduc.hRelativeBrauer K L).injective
  rw [h_brauer_inflation,
    h_brauer_fundamental, map_pow,
    h_brauer_fundamental]
  exact tower_inclusion_fundamental K E L

/-- Formula (33) in Mathlib's categorical additive group cohomology. -/
theorem inflation_fundamental_class :
    letI : FiniteDimensional K E := FiniteDimensional.left K E L
    letI : FiniteDimensional E L := FiniteDimensional.right K E L
    hInflationAdd K E L
        (hFundamentalClass K E) =
      Module.finrank E L • hFundamentalClass K L := by
  letI : FiniteDimensional K E := FiniteDimensional.left K E L
  letI : FiniteDimensional E L := FiniteDimensional.right K E L
  rw [h_inflation_add]
  simp only [hFundamentalClass,
    ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rw [h_inflation_fundamental, map_pow]
  rfl

end LocalTower

end

end Towers.CField.LClass
