import Submission.ClassField.TateCohomology.AddEquivAbelianization
import Submission.ClassField.Shifting.RestrictedBoundaryShift
import Submission.ClassField.LocalClass.FiniteRelativeCardinality
import Submission.ClassField.LocalReciprocity.SubgroupHTransport
import Submission.ClassField.LocalReciprocity.SubgroupHilbert90
import Submission.ClassField.LocalReciprocity.TateZeroQuotient

/-!
# Theorem III.3.1 from the degree-two cardinality theorem

This file is the formal assembly step following Lemma III.2.6.  Its only
arithmetic inputs are the expected cardinality of `H²(L/K,Lˣ)` and the
same result over every subgroup fixed field.  It does not assume or use a
local-invariant base-change formula.

The cardinality at the base constructs the canonically normalized class of
invariant `1 / [L : K]`.  Fixed-field cardinalities and subgroup Hilbert 90
then discharge Tate's theorem.  The degree-minus-two component is finally
identified with the norm quotient, yielding the finite norm-residue map and
its inverse, the abstract Artin map.
-/

namespace Submission.CField.LRecip

open AddSubgroup CategoryTheory.Limits Rep
open Submission.CField.LFTheory
open Submission.CField.TCohomo
open Submission.CField.Shifting
open Submission.CField.LClass
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer
open scoped IsMulCommutative

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance fromH2CardinalityValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance fromH2CardinalityValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

private abbrev localUnitsRep :=
  Rep.ofMulDistribMulAction Gal(L/K) Lˣ

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- The categorical `H²` cardinality is the same cardinality statement for
the relative Brauer group used to construct the normalized fundamental
class. -/
theorem relative_brauer_cardinality
    (hcardK : Nat.card (groupCohomology.H2 (localUnitsRep K L)) =
      Module.finrank K L) :
    Nat.card (relativeBrauerGroup K L) = Module.finrank K L := by
  calc
    Nat.card (relativeBrauerGroup K L) =
        Nat.card (MHTwo Gal(L/K) Lˣ) :=
      Nat.card_congr (CProduc.hRelativeBrauer K L).symm.toEquiv
    _ = Nat.card
        (Multiplicative (groupCohomology.H2 (localUnitsRep K L))) :=
      Nat.card_congr
        (multiplicativeHCohomology
          (G := Gal(L/K)) (M := Lˣ)).toEquiv
    _ = Nat.card (groupCohomology.H2 (localUnitsRep K L)) := rfl
    _ = Module.finrank K L := hcardK

/-- The cardinality-based finite invariant, expressed in the `ZMod` form
used to prove that the normalized class generates `H²`. -/
noncomputable def cohomologyZCardinality
    (hcardK : Nat.card (groupCohomology.H2 (localUnitsRep K L)) =
      Module.finrank K L) :
    groupCohomology.H2 (localUnitsRep K L) ≃+
      ZMod (Module.finrank K L) := by
  let n := Module.finrank K L
  letI : NeZero n := ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  let hrelative :=
    relative_brauer_cardinality K L hcardK
  exact
    (cohomologyTorsionCardinality
        K L hrelative).trans
      ((invariantTorsionPow n).symm.toAdditive.trans
        (torsionZMod n).symm)

/-- Under the `ZMod` coordinate supplied by cardinality, the canonical
fundamental class is `1`. -/
@[simp]
theorem z_fundamental_cardinality
    (hcardK : Nat.card (groupCohomology.H2 (localUnitsRep K L)) =
      Module.finrank K L) :
    cohomologyZCardinality K L hcardK
        (cohomologyFundamentalCardinality K L
          (relative_brauer_cardinality
            K L hcardK)) = 1 := by
  let n := Module.finrank K L
  letI : NeZero n := ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  simp only [cohomologyZCardinality,
    cohomologyFundamentalCardinality,
    invariantDivTorsion, localDivTorsion,
    AddEquiv.trans_apply, AddEquiv.apply_symm_apply,
    MulEquiv.toAdditive_apply_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, MonoidHom.coe_coe,
    MulEquiv.symm_apply_apply]
  exact (torsionZMod n).symm_apply_apply 1

/-- The normalized cardinality-based class generates all of degree-two
cohomology. -/
theorem zmultiples_fundamental_cardinality
    (hcardK : Nat.card (groupCohomology.H2 (localUnitsRep K L)) =
      Module.finrank K L)
    (x : groupCohomology.H2 (localUnitsRep K L)) :
    x ∈ AddSubgroup.zmultiples
      (cohomologyFundamentalCardinality K L
        (relative_brauer_cardinality
          K L hcardK)) := by
  let e := cohomologyZCardinality K L hcardK
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨ZMod.cast (e x), ?_⟩
  apply e.injective
  rw [map_zsmul,
    z_fundamental_cardinality]
  simp

/-- **Theorem III.3.1, represented Tate ranges.** Lemma III.2.6 at the base
and at every subgroup fixed field supplies Tate's two-degree shift for
`Lˣ`. -/
noncomputable def shiftHCardinality
    (hcardK : Nat.card (groupCohomology.H2 (localUnitsRep K L)) =
      Module.finrank K L)
    (hcardFixed : ∀ H : Subgroup Gal(L/K),
      Nat.card
          (groupCohomology.H2
            (Rep.ofMulDistribMulAction
              Gal(L/IntermediateField.fixedField H) Lˣ)) =
        Module.finrank (IntermediateField.fixedField H) L) :
    TateTwoShift (localUnitsRep K L) := by
  let gamma := cohomologyFundamentalCardinality K L
    (relative_brauer_cardinality K L hcardK)
  apply restrictedShiftStatement (localUnitsRep K L) gamma
  · exact zmultiples_fundamental_cardinality
      K L hcardK
  · exact hilbert_90_zero
  · exact h_fixed_cardinality K L hcardFixed

/-- The degree-minus-two fundamental-class equivalence, with Tate degree
zero identified as the field-unit norm quotient.  The initial negation is
the standard sign in the identification of Tate degree `-2` with
`H₁(G, ℤ)`: Mathlib's bar differential represents `g` by `g⁻¹ - 1`. -/
noncomputable def residueHCardinality
    (hcardK : Nat.card (groupCohomology.H2 (localUnitsRep K L)) =
      Module.finrank K L)
    (hcardFixed : ∀ H : Subgroup Gal(L/K),
      Nat.card
          (groupCohomology.H2
            (Rep.ofMulDistribMulAction
              Gal(L/IntermediateField.fixedField H) Lˣ)) =
        Module.finrank (IntermediateField.fixedField H) L) :
    Additive (Abelianization Gal(L/K)) ≃+
      Additive (Kˣ ⧸ normSubgroup K L) :=
  (AddEquiv.neg (Additive (Abelianization Gal(L/K)))).trans
    (homology1Abelianization Gal(L/K)).symm |>.trans
    (shiftHCardinality K L hcardK hcardFixed).negTwo |>.trans
      (galoisTateQuotient K L)

/-- The finite abstract Artin map: the inverse of the degree-minus-two
norm-residue equivalence. -/
noncomputable def artinHCardinality
    (hcardK : Nat.card (groupCohomology.H2 (localUnitsRep K L)) =
      Module.finrank K L)
    (hcardFixed : ∀ H : Subgroup Gal(L/K),
      Nat.card
          (groupCohomology.H2
            (Rep.ofMulDistribMulAction
              Gal(L/IntermediateField.fixedField H) Lˣ)) =
        Module.finrank (IntermediateField.fixedField H) L) :
    Additive (Kˣ ⧸ normSubgroup K L) ≃+
      Additive (Abelianization Gal(L/K)) :=
  (residueHCardinality
    K L hcardK hcardFixed).symm

/-- For an abelian finite Galois extension, the degree-minus-two Artin map
is a multiplicative equivalence with the Galois group itself. -/
noncomputable def abelianArtinCardinality
    [IsMulCommutative Gal(L/K)]
    (hcardK : Nat.card (groupCohomology.H2 (localUnitsRep K L)) =
      Module.finrank K L)
    (hcardFixed : ∀ H : Subgroup Gal(L/K),
      Nat.card
          (groupCohomology.H2
            (Rep.ofMulDistribMulAction
              Gal(L/IntermediateField.fixedField H) Lˣ)) =
        Module.finrank (IntermediateField.fixedField H) L) :
    (Kˣ ⧸ normSubgroup K L) ≃* Gal(L/K) :=
  let e : Additive (Kˣ ⧸ normSubgroup K L) ≃+ Additive Gal(L/K) :=
    (artinHCardinality K L hcardK hcardFixed).trans
      (Abelianization.equivOfComm (H := Gal(L/K))).symm.toAdditive
  { toFun := fun x => Additive.toMul (e (Additive.ofMul x))
    invFun := fun x => Additive.toMul (e.symm (Additive.ofMul x))
    left_inv := fun x => by
      change Additive.toMul (e.symm (e (Additive.ofMul x))) = x
      rw [e.symm_apply_apply]
      rfl
    right_inv := fun x => by
      change Additive.toMul (e (e.symm (Additive.ofMul x))) = x
      rw [e.apply_symm_apply]
      rfl
    map_mul' := fun x y => by
      rw [ofMul_mul, map_add, toMul_add] }

end

end Submission.CField.LRecip
