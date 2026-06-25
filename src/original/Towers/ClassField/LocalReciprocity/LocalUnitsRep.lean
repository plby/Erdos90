import Towers.ClassField.LocalClass.NatCardFinrank
import Towers.ClassField.LocalReciprocity.H2Cardinality

/-!
# Milne, Class Field Theory, Theorem III.3.1

This file removes the temporary degree-two cardinality hypotheses from the
finite local Tate isomorphism.  Lemma III.2.6 supplies the cardinality over
the base field and, after giving each subgroup fixed field its canonical
spectral local-field structure, over every fixed field as well.
-/

namespace Towers.CField.LRecip

open Towers.CField.LFTheory
open Towers.CField.Shifting
open Towers.CField.LClass
open Towers.CField.LBrauer
open scoped IsMulCommutative

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance localUnitsRepSourceValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance localUnitsRepSourceValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

private abbrev localUnitsRep :=
  Rep.ofMulDistribMulAction Gal(L/K) Lˣ

set_option maxHeartbeats 3000000 in
-- Fixed fields receive canonical spectral local structures before invoking Lemma III.2.6.
set_option synthInstance.maxHeartbeats 500000 in
/-- Lemma III.2.6, simultaneously over all subgroup fixed fields, in the
form required by Tate's theorem. -/
theorem cardinalityFixedFields
    (H : Subgroup Gal(L/K)) :
    Nat.card
        (groupCohomology.H2
          (Rep.ofMulDistribMulAction
            Gal(L/IntermediateField.fixedField H) Lˣ)) =
      Module.finrank (IntermediateField.fixedField H) L := by
  let F := IntermediateField.fixedField H
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField K F
  exact h_card_finrank F L

/-- **Theorem III.3.1.** Cup product with the finite local fundamental
class gives Tate's two-degree shift in every represented degree. -/
noncomputable def tateTwoShift :
    TateTwoShift (localUnitsRep K L) := by
  let hbase := h_card_finrank K L
  exact shiftHCardinality K L hbase
    (cardinalityFixedFields K L)

/-- The degree-minus-two component of Theorem III.3.1, identified with the
field-unit norm quotient. -/
noncomputable def localResidueEquiv :
    Additive (Abelianization Gal(L/K)) ≃+
      Additive (Kˣ ⧸ normSubgroup K L) := by
  let hbase := h_card_finrank K L
  exact residueHCardinality K L hbase
    (cardinalityFixedFields K L)

/-- The finite local Artin equivalence, inverse to the degree-minus-two
norm-residue equivalence. -/
noncomputable def localArtinEquiv :
    Additive (Kˣ ⧸ normSubgroup K L) ≃+
      Additive (Abelianization Gal(L/K)) :=
  (localResidueEquiv K L).symm

/-- For an abelian extension, Theorem III.3.1 identifies the norm quotient
with the Galois group itself. -/
noncomputable def abelianLocalArtin
    [IsMulCommutative Gal(L/K)] :
    (Kˣ ⧸ normSubgroup K L) ≃* Gal(L/K) :=
  ((localArtinEquiv K L).trans
    (Abelianization.equivOfComm (H := Gal(L/K))).symm.toAdditive).toMultiplicative

end

end Towers.CField.LRecip
