import Towers.FieldTheory.CentralEmbeddingRelative
import Towers.ClassField.CrossedProducts.Multiplicative2Comparison

/-!
# Fixed-field transport for Lemma III.2.6

This identifies the quotient/invariant term in inflation--restriction with
the ordinary degree-two cohomology of the corresponding fixed-field
extension.  It is the coefficient-transport step needed by Milne's
induction.
-/

namespace Towers.CField.LClass

open CategoryTheory
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.TBluepr

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- For a normal subgroup `H`, the quotient-coefficient `H²` in
inflation--restriction is the `H²` of the Galois extension
`Lᴴ/K`, where `Lᴴ` is the fixed field. -/
theorem nat_invariants_fixed
    (H : Subgroup Gal(L/K)) [H.Normal] :
    Nat.card (groupCohomology
        ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) 2) =
      Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction
          Gal(IntermediateField.fixedField H/K)
          (IntermediateField.fixedField H)ˣ) 2) := by
  let A := (Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H
  letI : MulDistribMulAction (Gal(L/K) ⧸ H) (Multiplicative A) :=
    representationMultiplicativeAction A
  let eRep : Rep.ofMulDistribMulAction (Gal(L/K) ⧸ H)
      (Multiplicative A) ≅ A :=
    representationRepIso A
  let eG : Gal(L/K) ⧸ H ≃* Gal(IntermediateField.fixedField H/K) :=
    IsGalois.normalAutEquivQuotient H
  let eM : Multiplicative A ≃* (IntermediateField.fixedField H)ˣ :=
    invariantsFixedEquiv H
  let eH2 : MHTwo (Gal(L/K) ⧸ H) (Multiplicative A) ≃*
      MHTwo Gal(IntermediateField.fixedField H/K)
        (IntermediateField.fixedField H)ˣ :=
    MHTrans.h2Equiv eG eM
      (invariants_fixed_equivariant H)
  calc
    Nat.card (groupCohomology A 2) =
        Nat.card (groupCohomology
          (Rep.ofMulDistribMulAction (Gal(L/K) ⧸ H)
            (Multiplicative A)) 2) :=
      Nat.card_congr
        ((groupCohomology.functor ℤ (Gal(L/K) ⧸ H) 2).mapIso
          eRep.symm).toLinearEquiv.toEquiv
    _ = Nat.card
        (MHTwo (Gal(L/K) ⧸ H) (Multiplicative A)) :=
      (Nat.card_congr
        (multiplicativeHCohomology
          (G := Gal(L/K) ⧸ H) (M := Multiplicative A)).toEquiv).symm
    _ = Nat.card
        (MHTwo Gal(IntermediateField.fixedField H/K)
          (IntermediateField.fixedField H)ˣ) :=
      Nat.card_congr eH2.toEquiv
    _ = Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction
          Gal(IntermediateField.fixedField H/K)
          (IntermediateField.fixedField H)ˣ) 2) :=
      Nat.card_congr
        (multiplicativeHCohomology
          (G := Gal(IntermediateField.fixedField H/K))
          (M := (IntermediateField.fixedField H)ˣ)).toEquiv

omit [IsGalois K L] in
/-- The restriction term for a subgroup `H` is the degree-two cohomology of
`L` over the fixed field `Lᴴ`. -/
theorem nat_restricted_top
    (H : Subgroup Gal(L/K)) :
    Nat.card (groupCohomology
        (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) =
      Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction
          Gal(L/IntermediateField.fixedField H) Lˣ) 2) := by
  let eG : H ≃* Gal(L/IntermediateField.fixedField H) :=
    IntermediateField.subgroupEquivAlgEquiv H
  let eH2 : MHTwo H Lˣ ≃*
      MHTwo Gal(L/IntermediateField.fixedField H) Lˣ :=
    MHTrans.h2Equiv eG (MulEquiv.refl Lˣ)
      (by intro g x; rfl)
  calc
    Nat.card (groupCohomology
        (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) =
        Nat.card (MHTwo H Lˣ) :=
      (Nat.card_congr
        (multiplicativeHCohomology
          (G := H) (M := Lˣ)).toEquiv).symm
    _ = Nat.card
        (MHTwo Gal(L/IntermediateField.fixedField H) Lˣ) :=
      Nat.card_congr eH2.toEquiv
    _ = Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction
          Gal(L/IntermediateField.fixedField H) Lˣ) 2) :=
      Nat.card_congr
        (multiplicativeHCohomology
          (G := Gal(L/IntermediateField.fixedField H))
          (M := Lˣ)).toEquiv

end

end Towers.CField.LClass
