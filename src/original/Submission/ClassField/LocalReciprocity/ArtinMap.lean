import Submission.ClassField.Shifting.FundamentalClassEquiv
import Submission.ClassField.LocalReciprocity.SubgroupHilbert90
import Submission.ClassField.LocalReciprocity.TateZeroQuotient
import Submission.ClassField.LocalBrauer.H2Cardinality
import Submission.ClassField.LocalBrauer.CohomologyTransport

/-!
# Finite local Artin maps from the local invariant

This file joins the explicit finite local fundamental class to Tate's
two-degree shift.  The local invariant and its base-change formula discharge
the ambient degree-two inputs.  What remains is exactly the subgroupwise
Hilbert 90 and degree-two cardinality data needed by Tate's theorem.
-/

namespace Submission.CField.LRecip

noncomputable section

open scoped IsMulCommutative
open CategoryTheory.Limits Rep
open Submission.CField.LFTheory
open Submission.CField.Shifting
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer

variable (K L : Type)
  [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- The local invariant base-change formula over every fixed field supplies
the subgroupwise degree-two cardinalities in Tate's theorem. -/
theorem fixed_base_change
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (invFixed : ∀ H : Subgroup Gal(L/K),
      BrauerGroup (IntermediateField.fixedField H) ≃*
        Multiplicative LocalInvariant)
    (hbaseFixed : ∀ (H : Subgroup Gal(L/K))
        (x : BrauerGroup (IntermediateField.fixedField H)),
      invL (brauerBaseChange (IntermediateField.fixedField H) L x) =
        invFixed H x ^
          Module.finrank (IntermediateField.fixedField H) L)
    (H : Subgroup Gal(L/K)) :
    Nat.card (groupCohomology
        (Rep.res H.subtype
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) = Nat.card H := by
  let F := IntermediateField.fixedField H
  let eG : H ≃* Gal(L/F) := IntermediateField.subgroupEquivAlgEquiv H
  let eH2 : MHTwo H Lˣ ≃* MHTwo Gal(L/F) Lˣ :=
    MHTrans.h2Equiv eG (MulEquiv.refl Lˣ) (by
      intro g x
      rfl)
  calc
    Nat.card (groupCohomology
        (Rep.res H.subtype
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) =
        Nat.card (Multiplicative
          (groupCohomology.H2
            (Rep.ofMulDistribMulAction H Lˣ))) := rfl
    _ = Nat.card (MHTwo H Lˣ) :=
      (Nat.card_congr
        (multiplicativeHCohomology
          (G := H) (M := Lˣ)).toEquiv).symm
    _ = Nat.card (MHTwo Gal(L/F) Lˣ) :=
      Nat.card_congr eH2.toEquiv
    _ = Nat.card (relativeBrauerGroup F L) :=
      Nat.card_congr
        (CProduc.hRelativeBrauer F L).toEquiv
    _ = Module.finrank F L :=
      relative_brauer_finrank F L
        (invFixed H) invL (hbaseFixed H)
    _ = Nat.card H := IntermediateField.finrank_fixedField_eq_card H

/-- The local invariant and its base-change formula supply the ambient
fundamental class and cardinality in Tate's theorem. -/
noncomputable def tateTwoShift
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L)
    (hcardH : ∀ H : Subgroup Gal(L/K),
      Nat.card (groupCohomology
        (Rep.res H.subtype
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) = Nat.card H) :
    TateTwoShift (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) := by
  let C := Rep.ofMulDistribMulAction Gal(L/K) Lˣ
  let gamma := localFundamentalClass K L invK invL hbase
  apply cohomologyResTop C gamma
  · intro x
    exact zmultiples_fundamental_class K L invK invL hbase x
  · calc
      Nat.card (groupCohomology C 2) = Module.finrank K L :=
        cohomology_units_finrank K L invK invL hbase
      _ = Nat.card Gal(L/K) := (IsGalois.card_aut_eq_finrank K L).symm
  · exact hilbert_90_zero
  · exact hcardH

/-- The resulting finite-level abstract Artin map.  Identifying its source
with `Kˣ / N_{L/K}(Lˣ)` and proving compatibility between finite levels are
the remaining formal steps toward Theorem I.1.1. -/
noncomputable def localAbstractArtin
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L)
    (hcardH : ∀ H : Subgroup Gal(L/K),
      Nat.card (groupCohomology
        (Rep.res H.subtype
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) = Nat.card H) :
    tateCohomologyZero (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ≃+
      Additive (Abelianization Gal(L/K)) := by
  let C := Rep.ofMulDistribMulAction Gal(L/K) Lˣ
  let gamma := localFundamentalClass K L invK invL hbase
  apply abstractArtinMap C gamma
  · intro x
    exact zmultiples_fundamental_class K L invK invL hbase x
  · calc
      Nat.card (groupCohomology C 2) = Module.finrank K L :=
        cohomology_units_finrank K L invK invL hbase
      _ = Nat.card Gal(L/K) := (IsGalois.card_aut_eq_finrank K L).symm
  · exact hilbert_90_zero
  · exact hcardH

/-- A finite local Artin map obtained from invariant base change over the
base field and over every subgroup fixed field. -/
noncomputable def abstractArtinChange
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L)
    (invFixed : ∀ H : Subgroup Gal(L/K),
      BrauerGroup (IntermediateField.fixedField H) ≃*
        Multiplicative LocalInvariant)
    (hbaseFixed : ∀ (H : Subgroup Gal(L/K))
        (x : BrauerGroup (IntermediateField.fixedField H)),
      invL (brauerBaseChange (IntermediateField.fixedField H) L x) =
        invFixed H x ^
          Module.finrank (IntermediateField.fixedField H) L) :
    tateCohomologyZero (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ≃+
      Additive (Abelianization Gal(L/K)) :=
  localAbstractArtin K L invK invL hbase
    (fixed_base_change K L
      invL invFixed hbaseFixed)

/-- The finite norm-residue isomorphism supplied by the local invariant,
still targeting the abelianization for a general finite Galois extension. -/
noncomputable def residueAddEquiv
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L)
    (invFixed : ∀ H : Subgroup Gal(L/K),
      BrauerGroup (IntermediateField.fixedField H) ≃*
        Multiplicative LocalInvariant)
    (hbaseFixed : ∀ (H : Subgroup Gal(L/K))
        (x : BrauerGroup (IntermediateField.fixedField H)),
      invL (brauerBaseChange (IntermediateField.fixedField H) L x) =
        invFixed H x ^
          Module.finrank (IntermediateField.fixedField H) L) :
    Additive (Kˣ ⧸ normSubgroup K L) ≃+
      Additive (Abelianization Gal(L/K)) :=
  (galoisTateQuotient K L).symm.trans
    (abstractArtinChange K L
      invK invL hbase invFixed hbaseFixed)

/-- For an abelian finite Galois extension, the preceding equivalence is the
usual multiplicative norm-residue isomorphism. -/
noncomputable def abelianLocalResidue
    [IsMulCommutative Gal(L/K)]
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L)
    (invFixed : ∀ H : Subgroup Gal(L/K),
      BrauerGroup (IntermediateField.fixedField H) ≃*
        Multiplicative LocalInvariant)
    (hbaseFixed : ∀ (H : Subgroup Gal(L/K))
        (x : BrauerGroup (IntermediateField.fixedField H)),
      invL (brauerBaseChange (IntermediateField.fixedField H) L x) =
        invFixed H x ^
          Module.finrank (IntermediateField.fixedField H) L) :
    (Kˣ ⧸ normSubgroup K L) ≃* Gal(L/K) := by
  exact ((residueAddEquiv K L
    invK invL hbase invFixed hbaseFixed).trans
      (Abelianization.equivOfComm (H := Gal(L/K))).symm.toAdditive).toMultiplicative

end

end Submission.CField.LRecip
