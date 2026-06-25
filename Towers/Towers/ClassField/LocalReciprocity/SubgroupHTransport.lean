import Towers.ClassField.CrossedProducts.Multiplicative2Comparison
import Towers.ClassField.LocalBrauer.CohomologyTransport

/-!
# Transporting finite local `H²` cardinalities to subgroups

Tate's theorem is applied to `Gal(L/K)`, but its numerical hypothesis is
required after restriction to every subgroup `H`.  The fixed-field theorem
identifies `H` with `Gal(L/Lʰ)`; this file records that the corresponding
degree-two cohomology groups have the same cardinality.  No local invariant
or base-change formula is used here.
-/

namespace Towers.CField.LRecip

noncomputable section

open Towers.CField.CProduca
open Towers.CField.LBrauer

variable (K L : Type)
  [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- A degree-two cardinality calculation over every subgroup fixed field
supplies exactly the subgroupwise numerical hypothesis in Tate's theorem.

The premise is deliberately stated using the genuine Galois group
`Gal(L/Lʰ)`.  The conclusion concerns restriction of the original
`Gal(L/K)`-representation to `H`; the proof transports normalized
multiplicative cocycles along the canonical fixed-field equivalence. -/
theorem h_fixed_cardinality
    (hcard : ∀ H : Subgroup Gal(L/K),
      Nat.card
          (groupCohomology.H2
            (Rep.ofMulDistribMulAction
              Gal(L/IntermediateField.fixedField H) Lˣ)) =
        Module.finrank (IntermediateField.fixedField H) L)
    (H : Subgroup Gal(L/K)) :
    Nat.card
        (groupCohomology
          (Rep.res H.subtype
            (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) =
      Nat.card H := by
  let F := IntermediateField.fixedField H
  let eG : H ≃* Gal(L/F) := IntermediateField.subgroupEquivAlgEquiv H
  let eH2 : MHTwo H Lˣ ≃* MHTwo Gal(L/F) Lˣ :=
    MHTrans.h2Equiv eG (MulEquiv.refl Lˣ) (by
      intro g x
      rfl)
  calc
    Nat.card
        (groupCohomology
          (Rep.res H.subtype
            (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) =
        Nat.card
          (Multiplicative
            (groupCohomology.H2
              (Rep.ofMulDistribMulAction H Lˣ))) := rfl
    _ = Nat.card (MHTwo H Lˣ) :=
      (Nat.card_congr
        (multiplicativeHCohomology
          (G := H) (M := Lˣ)).toEquiv).symm
    _ = Nat.card (MHTwo Gal(L/F) Lˣ) :=
      Nat.card_congr eH2.toEquiv
    _ = Nat.card
        (Multiplicative
          (groupCohomology.H2
            (Rep.ofMulDistribMulAction Gal(L/F) Lˣ))) :=
      Nat.card_congr
        (multiplicativeHCohomology
          (G := Gal(L/F)) (M := Lˣ)).toEquiv
    _ = Module.finrank F L := hcard H
    _ = Nat.card H := IntermediateField.finrank_fixedField_eq_card H

end

end Towers.CField.LRecip
