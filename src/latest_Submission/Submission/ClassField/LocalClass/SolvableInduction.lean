import Submission.ClassField.Shifting.SolvableGroup
import Submission.ClassField.LocalClass.FixedFieldTransport
import Submission.ClassField.LocalClass.InflationRestriction
import Submission.ClassField.LocalClass.LocalGaloisSolvable

/-!
# The solvable-group induction in Lemma III.2.6

This file isolates the formal induction in Milne's proof.  Its only
arithmetic inputs are the known lower bound for finite Galois extensions and
the cardinality formula in the cyclic case.  The intermediate fields used by
the induction, their Galois structures, and both cohomology terms in
inflation--restriction are derived internally.
-/

namespace Submission.CField.LClass

open CategoryTheory
open Submission.CField.Shifting
open Submission.CField.LBrauer

noncomputable section

attribute [local instance] Units.mulDistribMulActionRight

/-- The lower-bound input in Lemma III.2.6, stated uniformly so that it can
be applied to the proper subextensions produced by solvable-group
induction. -/
abbrev GaloisUnitsBound : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E],
    Module.finrank F E ≤
      Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ) 2)

/-- The cyclic-extension input in Lemma III.2.6, again uniform in the
extension rather than postulated separately for intermediate fields. -/
abbrev CyclicGaloisCardinality : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [IsCyclic Gal(E/F)],
    Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ) 2) =
      Module.finrank F E

/-- The actual local lower-bound input from the text.  Only the base field
is topological; the finite Galois extension receives no additional public
structure. -/
abbrev UnitsHBound : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E],
    Module.finrank F E ≤
      Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ) 2)

/-- The actual cyclic local-extension input from Lemma III.2.5. -/
abbrev CyclicUnitsCardinality : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [IsCyclic Gal(E/F)],
    Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ) 2) =
      Module.finrank F E

set_option maxHeartbeats 2000000 in
-- Recursive elaboration compares cohomology over a normal subgroup and its fixed field.
/-- The inductive core of Lemma III.2.6.  For a finite solvable Galois
extension, the universal lower bound and the cyclic case imply the full
degree-two cardinality formula. -/
theorem galois_units_solvable
    (hLower : GaloisUnitsBound)
    (hCyclic : CyclicGaloisCardinality)
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsSolvable Gal(L/K)] :
    Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) =
      Module.finrank K L := by
  classical
  let G := Gal(L/K)
  have hLowerKL := hLower K L
  letI : Finite (groupCohomology
      (Rep.ofMulDistribMulAction G Lˣ) 2) :=
    Nat.finite_of_card_ne_zero <| by
      apply Nat.ne_of_gt
      exact (Module.finrank_pos (R := K) (M := L)).trans_le hLowerKL
  apply Nat.le_antisymm
  · by_cases hG : Nontrivial G
    · letI : Nontrivial G := hG
      obtain ⟨H, hHtop, hnormal, hcyclic⟩ :=
        proper_normal_cyclic (G := G)
      letI : H.Normal := hnormal
      let F := IntermediateField.fixedField H
      let eQ : G ⧸ H ≃* Gal(F/K) :=
        IsGalois.normalAutEquivQuotient H
      have hcyclicF : IsCyclic Gal(F/K) := eQ.isCyclic.mp hcyclic
      letI : IsCyclic Gal(F/K) := hcyclicF
      have hcardF : Nat.card (groupCohomology
          (Rep.ofMulDistribMulAction Gal(F/K) Fˣ) 2) =
          Module.finrank K F := hCyclic K F
      let eH : H ≃* Gal(L/F) :=
        IntermediateField.subgroupEquivAlgEquiv H
      letI : IsSolvable Gal(L/F) :=
        solvable_of_surjective (f := eH.toMonoidHom) eH.surjective
      have hcardH : Nat.card (groupCohomology
          (Rep.ofMulDistribMulAction Gal(L/F) Lˣ) 2) =
          Module.finrank F L :=
        galois_units_solvable
          hLower hCyclic F L
      have hquotientCard : Nat.card (groupCohomology
          ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) 2) =
          Module.finrank K F := by
        rw [nat_invariants_fixed K L H]
        exact hcardF
      have hrestrictedCard : Nat.card (groupCohomology
          (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) =
          Module.finrank F L := by
        rw [nat_restricted_top K L H]
        exact hcardH
      letI : Finite (groupCohomology
          ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) 2) :=
        Nat.finite_of_card_ne_zero <| by
          rw [hquotientCard]
          exact Nat.ne_of_gt Module.finrank_pos
      letI : Finite (groupCohomology
          (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) :=
        Nat.finite_of_card_ne_zero <| by
          rw [hrestrictedCard]
          exact Nat.ne_of_gt Module.finrank_pos
      letI : Finite (groupCohomology
          ((Rep.ofMulDistribMulAction Gal(L/K) Lˣ).quotientToInvariants H) 2) := by
        change Finite (groupCohomology
          ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) 2)
        infer_instance
      letI : Finite (groupCohomology
          (Rep.res H.subtype (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) := by
        change Finite (groupCohomology
          (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2)
        infer_instance
      calc
        Nat.card (groupCohomology
            (Rep.ofMulDistribMulAction G Lˣ) 2) ≤
            Nat.card (groupCohomology
              ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) 2) *
              Nat.card (groupCohomology
                (Rep.res H.subtype
                  (Rep.ofAlgebraAutOnUnits K L)) 2) :=
          nat_units_normal (K := K) (L := L) H
        _ = Module.finrank K F * Module.finrank F L := by
          rw [hquotientCard, hrestrictedCard]
        _ = Module.finrank K L := Module.finrank_mul_finrank K F L
    · letI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG
      letI : IsCyclic G := inferInstance
      exact (hCyclic K L).le
  · exact hLowerKL
termination_by Nat.card Gal(L/K)
decreasing_by
  rw [← Nat.card_congr eH.toEquiv]
  exact nat_ne_top H hHtop

section LocalField

set_option maxHeartbeats 2000000 in
-- Each recursive fixed field is equipped with its canonical spectral local-field structure.
/-- Lemma III.2.6 reduced to precisely its two remaining numerical inputs.
Solvability of the local Galois group is supplied unconditionally by the
canonical spectral local-field structure on `L`. -/
theorem units_h_finrank
    (hLower : UnitsHBound)
    (hCyclic : CyclicUnitsCardinality)
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    (hK : letI : ValuativeRel K :=
      ValuativeRel.ofValuation (NormedField.valuation (K := K))
      IsNonarchimedeanLocalField K)
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) =
      Module.finrank K L := by
  classical
  letI : ValuativeRel K :=
    ValuativeRel.ofValuation (NormedField.valuation (K := K))
  letI : Valuation.Compatible (NormedField.valuation (K := K)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := K))
  letI : IsNonarchimedeanLocalField K := hK
  let G := Gal(L/K)
  letI : IsSolvable G := local_galois_solvable K L
  have hLowerKL := hLower K L
  letI : Finite (groupCohomology
      (Rep.ofMulDistribMulAction G Lˣ) 2) :=
    Nat.finite_of_card_ne_zero <| by
      apply Nat.ne_of_gt
      exact (Module.finrank_pos (R := K) (M := L)).trans_le hLowerKL
  apply Nat.le_antisymm
  · by_cases hG : Nontrivial G
    · letI : Nontrivial G := hG
      obtain ⟨H, hHtop, hnormal, hcyclic⟩ :=
        proper_normal_cyclic (G := G)
      letI : H.Normal := hnormal
      let F := IntermediateField.fixedField H
      letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
      letI : NontriviallyNormedField F :=
        FLExt.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := FLExt.valuativeRel K F
      letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
        Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
      letI : IsNonarchimedeanLocalField F :=
        FLExt.nonarchimedeanLocalField K F
      let eQ : G ⧸ H ≃* Gal(F/K) :=
        IsGalois.normalAutEquivQuotient H
      have hcyclicF : IsCyclic Gal(F/K) := eQ.isCyclic.mp hcyclic
      letI : IsCyclic Gal(F/K) := hcyclicF
      have hcardF : Nat.card (groupCohomology
          (Rep.ofMulDistribMulAction Gal(F/K) Fˣ) 2) =
          Module.finrank K F := hCyclic K F
      let eH : H ≃* Gal(L/F) :=
        IntermediateField.subgroupEquivAlgEquiv H
      have hcardH : Nat.card (groupCohomology
          (Rep.ofMulDistribMulAction Gal(L/F) Lˣ) 2) =
          Module.finrank F L :=
        units_h_finrank
          hLower hCyclic F L (inferInstance : IsNonarchimedeanLocalField F)
      have hquotientCard : Nat.card (groupCohomology
          ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) 2) =
          Module.finrank K F := by
        rw [nat_invariants_fixed K L H]
        exact hcardF
      have hrestrictedCard : Nat.card (groupCohomology
          (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) =
          Module.finrank F L := by
        rw [nat_restricted_top K L H]
        exact hcardH
      letI : Finite (groupCohomology
          ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) 2) :=
        Nat.finite_of_card_ne_zero <| by
          rw [hquotientCard]
          exact Nat.ne_of_gt Module.finrank_pos
      letI : Finite (groupCohomology
          (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) :=
        Nat.finite_of_card_ne_zero <| by
          rw [hrestrictedCard]
          exact Nat.ne_of_gt Module.finrank_pos
      letI : Finite (groupCohomology
          ((Rep.ofMulDistribMulAction Gal(L/K) Lˣ).quotientToInvariants H) 2) := by
        change Finite (groupCohomology
          ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) 2)
        infer_instance
      letI : Finite (groupCohomology
          (Rep.res H.subtype (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) := by
        change Finite (groupCohomology
          (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2)
        infer_instance
      calc
        Nat.card (groupCohomology
            (Rep.ofMulDistribMulAction G Lˣ) 2) ≤
            Nat.card (groupCohomology
              ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) 2) *
              Nat.card (groupCohomology
                (Rep.res H.subtype
                  (Rep.ofAlgebraAutOnUnits K L)) 2) :=
          nat_units_normal (K := K) (L := L) H
        _ = Module.finrank K F * Module.finrank F L := by
          rw [hquotientCard, hrestrictedCard]
        _ = Module.finrank K L := Module.finrank_mul_finrank K F L
    · letI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG
      letI : IsCyclic G := inferInstance
      exact (hCyclic K L).le
  · exact hLowerKL
termination_by Nat.card Gal(L/K)
decreasing_by
  rw [← Nat.card_congr
    (IntermediateField.subgroupEquivAlgEquiv H).toEquiv]
  exact nat_ne_top H hHtop

end LocalField

end

end Submission.CField.LClass
