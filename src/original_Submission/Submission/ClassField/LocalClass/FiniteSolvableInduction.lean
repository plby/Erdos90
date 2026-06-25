import Submission.ClassField.LocalClass.LocalUnitsRep
import Submission.ClassField.LocalClass.HerbrandQuotientsField
import Submission.ClassField.LocalClass.SolvableInduction
import Submission.ClassField.LocalReciprocity.SubgroupHilbert90

/-!
# Milne III.2.6 via solvable induction

This file follows the proof given in the source: Lemma III.2.2 supplies the
lower bound, Lemma III.2.5 plus Hilbert 90 settles cyclic extensions, and
solvability of finite local Galois groups reduces the general case to the
cyclic case.
-/

namespace Submission.CField.LClass

open CategoryTheory CategoryTheory.Limits
open Submission.CField.Shifting
open Submission.CField.LRecip
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

attribute [local instance] Units.mulDistribMulActionRight

/-- The lower bound from Lemma III.2.2, uniformly for canonically normed
local fields. -/
abbrev CanonicalUnitsBound : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    (_hF : letI : ValuativeRel F :=
      ValuativeRel.ofValuation (NormedField.valuation (K := F))
      IsNonarchimedeanLocalField F)
    [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E],
    Module.finrank F E ≤
      Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ) 2)

/-- The cyclic numerical input in the characteristic-zero proof of
Lemma III.2.6, uniformly for canonically normed local fields. -/
abbrev CyclicCharCardinality : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    [CharZero F]
    (_hF : letI : ValuativeRel F :=
      ValuativeRel.ofValuation (NormedField.valuation (K := F))
      IsNonarchimedeanLocalField F)
    [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [IsCyclic Gal(E/F)],
    Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ) 2) =
      Module.finrank F E

/-- Lemma III.2.5 and Hilbert 90 give the degree-two cardinality formula
for a cyclic extension. -/
theorem cyclic_units_finrank
    (F E : Type)
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] [CharZero F]
    [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [IsCyclic Gal(E/F)] :
    Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ) 2) =
      Module.finrank F E := by
  letI : CommGroup Gal(E/F) := IsCyclic.commGroup
  obtain ⟨-, hquotient⟩ := local_herbrand_quotients F E
  obtain ⟨hfiniteOne, hfiniteTwo, hquotient⟩ := hquotient
  letI : Finite (groupCohomology
      (Rep.ofAlgebraAutOnUnits F E) 1) := hfiniteOne
  letI : Finite (groupCohomology
      (Rep.ofAlgebraAutOnUnits F E) 2) := hfiniteTwo
  have hcardOne : Nat.card (groupCohomology
      (Rep.ofAlgebraAutOnUnits F E) 1) = 1 :=
    Nat.card_unique
  change (Nat.card (groupCohomology
      (Rep.ofAlgebraAutOnUnits F E) 2) : ℚ) /
      Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits F E) 1) =
      Module.finrank F E at hquotient
  rw [hcardOne, Nat.cast_one, div_one] at hquotient
  exact_mod_cast hquotient

/-- Canonical-valuation wrapper for the cyclic calculation. -/
theorem cyclic_finrank_canonical
    (F E : Type)
    [NontriviallyNormedField F] [IsUltrametricDist F] [CharZero F]
    (hF : letI : ValuativeRel F :=
      ValuativeRel.ofValuation (NormedField.valuation (K := F))
      IsNonarchimedeanLocalField F)
    [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [IsCyclic Gal(E/F)] :
    Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ) 2) =
      Module.finrank F E := by
  letI : ValuativeRel F :=
    ValuativeRel.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F := hF
  exact cyclic_units_finrank F E

/-- Lemma III.2.2 supplies the numerical lower bound used in the induction:
its canonical copy of `ZMod [E:F]` injects into degree-two cohomology. -/
theorem canonical_units_bound :
    CanonicalUnitsBound := by
  intro F E _ _ hF _ _ _ _
  letI : ValuativeRel F :=
    ValuativeRel.ofValuation (NormedField.valuation (K := F))
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F := hF
  let n := Module.finrank F E
  letI : NeZero n :=
    ⟨(Module.finrank_pos (R := F) (M := E)).ne'⟩
  let T := invariantPowTorsion n
  let eT : Multiplicative (ZMod n) ≃* T :=
    (torsionZMod n).toMultiplicative.trans
      (invariantTorsionPow n)
  let toTorsion := brauerInvariantTorsion F E
  have hToTorsion : Function.Injective toTorsion := by
    intro x y hxy
    apply Subtype.ext
    apply (carryBrauerInvariant F).injective
    simpa [toTorsion, brauerInvariantTorsion] using
      congrArg Subtype.val hxy
  letI : Finite T := Finite.of_injective eT.symm eT.symm.injective
  letI : Finite (relativeBrauerGroup F E) :=
    Finite.of_injective toTorsion hToTorsion
  let eRelative := CProduc.hRelativeBrauer F E
  letI : Finite (MHTwo Gal(E/F) Eˣ) :=
    Finite.of_equiv (relativeBrauerGroup F E) eRelative.symm.toEquiv
  let eCohomology :=
    multiplicativeHCohomology (G := Gal(E/F)) (M := Eˣ)
  letI : Finite (Multiplicative
      (groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ))) :=
    Finite.of_equiv (MHTwo Gal(E/F) Eˣ) eCohomology.toEquiv
  letI : Finite (groupCohomology.H2
      (Rep.ofMulDistribMulAction Gal(E/F) Eˣ)) :=
    Finite.of_equiv
      (Multiplicative
        (groupCohomology.H2
          (Rep.ofMulDistribMulAction Gal(E/F) Eˣ)))
      Multiplicative.toAdd
  calc
    Module.finrank F E = Nat.card (ZMod (Module.finrank F E)) :=
      (Nat.card_zmod _).symm
    _ ≤ Nat.card (groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(E/F) Eˣ)) :=
      Nat.card_le_card_of_injective
        (canonicalEmbedding F E)
        (canonicalEmbedding_injective F E)

set_option maxHeartbeats 2000000 in
-- Recursive elaboration compares cohomology over a normal subgroup and its fixed field.
/-- Characteristic-zero form of the solvable induction in Lemma III.2.6.
The extra characteristic assumption is propagated to every recursive fixed
field, rather than being postulated independently there. -/
theorem units_finrank_char
    (hLower : CanonicalUnitsBound)
    (hCyclic : CyclicCharCardinality)
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K] [CharZero K]
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
  have hLowerKL := hLower K L hK
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
      letI : CharZero F :=
        charZero_of_injective_algebraMap (algebraMap K F).injective
      let eQ : G ⧸ H ≃* Gal(F/K) :=
        IsGalois.normalAutEquivQuotient H
      have hcyclicF : IsCyclic Gal(F/K) := eQ.isCyclic.mp hcyclic
      letI : IsCyclic Gal(F/K) := hcyclicF
      have hcardF : Nat.card (groupCohomology
          (Rep.ofMulDistribMulAction Gal(F/K) Fˣ) 2) =
          Module.finrank K F := hCyclic K F hK
      let eH : H ≃* Gal(L/F) :=
        IntermediateField.subgroupEquivAlgEquiv H
      have hcardH : Nat.card (groupCohomology
          (Rep.ofMulDistribMulAction Gal(L/F) Lˣ) 2) =
          Module.finrank F L :=
        units_finrank_char
          hLower hCyclic F L
            (inferInstance : IsNonarchimedeanLocalField F)
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
          (Rep.res H.subtype
            (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) := by
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
      exact (hCyclic K L hK).le
  · exact hLowerKL
termination_by Nat.card Gal(L/K)
decreasing_by
  rw [← Nat.card_congr
    (IntermediateField.subgroupEquivAlgEquiv H).toEquiv]
  exact nat_ne_top H hHtop

section SourceStatement

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K] [CharZero K]

local instance solvableSourceValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance solvableSourceValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Lemma III.2.6 (the proof from the source).**  For a finite Galois
extension of characteristic-zero nonarchimedean local fields, `H²(L/K)` has
order `[L : K]`.  The proof uses Lemma III.2.2 for the lower bound,
Lemma III.2.5 and Hilbert 90 for cyclic extensions, and solvable induction. -/
theorem h_finrank_solvable :
    Nat.card
        (groupCohomology.H2
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) =
      Module.finrank K L :=
  units_finrank_char
    canonical_units_bound
    cyclic_finrank_canonical
    K L (inferInstance : IsNonarchimedeanLocalField K)

end SourceStatement

end

end Submission.CField.LClass
