import Submission.ClassField.LocalReciprocity.MaximalIntermediate
import Submission.ClassField.LocalReciprocity.Continuity
import Submission.ClassField.LocalExistence.RelativeNormCore
import Submission.ClassField.LocalExistence.FiniteIndexGroup
import Submission.ClassField.LocalReciprocity.GlobalBrauer
import Submission.ClassField.HilbertSymbols.Nondegeneracy
import Submission.ClassField.KummerTheory.KummerCorrespondenceProof
import Submission.ClassField.KummerNormIndex.ComplexAbsoluteValue

/-!
# Milne, Theorem III.5.1: Local Existence Theorem

This file proves the source-facing statement of the local existence theorem.
The central compactness argument chooses a norm preimage lying in every
relative norm subgroup over a fixed finite Galois extension.  The full Kummer
extension then shows that this preimage is an `n`th power.  Taking its norm
provides the roots required to prove that the intersection of all finite
abelian norm groups is divisible, completing Milne's existence argument.
-/

namespace Submission.CField.LExist

open Submission.CField.LFTheory
open Submission.CField.LRecip
open Submission.CField.HSymbol
open Submission.CField.LBrauer
open Submission.CField.KTheory
open Submission.CField.KNIndex

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance proofValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance proofValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

theorem norm_galois_core
    (P : Type) [Field P] [Algebra K P] [FiniteDimensional K P] [IsGalois K P]
    (a : Kˣ) (ha : a ∈ localNormCore K) :
    a ∈ normSubgroup K P := by
  let E := maximalAbelianIntermediate K P
  let Eext : FAExt K :=
    { carrier := E
      field := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      isGalois := inferInstance
      isAbelian := inferInstance }
  let M : FASubext K := Eext.finiteAbelianSubextension
  have haM : a ∈ M.normGroup := by
    rw [localNormCore, familyCore, Subgroup.mem_iInf] at ha
    exact ha M
  have haE : a ∈ normSubgroup K E := by
    change a ∈ Eext.normGroup
    rw [Eext.norm_abelian_subextension]
    exact haM
  rw [abelian_intermediate_field K P]
  exact haE

/-- A finite Galois extension of `K` containing `L`. -/
structure FGOverfi
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) where
  upper : FiniteGaloisIntermediateField K (AlgebraicClosure K)
  le : L.toIntermediateField ≤ upper.toIntermediateField

namespace FGOverfi

variable {K} {L : FiniteGaloisIntermediateField K (AlgebraicClosure K)}

noncomputable def sup (P Q : FGOverfi K L) :
    FGOverfi K L := by
  let E := P.upper ⊔ Q.upper
  exact ⟨E, P.le.trans le_sup_left⟩

end FGOverfi

noncomputable def galoisRelativeSubgroup
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (P : FGOverfi K L) : Subgroup L.1ˣ := by
  letI : Algebra L.1 P.upper.1 :=
    RingHom.toAlgebra (IntermediateField.inclusion P.le)
  exact normSubgroup L.1 P.upper.1

def galoisRelativeFiber
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (a : Kˣ)
    (P : FGOverfi K L) : Set L.1ˣ :=
  (galoisRelativeSubgroup K L P : Set L.1ˣ) ∩ normUnitFiber K L.1 a

set_option maxHeartbeats 1000000 in
-- Elaborating norm transitivity through the two intermediate-field subtypes is expensive.
set_option synthInstance.maxHeartbeats 200000 in
theorem fiber_nonempty_core
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (a : Kˣ)
    (ha : a ∈ localNormCore K)
    (P : FGOverfi K L) :
    (galoisRelativeFiber K L a P).Nonempty := by
  letI : Algebra L.1 P.upper.1 :=
    RingHom.toAlgebra (IntermediateField.inclusion P.le)
  letI : IsScalarTower K L.1 P.upper.1 :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  have haP : a ∈ normSubgroup K P.upper.1 :=
    norm_galois_core K P.upper.1 a ha
  obtain ⟨z, hz⟩ := haP
  refine ⟨normOnUnits L.1 P.upper.1 z, ⟨z, rfl⟩, ?_⟩
  apply Units.ext
  exact (Algebra.norm_norm (R := K) (S := L.1)
    (A := P.upper.1) (a := (z : P.upper.1))).trans
    (congrArg Units.val hz)

namespace FGOverfi

set_option maxHeartbeats 5000000 in
-- Both compositum projections require synthesizing several finite scalar towers.
set_option synthInstance.maxHeartbeats 200000 in
omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
theorem relative_subgroup_sup
    {L : FiniteGaloisIntermediateField K (AlgebraicClosure K)}
    (P Q : FGOverfi K L) :
    galoisRelativeSubgroup K L (P.sup Q) ≤
      galoisRelativeSubgroup K L P ⊓ galoisRelativeSubgroup K L Q := by
  intro y hy
  constructor
  · obtain ⟨z, rfl⟩ := hy
    let hPsup : P.upper.toIntermediateField ≤ (P.sup Q).upper.toIntermediateField :=
      le_sup_left
    letI : Algebra L.1 P.upper.1 :=
      RingHom.toAlgebra (IntermediateField.inclusion P.le)
    letI : Algebra P.upper.1 (P.sup Q).upper.1 :=
      RingHom.toAlgebra (IntermediateField.inclusion hPsup)
    letI : Algebra L.1 (P.sup Q).upper.1 :=
      RingHom.toAlgebra (IntermediateField.inclusion (P.sup Q).le)
    letI : IsScalarTower L.1 P.upper.1 (P.sup Q).upper.1 :=
      IsScalarTower.of_algebraMap_eq fun x => by
        exact (IntermediateField.inclusion_inclusion P.le hPsup x).symm
    letI : IsScalarTower K L.1 P.upper.1 :=
      IsScalarTower.of_algebraMap_eq fun x => by rfl
    letI : IsScalarTower K P.upper.1 (P.sup Q).upper.1 :=
      IsScalarTower.of_algebraMap_eq fun x => by rfl
    letI : Module.Finite L.1 P.upper.1 :=
      Module.Finite.of_restrictScalars_finite K L.1 P.upper.1
    letI : Module.Finite P.upper.1 (P.sup Q).upper.1 :=
      Module.Finite.of_restrictScalars_finite K P.upper.1 (P.sup Q).upper.1
    exact ⟨normOnUnits P.upper.1 (P.sup Q).upper.1 z, by
      apply Units.ext
      exact Algebra.norm_norm (R := L.1) (S := P.upper.1)
        (A := (P.sup Q).upper.1) (a := (z : (P.sup Q).upper.1))⟩
  · obtain ⟨z, rfl⟩ := hy
    let hQsup : Q.upper.toIntermediateField ≤ (P.sup Q).upper.toIntermediateField :=
      le_sup_right
    letI : Algebra L.1 Q.upper.1 :=
      RingHom.toAlgebra (IntermediateField.inclusion Q.le)
    letI : Algebra Q.upper.1 (P.sup Q).upper.1 :=
      RingHom.toAlgebra (IntermediateField.inclusion hQsup)
    letI : Algebra L.1 (P.sup Q).upper.1 :=
      RingHom.toAlgebra (IntermediateField.inclusion (P.sup Q).le)
    letI : IsScalarTower L.1 Q.upper.1 (P.sup Q).upper.1 :=
      IsScalarTower.of_algebraMap_eq fun x => by
        exact (IntermediateField.inclusion_inclusion Q.le hQsup x).symm
    letI : IsScalarTower K L.1 Q.upper.1 :=
      IsScalarTower.of_algebraMap_eq fun x => by rfl
    letI : IsScalarTower K Q.upper.1 (P.sup Q).upper.1 :=
      IsScalarTower.of_algebraMap_eq fun x => by rfl
    letI : Module.Finite L.1 Q.upper.1 :=
      Module.Finite.of_restrictScalars_finite K L.1 Q.upper.1
    letI : Module.Finite Q.upper.1 (P.sup Q).upper.1 :=
      Module.Finite.of_restrictScalars_finite K Q.upper.1 (P.sup Q).upper.1
    exact ⟨normOnUnits Q.upper.1 (P.sup Q).upper.1 z, by
      apply Units.ext
      exact Algebra.norm_norm (R := L.1) (S := Q.upper.1)
        (A := (P.sup Q).upper.1) (a := (z : (P.sup Q).upper.1))⟩

end FGOverfi

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
theorem galois_fiber_directed
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (a : Kˣ)
    (P Q : FGOverfi K L) :
    ∃ R : FGOverfi K L,
      galoisRelativeFiber K L a R ⊆
        galoisRelativeFiber K L a P ∩ galoisRelativeFiber K L a Q := by
  refine ⟨P.sup Q, ?_⟩
  rintro y ⟨hy, hya⟩
  have h := FGOverfi.relative_subgroup_sup
    (K := K) P Q hy
  exact ⟨⟨h.1, hya⟩, ⟨h.2, hya⟩⟩

set_option maxHeartbeats 1000000 in
-- Constructing the inherited local-field structure and Artin equivalence is expensive.
set_option synthInstance.maxHeartbeats 200000 in
theorem galois_relative_index
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (P : FGOverfi K L) :
    (galoisRelativeSubgroup K L P).FiniteIndex := by
  letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
  letI : NontriviallyNormedField L.1 :=
    FLExt.nontriviallyNormedField K L.1
  letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
  letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
  letI : IsNonarchimedeanLocalField L.1 :=
    FLExt.nonarchimedeanLocalField K L.1
  letI : Algebra L.1 P.upper.1 :=
    RingHom.toAlgebra (IntermediateField.inclusion P.le)
  letI : IsScalarTower K L.1 P.upper.1 :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  letI : Module.Finite L.1 P.upper.1 :=
    Module.Finite.of_restrictScalars_finite K L.1 P.upper.1
  letI : IsGalois L.1 P.upper.1 :=
    IsGalois.tower_top_of_isGalois K L.1 P.upper.1
  letI : Finite (L.1ˣ ⧸ normSubgroup L.1 P.upper.1) :=
    Finite.of_injective (localArtinEquiv L.1 P.upper.1)
      (localArtinEquiv L.1 P.upper.1).injective
  change (normSubgroup L.1 P.upper.1).FiniteIndex
  exact Subgroup.finiteIndex_of_finite_quotient

set_option maxHeartbeats 1000000 in
-- The compact-fibre proof synthesizes the full finite local-extension structure.
set_option synthInstance.maxHeartbeats 200000 in
theorem galois_fiber_compact
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (a : Kˣ)
    (ha : a ∈ localNormCore K)
    (P : FGOverfi K L) :
    letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
    letI : NontriviallyNormedField L.1 :=
      FLExt.nontriviallyNormedField K L.1
    letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
    letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
    letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
    letI : IsNonarchimedeanLocalField L.1 :=
      FLExt.nonarchimedeanLocalField K L.1
    IsCompact (galoisRelativeFiber K L a P) := by
  letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
  letI : NontriviallyNormedField L.1 :=
    FLExt.nontriviallyNormedField K L.1
  letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
  letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
  letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
  letI : IsNonarchimedeanLocalField L.1 :=
    FLExt.nonarchimedeanLocalField K L.1
  letI : Algebra L.1 P.upper.1 :=
    RingHom.toAlgebra (IntermediateField.inclusion P.le)
  letI : IsScalarTower K L.1 P.upper.1 :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  letI : Module.Finite L.1 P.upper.1 :=
    Module.Finite.of_restrictScalars_finite K L.1 P.upper.1
  letI : IsGalois L.1 P.upper.1 :=
    IsGalois.tower_top_of_isGalois K L.1 P.upper.1
  letI : (galoisRelativeSubgroup K L P).FiniteIndex :=
    galois_relative_index K L P
  letI : (normSubgroup L.1 P.upper.1).FiniteIndex := by
    change (galoisRelativeSubgroup K L P).FiniteIndex
    infer_instance
  change IsCompact ((normSubgroup L.1 P.upper.1 : Set L.1ˣ) ∩ normUnitFiber K L.1 a)
  have hopen : IsOpen (normSubgroup L.1 P.upper.1 : Set L.1ˣ) :=
    norm_subgroup L.1 P.upper.1
  have haL : a ∈ normSubgroup K L.1 :=
    norm_galois_core K L.1 a ha
  obtain ⟨y₀, hy₀⟩ := haL
  exact (fiber_compact_ker K L.1 a y₀ hy₀
    (units_ker_compact K L.1)).inter_left
      ((normSubgroup L.1 P.upper.1).isClosed_of_isOpen hopen)

theorem preimage_all_subgroups
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (a : Kˣ)
    (ha : a ∈ localNormCore K) :
    ∃ y : L.1ˣ, normOnUnits K L.1 y = a ∧
      ∀ P : FGOverfi K L,
        y ∈ galoisRelativeSubgroup K L P := by
  letI : Nonempty (FGOverfi K L) := ⟨⟨L, le_rfl⟩⟩
  letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
  letI : NontriviallyNormedField L.1 :=
    FLExt.nontriviallyNormedField K L.1
  letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
  letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
  letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
  letI : IsNonarchimedeanLocalField L.1 :=
    FLExt.nonarchimedeanLocalField K L.1
  obtain ⟨y, hy⟩ := inter_directed_compact
    (fun P : FGOverfi K L ↦ galoisRelativeFiber K L a P)
    (galois_fiber_directed K L a)
    (fiber_nonempty_core K L a ha)
    (galois_fiber_compact K L a ha)
  refine ⟨y, ?_, ?_⟩
  · let P : FGOverfi K L := Classical.choice inferInstance
    exact (Set.mem_iInter.mp hy P).2
  · intro P
    exact (Set.mem_iInter.mp hy P).1

set_option maxHeartbeats 3000000 in
-- The Kummer degree and norm-index calculation has a large finite-group search space.
set_option synthInstance.maxHeartbeats 500000 in
theorem maximal_kummer_range
    [CharZero K] (Omega : Type) [Field Omega] [Algebra K Omega]
    [IsAlgClosure K Omega]
    (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) :
    letI : Finite (PowerClassGroup K n) :=
      Finite.of_finite_univ (local_power_class K n hn hζ)
    let B : PCSubgro K n :=
      ⟨⊤, Set.toFinite _⟩
    let E : AESubext K Omega n :=
      kummerFieldSubextension K Omega n hn hζ B
    normSubgroup K E.carrier =
      (powMonoidHom n : Kˣ →* Kˣ).range := by
  letI : Finite (PowerClassGroup K n) :=
    Finite.of_finite_univ (local_power_class K n hn hζ)
  let B : PCSubgro K n := ⟨⊤, Set.toFinite _⟩
  let E : AESubext K Omega n :=
    kummerFieldSubextension K Omega n hn hζ B
  letI : FiniteDimensional K E.carrier := inferInstance
  letI : IsGalois K E.carrier := inferInstance
  letI : IsMulCommutative Gal(E.carrier/K) := inferInstance
  have hle : (powMonoidHom n : Kˣ →* Kˣ).range ≤
      normSubgroup K E.carrier := by
    rintro _ ⟨x, rfl⟩
    rw [← abelian_artin_ker K E.carrier]
    change abelianArtinHom K E.carrier (x ^ n) = 1
    rw [map_pow, E.exponent_dvd]
  letI : (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex :=
    Subgroup.finiteIndex_iff_finite_quotient.mpr inferInstance
  letI : Finite (Kˣ ⧸ normSubgroup K E.carrier) :=
    Finite.of_injective (abelianLocalArtin K E.carrier)
      (abelianLocalArtin K E.carrier).injective
  letI : (normSubgroup K E.carrier).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  change normSubgroup K E.carrier =
    (powMonoidHom n : Kˣ →* Kˣ).range
  symm
  apply subgroup_index hle
  calc
    (powMonoidHom n : Kˣ →* Kˣ).range.index =
        Nat.card (PowerClassGroup K n) := by
      rw [PowerClassGroup, Subgroup.index_eq_card]
    _ = B.card := by
      rw [PCSubgro.card_eq_card]
      exact (Nat.card_congr (Equiv.Set.univ (PowerClassGroup K n))).symm
    _ = Module.finrank K E.carrier := by
      symm
      exact finrank_kummer_field
        (K := K) (Omega := Omega) n hn
        ⟨ζ, (mem_primitiveRoots hn).2 hζ⟩ B
    _ = Nat.card Gal(E.carrier/K) :=
      (IsGalois.card_aut_eq_finrank K E.carrier).symm
    _ = Nat.card (Kˣ ⧸ normSubgroup K E.carrier) :=
      Nat.card_congr (abelianLocalArtin K E.carrier).symm.toEquiv
    _ = (normSubgroup K E.carrier).index := by
      rw [Subgroup.index_eq_card]

set_option maxHeartbeats 5000000 in
-- Embedding the Kummer field into a normal closure creates several scalar towers.
set_option synthInstance.maxHeartbeats 500000 in
theorem nth_all_subgroups
    [CharZero K]
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (n : ℕ) (hn : 0 < n) (ζ : L.1) (hζ : IsPrimitiveRoot ζ n)
    (y : L.1ˣ)
    (hy : ∀ P : FGOverfi K L,
      y ∈ galoisRelativeSubgroup K L P) :
    IsNthPower n y := by
  letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
  letI : NontriviallyNormedField L.1 :=
    FLExt.nontriviallyNormedField K L.1
  letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
  letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
  letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
  letI : IsNonarchimedeanLocalField L.1 :=
    FLExt.nonarchimedeanLocalField K L.1
  let OmegaK := AlgebraicClosure K
  let OmegaL := AlgebraicClosure L.1
  letI : Finite (PowerClassGroup L.1 n) :=
    Finite.of_finite_univ (local_power_class L.1 n hn hζ)
  let B : PCSubgro L.1 n := ⟨⊤, Set.toFinite _⟩
  let E : AESubext L.1 OmegaL n :=
    kummerFieldSubextension L.1 OmegaL n hn hζ B
  letI : Algebra L.1 OmegaK := (IntermediateField.val L.1).toRingHom.toAlgebra
  letI : IsScalarTower K L.1 OmegaK :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  let fE : E.carrier →ₐ[L.1] OmegaK := IsAlgClosed.lift
  let EF : IntermediateField L.1 OmegaK := fE.fieldRange
  let eEF : E.carrier ≃ₐ[L.1] EF := AlgEquiv.ofInjectiveField fE
  letI : Module.Finite L.1 EF := Module.Finite.equiv eEF.toLinearEquiv
  let E0 : IntermediateField K OmegaK := EF.restrictScalars K
  have hLE0 : L.toIntermediateField ≤ E0 := by
    intro x hx
    let xL : L.1 := ⟨x, hx⟩
    exact EF.algebraMap_mem xL
  letI : Algebra L.1 E0 :=
    RingHom.toAlgebra (IntermediateField.inclusion hLE0)
  letI : IsScalarTower K L.1 E0 :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  letI : Module.Finite L.1 E0 := by
    change Module.Finite L.1 EF
    infer_instance
  letI : Module.Finite K E0 := Module.Finite.trans L.1 E0
  let S0 : IntermediateField K OmegaK :=
    IntermediateField.normalClosure K E0 OmegaK
  letI : IsGalois K S0 := IsGalois.normalClosure K E0 OmegaK
  letI : FiniteDimensional K S0 :=
    normalClosure.is_finiteDimensional K E0 OmegaK
  let S : FiniteGaloisIntermediateField K OmegaK :=
    { S0 with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  have hE0S : E0 ≤ S0 := IntermediateField.le_normalClosure E0
  let P : FGOverfi K L := ⟨S, hLE0.trans hE0S⟩
  letI : Algebra L.1 S0 :=
    RingHom.toAlgebra (IntermediateField.inclusion (hLE0.trans hE0S))
  letI : IsScalarTower K L.1 S0 :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  letI : Module.Finite L.1 S0 :=
    Module.Finite.of_restrictScalars_finite K L.1 S0
  have hyS : y ∈ normSubgroup L.1 S0 := by
    exact hy P
  let j : EF →+* S0 := (IntermediateField.inclusion hE0S).toRingHom
  letI : Algebra EF S0 := j.toAlgebra
  letI : IsScalarTower L.1 EF S0 :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  letI : Module.Finite EF S0 :=
    Module.Finite.of_restrictScalars_finite L.1 EF S0
  have hyEF : y ∈ normSubgroup L.1 EF :=
    norm_subgroup_tower L.1 S0 EF hyS
  have hyE : y ∈ normSubgroup L.1 E.carrier := by
    rw [norm_alg_equiv L.1 E.carrier EF eEF]
    exact hyEF
  rw [maximal_kummer_range
    L.1 OmegaL n hn ζ hζ] at hyE
  exact hyE

set_option maxHeartbeats 5000000 in
-- The final candidate construction combines two algebraic closures and their compositum.
set_option synthInstance.maxHeartbeats 500000 in
theorem local_candidates_nonempty
    [CharZero K]
    (n : ℕ) (hn : n ≠ 0) (a : Kˣ) (ha : a ∈ localNormCore K)
    (A : FASubext K) :
    (localRootCandidates K n a A).Nonempty := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let Omega := AlgebraicClosure K
  letI : NeZero n := ⟨hn⟩
  let ζ : Omega := IsCyclotomicExtension.zeta n Omega Omega
  have hζ : IsPrimitiveRoot ζ n := IsCyclotomicExtension.zeta_spec n Omega Omega
  let f : A.1 →ₐ[K] Omega := IsAlgClosed.lift
  let AF0 : IntermediateField K Omega := f.fieldRange
  let eAF : A.1 ≃ₐ[K] AF0 := AlgEquiv.ofInjectiveField f
  letI : Module.Finite K AF0 := Module.Finite.equiv eAF.toLinearEquiv
  letI : IsGalois K AF0 := IsGalois.of_algEquiv eAF
  let AF : FiniteGaloisIntermediateField K Omega :=
    { AF0 with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let Z : FiniteGaloisIntermediateField K Omega :=
    FiniteGaloisIntermediateField.adjoin K ({ζ} : Set Omega)
  let L : FiniteGaloisIntermediateField K Omega := AF ⊔ Z
  have hζZ : ζ ∈ Z.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K ({ζ} : Set Omega)
      (Set.mem_singleton ζ)
  let ζL : L.1 := ⟨ζ, (le_sup_right : Z ≤ L) hζZ⟩
  have hζL : IsPrimitiveRoot ζL n := by
    apply IsPrimitiveRoot.of_map_of_injective (f := L.1.val)
    · exact hζ
    · exact L.1.val.injective
  obtain ⟨y, hya, hy⟩ :=
    preimage_all_subgroups K L a ha
  have hypow : IsNthPower n y :=
    nth_all_subgroups
      K L n hnpos ζL hζL y hy
  obtain ⟨c, hc⟩ := hypow
  let b : Kˣ := normOnUnits K L.1 c
  refine ⟨b, ?_, ?_⟩
  · calc
      b ^ n = normOnUnits K L.1 (c ^ n) := by
        rw [map_pow]
      _ = normOnUnits K L.1 y := congrArg (normOnUnits K L.1) hc
      _ = a := hya
  · have hAFL : AF.toIntermediateField ≤ L.toIntermediateField := le_sup_left
    letI : Algebra AF.1 L.1 :=
      RingHom.toAlgebra (IntermediateField.inclusion hAFL)
    letI : IsScalarTower K AF.1 L.1 :=
      IsScalarTower.of_algebraMap_eq fun x => by rfl
    letI : Module.Finite AF.1 L.1 :=
      Module.Finite.of_restrictScalars_finite K AF.1 L.1
    have hbAF : b ∈ normSubgroup K AF.1 := by
      refine ⟨normOnUnits AF.1 L.1 c, ?_⟩
      apply Units.ext
      exact Algebra.norm_norm (R := K) (S := AF.1)
        (A := L.1) (a := (c : L.1))
    have hnormEq : normSubgroup K A.1 = normSubgroup K AF.1 :=
      norm_alg_equiv K A.1 AF.1 eAF
    change b ∈ A.normGroup
    rw [show A.normGroup = normSubgroup K AF.1 from hnormEq]
    exact hbAF

theorem candidateNonemptinessStatement [CharZero K] :
    (IDSubgro (localNormCore K)) := by
  apply candidate_nonemptiness K
  intro n hn a ha A
  exact local_candidates_nonempty K n hn a ha A

/-- **Theorem III.5.1 (Existence Theorem).** -/
theorem localExistenceStatement [CharZero K] :
    IndexNormExistence K := by
  exact existence_candidate_statement K
    (assembledArtinHom K)
    (induces_assembled_all K)
    (candidateNonemptinessStatement K)

end
end Submission.CField.LExist
