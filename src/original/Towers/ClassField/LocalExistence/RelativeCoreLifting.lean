import Towers.ClassField.LocalExistence.RelativeNormCompactness

/-!
# Compact lifting to the relative norm core

This file completes the point-set part of Milne's Step III.5.2 for the
finite abelian overfields of a fixed finite abelian subextension in the
chosen separable closure.  In particular, one norm-core element admits a
single preimage which is simultaneously a relative norm from every such
overfield.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.LBrauer

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

namespace FAOverfi

variable {K} {L : FASubext K}

set_option maxHeartbeats 5000000 in
-- Norm transitivity over the dependent compositum overfield is elaboration-heavy.
set_option synthInstance.maxHeartbeats 200000 in
-- Both inclusions require synthesized algebra towers through the compositum.
omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The `sup` overfield maps into each of the two relative norm groups, by
transitivity of the field norm. -/
theorem relative_subgroup_sup
    (P Q : FAOverfi K L) :
    relativeNormSubgroup K L (P.sup Q) ≤
      relativeNormSubgroup K L P ⊓ relativeNormSubgroup K L Q := by
  intro y hy
  constructor
  · obtain ⟨z, rfl⟩ := hy
    let hPsup : P.upper.intermediateField ≤ (P.sup Q).upper.intermediateField :=
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
    let hQsup : Q.upper.intermediateField ≤ (P.sup Q).upper.intermediateField :=
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

end FAOverfi

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Relative norm fibres are downward directed under compositum. -/
theorem relative_fiber_directed
    (L : FASubext K) (a : Kˣ)
    (P Q : FAOverfi K L) :
    ∃ R : FAOverfi K L,
      relativeNormFiber K L a R ⊆
        relativeNormFiber K L a P ∩ relativeNormFiber K L a Q := by
  refine ⟨P.sup Q, ?_⟩
  rintro y ⟨hy, hya⟩
  have h := FAOverfi.relative_subgroup_sup
    (K := K) P Q hy
  exact ⟨⟨h.1, hya⟩, ⟨h.2, hya⟩⟩

set_option maxHeartbeats 1000000 in
-- Compactness unfolds the relative norm fibre and its induced local topology.
set_option synthInstance.maxHeartbeats 200000 in
-- The proof synthesizes transported structures on the finite overfield.
/-- Each relative norm fibre is a closed subset of the compact absolute
norm fibre, hence compact. -/
theorem relative_fiber_compact
    (L : FASubext K) (a : Kˣ)
    (ha : a ∈ localNormCore K)
    (hfiniteIndex : ∀ P : FAOverfi K L,
      (relativeNormSubgroup K L P).FiniteIndex)
    (P : FAOverfi K L) :
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
    IsCompact (relativeNormFiber K L a P) := by
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
  letI : (relativeNormSubgroup K L P).FiniteIndex := hfiniteIndex P
  letI : (normSubgroup L.1 P.upper.1).FiniteIndex := by
    change (relativeNormSubgroup K L P).FiniteIndex
    infer_instance
  change IsCompact ((normSubgroup L.1 P.upper.1 : Set L.1ˣ) ∩ normUnitFiber K L.1 a)
  have hopen : IsOpen (normSubgroup L.1 P.upper.1 : Set L.1ˣ) := by
    exact norm_subgroup L.1 P.upper.1
  exact (fiber_compact_core K a ha L).inter_left
    ((normSubgroup L.1 P.upper.1).isClosed_of_isOpen hopen)

/-- A base norm-core element has a norm preimage which belongs to every
relative norm group arising from a finite abelian overfield over `K`. -/
theorem preimage_relative_subgroups
    (L : FASubext K) (a : Kˣ)
    (ha : a ∈ localNormCore K) :
    (∀ P : FAOverfi K L,
      (relativeNormSubgroup K L P).FiniteIndex) →
    ∃ y : L.1ˣ, normOnUnits K L.1 y = a ∧
      ∀ P : FAOverfi K L,
        y ∈ relativeNormSubgroup K L P := by
  intro hfiniteIndex
  letI : Nonempty (FAOverfi K L) :=
    ⟨⟨L, le_rfl⟩⟩
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
    (fun P : FAOverfi K L ↦ relativeNormFiber K L a P)
    (relative_fiber_directed K L a)
    (relative_fiber_core K L a ha)
    (relative_fiber_compact K L a ha hfiniteIndex)
  refine ⟨y, ?_, ?_⟩
  · let P : FAOverfi K L := Classical.choice inferInstance
    exact (Set.mem_iInter.mp hy P).2
  · intro P
    exact (Set.mem_iInter.mp hy P).1

end

end Towers.CField.LExist
