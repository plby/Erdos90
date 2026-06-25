import Towers.ClassField.LocalReciprocity.LocalUnitsRep
import Towers.ClassField.LocalExistence.RelativeCoreLifting

/-!
# Milne, Class Field Theory, Section III.5, Step 2

Fix a finite abelian subextension `L/K` in the chosen separable closure.  The
relative norm core below is the intersection of the groups
`N_{P/L}(P×)`, where `P/K` ranges over the finite abelian overfields of `L`
in that same closure.  Milne's compact-fibre argument proves

`N_{L/K}(relativeLocalCore K L) = localNormCore K`.

The source writes the group on the left as `D_L`, indexed by all finite
abelian extensions of `L` in a separable closure of `L`.  Identifying that
independently chosen indexing family with the relative overfields used here
requires a cofinality/base-change theorem for finite abelian extensions and
norm groups.  That bridge is not yet present in the repository.  Thus the
equality below is the exact unconditional statement supplied by the current
indexing API; no cofinality hypothesis is added to its public statement.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.LRecip
open Towers.CField.LBrauer

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance relativeNormCoreValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance relativeNormCoreValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

/-- The intersection of all relative norm groups coming from finite abelian
overfields of `L/K` in the fixed separable closure of `K`. -/
def relativeLocalCore (L : FASubext K) : Subgroup L.1ˣ :=
  ⨅ P : FAOverfi K L, relativeNormSubgroup K L P

set_option maxHeartbeats 3000000 in
-- Building the spectral local structures and finite Artin quotient is instance-heavy.
set_option synthInstance.maxHeartbeats 500000 in
/-- Theorem III.3.1 makes each relative norm group have finite index, so the
finite-index premise internal to the compact-fibre construction is automatic.
-/
theorem relative_norm_index
    (L : FASubext K)
    (P : FAOverfi K L) :
    (relativeNormSubgroup K L P).FiniteIndex := by
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

/-- A norm-core element of `K` has one preimage in `L` which is
simultaneously a norm from every finite abelian overfield of `L/K`. -/
theorem preimage_relative_core
    (L : FASubext K) (a : Kˣ)
    (ha : a ∈ localNormCore K) :
    ∃ y : L.1ˣ, normOnUnits K L.1 y = a ∧
      y ∈ relativeLocalCore K L := by
  obtain ⟨y, hya, hy⟩ := preimage_relative_subgroups
    K L a ha (relative_norm_index K L)
  refine ⟨y, hya, ?_⟩
  rw [relativeLocalCore, Subgroup.mem_iInf]
  exact hy

set_option maxHeartbeats 3000000 in
-- The two norm-transitivity towers through a compositum are instance-heavy.
set_option synthInstance.maxHeartbeats 500000 in
omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- Norming the relative core down to `K` lands in every finite-abelian norm
group over `K`.  For a test extension `M/K`, use the overfield `LM`, then
apply norm transitivity through `L` and through `M`. -/
theorem relative_local_core
    (L : FASubext K) :
    (relativeLocalCore K L).map (normOnUnits K L.1) ≤
      localNormCore K := by
  rintro a ⟨y, hy, rfl⟩
  rw [localNormCore, familyCore, Subgroup.mem_iInf]
  intro M
  let S : FASubext K := L.sup M
  have hLS : L.intermediateField ≤ S.intermediateField := by
    dsimp [S]
    exact le_sup_left
  have hMS : M.intermediateField ≤ S.intermediateField := by
    dsimp [S]
    exact le_sup_right
  let P : FAOverfi K L := ⟨S, hLS⟩
  have hyP : y ∈ relativeNormSubgroup K L P := by
    exact Subgroup.mem_iInf.mp hy P
  letI : Algebra L.1 S.1 :=
    RingHom.toAlgebra (IntermediateField.inclusion hLS)
  letI : Algebra M.1 S.1 :=
    RingHom.toAlgebra (IntermediateField.inclusion hMS)
  letI : IsScalarTower K L.1 S.1 :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  letI : IsScalarTower K M.1 S.1 :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  letI : Module.Finite L.1 S.1 :=
    Module.Finite.of_restrictScalars_finite K L.1 S.1
  letI : Module.Finite M.1 S.1 :=
    Module.Finite.of_restrictScalars_finite K M.1 S.1
  change y ∈ normSubgroup L.1 S.1 at hyP
  obtain ⟨z, hz⟩ := hyP
  refine ⟨normOnUnits M.1 S.1 z, ?_⟩
  apply Units.ext
  exact (Algebra.norm_norm (R := K) (S := M.1) (A := S.1)
    (a := (z : S.1))).trans
    ((Algebra.norm_norm (R := K) (S := L.1) (A := S.1)
      (a := (z : S.1))).symm.trans
        (congrArg Units.val (congrArg (normOnUnits K L.1) hz)))

/-- **Section III.5, Step 2, in the fixed-relative indexing.**  The norm of
the common relative norm subgroup over `L` is exactly the common norm subgroup
over `K`.  Both inclusions are unconditional: compact relative fibres give
the reverse inclusion, while composita and norm transitivity give the forward
one. -/
theorem norm_relative_core
    (L : FASubext K) :
    (relativeLocalCore K L).map (normOnUnits K L.1) =
      localNormCore K := by
  apply le_antisymm
  · exact relative_local_core K L
  · intro a ha
    obtain ⟨y, hya, hy⟩ :=
      preimage_relative_core K L a ha
    exact ⟨y, hy, hya⟩

end

end Towers.CField.LExist
