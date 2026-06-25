import Submission.ClassField.LocalExistence.NormFiberCompactness

/-!
# Relative norm fibres in a fixed finite overfield

This file formalizes the compact-intersection part of Step III.5.2 inside a
chosen separable closure of the base field.  The indexing objects are finite
abelian overfields of a fixed finite abelian subextension.  The final
comparison with *all* finite abelian extensions of the intermediate field is
stated separately as a cofinality condition; this is precisely the remaining
norm-limitation input, rather than a hidden identification of two different
chosen separable closures.
-/

namespace Submission.CField.LExist

open Submission.CField.LFTheory
open Submission.CField.LBrauer

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

/-- A finite abelian extension of `K` in the chosen separable closure which
contains the fixed finite abelian subextension `L`. -/
structure FAOverfi (L : FASubext K) where
  upper : FASubext K
  le : L.intermediateField ≤ upper.intermediateField

namespace FAOverfi

variable {K} {L : FASubext K}

/-- The compositum of two overfields is again an overfield. -/
noncomputable def sup (P Q : FAOverfi K L) :
    FAOverfi K L where
  upper := P.upper.sup Q.upper
  le := by
    rw [FASubext.sup_intermediateField]
    exact P.le.trans le_sup_left

end FAOverfi

/-- The relative norm subgroup `N_{M/L}(M×)` attached to an overfield
`M/K` containing `L/K`. -/
noncomputable def relativeNormSubgroup
    (L : FASubext K)
    (P : FAOverfi K L) : Subgroup L.1ˣ := by
  letI : Algebra L.1 P.upper.1 :=
    RingHom.toAlgebra (IntermediateField.inclusion P.le)
  exact normSubgroup L.1 P.upper.1

/-- The part of the fibre `N_{L/K}^{-1}(a)` which is a relative norm from
the overfield `P`. -/
def relativeNormFiber
    (L : FASubext K) (a : Kˣ)
    (P : FAOverfi K L) : Set L.1ˣ :=
  (relativeNormSubgroup K L P : Set L.1ˣ) ∩ normUnitFiber K L.1 a

set_option maxHeartbeats 1000000 in
-- Expanding norm transitivity through a dependent overfield is elaboration-heavy.
set_option synthInstance.maxHeartbeats 200000 in
-- The relative tower requires synthesizing its induced algebra structures.
omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K] in
/-- A base norm-core element has a preimage in every relative norm fibre.
This is just transitivity of the algebra norm. -/
theorem relative_fiber_core
    (L : FASubext K) (a : Kˣ)
    (ha : a ∈ localNormCore K)
    (P : FAOverfi K L) :
    (relativeNormFiber K L a P).Nonempty := by
  letI : Algebra L.1 P.upper.1 :=
    RingHom.toAlgebra (IntermediateField.inclusion P.le)
  letI : IsScalarTower K L.1 P.upper.1 :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  rw [localNormCore, familyCore, Subgroup.mem_iInf] at ha
  obtain ⟨z, hz⟩ := ha P.upper
  refine ⟨normOnUnits L.1 P.upper.1 z, ?_, ?_⟩
  · exact ⟨z, rfl⟩
  · apply Units.ext
    exact (Algebra.norm_norm (R := K) (S := L.1)
      (A := P.upper.1) (a := (z : P.upper.1))).trans
      (congrArg Units.val hz)

end

end Submission.CField.LExist
