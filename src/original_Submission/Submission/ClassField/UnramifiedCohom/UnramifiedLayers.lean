import Mathlib.FieldTheory.Galois.Profinite
import Submission.ClassField.UnramifiedCohom.NormInteger

/-!
# Finite layers of an infinite unramified extension

Milne calls an algebraic Galois extension unramified when all of its finite
subextensions are unramified.  This file records that intrinsic definition
using the spectral-integer predicate from Proposition III.1.1 and proves
that the fixed field of every open normal subgroup is one of those finite
unramified layers.
-/

namespace Submission.CField.UCohom

noncomputable section

namespace IUExt

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [IsGalois K L]

/-- An algebraic Galois extension is unramified if every finite Galois
intermediate field is intrinsically unramified over the base local field. -/
def IsUnramified : Prop :=
  ∀ E : FiniteGaloisIntermediateField K L,
    FUExt.IsUnramified K E

/-- The field fixed by an open normal subgroup is finite Galois and hence is
covered by the defining finite-layer condition. -/
theorem fixed_field_unramified
    (h : IsUnramified K L) (N : OpenNormalSubgroup Gal(L/K)) :
    let F := IntermediateField.fixedField (N : Subgroup Gal(L/K))
    letI : FiniteDimensional K F := by
      let H : ClosedSubgroup Gal(L/K) :=
        ⟨(N : Subgroup Gal(L/K)), N.toOpenSubgroup.isClosed⟩
      apply (InfiniteGalois.isOpen_iff_finite F).mp
      rw [InfiniteGalois.fixingSubgroup_fixedField H]
      exact N.toOpenSubgroup.isOpen'
    FUExt.IsUnramified K F := by
  let F := IntermediateField.fixedField (N : Subgroup Gal(L/K))
  let H : ClosedSubgroup Gal(L/K) :=
    ⟨(N : Subgroup Gal(L/K)), N.toOpenSubgroup.isClosed⟩
  have hopen : IsOpen F.fixingSubgroup.carrier := by
    rw [InfiniteGalois.fixingSubgroup_fixedField H]
    exact N.toOpenSubgroup.isOpen'
  letI : FiniteDimensional K F :=
    (InfiniteGalois.isOpen_iff_finite F).mp hopen
  letI : IsGalois K F :=
    IsGalois.of_fixedField_normal_subgroup (N : Subgroup Gal(L/K))
  let E : FiniteGaloisIntermediateField K L :=
    { toIntermediateField := F }
  exact h E

end IUExt

end


end Submission.CField.UCohom
