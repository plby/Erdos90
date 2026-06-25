import Submission.ClassField.CyclicIdeles.ClassRestrictionComparison
import Submission.ClassField.CyclicIdeles.IdeleClassRep

/-!
# Chapter VII, Section 5, Lemma 5.3: the Sylow fixed-field bridge

Restriction of the idèle-class representation to a Sylow subgroup is the
idèle-class representation of the corresponding fixed-field extension.
-/

namespace Submission.CField.CIdeles

open CategoryTheory Limits
open IsDedekindDomain NumberField Representation
open Submission.CField.Shifting
open Submission.CField.ICohomo
open Submission.CField.HNorm

noncomputable section

universe u

set_option maxHeartbeats 3000000 in
-- The target record contains nested group-cohomology constructions.
private noncomputable def sylowFixedData
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K)) :
    SylowFixedData K L p P where
  h_1_equiv := by
    change groupCohomology (ideleCohomologyRepresentation
        (IntermediateField.fixedField (P : Subgroup Gal(L/K))) L) 1 ≃+
      groupCohomology (Rep.res (P : Subgroup Gal(L/K)).subtype
        (ideleCohomologyRepresentation K L)) 1
    let E := IntermediateField.fixedField (P : Subgroup Gal(L/K))
    let eP := IntermediateField.subgroupEquivAlgEquiv
      (P : Subgroup Gal(L/K))
    exact
      (cohomologyMulIso eP
        (ideleCohomologyRepresentation E L) 1).toLinearEquiv.toAddEquiv |>.trans
          (((groupCohomology.functor (ULift.{u} ℤ) P 1).mapIso
            (restrictedCohomologyIso K L P)).toLinearEquiv.toAddEquiv)
  h_2_equiv := by
    change groupCohomology (ideleCohomologyRepresentation
        (IntermediateField.fixedField (P : Subgroup Gal(L/K))) L) 2 ≃+
      groupCohomology (Rep.res (P : Subgroup Gal(L/K)).subtype
        (ideleCohomologyRepresentation K L)) 2
    let E := IntermediateField.fixedField (P : Subgroup Gal(L/K))
    let eP := IntermediateField.subgroupEquivAlgEquiv
      (P : Subgroup Gal(L/K))
    exact
      (cohomologyMulIso eP
        (ideleCohomologyRepresentation E L) 2).toLinearEquiv.toAddEquiv |>.trans
          (((groupCohomology.functor (ULift.{u} ℤ) P 2).mapIso
            (restrictedCohomologyIso K L P)).toLinearEquiv.toAddEquiv)

set_option maxHeartbeats 1000000 in
-- Unfolding the bridge exposes the same cohomology constructions.
/-- The actual extension over a Sylow fixed field gives the restricted
idèle-class cohomology groups. -/
theorem sylowFixedBridge : SylowFixedBridge.{u} := by
  intro K L _ _ _ _ _ _ _ p _ P
  exact ⟨sylowFixedData K L p P⟩

end

end Submission.CField.CIdeles
