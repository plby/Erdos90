import Submission.ClassField.GlobalClass.FiniteNormTransitivity
import Submission.ClassField.GlobalClass.GaloisNormLimitation
import Submission.ClassField.GlobalClass.GaloisClosureGroup
import Submission.ClassField.GlobalClass.TateIndex

/-!
# The corestriction diagram in global norm limitation

After choosing a finite Galois closure `L/K` and writing `E = Lᴴ`, Milne's
fundamental-class square identifies the cokernel of `Hᵃᵇ → Gᵃᵇ` with
`C_K / Nm(C_E)`.  The preceding group-theoretic file identifies that
cokernel with the Galois group of the maximal abelian subfield of `E`.

This file isolates only the cohomological square and proves all consequences
for the literal idèle-class norm quotient.
-/

namespace Submission.CField.GClass

open NumberField
open Submission.CField.LRecip
open Submission.CField.Ideles
open Submission.CField.NIndex
open scoped IsMulCommutative

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- The exact output of the fundamental-class/corestriction square in the
proof of Theorem VIII.4.8.  No norm-limitation conclusion is included. -/
def CorestrictionCokernelBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)),
    Nonempty
      ((CK K ⧸ (canonicalIdeleNorm (K := K)
          (L := IntermediateField.fixedField H)).range) ≃*
        (Abelianization Gal(L/K) ⧸
          (abelianizedSubgroupInclusion H).range))

/-- The corestriction square and the group calculation identify the norm
quotient of `Lᴴ/K` with the Galois group of its canonical maximal abelian
subfield. -/
noncomputable def fixedMaximalAbelian
    (hcore : CorestrictionCokernelBridge.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    (CK K ⧸ (canonicalIdeleNorm (K := K)
        (L := IntermediateField.fixedField H)).range) ≃*
      Gal(maximalSubfieldInside K L H/K) :=
  (Classical.choice (hcore K L H)).trans
    (abelianizedInclusionCoker K L H)

/-- Hence the non-Galois norm quotient has the order predicted in Milne's
proof. -/
theorem fixed_maximal_abelian
    (hcore : CorestrictionCokernelBridge.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    (canonicalIdeleNorm (K := K)
      (L := IntermediateField.fixedField H)).range.index =
        Nat.card Gal(maximalSubfieldInside K L H/K) := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr
    (fixedMaximalAbelian
      hcore K L H).toEquiv

/-- In particular, the norm subgroup from an arbitrary fixed field has
finite index. -/
theorem fixed_field_index
    (hcore : CorestrictionCokernelBridge.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    (canonicalIdeleNorm (K := K)
      (L := IntermediateField.fixedField H)).range.FiniteIndex := by
  apply Subgroup.finiteIndex_iff.mpr
  rw [fixed_maximal_abelian
    hcore K L H]
  exact Nat.card_pos.ne'

set_option maxHeartbeats 2000000 in
-- The three dependent intermediate-field norm maps elaborate simultaneously.
set_option maxRecDepth 100000 in
/-- Norm limitation for an arbitrary fixed field inside a finite Galois
closure.  This is the literal situation in Milne's proof before transporting
an arbitrary finite extension into a chosen closure. -/
theorem norm_maximal_abelian
    (hcore : CorestrictionCokernelBridge.{u})
    (hindex : GaloisIndexFormula.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    (canonicalIdeleNorm (K := K)
        (L := IntermediateField.fixedField H)).range =
      (canonicalIdeleNorm (K := K)
        (L := maximalSubfieldInside K L H)).range := by
  let E := IntermediateField.fixedField H
  let F := maximalSubfieldInside K L H
  have hFE : F ≤ E := maximal_abelian_inside K L H
  letI : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
  letI : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : FiniteDimensional F E := FiniteDimensional.right K F E
  have htrans : canonicalIdeleNorm (K := K) (L := E) =
      (canonicalIdeleNorm (K := K) (L := F)).comp
        (canonicalIdeleNorm (K := F) (L := E)) :=
    canonical_idele_trans
      (norm_trans_arbitrary (K := K) (E := F) (L := E))
  have hcontain :
      (canonicalIdeleNorm (K := K) (L := E)).range ≤
        (canonicalIdeleNorm (K := K) (L := F)).range := by
    rw [htrans]
    rintro _ ⟨c, rfl⟩
    exact ⟨canonicalIdeleNorm (K := F) (L := E) c, rfl⟩
  have hEindex :
      (canonicalIdeleNorm (K := K) (L := E)).range.index =
        Nat.card Gal(F/K) :=
    fixed_maximal_abelian hcore K L H
  have hFindex :
      (canonicalIdeleNorm (K := K) (L := F)).range.index =
        Nat.card (Abelianization Gal(F/K)) :=
    hindex K F
  have hcard : Nat.card Gal(F/K) =
      Nat.card (Abelianization Gal(F/K)) :=
    Nat.card_congr
      (Abelianization.equivOfComm (H := Gal(F/K))).toEquiv
  letI : (canonicalIdeleNorm (K := K) (L := E)).range.FiniteIndex :=
    fixed_field_index hcore K L H
  exact subgroup_index hcontain
    (hEindex.trans (hcard.trans hFindex.symm))

/-- Source-faithful fixed-field norm limitation assembled from Theorems
VII.5.1 and VIII.4.7, Tate's degree-minus-two shift, and the corestriction
square. -/
theorem fixed_previous_results
    (h51 : Submission.CField.CIdeles.IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hTate : TateNegBridge.{u})
    (hcore : CorestrictionCokernelBridge.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    (canonicalIdeleNorm (K := K)
        (L := IntermediateField.fixedField H)).range =
      (canonicalIdeleNorm (K := K)
        (L := maximalSubfieldInside K L H)).range := by
  apply norm_maximal_abelian hcore _ K L H
  apply galois_formula_isomorphism
  exact isomorphism_previous_results h51 h47 hTate

end

end Submission.CField.GClass
