import Submission.ClassField.LocalReciprocity.LocalUnitsRep
import Submission.ClassField.LocalReciprocity.FiniteIndexCore

/-!
# Milne, Class Field Theory, Theorem III.3.5: the Galois case

For a finite Galois extension `L/K`, the largest abelian intermediate field
is the fixed field of the commutator subgroup of `Gal(L/K)`.  Norm
transitivity gives one inclusion between the two norm groups.  Theorem
III.3.1 identifies their indices, so the inclusion is an equality.
-/

namespace Submission.CField.LRecip

open Submission.CField.LFTheory
open Submission.CField.LBrauer
open scoped IsMulCommutative

noncomputable section

/-- The largest abelian intermediate field of a finite Galois extension. -/
def maximalAbelianIntermediate (K L : Type*)
    [Field K] [Field L] [Algebra K L] : IntermediateField K L :=
  IntermediateField.fixedField (commutator Gal(L/K))

section GaloisCorrespondence

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The fixed field of the commutator is Galois over the base field. -/
instance maximal_abelian_galois :
    IsGalois K (maximalAbelianIntermediate K L) :=
  IsGalois.of_fixedField_normal_subgroup (commutator Gal(L/K))

/-- Its Galois group is the abelianization of the original Galois group. -/
noncomputable def maximalAbelianGalois :
    Abelianization Gal(L/K) ≃*
      Gal(maximalAbelianIntermediate K L/K) :=
  IsGalois.normalAutEquivQuotient (commutator Gal(L/K))

/-- In particular, the fixed field of the commutator is abelian over `K`. -/
instance maximal_abelian_commutative :
    IsMulCommutative Gal(maximalAbelianIntermediate K L/K) := by
  let e := maximalAbelianGalois K L
  refine ⟨⟨fun σ τ => ?_⟩⟩
  apply e.symm.injective
  simpa only [map_mul] using mul_comm (e.symm σ) (e.symm τ)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Every abelian Galois intermediate extension is contained in the fixed
field of the commutator.  This is the precise maximality assertion in
Milne's formulation. -/
theorem maximal_abelian_field
    (F : IntermediateField K L) [IsGalois K F]
    [IsMulCommutative Gal(F/K)] :
    F ≤ maximalAbelianIntermediate K L := by
  rw [maximalAbelianIntermediate, IntermediateField.le_iff_le]
  let r : Gal(L/K) →* Gal(F/K) :=
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F
  have hcomm : commutator Gal(L/K) ≤ r.ker :=
    Abelianization.commutator_subset_ker r
  change commutator Gal(L/K) ≤ F.fixingSubgroup
  rw [← IntermediateField.restrictNormalHom_ker F]
  simpa only [r] using hcomm

end GaloisCorrespondence

section LFields

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance maximalAbelianIntermediateFieldValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance maximalAbelianIntermediateFieldValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Theorem III.3.1 computes the index of a finite local norm subgroup as
the order of the abelianized Galois group. -/
theorem nat_card_abelianization :
    (normSubgroup K L).index = Nat.card (Abelianization Gal(L/K)) := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (localResidueEquiv K L).symm.toEquiv

/-- **Theorem III.3.5, Galois case (Norm Limitation).**  A finite Galois
extension and its largest abelian intermediate extension have the same norm
subgroup in the base field. -/
theorem abelian_intermediate_field :
    normSubgroup K L =
      normSubgroup K (maximalAbelianIntermediate K L) := by
  let E := maximalAbelianIntermediate K L
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  let hcontain : normSubgroup K L ≤ normSubgroup K E :=
    norm_subgroup_tower K L E
  letI : Finite (Kˣ ⧸ normSubgroup K L) :=
    Finite.of_injective (localArtinEquiv K L)
      (localArtinEquiv K L).injective
  letI : (normSubgroup K L).FiniteIndex := by
    apply Subgroup.finiteIndex_of_finite_quotient
  apply subgroups_equal_containment
    (normSubgroup K L) (normSubgroup K E) hcontain
  calc
    (normSubgroup K L).index =
        Nat.card (Abelianization Gal(L/K)) :=
      nat_card_abelianization K L
    _ = Nat.card Gal(E/K) :=
      Nat.card_congr (maximalAbelianGalois K L).toEquiv
    _ = Nat.card (Abelianization Gal(E/K)) :=
      Nat.card_congr (Abelianization.equivOfComm (H := Gal(E/K))).toEquiv
    _ = (normSubgroup K E).index :=
      (nat_card_abelianization K E).symm

end LFields

end

end Submission.CField.LRecip
