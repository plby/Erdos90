import Submission.ClassField.LocalClass.CardinalityCanonicalSplitting
import Submission.ClassField.LocalClass.FiniteGaloisExtensions

/-!
# Milne, Class Field Theory, Lemma III.2.2

For a finite Galois extension `L/K` of degree `n`, degree-two cohomology
contains the canonical cyclic subgroup of order `n`.  We represent
`(1/n) ℤ / ℤ` by `ZMod n`; the embedding is the inverse of the finite
local invariant coordinate constructed from the canonical Brauer class.
-/

namespace Submission.CField.LClass

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance localUnitsRepSourceValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance localUnitsRepSourceValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

private abbrev localUnitsRep :=
  Rep.ofMulDistribMulAction Gal(L/K) Lˣ

/-- The canonical inclusion `(1/n) ℤ / ℤ → H²(L/K)`, with the
source written as `ZMod n`. -/
noncomputable def canonicalEmbedding :
    ZMod (Module.finrank K L) →+
      groupCohomology.H2 (localUnitsRep K L) :=
  (cohomology_units_z
    K L (brauer_relative_galois K L)).symm.toAddMonoidHom

/-- The canonical cyclic subgroup singled out in Lemma III.2.2. -/
noncomputable def canonicalSubgroup :
    AddSubgroup (groupCohomology.H2 (localUnitsRep K L)) :=
  (canonicalEmbedding K L).range

/-- The canonical map of Lemma III.2.2 is injective. -/
theorem canonicalEmbedding_injective :
    Function.Injective (canonicalEmbedding K L) :=
  (cohomology_units_z
    K L (brauer_relative_galois K L)).symm.injective

/-- **Lemma III.2.2.** The displayed subgroup is canonically isomorphic to
`(1/n) ℤ / ℤ`, represented by `ZMod n`. -/
noncomputable def canonicalSubgroupEquiv :
    ZMod (Module.finrank K L) ≃+ canonicalSubgroup K L := by
  let f := canonicalEmbedding K L
  exact AddEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h ↦ canonicalEmbedding_injective K L
        (congrArg Subtype.val h),
      f.rangeRestrict_surjective⟩

end

end Submission.CField.LClass
