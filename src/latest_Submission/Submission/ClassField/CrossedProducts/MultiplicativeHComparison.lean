import Submission.ClassField.CrossedProducts.CohomologyRestriction
import Submission.ClassField.CrossedProducts.Multiplicative2Comparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Naturality of the degree-two cohomology comparison

The equivalence between normalized multiplicative `H²` and categorical
group cohomology commutes with restriction along a homomorphism when the two
coefficient actions agree.
-/

namespace Submission.CField.CProduca

open CategoryTheory groupCohomology

noncomputable section

variable {G H M : Type}
  [Group G] [Group H] [CommGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction H M]

/-- The identity on additive coefficient groups as a morphism from the
restricted `G`-representation to the compatible `H`-representation. -/
def multiplicativeRestrictionRep
    (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m) :
    Rep.res f (Rep.ofMulDistribMulAction G M) ⟶
      Rep.ofMulDistribMulAction H M :=
  Rep.ofHom ⟨LinearMap.id, fun h ↦ LinearMap.ext fun m ↦ by
    exact congrArg Additive.ofMul (hsmul h m.toMul).symm⟩

/-- Additive categorical `H²` restriction for compatible multiplicative
actions. -/
noncomputable def additive2Restriction
    (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m) :
    groupCohomology.H2 (Rep.ofMulDistribMulAction G M) →+
      groupCohomology.H2 (Rep.ofMulDistribMulAction H M) :=
  (groupCohomology.map f
    (multiplicativeRestrictionRep f hsmul) 2).hom

/-- The multiplicative/additive `H²` comparison commutes with
restriction. -/
theorem multiplicative_2_restriction
    (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    (x : MHTwo G M) :
    multiplicative2Additive
        (MHTwo.restrictionHom f hsmul x) =
      additive2Restriction f hsmul
        (multiplicative2Additive x) := by
  induction x using Quotient.inductionOn with
  | _ c =>
      change H2π (Rep.ofMulDistribMulAction H M) _ =
        groupCohomology.map f
          (multiplicativeRestrictionRep f hsmul) 2
          (H2π (Rep.ofMulDistribMulAction G M) _)
      rw [groupCohomology.H2π_comp_map_apply]
      congr 1

/-- Equivalence-level naturality of the canonical `H²` comparison. -/
theorem multiplicative_h_restriction
    (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    (x : MHTwo G M) :
    multiplicativeHCohomology
        (MHTwo.restrictionHom f hsmul x) =
      Multiplicative.ofAdd
        (additive2Restriction f hsmul
          (multiplicativeHCohomology x).toAdd) := by
  apply Multiplicative.toAdd.injective
  exact multiplicative_2_restriction f hsmul x

end

end Submission.CField.CProduca
