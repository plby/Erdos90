import Submission.ClassField.HasseNorm.LiftedH2
import Submission.ClassField.CrossedProducts.CohomologyRestriction
import Submission.FieldTheory.CentralFactorSet

/-!
# Restriction and coefficient naturality for resized multiplicative H²

This is the universe-polymorphic categorical form of the elementary
operation on normalized multiplicative cocycles: restrict the acting group
and then apply an equivariant homomorphism to the coefficients.
-/

namespace Submission.CField.RExist

open CategoryTheory Rep groupCohomology
open Submission.CField.CProduca
open Submission.CField.HNorm

noncomputable section

universe u

variable {G H M N : Type u}
  [Group G] [Group H] [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction H M]
  [MulDistribMulAction H N]

/-- Linearize a coefficient homomorphism after restricting the acting group.
The source `H`-action on `M` is allowed to be propositionally, rather than
definitionally, the restriction of the `G`-action. -/
noncomputable def uliftRestrictionHom
    (r : H →* G) (hM : ∀ h : H, ∀ m : M, h • m = r h • m)
    (f : M →* N) (hf : ∀ h : H, ∀ m : M, f (h • m) = h • f m) :
    Rep.res r (uliftMulRepresentation (G := G) (M := M)) ⟶
      uliftMulRepresentation (G := H) (M := N) := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x =>
            Additive.ofMul (f (show Additive M from x).toMul)
          map_add' := fun x y =>
            congrArg Additive.ofMul (map_mul f
              (show Additive M from x).toMul
              (show Additive M from y).toMul)
          map_smul' := fun a x => by
            change Additive.ofMul
                (f ((show Additive M from x).toMul ^ a.down)) =
              Additive.ofMul
                ((f (show Additive M from x).toMul) ^ a.down)
            exact congrArg Additive.ofMul
              (map_zpow f (show Additive M from x).toMul a.down) }
      isIntertwining' := fun h => by
        ext x
        change Additive.ofMul
            (f (r h • (show Additive M from x).toMul)) =
          Additive.ofMul
            (h • f (show Additive M from x).toMul)
        rw [← hM h (show Additive M from x).toMul,
          hf h (show Additive M from x).toMul] }

/-- The resized categorical realization of multiplicative `H²` commutes
with restriction followed by an equivariant coefficient map. -/
theorem multiplicative_additive_coefficients
    (r : H →* G) (hM : ∀ h : H, ∀ m : M, h • m = r h • m)
    (f : M →* N) (hf : ∀ h : H, ∀ m : M, f (h • m) = h • f m)
    (x : MHTwo G M) :
    groupCohomology.map r
        (uliftRestrictionHom r hM f hf) 2
        (multiplicativeLiftAdditive x) =
      multiplicativeLiftAdditive
        (MHTwo.mapCoefficientsHom f hf
          (MHTwo.restrictionHom r hM x)) := by
  obtain ⟨c, rfl⟩ := MHTwo.exists_mk_eq x
  rw [MHTwo.restrictionHom_mk,
    MHTwo.coefficients_hom_mk,
    multiplicative_additive_mk,
    multiplicative_additive_mk,
    normalizedCocycleU,
    normalizedCocycleU,
    H2π_comp_map_apply]
  congr 1

end

end Submission.CField.RExist
