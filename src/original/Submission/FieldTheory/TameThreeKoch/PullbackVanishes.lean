import Submission.FieldTheory.TameThreeKoch.PlaceCompletionGroup

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

universe u v w

open NumberField
open Submission.CField.Ideles
open Submission.CField.LBrauer

attribute [local instance]
  part2FiniteGaloisIntermediateFieldFiniteDimensional
  part2FiniteGaloisIntermediateFieldIsGalois
  part2AlgebraicClosureAlgebraic
  part2AlgebraicClosureNormal
  algebraicClosureIsGalois

set_option synthInstance.maxHeartbeats 1000000 in
-- The proposition installs the canonical completion actions on the pullback kernel.
set_option maxHeartbeats 8000000 in
-- Packaging this equality avoids repeated normalization at lemma boundaries.
def PullbackObstructionVanishes
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    [Fact (FinitePlace.mk P).val.IsNontrivial]
    [IsUltrametricDist (FinitePlace.mk P).val.Completion]
    (w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)
    [Finite
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    [Nonempty
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    [MulAction.IsPretransitive Gal(L/K)
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)] : Prop :=
  let v := (FinitePlace.mk P).val
  let f := placeCompletionGroup P w galoisEquiv
  letI : Algebra v.Completion w.1.Completion :=
    (Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionGalois v w
  let p := extensionPullbackProjection q f
  let hp : Function.Surjective p :=
    central_pullback_projection q hq f
  let hpc : p.ker ≤ Subgroup.center (CentralExtensionPullback q f) :=
    extension_pullback_projection q f hcentral
  let e := centralExtensionPullback q f
  let phiLocal := placeCompletionUnits P w kernelToUnits
  let phiPull := phiLocal.comp e.toMonoidHom
  let hfixedPull := fun sigma z ↦
    completion_units_fixed v
      (fun x y ↦ (FinitePlace.mk P).add_le x y)
      w kernelToUnits hfixed sigma (e z)
  letI : CommGroup p.ker := centralExtensionComm p hpc
  letI : MulDistribMulAction (placeCanonicalGal P w) p.ker :=
    trivialDistribAction (placeCanonicalGal P w) p.ker
  Submission.CField.CProduca.MHTwo.mapCoefficientsHom
      phiPull (fun sigma z ↦ (hfixedPull sigma z).symm)
      (extensionObstructionClass p hp hpc) = 1

end TBluepr
end Submission
