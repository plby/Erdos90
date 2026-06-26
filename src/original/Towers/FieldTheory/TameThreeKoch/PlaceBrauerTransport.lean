import Towers.FieldTheory.TameThreeKoch.PullbackVanishes


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

universe u v w

open NumberField
open Towers.CField.Ideles
open Towers.CField.LBrauer

attribute [local instance]
  part2FiniteGaloisIntermediateFieldFiniteDimensional
  part2FiniteGaloisIntermediateFieldIsGalois
  part2AlgebraicClosureAlgebraic
  part2AlgebraicClosureNormal
  algebraicClosureIsGalois

set_option synthInstance.maxHeartbeats 1000000 in
-- The completion and adic algebra structures require a broad instance search.
set_option maxHeartbeats 8000000 in
-- This transport is isolated so it has a fresh heartbeat budget after the local construction.
theorem change_pullback_obstruction
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
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)
    [Finite
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    [Nonempty
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    (hlocalPull : PullbackObstructionVanishes
      q hq hcentral galoisEquiv kernelToUnits hfixed P w) :
    @Towers.CField.BGroups.brauerBaseChange
        K (P.adicCompletion K) inferInstance inferInstance
        (FinitePlace.embedding P).toAlgebra
        (extensionRelativeBrauer q hq hcentral galoisEquiv
          kernelToUnits hfixed : BrauerGroup K) = 1 := by
  let v := (FinitePlace.mk P).val
  let f := placeCompletionGroup P w galoisEquiv
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  have hvna : IsNonarchimedean v :=
    fun x y ↦ (FinitePlace.mk P).add_le x y
  let hfixedLocal :=
    completion_units_fixed v hvna w kernelToUnits hfixed
  have hv :
      letI : Algebra K v.Completion :=
        Towers.NumberTheory.Milne.completionBaseAlgebra v
      Towers.CField.BGroups.brauerBaseChange K v.Completion
          (extensionRelativeBrauer q hq hcentral galoisEquiv
            kernelToUnits hfixed : BrauerGroup K) = 1 := by
    letI : CommGroup q.ker := centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction (placeCanonicalGal P w) q.ker :=
      trivialDistribAction (placeCanonicalGal P w) q.ker
    apply brauer_change_obstruction
      q hq hcentral galoisEquiv kernelToUnits hfixed v hvna w
    change
      Towers.CField.CProduca.MHTwo.mapCoefficientsHom
          (completionKernelUnits v w kernelToUnits)
          (fun sigma z ↦ (hfixedLocal sigma z).symm)
          (Towers.CField.CProduca.MHTwo.restrictionHom
            f (fun _ _ ↦ rfl)
            (extensionObstructionClass q hq hcentral)) = 1
    rw [← central_extension_pullback
      q hq hcentral f (completionKernelUnits v w kernelToUnits) hfixedLocal]
    exact hlocalPull
  letI : Algebra K v.Completion :=
    Towers.NumberTheory.Milne.completionBaseAlgebra v
  letI : Algebra K (P.adicCompletion K) :=
    (FinitePlace.embedding P).toAlgebra
  apply brauer_change_ring K v.Completion
    (P.adicCompletion K)
    (Towers.CField.Ideles.placeCompletionAdic P) ?_
    (extensionRelativeBrauer q hq hcentral galoisEquiv
      kernelToUnits hfixed) hv
  ext x
  exact finite_place_adic P x

end TBluepr
end Towers
