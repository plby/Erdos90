import Towers.FieldTheory.TameThreeKoch.PrimitiveRootObstruction


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
-- Transporting the isolated local obstruction to the adic completion unfolds
-- the canonical completion algebra structures and the relative Brauer class.
set_option maxHeartbeats 8000000 in
theorem change_tame_primitive
    {Q : Type v} {G : Type v} [Group Q] [Finite Q]
    [Group G] [Finite G]
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
    (I : Subgroup (placeCanonicalGal P w))
    [I.Normal]
    (n : ℕ) [NeZero n]
    (data : TamePrimitiveData
      q galoisEquiv kernelToUnits P w I n) :
    @Towers.CField.BGroups.brauerBaseChange
        K (P.adicCompletion K) inferInstance inferInstance
        (FinitePlace.embedding P).toAlgebra
        (extensionRelativeBrauer q hq hcentral galoisEquiv
          kernelToUnits hfixed : BrauerGroup K) = 1 := by
  apply change_pullback_obstruction
    q hq hcentral galoisEquiv kernelToUnits hfixed P w
  exact pullback_obstruction_primitive
    q hq hcentral galoisEquiv kernelToUnits hfixed P w I n data

end TBluepr
end Towers
