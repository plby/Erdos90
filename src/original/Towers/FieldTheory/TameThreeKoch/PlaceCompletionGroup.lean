import Towers.FieldTheory.TameThreeKoch.CompletionKernelUnits


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

noncomputable def placeCompletionGroup
    {G : Type w} [Group G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
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
    (galoisEquiv : Gal(L/K) ≃* G) :
    placeCanonicalGal P w →* G :=
  let v := (FinitePlace.mk P).val
  let hvna : IsNonarchimedean v :=
    fun x y ↦ (FinitePlace.mk P).add_le x y
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  completionDecomposition v hvna w galoisEquiv

end TBluepr
end Towers
