import Submission.FieldTheory.TameThreeKoch.CanonicalCompletionGal


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

noncomputable def placeCompletionUnits
    {C : Type v} {K L : Type u} [Group C]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)
    (kernelToUnits : C →* Lˣ) : C →* w.1.Completionˣ :=
  let v := (FinitePlace.mk P).val
  letI : Algebra v.Completion w.1.Completion :=
    (Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  completionKernelUnits v w kernelToUnits

end TBluepr
end Submission
