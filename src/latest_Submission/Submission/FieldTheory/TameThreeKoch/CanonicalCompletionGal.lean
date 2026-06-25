import Submission.FieldTheory.TameThreeKoch.LocalObstructionsStatement


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

noncomputable abbrev placeCanonicalGal
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val) :=
  let v := (FinitePlace.mk P).val
  letI : Algebra v.Completion w.1.Completion :=
    (Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  Gal(w.1.Completion/v.Completion)

end TBluepr
end Submission
