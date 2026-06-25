import Submission.ClassField.HasseNorm.ResizedIdeleSequence

/-!
# Idèle-class degree-one vanishing in the resized sequence

Theorem VII.5.1 is stated using the idèle-class representation whose
coefficient ring already lives in the number fields' universe.  The Hasse
norm argument uses the functorially resized integral representation instead.
This file transports the unconditional degree-one vanishing clause of
Theorem VII.5.1 across the explicit representation isomorphism.
-/

namespace Submission.CField.HNorm

open CategoryTheory CategoryTheory.Limits Representation
open IsDedekindDomain NumberField
open Submission.CField.CIdeles
open groupCohomology

noncomputable section

universe u

/-- The degree-one idèle-class vanishing of Theorem VII.5.1, transported to
the third term of the resized idèle-class sequence.  No cyclicity hypothesis
is used: Theorem VII.5.1 holds for every finite Galois extension. -/
theorem resized_h_1
    (h51 : IdeleCohomologyClaims.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsZero (H1 (resizedIdeleRepresentation K L)) := by
  have hzero : IsZero
      (H1 (ideleCohomologyRepresentation K L)) :=
    (h51 K L).2.1
  exact IsZero.of_iso hzero
    (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 1).mapIso
      (resizedIdeleIso K L)).symm)

/-- The same vanishing, in the exact shape required by the cohomological
data for the Hasse norm theorem. -/
theorem short_complex_3
    (h51 : IdeleCohomologyClaims.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsZero (H1 (resizedShortComplex K L).X₃) :=
  resized_h_1 h51 K L

end

end Submission.CField.HNorm
