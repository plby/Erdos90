import Towers.ClassField.HasseNorm.ULiftShapiro
import Towers.ClassField.HasseNorm.LocalStabilizerComparison
import Towers.ClassField.IdeleCohomology.ConcreteIdeleAction
import Mathlib.Algebra.DirectSum.Module

/-!
# The resized idèle representation and its local degree-two target

This file puts the concrete Chapter VII Galois action on the actual idèle
group in the universe used by the Hasse norm argument.  It also constructs,
for a simultaneous choice of completions, the direct sum of the local
completion-product `H²` groups and identifies that direct sum with the direct
sum of the corresponding place-stabilizer `H²` groups by Shapiro.

The remaining arithmetic statement of Proposition VII.2.5(b) is isolated as
the type `ResizedIdeleDecomposition`: it is an actual
additive equivalence from the cohomology of the concrete restricted idèle
representation, rather than a proposition-valued wrapper.
-/

namespace Towers.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The actual idèle representation, with its coefficient ring resized from
`Z` to `ULift Z`.  Its carrier is still the concrete restricted idèle group
of `L`, and its action is the coordinatewise Galois action constructed in
Chapter VII. -/
noncomputable def resizedConcreteRepresentation (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Rep (ULift.{u} ℤ) Gal(L/K) :=
  uliftIntegralRepresentation
    ((concreteActionData (K := K) (L := L)).representation)

/-- The normalized absolute value represented by a finite or infinite
number-field place. -/
def hasseAbsoluteValue (v : NumberFieldPlace K) :
    AbsoluteValue K ℝ :=
  match v with
  | .inl P => (FinitePlace.mk P).val
  | .inr v => v.1

/-- Convert the completion choices already used by the Hasse norm statement
to absolute-value extensions.  At a finite place this chooses the normalized
extension centered at the prescribed upper prime; at an infinite place the
chosen infinite place already has the required normalized restriction. -/
noncomputable def hasseChosenPlace
    (completion : HasseCompletionData K L) :
    (v : NumberFieldPlace K) →
      CompletionPlacesAbove (L := L) (hasseAbsoluteValue v)
  | .inl P =>
      (hasseCompletionModel K L P (completion.finiteUpper P)).place
  | .inr v =>
      let w := completion.infiniteUpper v
      ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩

/-- The resized product of all completed multiplicative groups above one
base-field place. -/
noncomputable def resizedPlaceRepresentation
    (v : NumberFieldPlace K) : Rep (ULift.{u} ℤ) Gal(L/K) :=
  uliftUnitsRepresentation
    (K := K) (L := L) (hasseAbsoluteValue v)

/-- The resized multiplicative group of the chosen completion, acted on by
its decomposition group inside `Gal(L/K)`. -/
noncomputable def chosenUnitsRepresentation
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    Rep (ULift.{u} ℤ)
      (CompletionPlaceStabilizer (hasseAbsoluteValue v)
        (hasseChosenPlace completion v)) :=
  uliftPlaceRepresentation
    (K := K) (L := L) (hasseAbsoluteValue v)
      (hasseChosenPlace completion v)

/-- The two universe-resized presentations of the chosen completed unit
group agree.  The left side is obtained by functorially resizing the Chapter
VII integral representation; the right side is the representation used by
the literal local norm-quotient comparison. -/
noncomputable def uliftIsoHasse
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :
    uliftPlaceRepresentation (K := K) (L := L) v w ≅
      hasseUnitsRepresentation v w := by
  apply Rep.mkIso
  refine
    { toLinearEquiv := LinearEquiv.refl (ULift.{u} ℤ) (Additive w.1.Completionˣ)
      isIntertwining' := ?_ }
  intro sigma
  rfl

/-- Degree-two cohomology is unchanged between the functorially resized and
the direct multiplicative presentations of the chosen completed units. -/
noncomputable def uliftHasseNorm
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :
    H2 (uliftPlaceRepresentation (K := K) (L := L) v w) ≃+
      H2 (hasseUnitsRepresentation v w) :=
  ((groupCohomology.functor (ULift.{u} ℤ)
      (CompletionPlaceStabilizer v w) 2).mapIso
    (uliftIsoHasse
      (K := K) (L := L) v w)).toLinearEquiv.toAddEquiv

/-- Shapiro in degree two at an arbitrary number-field place, using the
completion selected by the Hasse norm data.  Transitivity is supplied
arithmetically in both the finite and infinite cases. -/
noncomputable def resizedPlaceStabilizer
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    H2 (resizedPlaceRepresentation (K := K) (L := L) v) ≃+
      H2 (chosenUnitsRepresentation
        (K := K) (L := L) completion v) := by
  cases v with
  | inl P =>
      exact uliftUnitsH
        (K := K) (L := L) P
          (hasseChosenPlace completion (.inl P))
  | inr v =>
      exact uliftInfiniteUnits
        (K := K) (L := L) v
          (hasseChosenPlace completion (.inr v))

/-- Assemble the placewise Shapiro equivalences over every base-field place.
This is the complete local-to-stabilizer half of Proposition VII.2.5(b). -/
noncomputable def resizedDirectStabilizer
    (completion : HasseCompletionData K L) :
    DirectSum (NumberFieldPlace K)
        (fun v => H2 (resizedPlaceRepresentation
          (K := K) (L := L) v)) ≃+
      DirectSum (NumberFieldPlace K)
        (fun v => H2 (chosenUnitsRepresentation
          (K := K) (L := L) completion v)) :=
  DirectSum.congrAddEquiv fun v =>
    resizedPlaceStabilizer
      (K := K) (L := L) completion v

/-- The literal local norm quotient at any base place is the degree-two
cohomology of the functorially resized chosen-completion representation. -/
noncomputable def hasseResizedChosen
    (hcyclic : IsCyclic Gal(L/K))
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    Additive (HasseLocalQuotient completion v) ≃+
      H2 (chosenUnitsRepresentation
        (K := K) (L := L) completion v) := by
  cases v with
  | inl P =>
      exact (hasseStabilizer2
        (K := K) (L := L) hcyclic completion P).trans
          (uliftHasseNorm
            (K := K) (L := L) (FinitePlace.mk P).val
              (hasseChosenPlace completion (.inl P))).symm
  | inr v =>
      exact (infiniteHasseStabilizer
        (K := K) (L := L) hcyclic completion v).trans
          (uliftHasseNorm
            (K := K) (L := L) v.1
              (hasseChosenPlace completion (.inr v))).symm

/-- Assemble the literal local norm-quotient comparisons over all places. -/
noncomputable def hasseDirectChosen
    (hcyclic : IsCyclic Gal(L/K))
    (completion : HasseCompletionData K L) :
    DirectSum (NumberFieldPlace K)
        (fun v => Additive (HasseLocalQuotient completion v)) ≃+
      DirectSum (NumberFieldPlace K)
        (fun v => H2 (chosenUnitsRepresentation
          (K := K) (L := L) completion v)) :=
  DirectSum.congrAddEquiv fun v =>
    hasseResizedChosen
      (K := K) (L := L) hcyclic completion v

/-- The exact positive-degree restricted-idèle decomposition still required
from Proposition VII.2.5(b), specialized to the resized concrete idèle
representation and degree two.  A term of this type is the genuinely missing
equivalence; no additional arithmetic hypothesis occurs in its statement. -/
abbrev ResizedIdeleDecomposition (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  H2 (resizedConcreteRepresentation K L) ≃+
    DirectSum (NumberFieldPlace K)
      (fun v => H2 (resizedPlaceRepresentation
        (K := K) (L := L) v))

/-- The corresponding exact target after choosing one completion above each
place. -/
abbrev ResizedStabilizerDecomposition
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (completion : HasseCompletionData K L) :=
  H2 (resizedConcreteRepresentation K L) ≃+
    DirectSum (NumberFieldPlace K)
      (fun v => H2 (chosenUnitsRepresentation
        (K := K) (L := L) completion v))

/-- Once the restricted-product half of Proposition VII.2.5(b) is supplied,
all Shapiro identifications assemble to the stabilizer form needed by the
Hasse norm comparison. -/
noncomputable def resizedStabilizerDecomposition
    (completion : HasseCompletionData K L)
    (e : ResizedIdeleDecomposition K L) :
    ResizedStabilizerDecomposition K L completion :=
  e.trans
    (resizedDirectStabilizer
      (K := K) (L := L) completion)

/-- The exact local comparison required in the Hasse norm short exact
sequence, obtained from the restricted-product decomposition.  All local
cyclic-periodicity and Shapiro transports are already discharged here. -/
noncomputable def resizedIdeleDecomposition
    (hcyclic : IsCyclic Gal(L/K))
    (completion : HasseCompletionData K L)
    (e : ResizedIdeleDecomposition K L) :
    H2 (resizedConcreteRepresentation K L) ≃+
      DirectSum (NumberFieldPlace K)
        (fun v => Additive (HasseLocalQuotient completion v)) :=
  (resizedStabilizerDecomposition
      (K := K) (L := L) completion e).trans
    (hasseDirectChosen
      (K := K) (L := L) hcyclic completion).symm

end

end Towers.CField.HNorm
