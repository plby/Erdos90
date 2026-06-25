import Submission.ClassField.Reciprocity.ArtinMapStatements

/-!
# Chapter VII, Theorem 9.5: existence statement
-/

namespace Submission.CField.NLimita

open NumberField
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.Recip

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- A subgroup of the idele class group is a norm group if it is the image
of the idele-class norm from a finite abelian subextension. -/
def IdeleNormGroup
    (U : Subgroup (IdeleClassGroup (RingOfIntegers K) K)) : Prop :=
  ∃ L : FASubext K, ideleClassSubgroup L = U

/-- **Theorem VII.9.5, corrected statement.** Every open finite-index subgroup
of the idele class group is a norm group.  Although the displayed statement
in the source omits `open`, its proof uses openness through Lemmas 9.3 and 9.4,
and the solution to Exercise A-4 gives nonopen finite-index subgroups. -/
def EveryIndexGroup : Prop :=
  ∀ U : Subgroup (IdeleClassGroup (RingOfIntegers K) K),
    IsOpen (U : Set (IdeleClassGroup (RingOfIntegers K) K)) →
      U.FiniteIndex → IdeleNormGroup K U

/-- **V.5.5 implies VII.9.5.**  The idelic existence theorem gives a unique
finite abelian extension with prescribed open finite-index norm subgroup;
Theorem VII.9.5 only asks for existence. -/
theorem existence_theorem_implies
    (h : IdeleExistenceTheorem (K := K)) :
    EveryIndexGroup K := by
  intro U hopen hfinite
  rcases h U hopen hfinite with ⟨L, hL, _⟩
  exact ⟨L, hL⟩

/-- Conversely, VII.9.5 proves V.5.5 once class fields are known to be
determined by their idele-class norm subgroups.  This isolates the uniqueness
input in the passage from the existence theorem of Chapter VII to the
existence theorem of Chapter V. -/
theorem implies_global_existence
    (h95 : EveryIndexGroup K)
    (hinjective : Function.Injective
      (ideleClassSubgroup (K := K))) :
    IdeleExistenceTheorem (K := K) := by
  intro U hopen hfinite
  rcases h95 U hopen hfinite with ⟨L, hL⟩
  refine ⟨L, hL, ?_⟩
  intro M hM
  exact hinjective (hM.trans hL.symm)

end Submission.CField.NLimita
