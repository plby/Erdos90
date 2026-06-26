import Submission.ClassField.NormCorrespondence.LocalStatements
import Submission.ClassField.Ideles.IdeleNorm
import Submission.ClassField.GrunwaldWang.GrunwaldWangStatement

/-!
# Chapter VIII, Theorem 2.3: simultaneous local existence
-/

namespace Submission.CField.GWang

open IsDedekindDomain NumberField
open Submission.CField.LFTheory
open Submission.CField.Ideles

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- A finite abelian global extension realizes a prescribed local norm
subgroup when the norm from one completion above the place has exactly that
range.  Local class field theory identifies this condition with realizing the
local extension corresponding to the subgroup. -/
def RealizesLocalSubgroup
    (L : FASubext K) (v : Place K)
    (N : Subgroup (LocalMultiplicativeGroup K v)) : Prop := by
  letI : NumberField L.1 := NumberField.of_module_finite K L.1
  cases v with
  | inl P =>
      exact ∃ Q : UpperPrimeFactors (K := K) (L := L.1) P,
        (finiteCompletionNorm (K := K) (L := L.1) P Q).range = N
  | inr v =>
      exact ∃ w : InfinitePlacesAbove (K := K) (L := L.1) v,
        (infiniteCompletionNorm (K := K) (L := L.1) v w).range = N

/-- **Theorem VIII.2.3, statement.** Finitely many open finite-index local
norm subgroups can be realized simultaneously by a finite abelian extension
of the number field. -/
def SimultaneousExistenceTheorem : Prop :=
  ∀ (S : Finset (Place K))
      (N : ∀ v : S, Subgroup (LocalMultiplicativeGroup K v.1)),
    (∀ v : S, OFSubgro (N v)) →
      ∃ L : FASubext K,
        ∀ v : S, RealizesLocalSubgroup K L v.1 (N v)

end

end Submission.CField.GWang
