import Towers.ClassField.ReciprocityExistence.Realization

/-!
# Chapter VII, Section 8, Lemma 8.6

Proposition 7.2 realizes every absolute Brauer class as a class split by a
cyclic cyclotomic finite subextension.  Consequently the invariant-sum
formula for those subextensions implies the formula for every absolute
class, and hence for every relative class in every finite Galois extension.
-/

namespace Towers.CField.RExist

open NumberField
open Towers.CField.LFTheory
open Towers.CField.BGroups
open Towers.CField.CBrauer

noncomputable section

universe u

/-- The absolute form of Lemma VII.8.6.  The only hypothesis is precisely
the one in the printed lemma: invariant-sum reciprocity for cyclic
cyclotomic extensions. -/
theorem absolute_invariant_cyclotomic
    (K : Type u) [Field K] [NumberField K]
    (data : BData K)
    (hcyclic : ∀ E : FASubext K,
      CyclicCyclotomicSubextension K E →
        InvariantSumReciprocity K data E.1) :
    ∀ beta : BrauerGroup.{u, u} K,
      (BData.sumInvariant K data)
        (data.localization.localization (Additive.ofMul beta)) = 0 := by
  intro beta
  obtain ⟨E, hE, hsplit⟩ :=
    realization K beta
      (placeAlgStatement K beta)
  let betaE : relativeBrauerGroup K E.1 :=
    ⟨beta, (relative_brauer_group K E.1 beta).2 hsplit⟩
  exact hcyclic E hE betaE

/-- **Lemma VII.8.6.**  Recip for cyclic cyclotomic extensions implies
invariant-sum reciprocity for every finite Galois extension. -/
theorem invariantSumReciprocity
    (K : Type u) [Field K] [NumberField K]
    (data : BData K)
    (hcyclic : ∀ E : FASubext K,
      CyclicCyclotomicSubextension K E →
        InvariantSumReciprocity K data E.1)
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    InvariantSumReciprocity K data L := by
  intro beta
  exact absolute_invariant_cyclotomic K data hcyclic beta.1

end

end Towers.CField.RExist
