import Submission.Group.Zassenhaus.FrontierRecollection

/-!
# Order-preserving recollection of classified transient packets

The classified inner-reduction packet deliberately keeps attached and
excess-left terms interleaved in their original Hall-Petresco order.  This
file recollects that mixed packet without commuting any terms past one
another:

* balanced terms attach directly to ordinary symbolic factors and truncate;
* excess-left terms delegate to the transient singleton factory.

The resulting ordinary source evaluates exactly to `[inner ^ e, right]` and
is physically supported at the original outer-bracket weight.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open HACoeff

/--
An ordered attached-or-frontier packet recollected into ordinary bounded
symbolic factors at a requested physical support bound.
-/
structure TTRecol
    {d inputWeight : ℕ}
    (n lowerWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (rawSource :
      List (SOTerm H inputWeight)) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_weight_least :
    SPFactora.WordWeightLeast lowerWeight higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SOTerm.listValue (n := n) q rawSource

namespace TTRecol

/-- The empty mixed source recollects to the empty ordinary source. -/
def empty
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    TTRecol
      n lowerWeight H
        ([] : List (SOTerm H inputWeight)) where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro q
    rfl

/-- Concatenate independently recollected mixed sources. -/
def append
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {leftSource rightSource :
      List (SOTerm H inputWeight)}
    (left :
      TTRecol
        n lowerWeight H leftSource)
    (right :
      TTRecol
        n lowerWeight H rightSource) :
    TTRecol
      n lowerWeight H (leftSource ++ rightSource) where
  higherSource := left.higherSource ++ right.higherSource
  higher_source_truncated := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_source_truncated factor hfactor
    · exact right.higher_source_truncated factor hfactor
  higher_weight_least := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_weight_least factor hfactor
    · exact right.higher_weight_least factor hfactor
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append,
      left.list_higher_raw,
      right.list_higher_raw]
    simp [SOTerm.listValue]

/-- Compose singleton mixed-term recollections in their original order. -/
def of_singletons
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (rawSource :
      List (SOTerm H inputWeight))
    (recollection :
      ∀ term ∈ rawSource,
        TTRecol
          n lowerWeight H [term]) :
    TTRecol
      n lowerWeight H rawSource := by
  induction rawSource with
  | nil =>
      exact empty
  | cons head tail ih =>
      simpa using
        (append
          (recollection head (by simp))
          (ih fun term hterm => recollection term (by simp [hterm])))

/-- Attach and truncate one balanced ordinary word expansion. -/
noncomputable def singleton_attached
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : SWExp H inputWeight)
    (hweight :
      lowerWeight ≤
        wordExpansion.word.weight PEAddres.weight) :
    TTRecol
      n lowerWeight H [.attached wordExpansion] where
  higherSource :=
    SPFactora.truncate n wordExpansion.factors
  higher_source_truncated :=
    SPFactora.isTruncated_truncate wordExpansion.factors
  higher_weight_least :=
    SPFactora.word_least_truncate fun factor hfactor => by
      rw [wordExpansion.of_mem_factors hfactor]
      exact hweight
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_truncate,
      wordExpansion.listEval_factors]
    simp [SOTerm.listValue,
      SOTerm.value]

/-- Reuse a transient singleton recollection for one frontier term. -/
noncomputable def singleton_frontier
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (recollection :
      TTRecola
        n lowerWeight H [wordExpansion]) :
    TTRecol
      n lowerWeight H [.frontier wordExpansion] where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := by
    intro q
    rw [recollection.list_higher_raw]
    simp [TWExp.listValue,
      SOTerm.listValue,
      SOTerm.value]

end TTRecol

namespace PTSubsti

/-- Every transient inner-reduction recipe word is physically at least as
heavy as its original outer bracket. -/
lemma inner_outer_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    factor.word.weight PEAddres.weight ≤
      (innerReductionExpansion hinputWeight R factor innerWord
        rightWord).word.weight PEAddres.weight := by
  rw [inner_reduction_expansion, hword,
    CWord.weight_commutator]
  exact Nat.add_le_add
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R))
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R))

/--
Normalize one classified term in place.  Balanced terms attach immediately;
frontier terms invoke the recursive transient factory at their larger
physical word weight.
-/
noncomputable def recollection_classified_term
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      TTFtry
        d n inputWeight H)
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecol
      n (factor.word.weight PEAddres.weight) H
        [classifiedOuterTerm hinputWeight R factor innerWord
          rightWord hword] := by
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · rw [classified_outer_degree
      hinputWeight R factor innerWord rightWord hword hbalanced]
    exact
      TTRecol.singleton_attached
        (attachedInnerExpansion hinputWeight R factor
          innerWord rightWord hword hbalanced)
        (by
          rw [attached_inner_expansion]
          exact
            inner_outer_expansion
              hinputWeight R factor innerWord rightWord hword)
  · have hfrontier : R.rightDegree < R.leftDegree :=
      Nat.lt_of_not_ge hbalanced
    rw [classified_inner_degree
      hinputWeight R factor innerWord rightWord hword hfrontier]
    exact
      TTRecol.singleton_frontier
        (innerReductionExpansion hinputWeight R factor innerWord
          rightWord)
        ((factory.recollectionOrEmpty
          (innerReductionExpansion hinputWeight R factor innerWord
            rightWord)).weaken
              (inner_outer_expansion
                hinputWeight R factor innerWord rightWord hword))

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti

/--
Normalize the complete classified packet without changing its Hall-Petresco
term order.
-/
noncomputable def
    source_classified_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      TTFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecol
      n (factor.word.weight PEAddres.weight) H
        (packet.innerOuterTerms hinputWeight factor
          innerWord rightWord hword) :=
  TTRecol.of_singletons _
    fun term hterm => by
      let R := Classical.choose (List.mem_map.mp hterm)
      have hR :
          classifiedOuterTerm hinputWeight R factor innerWord
              rightWord hword =
            term :=
        (Classical.choose_spec (List.mem_map.mp hterm)).2
      exact hR ▸
        recollection_classified_term factory
          hinputWeight R factor innerWord rightWord hword

/-- The ordinary factors emitted by classified-packet recollection still
evaluate exactly to `[inner ^ factor.exponent, right]`. -/
lemma
    recollection_classified_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      TTFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (packet.source_classified_terms
          factory hinputWeight factor innerWord rightWord hword).higherSource =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [(packet.source_classified_terms
    factory hinputWeight factor innerWord rightWord hword)
      |>.list_higher_raw]
  exact
    packet.inner_reduction_terms hinputWeight factor
      innerWord rightWord hword q

end PFSubsti.TAPkt

end TCTex
end Submission
