import Submission.Group.Zassenhaus.SourceRecollectionCongruence
import
  Submission.Group.Zassenhaus.ConcreteClassifiedRecollection

/-!
# Transient replacement for powered-commutator bridge residuals

The classified transient collector replaces the temporary Hall-Petresco
correction packet by an ordinary bounded symbolic source.  Invert that source
and append the original outer factor to obtain a concrete replacement for the
powered-commutator bridge residual.

The replacement is physically supported in the parent bracket weight, while
its total value lies one lower-central layer deeper.  This isolates the
remaining recursive quotient after transient frontier normalization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace IPBridge

/--
Replace the temporary correction packet inside the powered bridge residual by
the ordinary source emitted by classified transient recollection.
-/
noncomputable def recollectedTransientSource
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
    List (SPFactora H inputWeight) :=
  SPFactora.inverseList
      (packet.source_classified_terms factory
        hinputWeight factor innerWord rightWord hword).higherSource ++
    [factor]

/-- The transient replacement evaluates like the established bridge source. -/
lemma recollected_transient_source
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
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (recollectedTransientSource factory packet hinputWeight
          factor innerWord rightWord hword) =
      SPFactora.listEval q
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe) := by
  rw [recollectedTransientSource, residualRawSource,
    SPFactora.listEval_append,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    SPFactora.list_eval_inverse,
    packet.recollected_classified_factors
      factory hinputWeight factor innerWord rightWord hword hrecipe]

/-- The transient replacement is truncated whenever its parent factor is. -/
theorem truncated_recollected_transient
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
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (recollectedTransientSource factory packet hinputWeight
        factor innerWord rightWord hword) := by
  intro x hx
  rw [recollectedTransientSource] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        (packet.source_classified_terms
          factory hinputWeight factor innerWord rightWord hword
            |>.higher_source_truncated) x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hfactorTruncated

/-- Every transient replacement factor is supported at the parent weight. -/
theorem least_recollected_transient
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
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (recollectedTransientSource factory packet hinputWeight
        factor innerWord rightWord hword) := by
  intro x hx
  rw [recollectedTransientSource] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.least_inverse_list
        (packet.source_classified_terms
          factory hinputWeight factor innerWord rightWord hword
            |>.higher_weight_least) x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact le_rfl

/--
The powered bridge quotient lies one lower-central layer above its parent
bracket weight.
-/
theorem list_raw_series
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (factor.word.weight PEAddres.weight) := by
  let K :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight)
  let temporary :=
    ⁅innerWord.eval
          (PEAddres.freeLowerTruncation
            (n := n)) ^
        factor.exponent q,
      rightWord.eval
        (PEAddres.freeLowerTruncation
          (n := n))⁆
  let parent := factor.eval (n := n) q
  have hforward : temporary * parent⁻¹ ∈ K := by
    simpa [K, temporary, parent, SPFactora.eval,
      SPFactora.wordValue, hword] using
      (eval_zpow_series
        (n := n) innerWord rightWord (factor.exponent q))
  have hinverse : (temporary * parent⁻¹)⁻¹ ∈ K :=
    K.inv_mem hforward
  have hconj :
      temporary⁻¹ * (temporary * parent⁻¹)⁻¹ * (temporary⁻¹)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem
      (temporary * parent⁻¹)⁻¹ hinverse temporary⁻¹
  rw [list_raw_source]
  change temporary⁻¹ * parent ∈ K
  have heq :
      temporary⁻¹ * (temporary * parent⁻¹)⁻¹ * (temporary⁻¹)⁻¹ =
        temporary⁻¹ * parent := by
    group
  simpa only [heq] using hconj

/-- The recollected transient replacement has the same deeper semantic value. -/
theorem
    recollected_transient_series
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
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (recollectedTransientSource factory packet hinputWeight
          factor innerWord rightWord hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (factor.word.weight PEAddres.weight) := by
  rw [recollected_transient_source
    factory packet hinputWeight factor innerWord rightWord hword hrecipe]
  exact
    list_raw_series packet hinputWeight
      factor innerWord rightWord hword hrecipe q

end IPBridge

namespace TSRecol

open IPBridge

/-- Reuse a recollection of the transient replacement for the bridge source. -/
noncomputable def residual_recollected_transient
    {d n inputWeight lowerWeight : ℕ}
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
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (recollection :
      TSRecol
        (n := n) (lowerWeight := lowerWeight) H
        (recollectedTransientSource factory packet hinputWeight
          factor innerWord rightWord hword)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
      (residualRawSource packet hinputWeight factor innerWord rightWord
        hrecipe) :=
  recollection.of_list_eq fun q =>
    recollected_transient_source
      factory packet hinputWeight factor innerWord rightWord hword hrecipe q

/-- Reuse a bridge recollection for the equivalent transient replacement. -/
noncomputable def recollected_transient_raw
    {d n inputWeight lowerWeight : ℕ}
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
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (recollection :
      TSRecol
        (n := n) (lowerWeight := lowerWeight) H
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
      (recollectedTransientSource factory packet hinputWeight
        factor innerWord rightWord hword) :=
  recollection.of_list_eq fun q =>
    (recollected_transient_source
      factory packet hinputWeight factor innerWord rightWord hword hrecipe
        q).symm

end TSRecol

end TCTex
end Submission
