import Towers.Group.Zassenhaus.SourceRecollectionCongruence
import Towers.Group.Zassenhaus.ContextualRecollection
import
  Towers.Group.Zassenhaus.PoweredBridgeReplacement
import Towers.Group.Zassenhaus.ClassifiedPacketDescent
import Towers.Group.Zassenhaus.ReductionOuter
import Towers.Group.Zassenhaus.SourceRecollectionComposition
import Towers.Group.Zassenhaus.ContextualPacketRecursion
import
  Towers.Group.Zassenhaus.ContextualOperations
import Towers.Group.Zassenhaus.SemanticallyHigherRecollection
import Towers.Group.Zassenhaus.FactoryBranchCases
import Towers.Group.Zassenhaus.SharpNormalizerFamilies

-- Merged from ContextualPoweredBridge.lean

/-!
# Contextual transient powered-commutator bridges

The ordered classified-packet collector supplies an ordinary bounded source
for `[inner ^ e, right]` without first reattaching the parent recipe to
`inner`.  Inverting that contextual source and appending the original outer
factor gives an unrestricted replacement for the powered-commutator bridge
residual.

The replacement is truncated with its parent, is supported at the parent
weight, and evaluates one lower-central layer deeper.  When the older recipe
restriction is available, it is pointwise equivalent to the established
powered-bridge raw source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace IPBridge

/--
Replace `[inner ^ e, right]` by the ordinary source emitted from its complete
ordered classified packet, then compare it with the original outer factor.
-/
noncomputable def contextualTransientSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
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
      (factory.recollectionOrTerminal packet hinputWeight factor
        innerWord rightWord hword).higherSource ++
    [factor]

/-- The contextual bridge is the quotient of `[inner ^ e, right]` from the
original outer factor. -/
lemma list_contextual_transient
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
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
        (contextualTransientSource factory packet hinputWeight
          factor innerWord rightWord hword) =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆⁻¹ *
        factor.eval q := by
  rw [contextualTransientSource,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    (factory.recollectionOrTerminal packet hinputWeight factor
      innerWord rightWord hword).list_higher_raw,
    packet.inner_reduction_terms]
  simp [SPFactora.listEval]

/-- The contextual bridge source is truncated whenever its parent is. -/
theorem truncated_contextual_transient
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
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
      (contextualTransientSource factory packet hinputWeight
        factor innerWord rightWord hword) := by
  intro x hx
  rw [contextualTransientSource] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        (factory.recollectionOrTerminal packet hinputWeight factor
          innerWord rightWord hword).higher_source_truncated x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hfactorTruncated

/-- Every contextual bridge factor is supported at the parent weight. -/
theorem least_contextual_transient
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
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
      (contextualTransientSource factory packet hinputWeight
        factor innerWord rightWord hword) := by
  intro x hx
  rw [contextualTransientSource] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.least_inverse_list
        (factory.recollectionOrTerminal packet hinputWeight factor
          innerWord rightWord hword).higher_weight_least x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact le_rfl

/-- The contextual bridge value lies one lower-central layer above its parent
bracket weight. -/
theorem
    contextual_transient_series
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
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
        (contextualTransientSource factory packet hinputWeight
          factor innerWord rightWord hword) ∈
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
  rw [list_contextual_transient]
  change temporary⁻¹ * parent ∈ K
  have heq :
      temporary⁻¹ * (temporary * parent⁻¹)⁻¹ * (temporary⁻¹)⁻¹ =
        temporary⁻¹ * parent := by
    group
  simpa only [heq] using hconj

/-- When the old recipe restriction is available, the contextual bridge
evaluates like the established bridge raw source. -/
lemma contextual_transient_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
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
        (contextualTransientSource factory packet hinputWeight
          factor innerWord rightWord hword) =
      SPFactora.listEval q
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe) := by
  rw [list_contextual_transient,
    list_raw_source]

/-- At the first nested-commutator cutoff, the contextual bridge is trivial. -/
lemma contextual_transient_cutoff
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤
        2 * innerWord.weight PEAddres.weight +
          rightWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (contextualTransientSource factory packet hinputWeight
          factor innerWord rightWord hword) =
      1 := by
  rw [list_contextual_transient,
    element_zpow_cutoff
      innerWord rightWord hcutoff]
  simp [SPFactora.eval, SPFactora.wordValue, hword]

end IPBridge

namespace TSRecol

open IPBridge

/-- At the first nested-commutator cutoff, the contextual bridge recollects
to the empty higher source at any requested support bound. -/
def contextual_transient_raw
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤
        2 * innerWord.weight PEAddres.weight +
          rightWord.weight PEAddres.weight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
      (contextualTransientSource factory packet hinputWeight factor
        innerWord rightWord hword) where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_weight_least := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa using
      (contextual_transient_cutoff factory
        packet hinputWeight factor innerWord rightWord hword hcutoff q).symm

/-- Reuse a contextual-bridge recollection for the established bridge source
when the older recipe restriction is available. -/
noncomputable def residual_contextual_transient
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
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
        (contextualTransientSource factory packet hinputWeight
          factor innerWord rightWord hword)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
      (residualRawSource packet hinputWeight factor innerWord rightWord
        hrecipe) :=
  recollection.of_list_eq fun q =>
    contextual_transient_source factory
      packet hinputWeight factor innerWord rightWord hword hrecipe q

end TSRecol

end TCTex
end Towers

-- Merged from ContextualPoweredBridgeReplacement.lean

/-!
# Contextual transient replacement for powered bridge residuals

The contextual classified-packet factory allows transient frontier terms to
cancel in their complete ordered packet before returning to ordinary symbolic
factors.  This file inserts any such contextual recollection into the
powered-commutator bridge residual and specializes the construction to the
active-or-terminal dispatcher.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace IPBridge

/--
Replace the temporary correction packet by the ordinary source emitted by an
arbitrary contextual recollection of its complete classified packet.
-/
noncomputable def contextualRecollectedSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (recollection :
      TTRecol
        n (factor.word.weight PEAddres.weight) H
          (packet.innerOuterTerms hinputWeight factor
            innerWord rightWord hword)) :
    List (SPFactora H inputWeight) :=
  SPFactora.inverseList recollection.higherSource ++ [factor]

/-- A contextual transient replacement evaluates like the bridge residual. -/
lemma contextual_recollected_source
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
    (recollection :
      TTRecol
        n (factor.word.weight PEAddres.weight) H
          (packet.innerOuterTerms hinputWeight factor
            innerWord rightWord hword))
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (contextualRecollectedSource packet hinputWeight factor
          innerWord rightWord hword recollection) =
      SPFactora.listEval q
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe) := by
  rw [contextualRecollectedSource, residualRawSource,
    SPFactora.listEval_append,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    SPFactora.list_eval_inverse,
    packet.classified_recollection_factors
      hinputWeight factor innerWord rightWord hword hrecipe recollection]

/-- A contextual bridge replacement is physically truncated. -/
theorem truncated_contextual_recollected
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (recollection :
      TTRecol
        n (factor.word.weight PEAddres.weight) H
          (packet.innerOuterTerms hinputWeight factor
            innerWord rightWord hword))
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (contextualRecollectedSource packet hinputWeight factor
        innerWord rightWord hword recollection) := by
  intro x hx
  rw [contextualRecollectedSource] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        recollection.higher_source_truncated x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hfactorTruncated

/-- Every contextual replacement factor retains the parent support bound. -/
theorem least_contextual_recollected
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (recollection :
      TTRecol
        n (factor.word.weight PEAddres.weight) H
          (packet.innerOuterTerms hinputWeight factor
            innerWord rightWord hword)) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (contextualRecollectedSource packet hinputWeight factor
        innerWord rightWord hword recollection) := by
  intro x hx
  rw [contextualRecollectedSource] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.least_inverse_list
        recollection.higher_weight_least x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact le_rfl

/--
Use the active classified-packet dispatcher to construct the explicit bridge
replacement quotient.
-/
noncomputable def activeClassifiedSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    List (SPFactora H inputWeight) :=
  contextualRecollectedSource packet hinputWeight factor innerWord
    rightWord hword
      (factory.recollectionOrTerminal packet hinputWeight factor
        innerWord rightWord hword)

/-- The dispatched contextual quotient evaluates like the bridge residual. -/
lemma active_classified_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
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
        (activeClassifiedSource factory packet hinputWeight factor
          innerWord rightWord hword) =
      SPFactora.listEval q
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe) :=
  contextual_recollected_source packet
    hinputWeight factor innerWord rightWord hword hrecipe
      (factory.recollectionOrTerminal packet hinputWeight factor
        innerWord rightWord hword) q

end IPBridge

namespace TSRecol

open IPBridge

/--
The only remaining bridge obligation after contextual transient collection is
a recollection of the explicit dispatched replacement quotient.
-/
noncomputable def residual_active_classified
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
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
        (activeClassifiedSource factory packet hinputWeight factor
          innerWord rightWord hword)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
      (residualRawSource packet hinputWeight factor innerWord rightWord
        hrecipe) :=
  recollection.of_list_eq fun q =>
    active_classified_source factory
      packet hinputWeight factor innerWord rightWord hword hrecipe q

end TSRecol

end TCTex
end Towers

-- Merged from ContextualRecursionStep.lean

/-!
# Context-preserving recursion steps for transient inner reduction

The recursive inner-reduction obligation is a complete ordered classified
packet, not a collection of independent transient singletons.  Retaining the
interleaved packet matters because attached and frontier terms may cancel in
context before returning to the ordinary symbolic language.

This file packages the corresponding well-founded recursion surface.  A local
step receives the complete packet together with its strict
Dershowitz-Manna frontier-defect descent certificate, and compiles into the
active classified-packet factory used by contextual powered collection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
A context-preserving recursive step for an active classified packet.  The
callback receives the complete ordered packet and the strict multiset descent
certificate that justifies a recursive call.
-/
structure DCRecol
    (d n inputWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  sourceRecollection :
    ∀
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (hinputWeight : 0 < inputWeight)
      (factor : SPFactora H inputWeight)
      (innerWord rightWord : CWord (HEAddres H))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight PEAddres.weight + 1 < n →
        Multiset.IsDershowitzMannaLT
            (SOTerm.frontierDefectMultiset
              n
              (packet.innerOuterTerms hinputWeight factor
                innerWord rightWord hword))
            {SPFactora.cutoffDefect n factor} →
          TTRecol
            n (factor.word.weight PEAddres.weight) H
              (packet.innerOuterTerms hinputWeight factor
                innerWord rightWord hword)

namespace DCRecol

/--
Compile a context-preserving descending step into the active classified-packet
factory.  The strict multiset certificate is derived from the active-stratum
hypothesis.
-/
noncomputable def toActiveFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (step :
      DCRecol
        d n inputWeight H) :
    ACFtry
      d n inputWeight H where
  sourceRecollection packet hinputWeight factor innerWord rightWord hword
      hactive :=
    step.sourceRecollection packet hinputWeight factor innerWord rightWord
      hword hactive
        (packet.frontier_multiset_singleton
          hinputWeight factor innerWord rightWord hword
            (Nat.lt_trans (Nat.lt_succ_self _) hactive))

/--
Any existing active classified-packet factory supplies the stronger descending
step interface by ignoring the certificate.  This records backward
compatibility while keeping the certificate visible to future recursion.
-/
noncomputable def ofActiveFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
        d n inputWeight H) :
    DCRecol
      d n inputWeight H where
  sourceRecollection packet hinputWeight factor innerWord rightWord hword
      hactive _ :=
    factory.sourceRecollection packet hinputWeight factor innerWord rightWord
      hword hactive

end DCRecol

end TCTex
end Towers

-- Merged from ContextualPoweredResidualComposition.lean

/-!
# Contextual powered decomposition of outer residuals

The contextual transient bridge does not need to restrict the parent recipe
to the inner commutator word.  Insert its collected classified packet between
the concrete Hall-child packet and the original parent factor.  This splits
the ordinary outer residual into:

* comparison of the recipe-correct Hall children with the contextual packet;
* the contextual transient powered bridge.

The decomposition is valid without an inner recipe restriction.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

open IPBridge

namespace HEWord

/--
Compare recipe-correct Hall children with the ordinary packet emitted by the
contextual classified-term collector.
-/
noncomputable def contextualPoweredSource
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
      (innerOuterFactors factor innerWord rightWord hword) ++
    (factory.recollectionOrTerminal packet hinputWeight factor
      innerWord rightWord hword).higherSource

/-- Evaluation of the contextual powered comparison is child-packet division. -/
theorem contextual_powered_source
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (contextualPoweredSource factory
          packet hinputWeight factor innerWord rightWord hword) =
      (SPFactora.listEval q
        (innerOuterFactors factor innerWord rightWord hword))⁻¹ *
          ⁅innerWord.eval
                (PEAddres.freeLowerTruncation
                  (n := n)) ^
              factor.exponent q,
            rightWord.eval
              (PEAddres.freeLowerTruncation
                (n := n))⁆ := by
  rw [contextualPoweredSource,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    (factory.recollectionOrTerminal packet hinputWeight factor
      innerWord rightWord hword).list_higher_raw,
    packet.inner_reduction_terms]

/-- Insert the contextual classified packet between Hall children and parent. -/
noncomputable def
    innerContextualPowered
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  contextualPoweredSource factory packet
      hinputWeight factor innerWord rightWord hword ++
    contextualTransientSource factory packet hinputWeight factor
      innerWord rightWord hword

/--
Evaluation of the unrestricted contextual decomposition recovers the ordinary
child-to-parent outer residual.
-/
theorem
    contextual_powered_residual
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerContextualPowered
          factory packet hinputWeight factor innerWord rightWord hword) =
      SPFactora.listEval q
        (innerRawSource
          factor innerWord rightWord hword) := by
  rw [innerContextualPowered,
    SPFactora.listEval_append,
    contextual_powered_source,
    list_contextual_transient,
    inner_raw_source]
  group

end HEWord

namespace TSRecol

/--
Compose recollections of the contextual comparison and bridge into a
recollection of the ordinary outer residual.
-/
noncomputable def
    contextual_powered_pieces
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (comparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.contextualPoweredSource
          factory packet hinputWeight factor innerWord rightWord hword))
    (bridge :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (contextualTransientSource factory packet hinputWeight
          factor innerWord rightWord hword)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  (comparison.append bridge).of_list_eq fun q => by
    simpa only [
      HEWord.innerContextualPowered]
      using
        HEWord.contextual_powered_residual
          factory packet hinputWeight factor innerWord rightWord hword q

end TSRecol

end TCTex
end Towers

-- Merged from ContextualRecursiveRecollection.lean

/-!
# Recursive recollection of contextual transient packets

The contextual packet fixpoint is generic in its result.  This file
specializes that fixpoint to ordinary recollections of complete ordered mixed
packets.  A local resolver may use recursive recollections for strictly
smaller frontier-defect multisets; the compiled fixpoint then supplies the
descending classified-packet factory used by powered outer-residual routing.

The local resolver is the remaining place for packet-specific cancellation
rules.  Its recursive input retains the complete interleaved packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
One contextual recollection resolver for complete ordered mixed packets.
Every recursive recollection is available only at a strictly smaller
frontier-defect multiset.
-/
structure TCReca
    (d n inputWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  resolve :
    ∀
      (lowerWeight : ℕ)
      (parent :
        List (SOTerm H inputWeight)),
      (∀ child,
        SOTerm.FrontierDefectMultiset
            n child parent →
          TTRecol
            n lowerWeight H child) →
        TTRecol
          n lowerWeight H parent

namespace TCReca

/-- Forget the recollection specialization into the generic packet resolver. -/
noncomputable def toRecursiveStep
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (step :
      TCReca
        d n inputWeight H)
    (lowerWeight : ℕ) :
    TRStep
      (n := n) (inputWeight := inputWeight) H fun
        terms : List (SOTerm H inputWeight) =>
        TTRecol
          n lowerWeight H terms where
  resolve := step.resolve lowerWeight

/-- Run contextual mixed-packet recollection by frontier-defect recursion. -/
noncomputable def sourceRecollection
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (step :
      TCReca
        d n inputWeight H)
    (lowerWeight : ℕ)
    (terms :
      List (SOTerm H inputWeight)) :
    TTRecol
      n lowerWeight H terms :=
  (step.toRecursiveStep lowerWeight).recursiveResult terms

/-- Unfold one contextual mixed-packet recollection resolver call. -/
theorem sourceRecollection_eq
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (step :
      TCReca
        d n inputWeight H)
    (lowerWeight : ℕ)
    (terms :
      List (SOTerm H inputWeight)) :
    step.sourceRecollection lowerWeight terms =
      step.resolve lowerWeight terms fun child _ =>
        step.sourceRecollection lowerWeight child := by
  rw [sourceRecollection,
    TRStep.recursiveResult_eq]
  rfl

/--
Compile a contextual packet resolver into the certificate-carrying active
inner-reduction step.
-/
noncomputable def toDescendingStep
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (step :
      TCReca
        d n inputWeight H) :
    DCRecol
      d n inputWeight H where
  sourceRecollection packet hinputWeight factor innerWord rightWord hword
      _ _ :=
    step.sourceRecollection
      (factor.word.weight PEAddres.weight)
      (packet.innerOuterTerms hinputWeight factor innerWord
        rightWord hword)

/--
Compile a contextual packet resolver directly into the active classified
packet factory used by powered collection.
-/
noncomputable def toActiveFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (step :
      TCReca
        d n inputWeight H) :
    ACFtry
      d n inputWeight H :=
  step.toDescendingStep.toActiveFactory

end TCReca

end TCTex
end Towers

-- Merged from ContextualPoweredComparisonSupport.lean

/-!
# Support of contextual powered outer-reduction comparisons

The contextual powered comparison divides the recipe-correct Hall-child
packet by the ordinary packet emitted by the classified-term collector.  Its
source is physically supported in the parent bracket weight, while its
evaluated product lies one lower-central layer deeper.

Unlike the older powered-comparison support, this route does not restrict the
parent recipe to the inner commutator word.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

open IPBridge

namespace HEWord

/-- A truncated parent gives a physically truncated contextual comparison. -/
theorem truncated_contextual_powered
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (contextualPoweredSource factory packet
        hinputWeight factor innerWord rightWord hword) := by
  intro x hx
  rw [contextualPoweredSource] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_inner_factors factor innerWord rightWord
          hword hfactorTruncated) x hx
  · exact
      (factory.recollectionOrTerminal packet hinputWeight factor
        innerWord rightWord hword).higher_source_truncated x hx

/-- Every contextual comparison factor is supported at the parent weight. -/
theorem
    least_contextual_powered
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (contextualPoweredSource factory packet
        hinputWeight factor innerWord rightWord hword) := by
  intro x hx
  rw [contextualPoweredSource] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.least_inverse_list
        (least_inner_factors factor innerWord
          rightWord hword) x hx
  · exact
      (factory.recollectionOrTerminal packet hinputWeight factor
        innerWord rightWord hword).higher_weight_least x hx

/-- The contextual comparison evaluates one lower-central layer deeper. -/
theorem
    contextual_powered_series
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (contextualPoweredSource factory
          packet hinputWeight factor innerWord rightWord hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (factor.word.weight PEAddres.weight) := by
  let K :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight)
  let children :=
    SPFactora.listEval (n := n) q
      (innerOuterFactors factor innerWord rightWord hword)
  let temporary :=
    ⁅innerWord.eval
          (PEAddres.freeLowerTruncation
            (n := n)) ^
        factor.exponent q,
      rightWord.eval
        (PEAddres.freeLowerTruncation
          (n := n))⁆
  have hchildren :
      children⁻¹ * (factor.eval (n := n) q) ∈ K := by
    exact
      inner_inv_series
        factor innerWord rightWord hword q
  have hpower :
      temporary * (factor.eval (n := n) q)⁻¹ ∈ K := by
    have hraw :=
      eval_zpow_series
        (n := n) innerWord rightWord (factor.exponent q)
    simpa [K, temporary, SPFactora.eval,
      SPFactora.wordValue, hword] using hraw
  rw [contextual_powered_source]
  change children⁻¹ * temporary ∈ K
  have hchildrenQuotient :
      QuotientGroup.mk' K children⁻¹ =
        QuotientGroup.mk' K (factor.eval (n := n) q)⁻¹ := by
    apply (mul_inv_quotient K).mp
    simpa only [inv_inv] using hchildren
  have hpowerQuotient :
      QuotientGroup.mk' K temporary =
        QuotientGroup.mk' K (factor.eval (n := n) q) :=
    (mul_inv_quotient K).mp hpower
  have htarget :
      children⁻¹ * (temporary⁻¹)⁻¹ ∈ K := by
    apply (mul_inv_quotient K).mpr
    simpa only [map_inv] using
      hchildrenQuotient.trans (congrArg Inv.inv hpowerQuotient.symm)
  simpa only [inv_inv] using htarget

/-- At the next-stratum endpoint, the contextual comparison is trivial. -/
theorem
    powered_comparison_terminal
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (contextualPoweredSource factory
          packet hinputWeight factor innerWord rightWord hword) =
      1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (contextual_powered_series
      factory packet hinputWeight factor innerWord rightWord hword q)

/-- The terminal contextual comparison recollects to the empty source. -/
def contextual_comparison_terminal
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (contextualPoweredSource factory packet
        hinputWeight factor innerWord rightWord hword) where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_weight_least := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa using
      (powered_comparison_terminal
        factory packet hinputWeight factor innerWord rightWord hword hcutoff
          q).symm

/-- A parent-stratum normalizer recollects the contextual comparison higher. -/
noncomputable def contextual_powered_normalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (contextualPoweredSource factory packet
        hinputWeight factor innerWord rightWord hword) :=
  normalizer.source_recollection_series hn
    (concreteBasicCommutators.{u} d) hH
      (contextualPoweredSource factory packet
        hinputWeight factor innerWord rightWord hword)
      factor.word_weight_pos hfactorTruncated
      (truncated_contextual_powered
        factory packet hinputWeight factor innerWord rightWord hword
          hfactorTruncated)
      (least_contextual_powered
        factory packet hinputWeight factor innerWord rightWord hword)
      (contextual_powered_series
        factory packet hinputWeight factor innerWord rightWord hword)

end HEWord

end TCTex
end Towers

-- Merged from ContextualPoweredOuterResidualSupport.lean

/-!
# Outer-residual support from contextual powered pieces

The contextual powered comparison and bridge both lie one lower-central layer
above their parent bracket weight.  This file supplies the symmetric bridge
support adapters and composes the two pieces into the ordinary outer residual.

At the next parent-stratum endpoint both pieces recollect to empty sources.
A parent-stratum normalizer remains available as an explicit compatibility
route away from that endpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open IPBridge

namespace IPBridge

/-- The contextual bridge vanishes at the next parent-stratum endpoint. -/
lemma contextual_transient_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (contextualTransientSource factory packet hinputWeight
          factor innerWord rightWord hword) =
      1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (contextual_transient_series
      factory packet hinputWeight factor innerWord rightWord hword q)

end IPBridge

namespace TSRecol

/-- At the parent endpoint the contextual bridge recollects to empty. -/
def contextual_raw_terminal
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      ACFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
      (contextualTransientSource factory packet hinputWeight factor
        innerWord rightWord hword) where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_weight_least := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa using
      (contextual_transient_terminal factory
        packet hinputWeight factor innerWord rightWord hword hcutoff q).symm

/--
At the next parent-stratum endpoint both contextual powered pieces erase, so
the ordinary outer residual recollects to empty without a normalizer.
-/
def inner_contextual_terminal
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  contextual_powered_pieces
    factory packet hinputWeight factor innerWord rightWord hword
      (HEWord.contextual_comparison_terminal
          factory packet hinputWeight factor innerWord rightWord hword hcutoff)
      (contextual_raw_terminal factory packet
        hinputWeight factor innerWord rightWord hword hcutoff)

end TSRecol

namespace TSNormalb

/-- A parent-stratum normalizer recollects the contextual bridge one layer up. -/
noncomputable def contextual_transient_residual
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factory :
      ACFtry
        d n inputWeight H)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight) H) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      H
      (contextualTransientSource factory packet hinputWeight factor
        innerWord rightWord hword) :=
  normalizer.source_recollection_series hn H hH
    (contextualTransientSource factory packet hinputWeight factor
      innerWord rightWord hword)
    factor.word_weight_pos hfactorTruncated
    (truncated_contextual_transient factory packet
      hinputWeight factor innerWord rightWord hword hfactorTruncated)
    (least_contextual_transient factory packet
      hinputWeight factor innerWord rightWord hword)
    (contextual_transient_series
      factory packet hinputWeight factor innerWord rightWord hword)

end TSNormalb

namespace TSRecol

/--
Compatibility route: a parent-stratum normalizer recollects both contextual
powered pieces and therefore the ordinary outer residual.
-/
noncomputable def
    inner_contextual_normalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  contextual_powered_pieces
    factory packet hinputWeight factor innerWord rightWord hword
      (HEWord.contextual_powered_normalizer
          hn hH factory packet hinputWeight factor innerWord rightWord hword
            hfactorTruncated normalizer)
      (normalizer.contextual_transient_residual hn hH
        factory packet hinputWeight factor innerWord rightWord hword
          hfactorTruncated)

end TSRecol

end TCTex
end Towers

-- Merged from ContextualPoweredResidualTerminal.lean

/-!
# Terminal contextual powered outer residuals

At the next parent-weight stratum, the contextual comparison is trivial.  The
powered-commutator bridge is also trivial: positivity of the inner word puts
the same endpoint beyond its first nested-commutator cutoff.

Consequently the ordinary outer residual recollects to the empty source
without restricting the parent recipe to the inner commutator word.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord
open IPBridge

namespace HEWord

/-- The next parent-weight stratum reaches the nested bridge cutoff. -/
lemma contextual_powered_bridge
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    factor.word.weight PEAddres.weight + 1 ≤
      2 * innerWord.weight PEAddres.weight +
        rightWord.weight PEAddres.weight := by
  have hinner :=
    CWord.weight_pos PEAddres.weight
      PEAddres.weight_pos innerWord
  rw [hword, CWord.weight_commutator]
  omega

/-- At the next parent-weight stratum, the ordinary outer residual vanishes. -/
theorem
    inner_powered_terminal
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerRawSource factor innerWord rightWord
          hword) =
      1 := by
  rw [←
    contextual_powered_residual
      factory packet hinputWeight factor innerWord rightWord hword q,
    innerContextualPowered,
    SPFactora.listEval_append,
    powered_comparison_terminal
      factory packet hinputWeight factor innerWord rightWord hword hcutoff q,
    contextual_transient_cutoff factory
      packet hinputWeight factor innerWord rightWord hword
        (hcutoff.trans
          (contextual_powered_bridge factor innerWord
            rightWord hword))
        q,
    one_mul]

end HEWord

namespace TSRecol

/--
Once the nested bridge is cut off, a recollection of the contextual
comparison already recollects the ordinary outer residual.
-/
noncomputable def
    inner_contextual_powered
    {d n inputWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤
        2 * innerWord.weight PEAddres.weight +
          rightWord.weight PEAddres.weight)
    (comparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.contextualPoweredSource
          factory packet hinputWeight factor innerWord rightWord hword)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  contextual_powered_pieces
    factory packet hinputWeight factor innerWord rightWord hword comparison
      (contextual_transient_raw factory packet
        hinputWeight factor innerWord rightWord hword hcutoff)

/--
At the next parent-weight endpoint, the ordinary outer residual recollects to
the empty source at any requested support bound.
-/
def recollection_powered_terminal
    {d n inputWeight lowerWeight : ℕ}
    (factory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_weight_least := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa using
      (inner_powered_terminal
        factory packet hinputWeight factor innerWord rightWord hword hcutoff
          q).symm

end TSRecol

end TCTex
end Towers

-- Merged from ContextualPoweredOuterResidualFactory.lean

/-!
# Factory routing for contextual powered outer residuals

Away from the next parent-stratum endpoint, contextual powered collection has
two explicit residual obligations: recollect the Hall-child comparison and
recollect the transient bridge.  At the endpoint both obligations erase.

This file packages those active obligations, dispatches the endpoint
automa, and adapts the result to the outer-residual factory consumed by
the Hall-ranked scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open IPBridge
open TSRecol

/--
Active contextual powered recollections.  The fields are requested only while
one complete parent stratum remains below the cutoff.
-/
structure CPFtry
    (d n inputWeight : ℕ)
    (classifiedFactory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight) where
  comparisonRecollection :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (innerWord rightWord :
        CWord
          (HEAddres (concreteBasicCommutators.{u} d)))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight PEAddres.weight + 1 < n →
        TSRecol
          (n := n)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
          (concreteBasicCommutators.{u} d)
          (HEWord.contextualPoweredSource
            classifiedFactory packet hinputWeight factor innerWord rightWord
              hword)
  bridgeRecollection :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (innerWord rightWord :
        CWord
          (HEAddres (concreteBasicCommutators.{u} d)))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight PEAddres.weight + 1 < n →
        TSRecol
          (n := n)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
          (concreteBasicCommutators.{u} d)
          (contextualTransientSource classifiedFactory packet
            hinputWeight factor innerWord rightWord hword)

namespace CPFtry

/--
Dispatch active contextual powered pieces or close the next-stratum endpoint
without requesting either active recollection.
-/
noncomputable def recollectionOrTerminal
    {d n inputWeight : ℕ}
    {classifiedFactory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d)}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (pieces :
      CPFtry
        d n inputWeight classifiedFactory packet hinputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) := by
  by_cases hactive :
      factor.word.weight PEAddres.weight + 1 < n
  · exact
      contextual_powered_pieces
          classifiedFactory packet hinputWeight factor innerWord rightWord
            hword
              (pieces.comparisonRecollection factor innerWord rightWord hword
                hactive)
              (pieces.bridgeRecollection factor innerWord rightWord hword
                hactive)
  · exact
      inner_contextual_terminal
          classifiedFactory packet hinputWeight factor innerWord rightWord
            hword (Nat.le_of_not_gt hactive)

/-- Forget contextual powered pieces as the ordinary outer-residual factory. -/
noncomputable def outerRecollectionFactory
    {d n inputWeight : ℕ}
    {classifiedFactory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d)}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (pieces :
      CPFtry
        d n inputWeight classifiedFactory packet hinputWeight) :
    IRFtry
      d n inputWeight where
  sourceRecollection factor innerWord rightWord hword _ :=
    pieces.recollectionOrTerminal factor innerWord rightWord hword

/-- A complete normalizer family supplies both active compatibility pieces. -/
noncomputable def ofNormalizerFamily
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (classifiedFactory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    CPFtry
      d n inputWeight classifiedFactory packet hinputWeight where
  comparisonRecollection factor innerWord rightWord hword hactive :=
    HEWord.contextual_powered_normalizer
        hn hH classifiedFactory packet hinputWeight factor innerWord rightWord
          hword (Nat.lt_trans (Nat.lt_succ_self _) hactive)
            (family.normalizer
              (factor.word.weight PEAddres.weight))
  bridgeRecollection factor innerWord rightWord hword hactive :=
    (family.normalizer
      (factor.word.weight PEAddres.weight))
        |>.contextual_transient_residual hn hH
          classifiedFactory packet hinputWeight factor innerWord rightWord
            hword (Nat.lt_trans (Nat.lt_succ_self _) hactive)

end CPFtry

namespace OFRoute

/--
Feed contextual powered pieces into the existing Hall-ranked outer-factory
routing interface.
-/
noncomputable def factory_powered_pieces
    {d n inputWeight : ℕ}
    {classifiedFactory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d)}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (pieces :
      CPFtry
        d n inputWeight classifiedFactory packet hinputWeight) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) :=
  factory_above_outer schedule normalizerAbove
    pieces.outerRecollectionFactory

end OFRoute

end TCTex
end Towers

-- Merged from ContextualPoweredOuterResidualFactoryCompatibility.lean

/-!
# Compatibility constructors for contextual powered outer-residual routing

The contextual powered pieces factory is the scheduler-facing interface for
outer residuals.  This file records two compact constructors:

* a normalizer family supplies the active contextual pieces;
* the older transient-singleton factory can first be forgotten into the
  contextual classified-packet interface.

These adapters keep the stronger historical assumption available as a
compatibility route while exposing the contextual interface as the recursive
boundary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace CPFtry

/--
The older singleton transient factory and a complete normalizer family supply
all active contextual powered pieces.
-/
noncomputable def transientFactoryNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (transientFactory :
      TTFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    CPFtry
      d n inputWeight
        (ACFtry.ofTransientFactory
          transientFactory)
        packet hinputWeight :=
  ofNormalizerFamily hn hH
    (ACFtry.ofTransientFactory
      transientFactory)
    packet hinputWeight family

end CPFtry

namespace OFRoute

/--
Compile a contextual classified-packet factory and normalizer family directly
into the Hall-ranked scheduler's outer-factory routing data.
-/
noncomputable def
    factoryContextualPowered
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (classifiedFactory :
      ACFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) :=
  factory_powered_pieces schedule
    normalizerAbove
      (CPFtry.ofNormalizerFamily
        hn hH classifiedFactory packet hinputWeight family)

/--
Compile the historical singleton transient factory into scheduler routing by
first forgetting it into the contextual classified-packet interface.
-/
noncomputable def
    factoryNormalizerTransient
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (transientFactory :
      TTFtry
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) :=
  factoryContextualPowered
    hn hH schedule normalizerAbove
      (ACFtry.ofTransientFactory
        transientFactory)
      packet hinputWeight family

end OFRoute

end TCTex
end Towers

-- Merged from ContextualRecursiveRouting.lean

/-!
# Routing contextual transient-packet recursion

A complete mixed-packet recollection resolver compiles into the active
classified-packet factory.  This file threads that compiled factory through
the existing powered-pieces and Hall-ranked scheduler interfaces.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace CPFtry

/--
A recursive contextual packet resolver and a normalizer family supply all
active powered pieces.
-/
noncomputable def recursiveNormalizerFamily
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (step :
      TCReca
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    CPFtry
      d n inputWeight step.toActiveFactory packet hinputWeight :=
  ofNormalizerFamily hn hH step.toActiveFactory packet hinputWeight family

end CPFtry

namespace OFRoute

/--
Compile a recursive contextual packet resolver directly into the Hall-ranked
scheduler's outer-factory routing data.
-/
noncomputable def
    factoryNormalizerRecursive
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (step :
      TCReca
        d n inputWeight (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) :=
  factoryContextualPowered
    hn hH schedule normalizerAbove step.toActiveFactory packet hinputWeight
      family

end OFRoute

end TCTex
end Towers
