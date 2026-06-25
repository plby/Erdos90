import Towers.Group.Zassenhaus.Transient
import Towers.Group.Zassenhaus.Contextual
import Towers.Group.Zassenhaus.FactoryBranchCases

/-!
# Fixed-packet contextual powered outer residuals

The contextual powered bridge is used with one selected Hall-Petresco packet.
This file rebuilds its thin outer-residual layer over the packet-indexed
classified recollection factory.  The semantic core is unchanged: insert the
collected temporary packet between recipe-correct Hall children and the
original outer factor, then recollect the two resulting quotients.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace SCPowere

/--
Compare the temporary powered commutator emitted by the fixed packet with its
original outer Hall factor.
-/
noncomputable def transientRawSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight H packet)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    List (SPFactora H inputWeight) :=
  SPFactora.inverseList
      (factory.recollectionOrTerminal hinputWeight factor innerWord
        rightWord hword).higherSource ++
    [factor]

/-- Evaluation of the fixed-packet bridge is powered-commutator division. -/
lemma transient_raw_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight H packet)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (transientRawSource factory hinputWeight factor innerWord
          rightWord hword) =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆⁻¹ *
        factor.eval q := by
  rw [transientRawSource,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    (factory.recollectionOrTerminal hinputWeight factor innerWord
      rightWord hword).list_higher_raw,
    packet.inner_reduction_terms]
  simp [SPFactora.listEval]

/-- The fixed-packet bridge value lies one layer deeper than its parent. -/
theorem transient_raw_series
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight H packet)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (transientRawSource factory hinputWeight factor innerWord
          rightWord hword) ∈
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
      (IPBridge.eval_zpow_series
        (n := n) innerWord rightWord (factor.exponent q))
  have hinverse : (temporary * parent⁻¹)⁻¹ ∈ K :=
    K.inv_mem hforward
  have hconj :
      temporary⁻¹ * (temporary * parent⁻¹)⁻¹ * (temporary⁻¹)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem
      (temporary * parent⁻¹)⁻¹ hinverse temporary⁻¹
  rw [transient_raw_source]
  change temporary⁻¹ * parent ∈ K
  have heq :
      temporary⁻¹ * (temporary * parent⁻¹)⁻¹ * (temporary⁻¹)⁻¹ =
        temporary⁻¹ * parent := by
    group
  simpa only [heq] using hconj

/-- At the next parent stratum, the fixed-packet bridge vanishes. -/
lemma transient_raw_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight H packet)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (transientRawSource factory hinputWeight factor innerWord
          rightWord hword) =
      1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (transient_raw_series factory
      hinputWeight factor innerWord rightWord hword q)

end SCPowere

namespace HEWord

open SCPowere

/--
Compare recipe-correct Hall children with the ordinary source emitted by the
fixed packet's classified-term collector.
-/
noncomputable def contextualPoweredComparison
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
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
    (factory.recollectionOrTerminal hinputWeight factor innerWord
      rightWord hword).higherSource

/-- Evaluation of the fixed-packet comparison is child-packet division. -/
theorem contextual_powered_comparison
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
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
        (contextualPoweredComparison
          factory hinputWeight factor innerWord rightWord hword) =
      (SPFactora.listEval q
        (innerOuterFactors factor innerWord rightWord hword))⁻¹ *
          ⁅innerWord.eval
                (PEAddres.freeLowerTruncation
                  (n := n)) ^
              factor.exponent q,
            rightWord.eval
              (PEAddres.freeLowerTruncation
                (n := n))⁆ := by
  rw [contextualPoweredComparison,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    (factory.recollectionOrTerminal hinputWeight factor innerWord
      rightWord hword).list_higher_raw,
    packet.inner_reduction_terms]

/-- The fixed-packet comparison value lies one layer deeper than its parent. -/
theorem
    inner_powered_series
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
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
        (contextualPoweredComparison
          factory hinputWeight factor innerWord rightWord hword) ∈
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
      IPBridge.eval_zpow_series
        (n := n) innerWord rightWord (factor.exponent q)
    simpa [K, temporary, SPFactora.eval,
      SPFactora.wordValue, hword] using hraw
  rw [contextual_powered_comparison]
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

/-- At the next parent stratum, the fixed-packet comparison vanishes. -/
theorem
    contextual_powered_terminal
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
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
        (contextualPoweredComparison
          factory hinputWeight factor innerWord rightWord hword) =
      1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (inner_powered_series
      factory hinputWeight factor innerWord rightWord hword q)

/-- Insert the fixed packet between Hall children and the original parent. -/
noncomputable def
    innerPoweredDecomp
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
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
  contextualPoweredComparison factory
      hinputWeight factor innerWord rightWord hword ++
    transientRawSource factory hinputWeight factor innerWord rightWord
      hword

/-- Evaluation of the fixed-packet decomposition recovers the outer residual. -/
theorem contextual_powered_decomposition
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
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
        (innerPoweredDecomp
          factory hinputWeight factor innerWord rightWord hword) =
      SPFactora.listEval q
        (innerRawSource
          factor innerWord rightWord hword) := by
  rw [innerPoweredDecomp,
    SPFactora.listEval_append,
    contextual_powered_comparison,
    transient_raw_source,
    inner_raw_source]
  group

/-- At the next parent stratum, the ordinary outer residual vanishes. -/
theorem inner_fixed_terminal
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
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
  rw [← contextual_powered_decomposition
      factory hinputWeight factor innerWord rightWord hword q,
    innerPoweredDecomp,
    SPFactora.listEval_append,
    contextual_powered_terminal
      factory hinputWeight factor innerWord rightWord hword hcutoff q,
    transient_raw_terminal factory hinputWeight
      factor innerWord rightWord hword hcutoff q,
    one_mul]

end HEWord

namespace TSRecol

open SCPowere

/-- Combine the two active fixed-packet pieces into the ordinary residual. -/
noncomputable def
    contextual_pieces
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
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
        (HEWord.contextualPoweredComparison
          factory hinputWeight factor innerWord rightWord hword))
    (bridge :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (transientRawSource factory hinputWeight factor innerWord
          rightWord hword)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  (comparison.append bridge).of_list_eq fun q => by
    simpa only [
      HEWord.innerPoweredDecomp]
      using
        HEWord.contextual_powered_decomposition
          factory hinputWeight factor innerWord rightWord hword q

/-- At the next parent stratum, recollect the ordinary residual to empty. -/
def fixed_packet_terminal
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet)
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
      (HEWord.inner_fixed_terminal
        factory hinputWeight factor innerWord rightWord hword hcutoff q).symm

end TSRecol

/-- Active powered recollections for one selected Hall-Petresco packet. -/
structure PPFtry
    (d n inputWeight : ℕ)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (classifiedFactory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet) where
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
          (HEWord.contextualPoweredComparison
            classifiedFactory hinputWeight factor innerWord rightWord hword)
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
          (SCPowere.transientRawSource
            classifiedFactory hinputWeight factor innerWord rightWord hword)

namespace PPFtry

/-- Dispatch the two active pieces or close the parent-stratum endpoint. -/
noncomputable def recollectionOrTerminal
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    {classifiedFactory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet}
    (pieces :
      PPFtry
        d n inputWeight packet hinputWeight classifiedFactory)
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
      TSRecol.contextual_pieces
        classifiedFactory hinputWeight factor innerWord rightWord hword
          (pieces.comparisonRecollection factor innerWord rightWord hword
            hactive)
          (pieces.bridgeRecollection factor innerWord rightWord hword hactive)
  · exact
      TSRecol.fixed_packet_terminal
        classifiedFactory hinputWeight factor innerWord rightWord hword
          (Nat.le_of_not_gt hactive)

/-- Forget fixed-packet powered pieces as the ordinary outer-residual factory. -/
noncomputable def outerRecollectionFactory
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    {classifiedFactory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet}
    (pieces :
      PPFtry
        d n inputWeight packet hinputWeight classifiedFactory) :
    IRFtry
      d n inputWeight where
  sourceRecollection factor innerWord rightWord hword _ :=
    pieces.recollectionOrTerminal factor innerWord rightWord hword

end PPFtry

namespace
  OFRoute

/-- Feed fixed-packet powered pieces into Hall-ranked outer-residual routing. -/
noncomputable def
    factoryPoweredPieces
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    {classifiedFactory :
      CRFtry
        d n inputWeight (concreteBasicCommutators.{u} d) packet}
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
      PPFtry
        d n inputWeight packet hinputWeight classifiedFactory) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) :=
  factory_above_outer schedule normalizerAbove
    pieces.outerRecollectionFactory

end
  OFRoute

end TCTex
end Towers
