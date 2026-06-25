import Submission.Group.Zassenhaus.TransientResidual
import
  Submission.Group.Zassenhaus.ContextualOperations

/-!
# Contextual recollection of reworded transient residuals

Rewording a transient exponent onto an inner Hall word produces a temporary
classified packet and a powered-commutator residual.  The original frontier
singleton is the ordered product of those two pieces.

This file embeds transient residual lists into mixed contextual packets,
proves that ordered factorization, and packages its recollection composition
rule.  At the next outer-word stratum, the residual vanishes semantically and
the same rule needs only a recollection of the temporary classified packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SOTerm

/-- Regard a transient source as a mixed packet containing only frontiers. -/
def frontierTerms
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (source :
      List (TWExp H inputWeight)) :
    List (SOTerm H inputWeight) :=
  source.map .frontier

/-- Embedding a transient source as frontier terms preserves its value. -/
lemma value_frontier_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (source :
      List (TWExp H inputWeight)) :
    listValue (n := n) q (frontierTerms source) =
      TWExp.listValue q source := by
  induction source with
  | nil =>
      rfl
  | cons wordExpansion source ih =>
      change
        wordExpansion.value q * listValue q (frontierTerms source) =
          wordExpansion.value q *
            TWExp.listValue q source
      rw [ih]

@[simp]
lemma listValue_append
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (left right :
      List (SOTerm H inputWeight)) :
    listValue (n := n) q (left ++ right) =
      listValue q left * listValue q right := by
  simp [listValue]

@[simp]
lemma value_singleton_frontier
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (wordExpansion :
      TWExp H inputWeight) :
    listValue (n := n) q [.frontier wordExpansion] =
      wordExpansion.value q := by
  simp [listValue, value]

end SOTerm

namespace TTRecola

/-- A semantically trivial transient source recollects to the empty source. -/
def empty_list_value
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (rawSource :
      List (TWExp H inputWeight))
    (hvalue :
      ∀ q : ℕ,
        TWExp.listValue (n := n) q
          rawSource = 1) :
    TTRecola
      n lowerWeight H rawSource where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro q
    simpa only [SPFactora.listEval_nil] using (hvalue q).symm

end TTRecola

namespace TTRecol

/-- Embed a recollected transient source as an all-frontier mixed packet. -/
def transient_source_recollect
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {rawSource :
      List (TWExp H inputWeight)}
    (recollection :
      TTRecola
        n lowerWeight H rawSource) :
    TTRecol
      n lowerWeight H
        (SOTerm.frontierTerms rawSource) where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := fun q =>
    (recollection.list_higher_raw q).trans
      (SOTerm.value_frontier_terms
        q rawSource).symm

end TTRecol

namespace PFSubsti.TAPkt

/--
The ordered contextual expansion of one transient outer carrier: first its
classified reworded packet, then its transient powered-bridge residual.
-/
def transientInnerContextual
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (SOTerm H inputWeight) :=
  packet.transientInnerTerms hinputWeight
      wordExpansion innerWord rightWord ++
    SOTerm.frontierTerms
      (packet.transientInnerReduction hinputWeight
        wordExpansion innerWord rightWord)

/-- The ordered contextual expansion evaluates to the original carrier. -/
lemma inner_contextual_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (q : ℕ) :
    SOTerm.listValue (n := n) q
        (packet.transientInnerContextual hinputWeight
          wordExpansion innerWord rightWord) =
      wordExpansion.value q := by
  rw [transientInnerContextual,
    SOTerm.listValue_append,
    packet.value_classified_terms,
    SOTerm.value_frontier_terms,
    packet.transient_inner_raw]
  group

/--
Compose recollections of the classified temporary packet and residual, then
transport the result back to the original frontier singleton.
-/
noncomputable def
    frontier_reworded_residual
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (packetRecollection :
      TTRecol
        n lowerWeight H
          (packet.transientInnerTerms hinputWeight
            wordExpansion innerWord rightWord))
    (residualRecollection :
      TTRecola
        n lowerWeight H
          (packet.transientInnerReduction hinputWeight
            wordExpansion innerWord rightWord)) :
    TTRecol
      n lowerWeight H [.frontier wordExpansion] :=
  let residualTermsRecollection :=
    TTRecol.transient_source_recollect
      residualRecollection
  TTRecol.list_value
    (TTRecol.append
      packetRecollection residualTermsRecollection) fun q => by
      simpa only [transientInnerContextual,
        SOTerm.value_singleton_frontier]
        using
          packet.inner_contextual_terms
            hinputWeight wordExpansion innerWord rightWord q

/-- At the next outer-word stratum, the transient residual is trivial. -/
lemma
    transient_inner_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : wordExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ wordExpansion.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (packet.transientInnerReduction hinputWeight
          wordExpansion innerWord rightWord) =
      1 := by
  exact eq_bot_iff.mp
    (SPFactora.trunc_last_bot
      (d := d) (n := n))
    (Subgroup.lowerCentralSeries_antitone (by omega)
      (packet
        |>.transient_inner_series
          hinputWeight wordExpansion innerWord rightWord hword q))

/-- At the next outer-word stratum, recollect the residual to empty. -/
def recollection_transient_terminal
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : wordExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ wordExpansion.word.weight PEAddres.weight + 1) :
    TTRecola
      n lowerWeight H
        (packet.transientInnerReduction hinputWeight
          wordExpansion innerWord rightWord) :=
  TTRecola.empty_list_value
    _ fun q =>
      packet
        |>.transient_inner_terminal
          hinputWeight wordExpansion innerWord rightWord hword hcutoff q

/--
At the next outer-word stratum, a recollection of the classified temporary
packet already recollects the original frontier singleton.
-/
noncomputable def frontier_reworded_terminal
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : wordExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ wordExpansion.word.weight PEAddres.weight + 1)
    (packetRecollection :
      TTRecol
        n lowerWeight H
          (packet.transientInnerTerms hinputWeight
            wordExpansion innerWord rightWord)) :
    TTRecol
      n lowerWeight H [.frontier wordExpansion] :=
  packet.frontier_reworded_residual
    hinputWeight wordExpansion innerWord rightWord packetRecollection
      (packet
        |>.recollection_transient_terminal
          hinputWeight wordExpansion innerWord rightWord hword hcutoff)

end PFSubsti.TAPkt

end TCTex
end Submission
