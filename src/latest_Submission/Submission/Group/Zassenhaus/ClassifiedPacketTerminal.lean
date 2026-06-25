import
  Submission.Group.Zassenhaus.ClassifiedPacketRecollection

/-!
# Terminal recollection of classified transient packets

Once the next parent stratum reaches the nilpotent cutoff, every excess-left
frontier word vanishes.  The balanced terms still attach in their original
positions, so the complete classified packet recollects without a recursive
transient factory and without commuting any terms.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open HACoeff

namespace PTSubsti

/--
Normalize one classified term at the next parent-stratum endpoint.  Balanced
terms attach normally; excess-left terms vanish at the truncation cutoff.
-/
noncomputable def
    classified_inner_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
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
    have hwordWeight :=
      factor_inner_degree
        hinputWeight R factor innerWord rightWord hword hfrontier
    rw [classified_inner_degree
      hinputWeight R factor innerWord rightWord hword hfrontier]
    exact
      TTRecol.singleton_frontier
        (innerReductionExpansion hinputWeight R factor innerWord
          rightWord)
        (TTRecola.singleton_n_weight
          (innerReductionExpansion hinputWeight R factor innerWord
            rightWord)
          (hcutoff.trans (Nat.succ_le_of_lt hwordWeight)))

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti

/--
Normalize the complete classified packet at the next parent-stratum endpoint
without invoking a recursive transient factory.
-/
noncomputable def
    outer_classified_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
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
        classified_inner_terminal
          hinputWeight R factor innerWord rightWord hword hcutoff

/-- The terminal ordinary source still evaluates to the original outer
commutator. -/
lemma
    classified_terms_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
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
        (packet
          |>.outer_classified_terminal
            hinputWeight factor innerWord rightWord hword hcutoff).higherSource =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [(packet
    |>.outer_classified_terminal
      hinputWeight factor innerWord rightWord hword hcutoff)
      |>.list_higher_raw]
  exact
    packet.inner_reduction_terms hinputWeight factor
      innerWord rightWord hword q

end PFSubsti.TAPkt

end TCTex
end Submission
