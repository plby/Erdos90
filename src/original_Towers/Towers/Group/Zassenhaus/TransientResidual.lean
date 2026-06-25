import Towers.Group.Zassenhaus.TransientInversion
import Towers.Group.Zassenhaus.ReductionPoweredBridge

/-!
# Residual sources for reworded transient powers

Rewording a transient outer exponent onto its inner Hall word produces a
temporary Hall-Petresco packet for `[inner ^ e, right]`.  The original outer
carrier differs from that temporary packet by a powered-commutator residual.
This file represents the residual without prematurely attaching any transient
term: reverse-negate the complete temporary packet, then append the original
outer carrier.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

namespace PTSubsti

/--
Every temporary recipe output is at least as heavy as the original outer
bracket whose exponent was reworded onto the inner input.
-/
lemma outer_expansion_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    outerExpansion.word.weight PEAddres.weight ≤
      (wordExpansion hinputWeight R (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord)).word.weight
          PEAddres.weight := by
  rw [word_wordExpansion, weight_boundWord,
    TWExp.word_reword]
  change
    outerExpansion.word.weight PEAddres.weight ≤
      R.leftDegree * innerWord.weight PEAddres.weight +
        R.rightDegree * rightWord.weight PEAddres.weight
  rw [hword, CWord.weight_commutator]
  exact Nat.add_le_add
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R))
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R))

/--
Same-stratum temporary outputs can occur only for a recipe of bidegree
`(1, 1)`.  Every other recipe is physically heavier than the parent bracket.
-/
lemma left_expansion_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (heq :
      (wordExpansion hinputWeight R (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord)).word.weight
          PEAddres.weight =
        outerExpansion.word.weight PEAddres.weight) :
    R.leftDegree = 1 ∧ R.rightDegree = 1 := by
  have hinner :
      0 < innerWord.weight PEAddres.weight :=
    CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
        innerWord
  have hright :
      0 < rightWord.weight PEAddres.weight :=
    CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
        rightWord
  have hleftDegree :=
    BRSpec.leftDegree_pos R
  have hrightDegree :=
    BRSpec.rightDegree_pos R
  rw [word_wordExpansion, weight_boundWord,
    TWExp.word_reword] at heq
  change
    R.leftDegree * innerWord.weight PEAddres.weight +
          R.rightDegree * rightWord.weight PEAddres.weight =
      outerExpansion.word.weight PEAddres.weight at heq
  rw [hword, CWord.weight_commutator] at heq
  constructor
  · by_contra hne
    have htwo : 2 ≤ R.leftDegree := by
      omega
    have hleftMul :
        2 * innerWord.weight PEAddres.weight ≤
          R.leftDegree * innerWord.weight PEAddres.weight :=
      Nat.mul_le_mul_right _ htwo
    have hrightMul :
        rightWord.weight PEAddres.weight ≤
          R.rightDegree * rightWord.weight PEAddres.weight :=
      Nat.le_mul_of_pos_left _ hrightDegree
    omega
  · by_contra hne
    have htwo : 2 ≤ R.rightDegree := by
      omega
    have hleftMul :
        innerWord.weight PEAddres.weight ≤
          R.leftDegree * innerWord.weight PEAddres.weight :=
      Nat.le_mul_of_pos_left _ hleftDegree
    have hrightMul :
        2 * rightWord.weight PEAddres.weight ≤
          R.rightDegree * rightWord.weight PEAddres.weight :=
      Nat.mul_le_mul_right _ htwo
    omega

/--
Every temporary output whose recipe is not of bidegree `(1, 1)` is strictly
heavier than the original outer bracket.
-/
lemma outer_reword_bidegree
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hdegree : R.leftDegree ≠ 1 ∨ R.rightDegree ≠ 1) :
    outerExpansion.word.weight PEAddres.weight <
      (wordExpansion hinputWeight R (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord)).word.weight
          PEAddres.weight := by
  apply lt_of_le_of_ne
    (outer_expansion_reword
      hinputWeight R outerExpansion innerWord rightWord hword)
  intro heq
  have hone :=
    left_expansion_reword
      hinputWeight R outerExpansion innerWord rightWord hword heq.symm
  exact hdegree.elim (fun hleft => hleft hone.1) (fun hright => hright hone.2)

end PTSubsti

namespace PFSubsti.TAPkt

open IPBridge
open PTSubsti

/--
The transient powered-bridge quotient: inverse temporary correction followed
by the original outer carrier.
-/
def transientInnerReduction
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (wordExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (TWExp H inputWeight) :=
  TWExp.inverseList
      (packet.transientWordExpansions hinputWeight
        (wordExpansion.reword innerWord)
        (TWExp.wordUnit rightWord)) ++
    [wordExpansion]

/--
Every carrier in the transient quotient source is physically supported at
the original outer-bracket weight.
-/
theorem
    transient_inner_reduction
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
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        packet.transientInnerReduction hinputWeight
          wordExpansion innerWord rightWord) :
    wordExpansion.word.weight PEAddres.weight ≤
      nextExpansion.word.weight PEAddres.weight := by
  rw [transientInnerReduction] at hnext
  rcases List.mem_append.mp hnext with hnext | hnext
  · rw [TWExp.inverseList] at hnext
    rcases List.mem_map.mp hnext with ⟨sourceExpansion, hsource, rfl⟩
    rw [TWExp.word_neg]
    have hsource' :
        sourceExpansion ∈
          packet.transientWordExpansions hinputWeight
            (wordExpansion.reword innerWord)
            (TWExp.wordUnit rightWord) := by
      simpa using hsource
    rw [transientWordExpansions] at hsource'
    rcases recipe_word_expansions hsource' with
      ⟨R, _hR, rfl⟩
    exact
      outer_expansion_reword
        hinputWeight R wordExpansion innerWord rightWord hword
  · simp only [List.mem_singleton] at hnext
    subst nextExpansion
    exact le_rfl

/--
The transient residual is exactly the quotient of `[inner ^ e, right]` from
the original outer carrier.
-/
lemma transient_inner_raw
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
    TWExp.listValue (n := n) q
        (packet.transientInnerReduction hinputWeight
          wordExpansion innerWord rightWord) =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          wordExpansion.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆⁻¹ *
        wordExpansion.value q := by
  rw [transientInnerReduction]
  simp only [TWExp.listValue,
    List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  change
    TWExp.listValue (n := n) q
          (TWExp.inverseList
            (packet.transientWordExpansions hinputWeight
              (wordExpansion.reword innerWord)
              (TWExp.wordUnit rightWord))) *
        wordExpansion.value (n := n) q =
      _
  rw [TWExp.list_value_inverse,
    packet.transient_word_expansions]
  simp [TWExp.value]
  rfl

/--
When the outer carrier is the bracket `[inner, right]`, its powered-bridge
quotient lies one lower-central layer above the outer bracket weight.
-/
theorem
    transient_inner_series
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
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (packet.transientInnerReduction hinputWeight
          wordExpansion innerWord rightWord) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (wordExpansion.word.weight PEAddres.weight) := by
  let K :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (wordExpansion.word.weight PEAddres.weight)
  let temporary :=
    ⁅innerWord.eval
          (PEAddres.freeLowerTruncation
            (n := n)) ^
        wordExpansion.exponent q,
      rightWord.eval
        (PEAddres.freeLowerTruncation
          (n := n))⁆
  let parent := wordExpansion.value (n := n) q
  have hforward : temporary * parent⁻¹ ∈ K := by
    simpa [K, temporary, parent,
      TWExp.value, hword] using
      (eval_zpow_series
        (n := n) innerWord rightWord (wordExpansion.exponent q))
  have hinverse : (temporary * parent⁻¹)⁻¹ ∈ K :=
    K.inv_mem hforward
  have hconj :
      temporary⁻¹ * (temporary * parent⁻¹)⁻¹ * (temporary⁻¹)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem
      (temporary * parent⁻¹)⁻¹ hinverse temporary⁻¹
  rw [packet.transient_inner_raw]
  change temporary⁻¹ * parent ∈ K
  have heq :
      temporary⁻¹ * (temporary * parent⁻¹)⁻¹ * (temporary⁻¹)⁻¹ =
        temporary⁻¹ * parent := by
    group
  simpa only [heq] using hconj

end PFSubsti.TAPkt

end TCTex
end Towers
