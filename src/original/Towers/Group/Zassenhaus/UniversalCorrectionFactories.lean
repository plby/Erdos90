import Towers.Group.Zassenhaus.SemanticInsertionDerivations
import Towers.Group.Zassenhaus.WordExpansions

/-!
# Universal higher-word correction factories for symbolic Hall powers

The arithmetic part of repeated-power Hall collection is already explicit:
once a higher commutator word is assigned a finite correction formula, its
generalized-binomial exponent normalizes to a bounded repeated-block recipe.

The remaining group-theoretic input is the universal collection identity for
one powered adjacent swap.  This file states that input at two useful levels.
A general factory returns an ordered finite list of higher-word expansions.  A
single-word factory is a convenient specialization when one correction word
and one finite correction formula suffice.

Both interfaces compile to the physically truncated supported packet factory
consumed by semantic insertion scheduling.  The file is intentionally not
imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

/--
Universal collection data for supported powered adjacent swaps: an ordered
finite list of strictly higher symbolic words whose explicit recipe
expansions evaluate to the required commutator correction.
-/
structure SEFtry
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (lowerWeight : ℕ) where
  wordExpansions :
    ∀ (B A : SPFactora H inputWeight),
      lowerWeight ≤ B.word.weight PEAddres.weight →
      lowerWeight ≤ A.word.weight PEAddres.weight →
        List (SWExp H inputWeight)
  listValue_eq :
    ∀ (B A : SPFactora H inputWeight)
      (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
      (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
      (q : ℕ),
        SWExp.listValue (n := n) q
            (wordExpansions B A hB hA) =
          ⁅B.eval (n := n) q, A.eval (n := n) q⁆
  word_weight_left :
    ∀ (B A : SPFactora H inputWeight)
      (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
      (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
      (wordExpansion : SWExp H inputWeight),
        wordExpansion ∈ wordExpansions B A hB hA →
          B.word.weight PEAddres.weight <
            wordExpansion.word.weight PEAddres.weight
  word_weight_right :
    ∀ (B A : SPFactora H inputWeight)
      (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
      (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
      (wordExpansion : SWExp H inputWeight),
        wordExpansion ∈ wordExpansions B A hB hA →
          A.word.weight PEAddres.weight <
            wordExpansion.word.weight PEAddres.weight

namespace SEFtry

/--
Attach the explicit recipe expansions and erase factors reaching the quotient
cutoff.  The result is exactly the supported packet supply expected by the
one-stratum semantic collector.
-/
def correctionPacketFactory
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      SEFtry
        (n := n) (inputWeight := inputWeight) H lowerWeight) :
    TSFtrya
      (n := n) (inputWeight := inputWeight) H lowerWeight where
  packet B A hB hA :=
    (SHPkt.ofWordExpansions B A
      (factory.wordExpansions B A hB hA)
      (factory.listValue_eq B A hB hA)
      (factory.word_weight_left B A hB hA)
      (factory.word_weight_right B A hB hA)).truncate

/--
Universal higher-word collection data therefore supplies one delegated
normalized semantic adjacent rewrite.
-/
lemma supported_semantic_rewrites
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      SEFtry
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight) :
    ∃ normalization :
        TSNorma
          lowerWeight
            (factory.correctionPacketFactory.packet B A hB hA),
      SCRw
        (n := n) (lowerWeight := lowerWeight)
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.factors (n := n) ++ [A, B] ++ S) :=
  factory.correctionPacketFactory.supported_semantic_rewrites
    normalizer P S B A hB hA

/--
Universal higher-word collection data reduces one obstructed list-valued
insertion to routing its normalized higher correction endpoint.
-/
lemma semantic_inserts_obstruction
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      SEFtry
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (P : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
    (hcontinue :
      ∀ normalization :
          TSNorma
            lowerWeight
              (factory.correctionPacketFactory.packet B A hB hA),
        ∃ Q R : List (SPFactora H inputWeight),
          SBInsert
              (n := n) H inputWeight lowerWeight P
                (normalization.coordinates.factors (n := n)) Q ∧
            SSInsertc
              (n := n) H inputWeight lowerWeight Q A R) :
    ∃ R : List (SPFactora H inputWeight),
      SSInsertc
        (n := n) H inputWeight lowerWeight (P ++ [B]) A R :=
  factory.correctionPacketFactory.semantic_inserts_obstruction
    normalizer P B A hB hA hcontinue

end SEFtry

/--
Convenient universal collection data when one strictly higher output word and
one finite generalized-binomial correction formula represent each supported
adjacent swap.
-/
structure SFFtry
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (lowerWeight : ℕ) where
  word :
    ∀ (B A : SPFactora H inputWeight),
      lowerWeight ≤ B.word.weight PEAddres.weight →
      lowerWeight ≤ A.word.weight PEAddres.weight →
        CWord (HEAddres H)
  formula :
    ∀ (B A : SPFactora H inputWeight)
      (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
      (hA : lowerWeight ≤ A.word.weight PEAddres.weight),
        SCForm H inputWeight
          ((word B A hB hA).weight PEAddres.weight)
  formula_eval_eq :
    ∀ (B A : SPFactora H inputWeight)
      (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
      (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
      (q : ℕ),
        (word B A hB hA).eval
              PEAddres.freeLowerTruncation ^
            (formula B A hB hA).eval q =
          ⁅B.eval (n := n) q, A.eval (n := n) q⁆
  word_weight_left :
    ∀ (B A : SPFactora H inputWeight)
      (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
      (hA : lowerWeight ≤ A.word.weight PEAddres.weight),
        B.word.weight PEAddres.weight <
          (word B A hB hA).weight PEAddres.weight
  word_weight_right :
    ∀ (B A : SPFactora H inputWeight)
      (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
      (hA : lowerWeight ≤ A.word.weight PEAddres.weight),
        A.word.weight PEAddres.weight <
          (word B A hB hA).weight PEAddres.weight

namespace SFFtry

/-- A one-word universal correction formula supplies a truncated packet factory. -/
noncomputable def correctionPacketFactory
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 0 < inputWeight)
    (factory :
      SFFtry
        (n := n) (inputWeight := inputWeight) H lowerWeight) :
    TSFtrya
      (n := n) (inputWeight := inputWeight) H lowerWeight where
  packet B A hB hA :=
    (SHPkt.ofWordFormula hinputWeight B A
      (factory.word B A hB hA) (factory.formula B A hB hA)
      (factory.formula_eval_eq B A hB hA)
      (factory.word_weight_left B A hB hA)
      (factory.word_weight_right B A hB hA)).truncate

end SFFtry

end TCTex
end Towers
