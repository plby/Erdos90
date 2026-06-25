import Towers.Group.Zassenhaus.ConjugatedHigherRouting

/-!
# Conjugating recollected higher tails by symbolic factor lists

An attachable transient exponent generally expands into a finite list of
ordinary symbolic factors on one Hall word, rather than a single factor.
This file iterates the one-factor sharp higher-tail router without changing
the order of the represented parent product.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactora

/--
Conjugate a symbolic source successively by a list of factors.  The first
factor is the innermost conjugator, so the resulting value is conjugation by
the ordered product of the complete list.
-/
def conjugatedRawList
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    List (SPFactora H inputWeight) →
      List (SPFactora H inputWeight) →
        List (SPFactora H inputWeight)
  | [], source => source
  | conjugator :: conjugators, source =>
      conjugatedRawList conjugators
        (conjugatedRawSource conjugator source)

/-- Successive source conjugation agrees with conjugation by the list product. -/
lemma conjugated_raw_source
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (q : ℕ)
    (conjugators source : List (SPFactora H inputWeight)) :
    listEval (n := n) q (conjugatedRawList conjugators source) =
      (listEval q conjugators)⁻¹ * listEval q source *
        listEval q conjugators := by
  induction conjugators generalizing source with
  | nil =>
      simp [conjugatedRawList]
  | cons conjugator conjugators ih =>
      rw [conjugatedRawList, ih]
      simp only [conjugatedRawSource, listEval_append, listEval_cons,
        listEval_nil, eval_neg, mul_one]
      group

end SPFactora

/--
An upward semantic recollection of a source conjugated by an ordered list of
active symbolic Hall-power factors.
-/
structure
    TruncatedConjugatedRecollection
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (conjugators rawSource : List (SPFactora H inputWeight)) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (lowerWeight + 1) higherSource
  list_conjugated_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (SPFactora.conjugatedRawList conjugators rawSource)

namespace TSFtrya

/--
Iterate sharp higher-tail routing over a finite ordered conjugator list.
-/
noncomputable def
    conjugated_sharp_normalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H) :
    ∀ (conjugators rawSource higherSource :
        List (SPFactora H inputWeight)),
      (∀ conjugator ∈ conjugators,
        conjugator.word.weight PEAddres.weight =
          lowerWeight) →
      SPFactora.IsTruncated n conjugators →
      SPFactora.IsTruncated n higherSource →
      SPFactora.WordWeightLeast
        (lowerWeight + 1) higherSource →
      (∀ q : ℕ,
        SPFactora.listEval (n := n) q higherSource =
          SPFactora.listEval q rawSource) →
      TruncatedConjugatedRecollection
        (n := n) (lowerWeight := lowerWeight) H conjugators rawSource
  | [], rawSource, higherSource, _, _, hhigherSourceTruncated,
      hhigherSourceSupported, hhigherSourceEval =>
        { higherSource := higherSource
          higher_source_truncated := hhigherSourceTruncated
          higher_least_succ := hhigherSourceSupported
          list_conjugated_raw := by
            intro q
            simpa [SPFactora.conjugatedRawList] using
              hhigherSourceEval q }
  | conjugator :: conjugators, rawSource, higherSource, hconjugatorWeights,
      hconjugatorsTruncated, hhigherSourceTruncated,
      hhigherSourceSupported, hhigherSourceEval => by
        let head :=
          factory.conjugated_recollection_normalizer
            sharp conjugator (hconjugatorWeights conjugator (by simp))
              (hconjugatorsTruncated conjugator (by simp))
                rawSource higherSource hhigherSourceTruncated
                  hhigherSourceSupported hhigherSourceEval
        let tail :=
          conjugated_sharp_normalizer
            factory sharp conjugators
              (SPFactora.conjugatedRawSource conjugator rawSource)
                head.higherSource
                  (fun next hnext =>
                    hconjugatorWeights next (by simp [hnext]))
                  (fun next hnext =>
                    hconjugatorsTruncated next (by simp [hnext]))
                  head.higher_source_truncated
                  head.higher_least_succ
                  head.higher_conjugated_raw
        exact
          { higherSource := tail.higherSource
            higher_source_truncated := tail.higher_source_truncated
            higher_least_succ :=
              tail.higher_least_succ
            list_conjugated_raw := by
              intro q
              simpa [SPFactora.conjugatedRawList] using
                tail.list_conjugated_raw q }

end TSFtrya

end TCTex
end Towers
