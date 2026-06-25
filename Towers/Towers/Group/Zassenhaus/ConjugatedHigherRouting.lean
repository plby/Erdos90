import Towers.Group.Zassenhaus.RestrictedSharp
import Towers.Group.Zassenhaus.FactorSourceReduction

/-!
# Conjugating recollected symbolic Hall-power higher tails

Suppose a symbolic source has already been recollected one stratum higher.
Conjugating that source by an active factor appears to reintroduce a
same-weight factor on each side.  The sharp higher-tail router removes those
wrappers operationally: move the right conjugator left across the recollected
higher tail, then cancel it semantically with the inverse conjugator.

This file packages the resulting upward recollection independently of any
particular concrete Hall-tree reduction.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactora

/-- A symbolic source conjugated by one factor. -/
def conjugatedRawSource
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (conjugator : SPFactora H inputWeight)
    (source : List (SPFactora H inputWeight)) :
    List (SPFactora H inputWeight) :=
  [conjugator.neg] ++ source ++ [conjugator]

end SPFactora

/--
An upward semantic recollection of a source conjugated by an active symbolic
Hall-power factor.
-/
structure SupportedSemanticConjugated
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (conjugator : SPFactora H inputWeight)
    (rawSource : List (SPFactora H inputWeight)) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (lowerWeight + 1) higherSource
  higher_conjugated_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (SPFactora.conjugatedRawSource conjugator rawSource)

namespace SSHigher

/--
A sharp route moving the right conjugator across a recollected higher source
supplies an upward recollection of the conjugated raw source.
-/
noncomputable def conjugatedRecollection
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {higherSource rawSource : List (SPFactora H inputWeight)}
    {conjugator : SPFactora H inputWeight}
    (route :
      SSHigher
        (n := n) (lowerWeight := lowerWeight) H higherSource conjugator)
    (hhigherSourceTruncated :
      SPFactora.IsTruncated n higherSource)
    (hconjugatorTruncated :
      conjugator.word.weight PEAddres.weight < n)
    (hhigherSourceEval :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q higherSource =
          SPFactora.listEval q rawSource) :
    SupportedSemanticConjugated
      (n := n) (lowerWeight := lowerWeight) H conjugator rawSource where
  higherSource := route.higherSource
  higher_source_truncated := by
    have hrouteTruncated :
        SPFactora.IsTruncated n
          ([conjugator] ++ route.higherSource) :=
      route.inserts.isTruncated hhigherSourceTruncated hconjugatorTruncated
    intro x hx
    exact hrouteTruncated x (by simp [hx])
  higher_least_succ :=
    route.higher_least_succ
  higher_conjugated_raw := by
    intro q
    have hroute := route.inserts.listEval_eq q
    simp only [SPFactora.conjugatedRawSource,
      SPFactora.listEval_append,
      SPFactora.listEval_cons,
      SPFactora.listEval_nil, mul_one,
      SPFactora.eval_neg] at hroute ⊢
    rw [← hhigherSourceEval q]
    calc
      SPFactora.listEval (n := n) q route.higherSource =
          (conjugator.eval q)⁻¹ *
            (conjugator.eval q *
              SPFactora.listEval q route.higherSource) := by
        group
      _ =
          (conjugator.eval q)⁻¹ *
            (SPFactora.listEval q higherSource *
              conjugator.eval q) := by
        rw [hroute]
      _ =
          (conjugator.eval q)⁻¹ *
              SPFactora.listEval q higherSource *
            conjugator.eval q := by
        group

end SSHigher

namespace TSFtrya

/--
Sharp higher-tail routing recollects a conjugated source from any upward
recollection of its unconjugated body.
-/
noncomputable def conjugated_recollection_normalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H)
    (conjugator : SPFactora H inputWeight)
    (hconjugatorWeight :
      conjugator.word.weight PEAddres.weight = lowerWeight)
    (hconjugatorTruncated :
      conjugator.word.weight PEAddres.weight < n)
    (rawSource higherSource :
      List (SPFactora H inputWeight))
    (hhigherSourceTruncated :
      SPFactora.IsTruncated n higherSource)
    (hhigherSourceSupported :
      SPFactora.WordWeightLeast
        (lowerWeight + 1) higherSource)
    (hhigherSourceEval :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q higherSource =
          SPFactora.listEval q rawSource) :
    SupportedSemanticConjugated
      (n := n) (lowerWeight := lowerWeight) H conjugator rawSource :=
  (factory.semantic_higher_normalizer
      sharp conjugator hconjugatorWeight higherSource hhigherSourceSupported
    |>.conjugatedRecollection
      hhigherSourceTruncated hconjugatorTruncated hhigherSourceEval)

end TSFtrya

end TCTex
end Towers
