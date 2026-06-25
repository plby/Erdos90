import Towers.Group.Zassenhaus.SemanticallyHigherRecollection
import Towers.Group.Zassenhaus.SourceRecollectionComposition

/-!
# Raising support of semantically deeper symbolic recollections

After one operational rewrite removes same-stratum wrappers, a source may be
physically supported above its original stratum while its value is known to
lie much deeper in the lower-central filtration.  Repeatedly normalize the
current physical stratum and discard its vanishing active block until the
full semantic support bound is reached.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TSRecol

/-- Compose two semantic source recollections. -/
noncomputable def trans
    {d n inputWeight firstWeight secondWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {rawSource : List (SPFactora H inputWeight)}
    (first :
      TSRecol
        (n := n) (lowerWeight := firstWeight) H rawSource)
    (second :
      TSRecol
        (n := n) (lowerWeight := secondWeight) H first.higherSource) :
    TSRecol
      (n := n) (lowerWeight := secondWeight) H rawSource where
  higherSource := second.higherSource
  higher_source_truncated := second.higher_source_truncated
  higher_weight_least :=
    second.higher_weight_least
  list_higher_raw := by
    intro q
    rw [second.list_higher_raw,
      first.list_higher_raw]

/--
Raise a recollected source by one support stratum when its value lies one
lower-central layer above the current physical support.
-/
noncomputable def succOfNormalizer
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H)
    {rawSource : List (SPFactora H inputWeight)}
    (recollection :
      TSRecol
        (n := n) (lowerWeight := lowerWeight) H rawSource)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hrawSourceMem :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q rawSource ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1) H rawSource :=
  recollection.trans
    (normalizer.source_recollection_series
      hn H hH recollection.higherSource hlowerWeightPos
        hlowerWeightTruncated recollection.higher_source_truncated
          recollection.higher_weight_least
            (fun q => by
              rw [recollection.list_higher_raw]
              exact hrawSourceMem q))

/--
Raise a recollected source through finitely many semantically vanishing
strata.  A normalizer is required only from the initial physical support
upward.
-/
noncomputable def raiseSupportBy
    {d n inputWeight initialWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (normalizerFrom :
      ∀ strongerWeight : ℕ,
        initialWeight ≤ strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight) H)
    {rawSource : List (SPFactora H inputWeight)}
    (recollection :
      TSRecol
        (n := n) (lowerWeight := initialWeight) H rawSource)
    (hinitialWeightPos : 1 ≤ initialWeight) :
    ∀ steps : ℕ,
      initialWeight + steps ≤ n →
        (∀ q : ℕ,
          SPFactora.listEval (n := n) q rawSource ∈
            Subgroup.lowerCentralSeries
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
              (initialWeight + steps - 1)) →
          TSRecol
            (n := n) (lowerWeight := initialWeight + steps) H rawSource
  | 0, _htargetTruncated, _hrawSourceMem => by
      simpa using recollection
  | steps + 1, htargetTruncated, hrawSourceMem => by
      have hinitialWeightTruncated : initialWeight < n := by
        omega
      let next :=
        recollection.succOfNormalizer hn H hH
          (normalizerFrom initialWeight (Nat.le_refl _))
          hinitialWeightPos hinitialWeightTruncated
          (fun q =>
            Subgroup.lowerCentralSeries_antitone (by omega) (hrawSourceMem q))
      let raised :=
        next.raiseSupportBy hn H hH
          (fun strongerWeight hstrongerWeight =>
            normalizerFrom strongerWeight (by omega))
          (by omega) steps (by omega)
          (by
            intro q
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              hrawSourceMem q)
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using raised

end TSRecol
end TCTex
end Towers
