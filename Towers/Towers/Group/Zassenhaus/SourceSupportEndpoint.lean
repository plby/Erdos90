import Towers.Group.Zassenhaus.SourceSupportRaising

/-!
# Endpoint support raising for symbolic recollections

Finite support raising is most convenient to consume by naming its target
stratum directly.  This file packages the subtraction arithmetic needed to
reach any semantically justified endpoint from an initial recollection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TSRecol

/--
Raise a recollected source directly to a chosen semantic support endpoint.
Normalizers are required only from the initial physical support upward.
-/
noncomputable def raiseSupportTo
    {d n inputWeight initialWeight targetWeight : ℕ}
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
    (hinitialWeightPos : 1 ≤ initialWeight)
    (hinitialTarget : initialWeight ≤ targetWeight)
    (htargetTruncated : targetWeight ≤ n)
    (hrawSourceMem :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q rawSource ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (targetWeight - 1)) :
    TSRecol
      (n := n) (lowerWeight := targetWeight) H rawSource := by
  have htarget :
      initialWeight + (targetWeight - initialWeight) = targetWeight :=
    Nat.add_sub_of_le hinitialTarget
  let raised :=
    recollection.raiseSupportBy hn H hH normalizerFrom hinitialWeightPos
      (targetWeight - initialWeight)
      (by simpa only [htarget] using htargetTruncated)
      (by simpa only [htarget] using hrawSourceMem)
  simpa only [htarget] using raised

end TSRecol
end TCTex
end Towers
