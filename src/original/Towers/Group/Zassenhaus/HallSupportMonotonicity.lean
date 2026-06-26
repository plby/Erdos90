import Towers.Group.Zassenhaus.HallRankDescent
import Towers.Group.Zassenhaus.Packet

/-!
# Support monotonicity for Hall-ranked residual descent

Hall-ranked recursion orders residual tasks lexicographically by cutoff defect
and a finite Hall-bracket defect. Below the physical cutoff, every descending
task therefore has ordinary word weight at least that of its parent. This is
the support invariant needed to restrict residual routing to tasks reachable
from one active stratum.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/-- A descending signed-polynomial residual task remains in the parent support stratum. -/
lemma word_ranked_descends
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {child parent : SPFactor H ι}
    {childRankDefect parentRankDefect : ℕ}
    (hparentTruncated :
      parent.word.weight HEAddres.weight < n)
    (hdescends :
      HallRankedDescends n child childRankDefect parent parentRankDefect) :
    parent.word.weight HEAddres.weight ≤
      child.word.weight HEAddres.weight := by
  rcases Prod.lex_def.mp hdescends with hdefect | ⟨hdefect, _hrank⟩
  · simp only [hallRankedMeasure, cutoffDefect] at hdefect
    omega
  · simp only [hallRankedMeasure, cutoffDefect] at hdefect
    omega

end SPFactor

namespace SPFactora

/-- A descending Hall-power residual task remains in the parent support stratum. -/
lemma word_ranked_descends
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {child parent : SPFactora H inputWeight}
    {childRankDefect parentRankDefect : ℕ}
    (hparentTruncated :
      parent.word.weight PEAddres.weight < n)
    (hdescends :
      HallRankedDescends n child childRankDefect parent parentRankDefect) :
    parent.word.weight PEAddres.weight ≤
      child.word.weight PEAddres.weight := by
  rcases Prod.lex_def.mp hdescends with hdefect | ⟨hdefect, _hrank⟩
  · simp only [hallRankedMeasure, cutoffDefect] at hdefect
    omega
  · simp only [hallRankedMeasure, cutoffDefect] at hdefect
    omega

end SPFactora

end TCTex
end Towers
