import Towers.Group.Zassenhaus.Active
import Towers.Group.Zassenhaus.RewriteMembership

/-!
# Recollecting intrinsic symbolic Hall-factor residuals

The intrinsic residual of one symbolic Hall factor is represented by a
concrete source word: invert its canonical active Hall block and append the
original factor.  This file isolates the remaining operational collection
obligation.  A truncated rewrite of that concrete source into factors of
strictly larger weight compiles to the semantic factor-residual expansion used
by the recursive collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SPFactora

/-- Negate the signed exponent carried by one symbolic Hall power factor. -/
def neg
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factor : SPFactora H inputWeight) :
    SPFactora H inputWeight where
  word := factor.word
  coefficient := -factor.coefficient
  recipe := factor.recipe

@[simp]
lemma word_neg
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factor : SPFactora H inputWeight) :
    factor.neg.word = factor.word :=
  rfl

@[simp]
lemma exponent_neg
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factor : SPFactora H inputWeight)
    (q : ℕ) :
    factor.neg.exponent q = -factor.exponent q := by
  simp [neg, exponent]

@[simp]
lemma wordValue_neg
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factor : SPFactora H inputWeight) :
    factor.neg.wordValue (n := n) = factor.wordValue :=
  rfl

@[simp]
lemma eval_neg
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factor : SPFactora H inputWeight)
    (q : ℕ) :
    factor.neg.eval (n := n) q = (factor.eval q)⁻¹ := by
  simp [eval]

/-- Reverse a symbolic factor list while negating every signed exponent. -/
def inverseList
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (source : List (SPFactora H inputWeight)) :
    List (SPFactora H inputWeight) :=
  source.reverse.map neg

/-- The symbolic inverse list evaluates to the inverse group element. -/
lemma list_eval_inverse
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (source : List (SPFactora H inputWeight))
    (q : ℕ) :
    listEval (n := n) q (inverseList source) = (listEval q source)⁻¹ := by
  induction source with
  | nil =>
      rfl
  | cons factor source ih =>
      rw [show inverseList (factor :: source) = inverseList source ++ [factor.neg] by
        simp [inverseList]]
      simp [ih]

/-- Inversion preserves physical truncation of symbolic source lists. -/
lemma truncated_inverse_list
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {source : List (SPFactora H inputWeight)}
    (hsource : IsTruncated n source) :
    IsTruncated n (inverseList source) := by
  intro factor hfactor
  rw [inverseList] at hfactor
  rcases List.mem_map.mp hfactor with ⟨sourceFactor, hsourceFactor, rfl⟩
  exact hsource sourceFactor (by simpa using hsourceFactor)

/--
The intrinsic Hall-normal residual source: inverse active Hall layer followed
by the original symbolic factor.
-/
noncomputable def activeRawSource
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (lowerWeight : ℕ) :
    List (SPFactora H inputWeight) :=
  inverseList
      ((factor.normalCoordinateExpansions hn H hH).weightFactors lowerWeight) ++
    [factor]

/-- The concrete residual source evaluates to the intrinsic residual value. -/
lemma active_raw_source
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (lowerWeight q : ℕ) :
    listEval (n := n) q
        (factor.activeRawSource
          hn H hH lowerWeight) =
      CCExpans.activeBlockValue
        hn H hH factor lowerWeight q := by
  simp [activeRawSource,
    CCExpans.activeBlockValue,
    CCExpans.activeNormalValue,
    list_eval_inverse]

/-- A truncated factor has a physically truncated intrinsic residual source. -/
lemma truncated_active_source
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    IsTruncated n
      (factor.activeRawSource hn H hH lowerWeight) := by
  intro residualFactor hresidualFactor
  rcases List.mem_append.mp hresidualFactor with hactive | hfactor
  · apply
      truncated_inverse_list
        (source :=
          (factor.normalCoordinateExpansions hn H hH).weightFactors lowerWeight)
        (by
          intro activeFactor hactiveFactor
          rw [(factor.normalCoordinateExpansions hn H hH).word_weight_factors
            hactiveFactor, ← hfactorWeight]
          exact hfactorTruncated)
        residualFactor hactive
  · simp only [List.mem_singleton] at hfactor
    subst residualFactor
    exact hfactorTruncated

end SPFactora

/--
Swap-only collection cannot recollect the intrinsic residual source to a
strictly heavier list: it preserves the original active-weight factor.
-/
lemma
    TSRwa.notfactor_residsource_highersource
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (higherSource : List (SPFactora H inputWeight))
    (hhigherSource :
      SPFactora.WordWeightLeast (lowerWeight + 1)
        higherSource) :
    ¬
    TSRwa (n := n)
      (factor.activeRawSource hn H hH lowerWeight)
      higherSource := by
  intro hrewrites
  have hfactorMem :
      factor ∈
        factor.activeRawSource hn H hH
          lowerWeight := by
    simp [SPFactora.activeRawSource]
  have hfactorMemHigher := hrewrites.mem_of_mem hfactorMem
  have hfactorHigher := hhigherSource factor hfactorMemHigher
  omega

/--
Semantic recollection data for the concrete intrinsic residual source.  A full
Hall collector must compress that source into a strictly heavier list using an
operation beyond adjacent swaps.
-/
structure
    TSSrc
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (factor.activeRawSource hn H hH lowerWeight)

namespace
  TSSrc

/--
Compile recollection of the concrete intrinsic residual source into the
higher-source package consumed by active-block recursion.
-/
def factorExpansion
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {factor : SPFactora H inputWeight}
    (recollection :
      TSSrc
        (lowerWeight := lowerWeight) hn H hH factor) :
    TSExp
      (lowerWeight := lowerWeight) hn H hH factor where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_least_succ :=
    recollection.higher_least_succ
  list_factor_value q :=
    (recollection.list_higher_raw q).trans
      (factor.active_raw_source
        hn H hH lowerWeight q)

/-- Present an intrinsic residual expansion as recollection of its concrete source. -/
def factorResidualExpansion
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {factor : SPFactora H inputWeight}
    (expansion :
      TSExp
        (lowerWeight := lowerWeight) hn H hH factor) :
    TSSrc
      (lowerWeight := lowerWeight) hn H hH factor where
  higherSource := expansion.higherSource
  higher_source_truncated := expansion.higher_source_truncated
  higher_least_succ :=
    expansion.higher_least_succ
  list_higher_raw q :=
    (expansion.list_factor_value q).trans
      (factor.active_raw_source
        hn H hH lowerWeight q).symm

open
  TSExp

private noncomputable def terminalResidualExpansion
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSExp
      (lowerWeight := lowerWeight) hn H hH factor :=
  of_highWeight hn H hH hcutoff factor hfactorWeight hfactorTruncated

/--
In the terminal high-weight range, the semantic Hall tail recollects the
concrete intrinsic residual source.
-/
noncomputable def of_highWeight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSSrc
      (lowerWeight := lowerWeight) hn H hH factor :=
  factorResidualExpansion
    (terminalResidualExpansion
      hn H hH hcutoff factor hfactorWeight hfactorTruncated)

end
  TSSrc

end TCTex
end Towers
