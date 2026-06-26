import Towers.Group.Zassenhaus.SemanticObstructionScheduling

/-!
# Weight strata of normalized symbolic Hall power endpoints

Normalized coordinate endpoints are concatenated in increasing ordinary Hall
weight.  A one-stratum scheduler needs to separate the already-visible prefix
through weight `lowerWeight` from the strictly higher tail.

This file packages that decomposition and its support properties.  When an
endpoint has no terms below `lowerWeight`, its visible prefix is exactly its
weight-`lowerWeight` block and every tail factor lies in the next support
stratum.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace CCExpans

/-- Normalized endpoint factors in weights strictly above `lowerWeight`. -/
def tailFactors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (lowerWeight : ℕ) :
    List (SPFactora H inputWeight) :=
  (List.range' lowerWeight (n - 1 - lowerWeight)).flatMap fun s =>
    R.weightFactors (s + 1)

/-- The prefix and higher tail concatenate back to the complete endpoint. -/
lemma factors_append_tail
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (hlowerWeight : lowerWeight ≤ n - 1) :
    R.factors (n := n) =
      R.prefixFactors lowerWeight ++ R.tailFactors (n := n) lowerWeight := by
  have hrange :
      List.range lowerWeight ++
          List.range' lowerWeight (n - 1 - lowerWeight) =
        List.range (n - 1) := by
    rw [List.range_eq_range', List.range_eq_range']
    simpa [Nat.add_sub_of_le hlowerWeight] using
      (List.range'_append
        (s := 0) (m := lowerWeight) (n := n - 1 - lowerWeight) (step := 1))
  unfold factors prefixFactors tailFactors
  rw [← List.flatMap_append, hrange]

/-- Every higher-tail factor has weight at least the next support stratum. -/
lemma word_tail_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    {x : SPFactora H inputWeight}
    (hx : x ∈ R.tailFactors (n := n) lowerWeight) :
    lowerWeight + 1 ≤ x.word.weight PEAddres.weight := by
  rcases List.mem_flatMap.mp hx with ⟨s, hs, hx⟩
  rw [R.word_weight_factors hx]
  have hsLower : lowerWeight ≤ s :=
    List.left_le_of_mem_range' hs
  omega

/-- The normalized higher tail is supported one stratum above the prefix. -/
lemma word_least_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight) :
    SPFactora.WordWeightLeast (lowerWeight + 1)
      (R.tailFactors (n := n) lowerWeight) :=
  fun _ hx => R.word_tail_factors hx

/-- Higher-tail factors are physically below the quotient cutoff. -/
lemma truncated_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (hlowerWeight : lowerWeight ≤ n - 1) :
    SPFactora.IsTruncated n
      (R.tailFactors (n := n) lowerWeight) := by
  intro x hx
  apply R.isTruncated_factors
  rw [R.factors_append_tail hlowerWeight]
  exact List.mem_append_right _ hx

/-- The higher endpoint tail evaluates to the ordinary collected Hall tail. -/
lemma list_tail_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (q lowerWeight : ℕ) :
    SPFactora.listEval (n := n) q
        (R.tailFactors (n := n) lowerWeight) =
      collectedTailProduct (n := n) H (R.eval q) lowerWeight := by
  unfold tailFactors collectedTailProduct
  induction (List.range' lowerWeight (n - 1 - lowerWeight)) with
  | nil =>
      simp
  | cons s weights ih =>
      simp only [List.flatMap_cons, List.map_cons, List.prod_cons,
        SPFactora.listEval_append]
      rw [R.list_weight_factors, ih]

/-- If one layer is below the endpoint support, its normalized block is empty. -/
lemma nil_terms_below
    {d inputWeight lowerWeight s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (R : CCExpans H inputWeight)
    (hR : R.NTBelow lowerWeight)
    (hs : s < lowerWeight) :
    R.weightFactors s = [] := by
  rw [weightFactors]
  apply List.flatMap_eq_nil_iff.2
  intro i _hi
  unfold BCExp.symbolicPowerFactors
  rw [hR s i hs]
  rfl

/--
If no terms occur below a positive support stratum, the endpoint prefix through
that stratum consists exactly of its current-weight block.
-/
lemma prefix_no_below
    {d inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (hR : R.NTBelow lowerWeight)
    (hlowerWeight : 1 ≤ lowerWeight) :
    R.prefixFactors lowerWeight = R.weightFactors lowerWeight := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : lowerWeight ≠ 0)
  rw [prefixFactors, List.range_succ, List.flatMap_append,
    List.flatMap_singleton]
  have hprevious :
      (List.range k).flatMap (fun s => R.weightFactors (s + 1)) = [] := by
    apply List.flatMap_eq_nil_iff.2
    intro s hs
    apply R.nil_terms_below hR
    have hsRange := List.mem_range.mp hs
    omega
  rw [hprevious, List.nil_append]

/--
A supported normalized endpoint splits into its current layer followed by a
tail supported one stratum higher.
-/
lemma append_no_below
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (hR : R.NTBelow lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightCutoff : lowerWeight ≤ n - 1) :
    R.factors (n := n) =
      R.weightFactors lowerWeight ++ R.tailFactors (n := n) lowerWeight := by
  rw [R.factors_append_tail hlowerWeightCutoff,
    R.prefix_no_below hR hlowerWeightPos]

end CCExpans

end TCTex
end Towers
