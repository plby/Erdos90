import Towers.Group.Zassenhaus.UniversalCollectionReduction

/-!
# Canonical higher-tail splicing for symbolic Hall power coordinates

At one active Hall-weight stratum, inserting a strictly heavier factor does
not change the current coordinate block.  The existing higher tail and the new
factor can be delegated together to the next-stratum semantic normalizer, then
spliced back above the untouched active block.

This file implements that canonical splice, proves its exact factor-list
equation, and constructs the strictly-heavier insertion branch.  It reduces a
full one-stratum insertion kernel to the genuinely difficult active-weight
branch.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace CCExpans

/--
Keep the base coordinates through `lowerWeight` and use `higher` strictly
above that stratum.
-/
def spliceHigherTail
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (base higher : CCExpans H inputWeight)
    (lowerWeight : ℕ) :
    CCExpans H inputWeight where
  expansion s i :=
    if s ≤ lowerWeight then base.expansion s i else higher.expansion s i

@[simp]
lemma expansion_splice_higher
    {d inputWeight lowerWeight s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (base higher : CCExpans H inputWeight)
    (hs : s ≤ lowerWeight)
    (i : (H s).index) :
    (base.spliceHigherTail higher lowerWeight).expansion s i =
      base.expansion s i := by
  simp [spliceHigherTail, hs]

@[simp]
lemma expansion_splice_tail
    {d inputWeight lowerWeight s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (base higher : CCExpans H inputWeight)
    (hs : lowerWeight < s)
    (i : (H s).index) :
    (base.spliceHigherTail higher lowerWeight).expansion s i =
      higher.expansion s i := by
  simp [spliceHigherTail, Nat.not_le_of_lt hs]

/-- Splicing preserves the lower support bound of the base endpoint. -/
lemma no_below_splice
    {d inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (base higher : CCExpans H inputWeight)
    (hbase : base.NTBelow lowerWeight) :
    (base.spliceHigherTail higher lowerWeight).NTBelow lowerWeight := by
  intro s i hs
  rw [base.expansion_splice_higher higher (by omega)]
  exact hbase s i hs

/-- Through the splice stratum, fixed-weight factors come from the base. -/
lemma splice_higher_tail
    {d inputWeight lowerWeight s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (base higher : CCExpans H inputWeight)
    (hs : s ≤ lowerWeight) :
    (base.spliceHigherTail higher lowerWeight).weightFactors s =
      base.weightFactors s := by
  unfold weightFactors
  apply List.flatMap_congr
  intro i _hi
  rw [base.expansion_splice_higher higher hs]

/-- Strictly above the splice stratum, fixed-weight factors come from `higher`. -/
lemma factors_splice_higher
    {d inputWeight lowerWeight s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (base higher : CCExpans H inputWeight)
    (hs : lowerWeight < s) :
    (base.spliceHigherTail higher lowerWeight).weightFactors s =
      higher.weightFactors s := by
  unfold weightFactors
  apply List.flatMap_congr
  intro i _hi
  rw [base.expansion_splice_tail higher hs]

/-- Any endpoint supported above a prefix has no factors in that prefix. -/
lemma nil_no_below
    {d inputWeight lowerWeight k : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (hR : R.NTBelow lowerWeight)
    (hk : k < lowerWeight) :
    R.prefixFactors k = [] := by
  unfold prefixFactors
  apply List.flatMap_eq_nil_iff.2
  intro s hs
  apply R.nil_terms_below hR
  have hsRange := List.mem_range.mp hs
  omega

/-- The spliced higher tail is exactly the tail supplied by `higher`. -/
lemma tail_splice_higher
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (base higher : CCExpans H inputWeight) :
    (base.spliceHigherTail higher lowerWeight).tailFactors
        (n := n) lowerWeight =
      higher.tailFactors (n := n) lowerWeight := by
  unfold tailFactors
  apply List.flatMap_congr
  intro s hs
  apply base.factors_splice_higher higher
  have hsLower := List.left_le_of_mem_range' hs
  omega

/--
If `higher` begins one stratum above the splice, its full endpoint is exactly
its tail above `lowerWeight`.
-/
lemma factors_no_below
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (higher : CCExpans H inputWeight)
    (hhigher : higher.NTBelow (lowerWeight + 1))
    (hlowerWeightCutoff : lowerWeight ≤ n - 1) :
    higher.factors (n := n) =
      higher.tailFactors (n := n) lowerWeight := by
  rw [higher.factors_append_tail hlowerWeightCutoff,
    higher.nil_no_below hhigher (by omega),
    List.nil_append]

/--
The factors of a supported splice are the untouched active block followed by
the complete normalized higher endpoint.
-/
lemma factors_higher_tail
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (base higher : CCExpans H inputWeight)
    (hbase : base.NTBelow lowerWeight)
    (hhigher : higher.NTBelow (lowerWeight + 1))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightCutoff : lowerWeight ≤ n - 1) :
    (base.spliceHigherTail higher lowerWeight).factors (n := n) =
      base.weightFactors lowerWeight ++ higher.factors (n := n) := by
  rw [append_no_below
        (base.spliceHigherTail higher lowerWeight)
        (base.no_below_splice higher hbase)
          hlowerWeightPos hlowerWeightCutoff,
    base.splice_higher_tail higher (Nat.le_refl _),
    base.tail_splice_higher higher,
    ← higher.factors_no_below hhigher
      hlowerWeightCutoff]

end CCExpans

namespace TSNormalb

/--
Insert a factor strictly above a positive active stratum by normalizing the
old higher tail together with the factor, then splicing that normalized tail
back above the untouched active coordinate block.
-/
lemma insertion_pos_weight
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hfactorWeight :
      lowerWeight < factor.word.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∃ next : CCExpans H inputWeight,
      next.NTBelow lowerWeight ∧
        ∀ q : ℕ,
          SPFactora.listEval (n := n) q
              (next.factors (n := n)) =
            SPFactora.listEval (n := n) q
              (coordinates.factors (n := n) ++ [factor]) := by
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  have htailTruncated :
      SPFactora.IsTruncated n
        (coordinates.tailFactors (n := n) lowerWeight) :=
    coordinates.truncated_factors hlowerWeightCutoff
  have htailSupported :
      SPFactora.WordWeightLeast (lowerWeight + 1)
        (coordinates.tailFactors (n := n) lowerWeight) :=
    coordinates.word_least_factors
  have hsourceTruncated :
      SPFactora.IsTruncated n
        (coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact htailTruncated x hx
    · rcases List.mem_singleton.mp hx with rfl
      exact hfactorTruncated
  have hsourceSupported :
      SPFactora.WordWeightLeast (lowerWeight + 1)
        (coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact htailSupported x hx
    · rcases List.mem_singleton.mp hx with rfl
      omega
  rcases normalizer.normalize
      (coordinates.tailFactors (n := n) lowerWeight ++ [factor])
      hsourceTruncated hsourceSupported with
    ⟨higher, hhigher, hhigherEval⟩
  refine
    ⟨coordinates.spliceHigherTail higher lowerWeight,
      coordinates.no_below_splice higher hcoordinates, ?_⟩
  intro q
  rw [coordinates.factors_higher_tail higher hcoordinates hhigher
      hlowerWeightPos hlowerWeightCutoff,
    coordinates.append_no_below
      hcoordinates hlowerWeightPos hlowerWeightCutoff,
    SPFactora.listEval_append,
    SPFactora.listEval_append,
    hhigherEval q,
    SPFactora.listEval_append,
    SPFactora.listEval_append]
  simp [mul_assoc]

/--
At stratum zero, every symbolic Hall factor is already strictly higher.  The
whole endpoint plus the inserted factor can be delegated directly to the
next-stratum normalizer.
-/
lemma insertion_zero
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := 1) H)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∃ next : CCExpans H inputWeight,
      next.NTBelow 0 ∧
        ∀ q : ℕ,
          SPFactora.listEval (n := n) q
              (next.factors (n := n)) =
            SPFactora.listEval (n := n) q
              (coordinates.factors (n := n) ++ [factor]) := by
  have hsourceTruncated :
      SPFactora.IsTruncated n
        (coordinates.factors (n := n) ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact coordinates.isTruncated_factors x hx
    · rcases List.mem_singleton.mp hx with rfl
      exact hfactorTruncated
  have hsourceSupported :
      SPFactora.WordWeightLeast 1
        (coordinates.factors (n := n) ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact SPFactora.word_weight_pos x
    · rcases List.mem_singleton.mp hx with rfl
      exact SPFactora.word_weight_pos x
  rcases normalizer.normalize
      (coordinates.factors (n := n) ++ [factor])
      hsourceTruncated hsourceSupported with
    ⟨next, _hnextSupported, hnextEval⟩
  exact ⟨next, fun s _i hs => False.elim (by omega), hnextEval⟩

/-- Delegate any insertion strictly above the active stratum. -/
lemma insertion_word_weight
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      lowerWeight < factor.word.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∃ next : CCExpans H inputWeight,
      next.NTBelow lowerWeight ∧
        ∀ q : ℕ,
          SPFactora.listEval (n := n) q
              (next.factors (n := n)) =
            SPFactora.listEval (n := n) q
              (coordinates.factors (n := n) ++ [factor]) := by
  by_cases hlowerWeight : lowerWeight = 0
  · subst lowerWeight
    exact normalizer.insertion_zero coordinates factor
      hfactorTruncated
  · exact normalizer.insertion_pos_weight coordinates
      factor hcoordinates (by omega) hfactorWeight hfactorTruncated

end TSNormalb

/--
The genuinely nontrivial local branch: insert a factor whose word weight is
exactly the active coordinate stratum.
-/
structure TruncatedInsertionBranch
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) : Prop where
  insert :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCExpans H inputWeight)
          (factor : SPFactora H inputWeight),
          coordinates.NTBelow lowerWeight →
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            ∃ next : CCExpans H inputWeight,
              next.NTBelow lowerWeight ∧
                ∀ q : ℕ,
                  SPFactora.listEval (n := n) q
                      (next.factors (n := n)) =
                    SPFactora.listEval (n := n) q
                      (coordinates.factors (n := n) ++ [factor])

namespace RIStep

/--
The strict-higher branch is automatic by tail delegation.  Therefore an
active-weight insertion branch supplies the complete one-stratum recursion
step.
-/
def insertion_branch
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (active :
      TruncatedInsertionBranch
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight normalizer := {
    insert := by
      intro coordinates factor hcoordinates hfactorSupported hfactorTruncated
      by_cases hfactorStrict :
          lowerWeight <
            factor.word.weight PEAddres.weight
      · exact normalizer.insertion_word_weight coordinates factor
          hcoordinates hfactorStrict hfactorTruncated
      · exact active.insert lowerWeight normalizer coordinates factor
          hcoordinates (by omega) hfactorTruncated }

end RIStep

namespace TSInput

/--
A correctly sourced repeated-block input and only the active-weight insertion
branch construct the Claim 5 polynomial data.  Strictly heavier insertions are
handled automa by canonical higher-tail splicing.
-/
theorem activeInsertionBranch
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (active :
      TruncatedInsertionBranch
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported
      (RIStep.insertion_branch
        active)
      hinputWeight

end TSInput

end TCTex
end Towers
