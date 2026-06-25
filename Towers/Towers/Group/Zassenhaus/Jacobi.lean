import Towers.Group.Zassenhaus.BasicTreeReduction
import Towers.Group.HallBasic.JacobiValueScaling
import Towers.Group.Zassenhaus.ResidualReachableScheduler
import Towers.Group.Zassenhaus.FormulaChooseSubstitution
import Towers.Group.Zassenhaus.ConjugatedHigherRouting
import Towers.Group.Zassenhaus.SharpNormalizerFamilies
import Towers.Group.Zassenhaus.SourceRecollectionOperations
import Towers.Group.Zassenhaus.IntegralStrictTail
import Towers.Group.Zassenhaus.SemanticallyHigherRecollection

-- Merged from JacobiDecomposition.lean

/-!
# Expanded Jacobi decomposition for concrete Hall-power factors

A nonbasic expanded Hall-tree root exposes its outer symbolic commutator.
Its inner Jacobi bracket may still be compressed into one canonical Hall
address when that inner bracket is basic.  This file re-encodes basic Hall
subtrees as canonical addresses and obtains symbolic representatives for all
three branches of every expanded left-normed Jacobi root.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace HEWord

universe u

/-- Compress one basic Hall tree back into its canonical Hall address. -/
noncomputable def addressBasicTree
    {d : ℕ}
    (basicTree : HallTree (FreeGenerator.{u} d))
    (hbasic : basicTree.IsBasic) :
    HEAddres (concreteBasicCommutators.{u} d) :=
  ⟨basicTree.weight,
    Classical.choose (concrete_basic_tree hbasic rfl)⟩

@[simp]
theorem address_tree_weight
    {d : ℕ}
    (basicTree : HallTree (FreeGenerator.{u} d))
    (hbasic : basicTree.IsBasic) :
    PEAddres.weight (addressBasicTree basicTree hbasic) =
      basicTree.weight :=
  rfl

@[simp]
theorem tree_atom_address
    {d : ℕ}
    (basicTree : HallTree (FreeGenerator.{u} d))
    (hbasic : basicTree.IsBasic) :
    tree (.atom (addressBasicTree basicTree hbasic)) = basicTree := by
  exact Classical.choose_spec (concrete_basic_tree hbasic rfl)

/--
Symbolic representatives for the three branches of an expanded left-normed
Jacobi root.  The representatives may use canonical addresses for compressed
basic subtrees.
-/
structure ExpandedJacobiDecomposition
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))) where
  left :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  middle :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  right :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  tree_eq :
    tree word =
      .commutator (.commutator (tree left) (tree middle)) (tree right)

/--
Every nonbasic expanded left-normed root admits symbolic representatives for
its three Jacobi branches.  If the inner bracket is basic, its children are
re-encoded as canonical Hall addresses.
-/
theorem nonempty_expanded_tree
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      tree word = .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic) :
    Nonempty (ExpandedJacobiDecomposition word) := by
  rcases
      words_tree_basic word
        (.commutator left middle) right htree houterNonbasic with
    ⟨innerWord, rightWord, hword, hinnerTree, hrightTree⟩
  by_cases hinnerBasic : (HallTree.commutator left middle).IsBasic
  · have hleftBasic := (HallTree.isBasic_commutator left middle).mp hinnerBasic |>.1
    have hmiddleBasic :=
      (HallTree.isBasic_commutator left middle).mp hinnerBasic |>.2.1
    exact
      ⟨{ left := .atom (addressBasicTree left hleftBasic)
         middle := .atom (addressBasicTree middle hmiddleBasic)
         right := rightWord
         tree_eq := by
           rw [hword, tree_commutator, tree_atom_address,
             tree_atom_address, hrightTree, hinnerTree] }⟩
  · rcases
        words_tree_basic innerWord
          left middle hinnerTree hinnerBasic with
      ⟨leftWord, middleWord, hinnerWord, hleftTree, hmiddleTree⟩
    exact
      ⟨{ left := leftWord
         middle := middleWord
         right := rightWord
         tree_eq := by
           rw [hword, tree_commutator, hinnerWord, tree_commutator,
             hleftTree, hmiddleTree, hrightTree] }⟩

/-- Choose symbolic representatives for an expanded nonbasic Jacobi root. -/
noncomputable def
    expandedTreeNonbasic
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      tree word = .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic) :
    ExpandedJacobiDecomposition word :=
  Classical.choice
    (nonempty_expanded_tree
      word left middle right htree houterNonbasic)

/-- The first descendant factor of an expanded Jacobi decomposition. -/
noncomputable def expandedJacobiFactor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight :=
  factor.reword
    (.commutator (.commutator decomposition.left decomposition.right)
      decomposition.middle)
    (by
      have hweight := congrArg HallTree.weight decomposition.tree_eq
      simp only [HallTree.weight_commutator, tree_weight] at hweight
      simp only [CWord.weight_commutator]
      omega)

/-- The negatively signed second descendant of an expanded Jacobi decomposition. -/
noncomputable def expandedJacobiSecond
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight :=
  (factor.reword
    (.commutator (.commutator decomposition.middle decomposition.right)
      decomposition.left)
    (by
      have hweight := congrArg HallTree.weight decomposition.tree_eq
      simp only [HallTree.weight_commutator, tree_weight] at hweight
      simp only [CWord.weight_commutator]
      omega)).neg

@[simp]
theorem exponent_expanded_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    (expandedJacobiFactor factor decomposition).exponent q =
      factor.exponent q := by
  simp [expandedJacobiFactor]

@[simp]
theorem exponent_expanded_jacobi
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    (expandedJacobiSecond factor decomposition).exponent q =
      -factor.exponent q := by
  simp [expandedJacobiSecond]

@[simp]
theorem expanded_jacobi_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    (expandedJacobiFactor factor decomposition).word.weight
        PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  have hweight := congrArg HallTree.weight decomposition.tree_eq
  simp only [HallTree.weight_commutator, tree_weight] at hweight
  simp only [expandedJacobiFactor, SPFactora.word_reword,
    CWord.weight_commutator]
  omega

@[simp]
theorem expanded_second_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    (expandedJacobiSecond factor decomposition).word.weight
        PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  have hweight := congrArg HallTree.weight decomposition.tree_eq
  simp only [HallTree.weight_commutator, tree_weight] at hweight
  simp only [expandedJacobiSecond, SPFactora.word_neg,
    SPFactora.word_reword, CWord.weight_commutator]
  omega

/-- Atomic packet residual attached to an expanded Jacobi decomposition. -/
noncomputable def expandedJacobiReduction
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList (basicReductionFactors factor) ++
    basicReductionFactors
      (expandedJacobiFactor factor decomposition) ++
        basicReductionFactors
          (expandedJacobiSecond factor decomposition)

/-- Continuation left after peeling an expanded atomic Jacobi packet. -/
noncomputable def expandedContinuationSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
      (basicReductionFactors
        (expandedJacobiSecond factor decomposition)) ++
    SPFactora.inverseList
      (basicReductionFactors
        (expandedJacobiFactor factor decomposition)) ++
      [factor]

/-- Truncation of the original factor truncates its expanded Jacobi packet. -/
theorem expanded_jacobi_reduction
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (expandedJacobiReduction factor decomposition) := by
  intro x hx
  simp only [expandedJacobiReduction, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors factor hfactor) x hx
  · exact
      truncated_reduction_factors
        (expandedJacobiFactor factor decomposition)
        (by
          simpa only [expanded_jacobi_factor] using hfactor)
        x hx
  · exact
      truncated_reduction_factors
        (expandedJacobiSecond factor decomposition)
        (by
          simpa only [expanded_second_factor] using hfactor)
        x hx

/-- Truncation of the original factor truncates its expanded continuation. -/
theorem truncated_expanded_continuation
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (expandedContinuationSource factor decomposition) := by
  intro x hx
  simp only [expandedContinuationSource, List.mem_append,
    List.mem_singleton] at hx
  rcases hx with (hx | hx) | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors
          (expandedJacobiSecond factor decomposition)
          (by
            simpa only [expanded_second_factor] using hfactor))
        x hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors
          (expandedJacobiFactor factor decomposition)
          (by
            simpa only [expanded_jacobi_factor] using hfactor))
        x hx
  · subst x
    exact hfactor

/--
The expanded atomic Jacobi packet and its continuation multiply to the true
factor residual.
-/
theorem
    expanded_jacobi_continuation
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedJacobiReduction factor decomposition) *
      SPFactora.listEval q
        (expandedContinuationSource factor decomposition) =
      SPFactora.listEval q
        (basicRawSource factor) := by
  simp only [expandedJacobiReduction,
    expandedContinuationSource,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    reduction_raw_source,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one]
  group

/-- The expanded continuation is atomic-correction division of the residual. -/
theorem
    expanded_continuation_residual
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedContinuationSource factor decomposition) =
      (SPFactora.listEval q
        (expandedJacobiReduction factor decomposition))⁻¹ *
        SPFactora.listEval q
          (basicRawSource factor) := by
  rw [←
    expanded_jacobi_continuation
      factor decomposition q]
  group

/-- Every factor in the expanded Jacobi correction is an atom in its layer. -/
theorem atom_expanded_jacobi
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ expandedJacobiReduction factor decomposition) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧
        address.weight =
          factor.word.weight PEAddres.weight := by
  simp only [expandedJacobiReduction, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact atom_reduction_factors factor hx
  · rcases
      atom_basic_factors
        (expandedJacobiFactor factor decomposition) hx with
      ⟨address, haddress, hweight⟩
    exact
      ⟨address, haddress,
        hweight.trans
          (expanded_jacobi_factor factor decomposition)⟩
  · rcases
      atom_basic_factors
        (expandedJacobiSecond factor decomposition) hx with
      ⟨address, haddress, hweight⟩
    exact
      ⟨address, haddress,
        hweight.trans
          (expanded_second_factor factor decomposition)⟩

/-- The expanded Jacobi correction evaluates one lower-central layer higher. -/
theorem expanded_reduction_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedJacobiReduction factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  have hfree :=
    HallTree.scaled_jacobi_series
      (tree decomposition.left) (tree decomposition.middle)
        (tree decomposition.right) (factor.exponent q)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [← tree_weight factor.word, decomposition.tree_eq]
          exact hfree))
  rw [expandedJacobiReduction,
    SPFactora.listEval_append,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    list_basic_factors, list_basic_factors,
    list_basic_factors]
  simpa only [map_mul, map_inv, tree_commutator,
    exponent_expanded_factor,
    exponent_expanded_jacobi, expandedJacobiFactor,
    expandedJacobiSecond, SPFactora.word_neg,
    SPFactora.word_reword,
    SPFactora.exponent_neg,
    SPFactora.exponent_reword, decomposition.tree_eq,
    mul_assoc] using hmap

/-- The expanded Jacobi continuation also evaluates one layer higher. -/
theorem jacobi_continuation_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedContinuationSource factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [
    expanded_continuation_residual
      factor decomposition q]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)).mul_mem
        (Subgroup.inv_mem _
          (expanded_reduction_series
            factor decomposition q))
        (list_reduction_series
          factor q)

end HEWord
end TCTex
end Towers

-- Merged from JacobiContinuation.lean

/-!
# Expanded concrete Jacobi continuation recollection

Every expanded nonbasic left-normed Jacobi root has symbolic branch
representatives, including the case where its inner bracket is compressed
into one canonical Hall address.  This file routes the resulting atomic
correction upward and packages the remaining continuation as the only
collector-facing obligation.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

namespace TSFtrya

/--
Route the finite expanded Jacobi coordinate correction into a source
supported one stratum higher.
-/
noncomputable def
    higher_expanded_raw
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∃ higherSource :
        List
          (SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
      SPFactora.IsTruncated n higherSource ∧
        SPFactora.WordWeightLeast
          (lowerWeight + 1) higherSource ∧
            ∀ q : ℕ,
              SPFactora.listEval (n := n) q higherSource =
                SPFactora.listEval q
                  (expandedJacobiReduction factor decomposition) := by
  apply factory.higher_atoms_series
      hn (concreteBasicCommutators.{u} d) hH sharp nextNormalizer
        (expandedJacobiReduction factor decomposition)
  · have hfactorPos := factor.word_weight_pos
    omega
  · omega
  · exact
      expanded_jacobi_reduction factor decomposition
        hfactorTruncated
  · intro x hx
    rcases
        atom_expanded_jacobi
          factor decomposition hx with
      ⟨address, haddress, haddressWeight⟩
    exact ⟨address, haddress, haddressWeight.trans hfactorWeight⟩
  · intro q
    simpa only [hfactorWeight] using
      expanded_reduction_series
        factor decomposition q

end TSFtrya

/--
Semantic recollection data for the continuation left after peeling an
expanded Jacobi atomic correction from a true concrete factor residual.
-/
structure ExpandedJacobiContinuation
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (expandedContinuationSource factor decomposition)

namespace
  TSRecollb

/--
Combine a strictly higher expanded atomic Jacobi correction with a strictly
higher recollection of its continuation.
-/
noncomputable def expanded_raw_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (jacobiHigherSource :
      List
        (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight))
    (hjacobiTruncated :
      SPFactora.IsTruncated n jacobiHigherSource)
    (hjacobiSupported :
      SPFactora.WordWeightLeast
        (factor.word.weight PEAddres.weight + 1)
        jacobiHigherSource)
    (hjacobiEval :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q jacobiHigherSource =
          SPFactora.listEval q
            (expandedJacobiReduction factor decomposition))
    (continuation :
      ExpandedJacobiContinuation
        (n := n) factor decomposition) :
    TSRecollb
      (n := n) factor where
  higherSource := jacobiHigherSource ++ continuation.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiTruncated x hx
    · exact continuation.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiSupported x hx
    · exact continuation.higher_least_succ x hx
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append, hjacobiEval q,
      continuation.list_higher_raw q,
      expanded_jacobi_continuation]

/--
Use the supported correction factory for the expanded atomic Jacobi packet,
leaving only its explicit continuation recollection as an input.
-/
noncomputable def expanded_reduction
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (continuation :
      ExpandedJacobiContinuation
        (n := n) factor decomposition) :
    TSRecollb
      (n := n) factor := by
  let jacobi :=
    factory.higher_expanded_raw hn hH
      sharp nextNormalizer factor decomposition hfactorWeight hfactorTruncated
  let jacobiHigherSource := Classical.choose jacobi
  have hjacobiTruncated := (Classical.choose_spec jacobi).1
  have hjacobiSupported := (Classical.choose_spec jacobi).2.1
  have hjacobiEval := (Classical.choose_spec jacobi).2.2
  exact
    expanded_raw_source factor decomposition
      jacobiHigherSource hjacobiTruncated
        (by simpa only [hfactorWeight] using hjacobiSupported)
          hjacobiEval continuation

/--
Compile the Hall-Petresco packet and a family of strictly deeper normalizers
into the data needed to lift one expanded Jacobi residual.
-/
noncomputable def expanded_normalizer_above
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (continuation :
      ExpandedJacobiContinuation
        (n := n) factor decomposition) :
    TSRecollb
      (n := n) factor :=
  expanded_reduction hn hH
    ((packet.powerSupportedFactory
      hinputWeight lowerWeight).correctionPacketFactory)
    (SSNormal.ofNormalizerAbove
      normalizerAbove)
    (normalizerAbove (lowerWeight + 1) (by omega))
    factor decomposition hfactorWeight hfactorTruncated continuation

end
  TSRecollb

/--
A cutoff packet and continuation recollections for expanded Jacobi brackets,
including brackets whose inner subtree is compressed into one Hall address.
-/
structure
    JCBuildb
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  expandedJacobiContinuation :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ExpandedJacobiContinuation
                (n := n) factor decomposition

namespace
  JCBuildb

open
  TSRecollb

/--
Lift one expanded Jacobi factor using only normalizers at strictly larger
support bounds.
-/
noncomputable def jacobiResidual
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      JCBuildb.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  expanded_normalizer_above hn hH builder.packet
    hinputWeight normalizerAbove factor decomposition hfactorWeight
      hfactorTruncated
        (builder.expandedJacobiContinuation lowerWeight hnonterminal factor
          decomposition hfactorWeight hfactorTruncated)

/--
Every expanded nonbasic left-normed Jacobi root enters the continuation
collector, whether or not its inner bracket was compressed into one address.
-/
noncomputable def jacobiTreeNonbasic
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      JCBuildb.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      HEWord.tree factor.word =
        .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  let decomposition :=
    expandedTreeNonbasic
      factor.word left middle right htree houterNonbasic
  builder.jacobiResidual hinputWeight lowerWeight hnonterminal normalizerAbove
    factor decomposition hfactorWeight hfactorTruncated

end
  JCBuildb
end TCTex
end Towers

-- Merged from JacobiDescendantTrees.lean

/-!
# Trees underlying expanded symbolic Jacobi descendants

Expanded symbolic Jacobi recollection leaves the two ordinary descendant
residuals as same-weight recursive obligations.  This file records their
underlying Hall trees explicitly.

It also isolates an important obstruction to a naive recursive closure:
following the first raw Jacobi descendant twice returns to the original
left-normed tree.  A terminating collector must therefore reduce the inner
bracket to its finite atomic Hall packet before recursing on the outer
brackets.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers

namespace HallTree

universe u

/-- The first tree produced by the left-normed Jacobi rewrite. -/
def leftJacobiDescendant
    {α : Type u}
    (left middle right : HallTree α) :
    HallTree α :=
  .commutator (.commutator left right) middle

/-- The second tree produced by the left-normed Jacobi rewrite. -/
def leftSecondDescendant
    {α : Type u}
    (left middle right : HallTree α) :
    HallTree α :=
  .commutator (.commutator middle right) left

@[simp]
theorem weight_jacobi_descendant
    {α : Type u}
    (left middle right : HallTree α) :
    (leftJacobiDescendant left middle right).weight =
      (.commutator (.commutator left middle) right : HallTree α).weight := by
  simp only [leftJacobiDescendant, weight_commutator]
  omega

@[simp]
theorem weight_second_descendant
    {α : Type u}
    (left middle right : HallTree α) :
    (leftSecondDescendant left middle right).weight =
      (.commutator (.commutator left middle) right : HallTree α).weight := by
  simp only [leftSecondDescendant, weight_commutator]
  omega

/--
Following the first raw Jacobi branch twice returns to the original tree.
Consequently raw first-descendant recursion alone is not well-founded.
-/
@[simp]
theorem left_descendant_cycle
    {α : Type u}
    (left middle right : HallTree α) :
    leftJacobiDescendant left right middle =
      .commutator (.commutator left middle) right :=
  rfl

end HallTree

namespace TCTex
namespace HEWord

universe u

/-- The expanded symbolic first descendant has the expected Hall tree. -/
@[simp]
theorem tree_expanded_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    tree (expandedJacobiFactor factor decomposition).word =
      HallTree.leftJacobiDescendant
        (tree decomposition.left) (tree decomposition.middle)
          (tree decomposition.right) := by
  simp only [expandedJacobiFactor, SPFactora.word_reword,
    tree_commutator, HallTree.leftJacobiDescendant]

/-- The expanded symbolic second descendant has the expected Hall tree. -/
@[simp]
theorem tree_expanded_jacobi
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    tree (expandedJacobiSecond factor decomposition).word =
      HallTree.leftSecondDescendant
        (tree decomposition.left) (tree decomposition.middle)
          (tree decomposition.right) := by
  simp only [expandedJacobiSecond, SPFactora.word_neg,
    SPFactora.word_reword, tree_commutator,
    HallTree.leftSecondDescendant]

end HEWord
end TCTex
end Towers

-- Merged from JacobiValueResidual.lean

/-!
# Expanded symbolic Jacobi value residuals

An expanded Jacobi decomposition may re-encode a compressed basic inner
bracket through canonical Hall addresses.  The value-level Jacobi packet is
still the same three-factor residual: the original nested value inverse,
followed by the two signed descendant values.

This file proves that packet lies one lower-central stratum higher without
requiring a syntactic left-normed word equality.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace HEWord

universe u

/-- Value-level residual attached to an expanded Jacobi decomposition. -/
noncomputable def expandedJacobiRaw
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  [factor.neg,
    expandedJacobiFactor factor decomposition,
    expandedJacobiSecond factor decomposition]

/-- Truncation of the original factor truncates its expanded value residual. -/
theorem expanded_jacobi_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (expandedJacobiRaw factor decomposition) := by
  intro x hx
  simp only [expandedJacobiRaw, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · simpa only [SPFactora.word_neg] using hfactor
  · simpa only [expanded_jacobi_factor] using hfactor
  · simpa only [expanded_second_factor] using hfactor

/--
The expanded symbolic Jacobi value residual evaluates one lower-central
stratum higher.
-/
theorem list_expanded_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedJacobiRaw factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  have hfree :=
    HallTree.jacobi_zpow_series
      (tree decomposition.left) (tree decomposition.middle)
        (tree decomposition.right) (factor.exponent q)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [← tree_weight factor.word, decomposition.tree_eq]
          exact hfree))
  rw [expandedJacobiRaw,
    SPFactora.listEval_cons,
    SPFactora.listEval_cons,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one]
  rw [← decomposition.tree_eq,
    ← tree_commutator decomposition.left decomposition.right,
    ← tree_commutator (.commutator decomposition.left decomposition.right)
      decomposition.middle,
    ← tree_commutator decomposition.middle decomposition.right,
    ← tree_commutator (.commutator decomposition.middle decomposition.right)
      decomposition.left] at hmap
  rw [map_mul, map_inv, map_zpow, map_mul, map_zpow, map_zpow,
    lower_truncation_tree,
    lower_truncation_tree,
    lower_truncation_tree] at hmap
  simpa only [map_mul, map_inv, map_zpow,
    SPFactora.eval_neg, SPFactora.eval,
    SPFactora.wordValue,
    exponent_expanded_factor, exponent_expanded_jacobi,
    expandedJacobiFactor, expandedJacobiSecond,
    SPFactora.word_neg, SPFactora.word_reword,
    SPFactora.exponent_neg,
    SPFactora.exponent_reword, decomposition.tree_eq,
    zpow_neg] using hmap

/-- Inverse orientation of the expanded Jacobi value residual. -/
noncomputable def expandedJacobiSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
    (expandedJacobiRaw factor decomposition)

/-- Truncation is preserved by inversion of the expanded value residual. -/
theorem truncated_expanded_jacobi
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (expandedJacobiSource factor decomposition) := by
  exact
    SPFactora.truncated_inverse_list
      (expanded_jacobi_source
        factor decomposition hfactor)

/--
The inverse expanded Jacobi value residual also lies one lower-central
stratum higher.
-/
theorem
    expanded_jacobi_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedJacobiSource factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [expandedJacobiSource,
    SPFactora.list_eval_inverse]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)).inv_mem
        (list_expanded_series
          factor decomposition q)

end HEWord
end TCTex
end Towers

-- Merged from JacobiRankedResidualRouting.lean

/-!
# Reachable ranked normalization of expanded Hall-power Jacobi descendants

The Hall-ranked inner-packet recursion does not classify an arbitrary
nonbasic root. It applies after a Jacobi rewrite, when the two descendants
have the forms `[[a, v], b]` and `[[b, v], a]`. Both descendants inherit the
classical rank defect of the original pair `[[a, b], v]`.

This file records those two recipe-correct ranked cases and the corresponding
reachable-descendant certificate.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

/-- The classical Hall-rank defect inherited by both Jacobi descendants. -/
def expandedParentDefect
    {d : ℕ}
    {word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))}
    (decomposition : ExpandedJacobiDecomposition word) :
    ℕ :=
  HallTree.bracketRankDefect
    ((tree (.commutator decomposition.left decomposition.middle)).weight +
      (tree decomposition.right).weight)
    (.commutator (tree decomposition.left) (tree decomposition.middle))
    (tree decomposition.right)

/--
The first Jacobi descendant `[[a, v], b]` is a recipe-correct ranked
inner-reduction case whenever `v < b`.
-/
noncomputable def expandedJacobiCase
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (hrightMiddle :
      tree decomposition.right < tree decomposition.middle)
    (hmiddleBasic : (tree decomposition.middle).IsBasic) :
    RankedInnerCase
      (n := n)
      (expandedJacobiFactor factor decomposition)
      (expandedParentDefect decomposition) where
  innerWord := .commutator decomposition.left decomposition.right
  rightWord := decomposition.middle
  hword := by
    simp only [expandedJacobiFactor, SPFactora.word_reword]
  hfactorTruncated := by
    simpa only [expanded_jacobi_factor] using hfactorTruncated
  added := tree decomposition.left
  originalRight := tree decomposition.right
  unchanged := tree decomposition.middle
  originalLeft :=
    .commutator (tree decomposition.left) (tree decomposition.middle)
  hinnerTree := by
    simp only [tree_commutator]
  hRightLeft :=
    hrightMiddle.trans
      (HallTree.weight_add_left
        (tree decomposition.left) (tree decomposition.middle)
        (.commutator (tree decomposition.left) (tree decomposition.middle))
        rfl)
  hRightUnchanged := hrightMiddle
  hunchangedBasic := hmiddleBasic
  rankDefect_eq := by
    simp only [expandedParentDefect, tree_commutator,
      HallTree.weight_commutator]
    congr 1
    omega

/--
The second Jacobi descendant `[[b, v], a]` is a recipe-correct ranked
inner-reduction case whenever `v < b < a`.
-/
noncomputable def expandedRankedCase
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (hrightMiddle :
      tree decomposition.right < tree decomposition.middle)
    (hmiddleLeft :
      tree decomposition.middle < tree decomposition.left)
    (hleftBasic : (tree decomposition.left).IsBasic) :
    RankedInnerCase
      (n := n)
      (expandedJacobiSecond factor decomposition)
      (expandedParentDefect decomposition) where
  innerWord := .commutator decomposition.middle decomposition.right
  rightWord := decomposition.left
  hword := by
    simp only [expandedJacobiSecond, SPFactora.word_neg,
      SPFactora.word_reword]
  hfactorTruncated := by
    simpa only [expanded_second_factor] using hfactorTruncated
  added := tree decomposition.middle
  originalRight := tree decomposition.right
  unchanged := tree decomposition.left
  originalLeft :=
    .commutator (tree decomposition.left) (tree decomposition.middle)
  hinnerTree := by
    simp only [tree_commutator]
  hRightLeft :=
    hrightMiddle.trans
      (HallTree.weight_add_left
        (tree decomposition.left) (tree decomposition.middle)
        (.commutator (tree decomposition.left) (tree decomposition.middle))
        rfl)
  hRightUnchanged := hrightMiddle.trans hmiddleLeft
  hunchangedBasic := hleftBasic
  rankDefect_eq := by
    simp only [expandedParentDefect, tree_commutator,
      HallTree.weight_commutator]
    congr 1
    omega

/--
An expanded Jacobi decomposition equipped with the Hall inequalities needed
to reduce both of its ordinary descendants by ranked inner reduction.
-/
structure TRDecomp
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) where
  decomposition : ExpandedJacobiDecomposition factor.word
  right_lt_middle :
    tree decomposition.right < tree decomposition.middle
  middle_lt_left :
    tree decomposition.middle < tree decomposition.left
  left_isBasic : (tree decomposition.left).IsBasic
  middle_isBasic : (tree decomposition.middle).IsBasic

namespace
  TRDecomp

/--
Choose symbolic representatives for a recipe-correct Hall-oriented Jacobi
root while retaining the inequalities needed by ranked descendant recursion.
-/
noncomputable def nonbasic_commutator_tree
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      tree factor.word = .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hrightMiddle : right < middle)
    (hmiddleLeft : middle < left)
    (hleftBasic : left.IsBasic)
    (hmiddleBasic : middle.IsBasic) :
    TRDecomp
      factor := by
  let decomposition :=
    expandedTreeNonbasic
      factor.word left middle right htree houterNonbasic
  have hroot :
      HallTree.commutator
          (HallTree.commutator
            (tree decomposition.left) (tree decomposition.middle))
          (tree decomposition.right) =
        HallTree.commutator (HallTree.commutator left middle) right := by
    rw [← decomposition.tree_eq, htree]
  injection hroot with hinner hright
  injection hinner with hleft hmiddle
  exact
    { decomposition := decomposition
      right_lt_middle := by
        simpa only [hright, hmiddle] using hrightMiddle
      middle_lt_left := by
        simpa only [hmiddle, hleft] using hmiddleLeft
      left_isBasic := by
        simpa only [hleft] using hleftBasic
      middle_isBasic := by
        simpa only [hmiddle] using hmiddleBasic }

/-- Compile the first ordinary descendant into a ranked local case. -/
noncomputable def firstCase
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (ranked :
      TRDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    RankedInnerCase
      (n := n)
      (expandedJacobiFactor factor ranked.decomposition)
      (expandedParentDefect ranked.decomposition) :=
  expandedJacobiCase factor
    ranked.decomposition hfactorTruncated ranked.right_lt_middle
      ranked.middle_isBasic

/-- Compile the second ordinary descendant into a ranked local case. -/
noncomputable def secondCase
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (ranked :
      TRDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    RankedInnerCase
      (n := n)
      (expandedJacobiSecond factor ranked.decomposition)
      (expandedParentDefect ranked.decomposition) :=
  expandedRankedCase factor
    ranked.decomposition hfactorTruncated ranked.right_lt_middle
      ranked.middle_lt_left ranked.left_isBasic

end
  TRDecomp

/-- Reachability of the two ranked descendants emitted by one Jacobi root. -/
structure
    ExpandedDescendantReachability
    {d inputWeight : ℕ}
    (Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) : Prop where
  first :
    Reachable
      (expandedJacobiFactor factor decomposition)
      (expandedParentDefect decomposition)
  second :
    Reachable
      (expandedJacobiSecond factor decomposition)
      (expandedParentDefect decomposition)

end TCTex
end Towers

-- Merged from JacobiContinuationDecomposition.lean

/-!
# Recursive decomposition of the expanded symbolic Jacobi continuation

The expanded Jacobi boundary also covers roots whose inner bracket is
compressed into one Hall address.  After its atomic coordinate packet is
peeled, the remaining continuation decomposes into:

* the true residual of the second descendant;
* the true residual of the first descendant, conjugated by the second
  descendant value; and
* the inverse value-level Jacobi residual.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace HEWord

universe u

/--
Recursive source whose evaluation is the expanded Jacobi continuation.

The singleton factors surrounding the first descendant residual encode its
conjugation by the second descendant value.
-/
noncomputable def expandedContinuationDecomposition
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  basicRawSource
      (expandedJacobiSecond factor decomposition) ++
    [(expandedJacobiSecond factor decomposition).neg] ++
      basicRawSource
          (expandedJacobiFactor factor decomposition) ++
        [expandedJacobiSecond factor decomposition] ++
          expandedJacobiSource factor decomposition

/-- Truncation of the factor truncates its recursive expanded continuation. -/
theorem expanded_continuation_decomposition
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (expandedContinuationDecomposition
        factor decomposition) := by
  have hfirst :
      (expandedJacobiFactor factor decomposition).word.weight
          PEAddres.weight < n := by
    simpa only [expanded_jacobi_factor] using hfactor
  have hsecond :
      (expandedJacobiSecond factor decomposition).word.weight
          PEAddres.weight < n := by
    simpa only [expanded_second_factor] using hfactor
  intro x hx
  simp only [expandedContinuationDecomposition,
    List.mem_append] at hx
  rcases hx with (((hx | hx) | hx) | hx) | hx
  · exact
      truncated_reduction_source
        (expandedJacobiSecond factor decomposition) hsecond x hx
  · simp only [List.mem_singleton] at hx
    subst x
    simpa only [SPFactora.word_neg] using hsecond
  · exact
      truncated_reduction_source
        (expandedJacobiFactor factor decomposition) hfirst x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hsecond
  · exact
      truncated_expanded_jacobi
        factor decomposition hfactor x hx

/--
The recursive decomposition evaluates exactly to the expanded continuation
left after the atomic coordinate correction.
-/
theorem
    expanded_continuation_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedContinuationDecomposition
          factor decomposition) =
      SPFactora.listEval q
        (expandedContinuationSource factor decomposition) := by
  simp only [expandedContinuationDecomposition,
    expandedContinuationSource,
    expandedJacobiSource,
    expandedJacobiRaw,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    reduction_raw_source,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one,
    SPFactora.eval_neg]
  group

/-- The recursive expanded decomposition inherits next-layer membership. -/
theorem
    expanded_continuation_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedContinuationDecomposition
          factor decomposition) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [
    expanded_continuation_source
      factor decomposition q]
  exact
    jacobi_continuation_series
      factor decomposition q

end HEWord
end TCTex
end Towers

-- Merged from JacobiContinuationRecursion.lean

/-!
# Recursive interface for expanded symbolic Jacobi continuations

Expanded Jacobi decompositions cover left-normed roots whose inner basic Hall
bracket may already be compressed into a canonical address.  Their atomic
coordinate packet routes upward through the existing supported-correction
factory, while recollection of the exact recursive continuation decomposition
supplies the remaining boundary.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

/-
These declarations are already provided by the merged JacobiContinuation
section above.

namespace TSFtrya

/--
Route the finite expanded Jacobi coordinate correction into a source
supported one stratum higher.
-/
noncomputable def higher_expanded_raw
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∃ higherSource :
        List
          (SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
      SPFactora.IsTruncated n higherSource ∧
        SPFactora.WordWeightLeast
          (lowerWeight + 1) higherSource ∧
            ∀ q : ℕ,
              SPFactora.listEval (n := n) q higherSource =
                SPFactora.listEval q
                  (expandedJacobiReduction factor decomposition) := by
  apply factory.higher_atoms_series
      hn (concreteBasicCommutators.{u} d) hH sharp nextNormalizer
        (expandedJacobiReduction factor decomposition)
  · have hfactorPos := factor.word_weight_pos
    omega
  · omega
  · exact
      expanded_jacobi_reduction factor decomposition
        hfactorTruncated
  · intro x hx
    rcases
        atom_expanded_jacobi
          factor decomposition hx with
      ⟨address, haddress, haddressWeight⟩
    exact ⟨address, haddress, haddressWeight.trans hfactorWeight⟩
  · intro q
    simpa only [hfactorWeight] using
      expanded_reduction_series
        factor decomposition q

end TSFtrya

/-- Semantic recollection data for an expanded Jacobi continuation. -/
structure ExpandedJacobiContinuation
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (expandedContinuationSource factor decomposition)

namespace
  TSRecollb

/--
Combine an upward expanded atomic Jacobi correction with an upward
recollection of its continuation.
-/
noncomputable def expanded_raw_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (jacobiHigherSource :
      List
        (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight))
    (hjacobiTruncated :
      SPFactora.IsTruncated n jacobiHigherSource)
    (hjacobiSupported :
      SPFactora.WordWeightLeast
        (factor.word.weight PEAddres.weight + 1)
        jacobiHigherSource)
    (hjacobiEval :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q jacobiHigherSource =
          SPFactora.listEval q
            (expandedJacobiReduction factor decomposition))
    (continuation :
      ExpandedJacobiContinuation
        (n := n) factor decomposition) :
    TSRecollb
      (n := n) factor where
  higherSource := jacobiHigherSource ++ continuation.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiTruncated x hx
    · exact continuation.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiSupported x hx
    · exact continuation.higher_least_succ x hx
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append, hjacobiEval q,
      continuation.list_higher_raw q,
      expanded_jacobi_continuation]

/--
Use the supported correction factory for an expanded atomic Jacobi packet,
leaving only recollection of its continuation as input.
-/
noncomputable def expanded_reduction
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (continuation :
      ExpandedJacobiContinuation
        (n := n) factor decomposition) :
    TSRecollb
      (n := n) factor := by
  let jacobi :=
    factory.higher_expanded_raw hn hH
      sharp nextNormalizer factor decomposition hfactorWeight hfactorTruncated
  let jacobiHigherSource := Classical.choose jacobi
  have hjacobiTruncated := (Classical.choose_spec jacobi).1
  have hjacobiSupported := (Classical.choose_spec jacobi).2.1
  have hjacobiEval := (Classical.choose_spec jacobi).2.2
  exact
    expanded_raw_source factor decomposition
      jacobiHigherSource hjacobiTruncated
        (by simpa only [hfactorWeight] using hjacobiSupported)
          hjacobiEval continuation

/--
Compile a Hall-Petresco packet and strictly deeper normalizers into the data
needed to lift one expanded Jacobi residual.
-/
noncomputable def expanded_normalizer_above
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (continuation :
      ExpandedJacobiContinuation
        (n := n) factor decomposition) :
    TSRecollb
      (n := n) factor :=
  expanded_reduction hn hH
    ((packet.powerSupportedFactory
      hinputWeight lowerWeight).correctionPacketFactory)
    (SSNormal.ofNormalizerAbove
      normalizerAbove)
    (normalizerAbove (lowerWeight + 1) (by omega))
    factor decomposition hfactorWeight hfactorTruncated continuation

end
  TSRecollb
-/

/--
Recollection data for the explicit recursive decomposition of an expanded
Jacobi continuation.
-/
structure
    CDRecoll
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight + 1) higherSource
  list_decomposition_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (expandedContinuationDecomposition
            factor decomposition)

namespace
  CDRecoll

/--
An upward recollection of the expanded recursive decomposition is an upward
recollection of the expanded Jacobi continuation.
-/
noncomputable def expandedContinuationRecollection
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {decomposition : ExpandedJacobiDecomposition factor.word}
    (recollection :
      CDRecoll
        (n := n) factor decomposition) :
    ExpandedJacobiContinuation
      (n := n) factor decomposition where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_least_succ :=
    recollection.higher_least_succ
  list_higher_raw := by
    intro q
    rw [recollection.list_decomposition_raw q,
  expanded_continuation_source]

end
  CDRecoll

/--
A Hall-Petresco packet and recursive expanded-continuation recollections.
-/
structure
    ECBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  expandedJacobiDecomposition :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              CDRecoll
                (n := n) factor decomposition

namespace
  ECBuild

open
  TSRecollb

/--
Lift one expanded left-normed Jacobi factor from recollection of its explicit
recursive continuation decomposition.
-/
noncomputable def jacobiResidual
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
  ECBuild.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  expanded_normalizer_above hn hH builder.packet
    hinputWeight normalizerAbove factor decomposition hfactorWeight
      hfactorTruncated
        (builder.expandedJacobiDecomposition lowerWeight
          hnonterminal factor decomposition hfactorWeight hfactorTruncated
          |>.expandedContinuationRecollection)

/--
Every expanded nonbasic left-normed Jacobi root enters the recursive
continuation collector, including roots with a compressed inner bracket.
-/
noncomputable def jacobiTreeNonbasic
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
  ECBuild.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      HEWord.tree factor.word =
        .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  let decomposition :=
    expandedTreeNonbasic
      factor.word left middle right htree houterNonbasic
  builder.jacobiResidual hinputWeight lowerWeight hnonterminal normalizerAbove
    factor decomposition hfactorWeight hfactorTruncated

end
  ECBuild
end TCTex
end Towers

-- Merged from JacobiContinuationSplicing.lean

/-!
# Splicing recursive expanded symbolic Jacobi continuations

The recursive expanded Jacobi continuation contains three semantic pieces:

* the true residual of the second descendant;
* the true residual of the first descendant, conjugated by the second
  descendant value; and
* the inverse value-level Jacobi residual.

The descendant residuals and the value-level residual can be recollected
independently.  The first descendant is the delicate piece: its same-weight
conjugating factors cannot remain in a source supported one stratum higher.
This file isolates exactly that upward conjugation route and splices the
three recollected sources into the continuation recollection consumed by the
expanded Jacobi collector.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

/-- Raw source for the first descendant residual conjugated by the second. -/
noncomputable def expandedJacobiConjugated
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  [(expandedJacobiSecond factor decomposition).neg] ++
    basicRawSource
      (expandedJacobiFactor factor decomposition) ++
    [expandedJacobiSecond factor decomposition]

/--
The expanded continuation decomposition is the concatenation of the second
descendant residual, the conjugated first descendant residual, and the
inverse value-level residual.
-/
theorem expanded_continuation_splice
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) :
    expandedContinuationDecomposition factor decomposition =
      basicRawSource
          (expandedJacobiSecond factor decomposition) ++
        expandedJacobiConjugated factor decomposition ++
          expandedJacobiSource factor decomposition := by
  simp [expandedContinuationDecomposition,
    expandedJacobiConjugated, List.append_assoc]

/--
Semantic upward recollection of the first descendant residual conjugated by
the second descendant value.  Constructing this package is the precise
same-weight conjugation-routing obligation exposed by recursive Jacobi
collection.
-/
structure
    ECRecol
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (expandedJacobiConjugated
            factor decomposition)

/-- Semantic upward recollection of the inverse value-level Jacobi residual. -/
structure
    TruncatedExpandedRecollection
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (expandedJacobiSource factor decomposition)

namespace
  CDRecoll

/--
Splice independently recollected recursive pieces into an upward recollection
of the full expanded Jacobi continuation decomposition.
-/
noncomputable def of_spliced
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (second :
      TSRecollb
        (n := n) (expandedJacobiSecond factor decomposition))
    (conjugatedFirst :
      ECRecol
        (n := n) factor decomposition)
    (valueResidualInverse :
      TruncatedExpandedRecollection
        (n := n) factor decomposition) :
    CDRecoll
      (n := n) factor decomposition where
  higherSource :=
    second.higherSource ++
      conjugatedFirst.higherSource ++
        valueResidualInverse.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact second.higher_source_truncated x hx
      · exact conjugatedFirst.higher_source_truncated x hx
    · exact valueResidualInverse.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · simpa only [expanded_second_factor] using
          second.higher_least_succ x hx
      · exact conjugatedFirst.higher_least_succ x hx
    · exact valueResidualInverse.higher_least_succ x hx
  list_decomposition_raw := by
    intro q
    rw [SPFactora.listEval_append,
      SPFactora.listEval_append,
      second.list_higher_raw q,
      conjugatedFirst.list_higher_raw q,
      valueResidualInverse.list_higher_raw q,
      expanded_continuation_splice,
      SPFactora.listEval_append,
      SPFactora.listEval_append]

end
  CDRecoll

/--
A Hall-Petresco packet together with explicit recollections of the three
recursive expanded-Jacobi continuation pieces.

Only `conjugatedFirstResidual` contains the same-weight conjugation boundary.
The other fields are ordinary upward recollections of recursive residuals.
-/
structure
    ECSplice
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  secondResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecollb
                (n := n) (expandedJacobiSecond factor decomposition)
  conjugatedFirstResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ECRecol
                (n := n) factor decomposition
  valueResidualInverse :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TruncatedExpandedRecollection
                (n := n) factor decomposition

namespace
  ECSplice

open
  CDRecoll

/--
Compile explicit recursive-piece recollections into the continuation builder
consumed by expanded Jacobi collection.
-/
noncomputable def expandedContinuationBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      ECSplice.{u}
        (inputWeight := inputWeight) hn hH) :
    ECBuild
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  expandedJacobiDecomposition :=
    fun lowerWeight hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      of_spliced factor decomposition
          (builder.secondResidual lowerWeight hnonterminal factor decomposition
            hfactorWeight hfactorTruncated)
          (builder.conjugatedFirstResidual lowerWeight hnonterminal factor
            decomposition hfactorWeight hfactorTruncated)
          (builder.valueResidualInverse lowerWeight hnonterminal factor
            decomposition hfactorWeight hfactorTruncated)

end
  ECSplice

end TCTex
end Towers

-- Merged from JacobiConjugatedResidualRouting.lean

/-!
# Routing conjugated expanded symbolic Jacobi residuals

The recursive expanded Jacobi continuation contains the conjugated source

`second⁻¹ * R(first) * second`.

Once `R(first)` has been recollected one stratum higher, the sharp higher-tail
router moves `second` left across that recollected source.  Its leading copy
cancels semantically with `second⁻¹`, leaving a physically higher source.

This file applies the generic conjugated-higher-tail route to expanded Jacobi
decompositions and removes the same-weight sandwich as an independent builder
obligation.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

namespace
  ECRecol

/--
Route the second descendant across an upward recollection of the first
descendant residual.
-/
noncomputable def of_firstResidual
    {d n inputWeight lowerWeight : ℕ}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (first :
      TSRecollb
        (n := n) (expandedJacobiFactor factor decomposition)) :
    ECRecol
      (n := n) factor decomposition := by
  have hsecondWeight :
      (expandedJacobiSecond factor decomposition).word.weight
          PEAddres.weight = lowerWeight := by
    simpa only [expanded_second_factor] using hfactorWeight
  have hsecondTruncated :
      (expandedJacobiSecond factor decomposition).word.weight
          PEAddres.weight < n := by
    simpa only [expanded_second_factor] using hfactorTruncated
  have hfirstSupported :
      SPFactora.WordWeightLeast
        (lowerWeight + 1) first.higherSource := by
    simpa only [expanded_jacobi_factor, hfactorWeight] using
      first.higher_least_succ
  let routed :=
    factory.conjugated_recollection_normalizer sharp
      (expandedJacobiSecond factor decomposition) hsecondWeight
        hsecondTruncated
          (basicRawSource
            (expandedJacobiFactor factor decomposition))
          first.higherSource first.higher_source_truncated hfirstSupported
            first.list_higher_raw
  exact
    { higherSource := routed.higherSource
      higher_source_truncated := routed.higher_source_truncated
      higher_least_succ := by
        simpa only [hfactorWeight] using
          routed.higher_least_succ
      list_higher_raw := by
        intro q
        simpa only [expandedJacobiConjugated,
          SPFactora.conjugatedRawSource] using
            routed.higher_conjugated_raw q }

/--
Compile a Hall-Petresco packet and strictly deeper normalizers into the route
for the conjugated first descendant residual.
-/
noncomputable def first_normalizer_above
    {d n inputWeight lowerWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (first :
      TSRecollb
        (n := n) (expandedJacobiFactor factor decomposition)) :
    ECRecol
      (n := n) factor decomposition :=
  of_firstResidual
    ((packet.powerSupportedFactory
      hinputWeight lowerWeight).correctionPacketFactory)
    (SSNormal.ofNormalizerAbove
      normalizerAbove)
    factor decomposition hfactorWeight hfactorTruncated first

end
  ECRecol

namespace
  CDRecoll

open
  ECRecol

/--
Splice the recursive expanded Jacobi continuation after routing the
conjugation surrounding the first descendant residual.
-/
noncomputable def of_routedFirst
    {d n inputWeight lowerWeight : ℕ}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (first :
      TSRecollb
        (n := n) (expandedJacobiFactor factor decomposition))
    (second :
      TSRecollb
        (n := n) (expandedJacobiSecond factor decomposition))
    (valueResidualInverse :
      TruncatedExpandedRecollection
        (n := n) factor decomposition) :
    CDRecoll
      (n := n) factor decomposition :=
  of_spliced factor decomposition second
    (of_firstResidual
      factory sharp factor decomposition hfactorWeight hfactorTruncated first)
    valueResidualInverse

/--
Compile a Hall-Petresco packet and strictly deeper normalizers into the
expanded Jacobi continuation splice.
-/
noncomputable def routed_normalizer_above
    {d n inputWeight lowerWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (first :
      TSRecollb
        (n := n) (expandedJacobiFactor factor decomposition))
    (second :
      TSRecollb
        (n := n) (expandedJacobiSecond factor decomposition))
    (valueResidualInverse :
      TruncatedExpandedRecollection
        (n := n) factor decomposition) :
    CDRecoll
      (n := n) factor decomposition :=
  of_spliced factor decomposition second
    (first_normalizer_above
      packet hinputWeight normalizerAbove factor decomposition hfactorWeight
        hfactorTruncated first)
    valueResidualInverse

end
  CDRecoll

end TCTex
end Towers

-- Merged from JacobiRoutedContinuationBuilder.lean

/-!
# Routed expanded-Jacobi continuation builders

The conjugation around the first expanded-Jacobi descendant is not an
independent recursive obligation.  A sharp higher-tail normalizer routes an
ordinary recollection of that descendant through the conjugation.

This file packages that route at the collection-builder boundary.  Recursive
callers provide the two ordinary descendant residual recollections and the
inverse value-residual recollection; the first conjugated recollection is
derived automa.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

open HEWord

universe u

/--
A recursive expanded-Jacobi continuation builder whose first descendant is
routed automa through its same-weight conjugation.
-/
structure
    ECRouted
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  normalizerFamily :
    SSNormala
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d)
  firstResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecollb
                (n := n) (expandedJacobiFactor factor decomposition)
  secondResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecollb
                (n := n) (expandedJacobiSecond factor decomposition)
  valueResidualInverse :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TruncatedExpandedRecollection
                (n := n) factor decomposition

namespace
  ECRouted

open
  ECRecol

/--
Compile the routed continuation builder into the explicit three-piece splice.
-/
noncomputable def splicedCollectionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      ECRouted.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight) :
    ECSplice
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  secondResidual := builder.secondResidual
  conjugatedFirstResidual :=
    fun lowerWeight hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      first_normalizer_above builder.packet hinputWeight
          (fun strongerWeight _ =>
            builder.normalizerFamily.normalizer strongerWeight)
          factor decomposition hfactorWeight hfactorTruncated
          (builder.firstResidual lowerWeight hnonterminal factor decomposition
            hfactorWeight hfactorTruncated)
  valueResidualInverse := builder.valueResidualInverse

/--
Compile the routed continuation builder into the builder consumed by expanded
Jacobi collection.
-/
noncomputable def expandedContinuationBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      ECRouted.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight) :
    ECBuild
      (inputWeight := inputWeight) hn hH :=
  (builder.splicedCollectionBuilder hinputWeight)
    |>.expandedContinuationBuilder

end
  ECRouted

end TCTex
end Towers

-- Merged from JacobiForwardValueResidual.lean

/-!
# Forward expanded-Jacobi value-residual recollections

The recursive expanded-Jacobi splice uses the inverse orientation of its
value-level residual.  It is enough for a recursive caller to recollect the
forward orientation: generic source inversion constructs the required
inverse recollection.

This file packages that reduction and exposes a builder with only forward
value-residual recollections.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

/-- Semantic upward recollection of the forward expanded-Jacobi value residual. -/
structure
    TJRecoll
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (expandedJacobiRaw factor decomposition)

namespace
  TJRecoll

/-- View a concrete forward value-residual recollection as a generic one. -/
noncomputable def toSourceRecollection
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {decomposition : ExpandedJacobiDecomposition factor.word}
    (recollection :
      TJRecoll
        (n := n) factor decomposition) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (expandedJacobiRaw factor decomposition) where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_least_succ
  list_higher_raw :=
    recollection.list_higher_raw

/-- Invert a forward expanded-Jacobi value-residual recollection. -/
noncomputable def toInverseRecollection
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {decomposition : ExpandedJacobiDecomposition factor.word}
    (recollection :
      TJRecoll
        (n := n) factor decomposition) :
    TruncatedExpandedRecollection
      (n := n) factor decomposition :=
  let inverse := recollection.toSourceRecollection.inverse
  {
    higherSource := inverse.higherSource
    higher_source_truncated := inverse.higher_source_truncated
    higher_least_succ :=
      inverse.higher_weight_least
    list_higher_raw := by
      intro q
      simpa only [expandedJacobiSource] using
        inverse.list_higher_raw q
  }

end
  TJRecoll

/--
A routed expanded-Jacobi continuation builder whose value residual is
supplied in the forward orientation.
-/
structure
    EJBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  normalizerFamily :
    SSNormala
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d)
  firstResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecollb
                (n := n) (expandedJacobiFactor factor decomposition)
  secondResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecollb
                (n := n) (expandedJacobiSecond factor decomposition)
  valueResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TJRecoll
                (n := n) factor decomposition

namespace
  EJBuild

open
  TJRecoll

/-- Compile forward value residuals into the routed continuation builder. -/
noncomputable def routedCollectionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      EJBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    ECRouted
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  normalizerFamily := builder.normalizerFamily
  firstResidual := builder.firstResidual
  secondResidual := builder.secondResidual
  valueResidualInverse :=
    fun lowerWeight hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      (builder.valueResidual lowerWeight hnonterminal factor decomposition
        hfactorWeight hfactorTruncated).toInverseRecollection

/--
Compile forward value residuals into the builder consumed by expanded Jacobi
collection.
-/
noncomputable def expandedContinuationBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      EJBuild.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight) :
    ECBuild
      (inputWeight := inputWeight) hn hH :=
  (builder.routedCollectionBuilder.splicedCollectionBuilder hinputWeight)
    |>.expandedContinuationBuilder

end
  EJBuild

end TCTex
end Towers

-- Merged from JacobiHallWittStrictTraceBridge.lean

/-!
# Hall-Witt strict-trace bridge for expanded Jacobi residuals

The expanded-Jacobi value residual is exactly the three-head Jacobi packet
represented by the substituted Hall-Witt strict trace.  Consequently, any
fixed symbolic strict-trace source already supported one layer above the
parent constructs the forward value recollection directly.  No semantic
normalizer at the parent layer is needed by this adapter.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


open CWTrace
open HEWord
open STSubsti
open TEAddres
open
  PCSrc

universe u

namespace HEWord

/--
The expanded-Jacobi value packet evaluates exactly to the substituted
Hall-Witt strict trace at its symbolic exponent.
-/
lemma expanded_jacobi_raw
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hx : ∃ left right, decomposition.left = .commutator left right)
    (hy : ∃ left right, decomposition.middle = .commutator left right)
    (hz : ∃ left right, decomposition.right = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedJacobiRaw factor decomposition) =
      wordListEval
        (PEAddres.freeLowerTruncation (n := n))
        (signedStrictTrace decomposition.left decomposition.middle
          decomposition.right (factor.exponent q)) := by
  rw [signed_strict_trace
    (PEAddres.freeLowerTruncation (n := n))
      decomposition.left decomposition.middle decomposition.right hx hy hz
        (factor.exponent q)]
  simp only [expandedJacobiRaw,
    SPFactora.listEval_cons, SPFactora.listEval_nil,
    mul_one, SPFactora.eval,
    SPFactora.wordValue, expandedJacobiFactor,
    expandedJacobiSecond, SPFactora.word_neg,
    SPFactora.word_reword, SPFactora.exponent_neg,
    SPFactora.exponent_reword, zpow_neg]
  have horiginal :
      factor.word.eval
          (PEAddres.freeLowerTruncation (n := n)) =
        (CWord.commutator
          (.commutator decomposition.left decomposition.middle)
            decomposition.right).eval
          (PEAddres.freeLowerTruncation
            (n := n)) := by
    rw [← lower_truncation_tree factor.word,
      ← lower_truncation_tree
        (.commutator (.commutator decomposition.left decomposition.middle)
          decomposition.right)]
    rw [decomposition.tree_eq]
    rfl
  rw [horiginal]
  simp only [inv_zpow]

end HEWord

namespace
  TJRecoll

/--
A fixed higher symbolic Hall-Witt strict-trace source directly supplies the
expanded-Jacobi value recollection, without a parent-layer normalizer.
-/
noncomputable def witt_strict_source
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hx : ∃ left right, decomposition.left = .commutator left right)
    (hy : ∃ left right, decomposition.middle = .commutator left right)
    (hz : ∃ left right, decomposition.right = .commutator left right)
    (strictTrace :
      TWSrc
        (n := n) (inputWeight := inputWeight)
        decomposition.left decomposition.middle decomposition.right
          factor.exponent) :
    TJRecoll
      (n := n) factor decomposition where
  higherSource := strictTrace.source
  higher_source_truncated := strictTrace.source_isTruncated
  higher_least_succ := by
    have hweight := congrArg HallTree.weight decomposition.tree_eq
    simp only [HallTree.weight_commutator, tree_weight] at hweight
    have hsource := strictTrace.source_weight_least
    change SPFactora.WordWeightLeast
      (decomposition.left.weight PEAddres.weight +
          decomposition.middle.weight PEAddres.weight +
        decomposition.right.weight PEAddres.weight + 1)
      strictTrace.source at hsource
    simpa only [hweight] using hsource
  list_higher_raw := by
    intro q
    rw [strictTrace.list_full_trace]
    exact
      (expanded_jacobi_raw
        factor decomposition hx hy hz q).symm

end
  TJRecoll

end TCTex
end Towers

-- Merged from JacobiSignedLeafHallWittTraceBridge.lean

/-!
# Signed-leaf Hall-Witt bridge for expanded Jacobi residuals

The expanded-Jacobi value residual is exactly the three-head Jacobi packet
represented by the signed-leaf Hall-Witt strict trace.  Unlike the root-swap
specialization, this bridge works for arbitrary compressed branch words,
including atomic generator branches.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


open CWTrace
open HEWord
open SLSubsti

universe u

namespace HEWord

/--
The expanded-Jacobi value packet evaluates exactly to the signed-leaf
Hall-Witt strict trace at its symbolic exponent, without visible-commutator
hypotheses on its three compressed branches.
-/
lemma expanded_jacobi_leaf
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedJacobiRaw factor decomposition) =
      wordListEval
        (SLeaf.eval
          (PEAddres.freeLowerTruncation (n := n)))
        (signedLeafStrict decomposition.left decomposition.middle
          decomposition.right (factor.exponent q)) := by
  rw [signed_leaf_strict
    (PEAddres.freeLowerTruncation (n := n))
      decomposition.left decomposition.middle decomposition.right
        (factor.exponent q)]
  simp only [expandedJacobiRaw,
    SPFactora.listEval_cons, SPFactora.listEval_nil,
    mul_one, SPFactora.eval,
    SPFactora.wordValue, expandedJacobiFactor,
    expandedJacobiSecond, SPFactora.word_neg,
    SPFactora.word_reword, SPFactora.exponent_neg,
    SPFactora.exponent_reword, zpow_neg]
  have horiginal :
      factor.word.eval
          (PEAddres.freeLowerTruncation (n := n)) =
        (CWord.commutator
          (.commutator decomposition.left decomposition.middle)
            decomposition.right).eval
          (PEAddres.freeLowerTruncation
            (n := n)) := by
    rw [← lower_truncation_tree factor.word,
      ← lower_truncation_tree
        (.commutator (.commutator decomposition.left decomposition.middle)
          decomposition.right)]
    rw [decomposition.tree_eq]
    rfl
  rw [horiginal]
  simp only [inv_zpow]

end HEWord

end TCTex
end Towers

-- Merged from JacobiValueResidualNormalization.lean

/-!
# Normalizing expanded-Jacobi value residuals

The forward expanded-Jacobi value packet is physically supported at the
parent Hall weight, but its evaluated product starts one lower-central layer
higher by the Jacobi identity.  A semantic normalizer at the parent stratum
therefore recollects this packet into its strictly higher coordinate tail.

Together with generic source inversion and conjugated higher-tail routing,
this removes every non-descendant residual input from expanded-Jacobi
continuation collection.  Recursive callers only need ordinary recollections
of the two Jacobi descendants.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

namespace
  TJRecoll

/--
Normalize the forward expanded-Jacobi value residual and discard its
vanishing active-weight block.
-/
noncomputable def ofNormalizer
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TJRecoll
      (n := n) factor decomposition := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    normalizer.source_recollection_series hn
      (concreteBasicCommutators.{u} d) hH
      (expandedJacobiRaw factor decomposition)
      hlowerWeightPos (by omega)
      (expanded_jacobi_source factor decomposition
        hfactorTruncated)
      (by
        intro x hx
        simp only [expandedJacobiRaw, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · simpa only [SPFactora.word_neg] using
            hfactorWeight.ge
        · simpa only [expanded_jacobi_factor] using
            hfactorWeight.ge
        · simpa only [expanded_second_factor] using
            hfactorWeight.ge)
      (by
        intro q
        simpa only [hfactorWeight] using
          list_expanded_series
            factor decomposition q)
  exact
    {
      higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_least_succ := by
        simpa only [hfactorWeight] using
          recollection.higher_weight_least
      list_higher_raw :=
        recollection.list_higher_raw
    }

/-- Use a normalizer family at the parent Hall-weight stratum. -/
noncomputable def ofNormalizerFamily
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TJRecoll
      (n := n) factor decomposition :=
  ofNormalizer hn hH (family.normalizer lowerWeight) factor decomposition
    hfactorWeight hfactorTruncated

end
  TJRecoll

/--
An expanded-Jacobi continuation builder with automatic conjugation routing
and automatic value-residual normalization.
-/
structure
    JABuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  normalizerFamily :
    SSNormala
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d)
  firstResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecollb
                (n := n) (expandedJacobiFactor factor decomposition)
  secondResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecollb
                (n := n) (expandedJacobiSecond factor decomposition)

namespace
  JABuild

open
  TJRecoll

/-- Compile automatic value-residual normalization into the forward builder. -/
noncomputable def forwardCollectionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      JABuild.{u}
        (inputWeight := inputWeight) hn hH) :
    EJBuild
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  normalizerFamily := builder.normalizerFamily
  firstResidual := builder.firstResidual
  secondResidual := builder.secondResidual
  valueResidual :=
    fun _lowerWeight _hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      ofNormalizerFamily hn hH builder.normalizerFamily factor decomposition
        hfactorWeight hfactorTruncated

/--
Compile automatic value-residual normalization into the builder consumed by
expanded Jacobi collection.
-/
noncomputable def expandedContinuationBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      JABuild.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight) :
    ECBuild
      (inputWeight := inputWeight) hn hH :=
  builder.forwardCollectionBuilder
    |>.expandedContinuationBuilder hinputWeight

end
  JABuild

end TCTex
end Towers

-- Merged from JacobiLocalRecursiveRecollection.lean

/-!
# Local recursive recollection for expanded Hall-power Jacobi roots

An expanded Jacobi root can be recollected once its two ordinary descendants
have been recollected. The remaining pieces are not recursive obligations:

* a semantic normalizer routes the conjugation around the first descendant
  residual;
* the same normalizer family recollects the value-level Jacobi residual;
* the supported Hall-Petresco packet lifts the atomic Jacobi correction.

This file packages that local composition without requiring a global
collection builder for every expanded root. It is intentionally not imported
by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace
  TSRecollb

open
  CDRecoll
  TJRecoll

/--
Recollect one expanded Jacobi root from recollections of its two ordinary
descendants. All nonrecursive packets are supplied by the cutoff packet and
the semantic normalizer family.
-/
noncomputable def expanded_normalizer_family
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
    (normalizerFamily :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (first :
      TSRecollb
        (n := n) (expandedJacobiFactor factor decomposition))
    (second :
      TSRecollb
        (n := n) (expandedJacobiSecond factor decomposition)) :
    TSRecollb
      (n := n) factor :=
  let normalizerAbove :=
    fun strongerWeight _ =>
      normalizerFamily.normalizer strongerWeight
  let valueResidual :=
    ofNormalizerFamily hn hH normalizerFamily factor decomposition
      hfactorWeight hfactorTruncated
  let continuation :=
    routed_normalizer_above packet hinputWeight normalizerAbove factor
      decomposition hfactorWeight hfactorTruncated first second
        valueResidual.toInverseRecollection
  expanded_normalizer_above hn hH packet hinputWeight
    normalizerAbove factor decomposition hfactorWeight hfactorTruncated
      continuation.expandedContinuationRecollection

end
  TSRecollb

end TCTex
end Towers
