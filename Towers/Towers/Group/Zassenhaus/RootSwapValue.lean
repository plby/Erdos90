import
  Towers.Group.Zassenhaus.ChildrenSwapValue
import Towers.Group.Zassenhaus.RootFrontierCollection
import Towers.Group.Zassenhaus.RootSwapRecollection

/-!
# Normalizing expanded-root swap value residuals

The generic sign-corrected root swap leaves a forward skew-value residual.
Its factors remain physically supported at the parent Hall weight, while
skew symmetry places its evaluated value one lower-central stratum higher.
A semantic normalizer at the parent stratum recollects it into a strictly
higher tail.

Together with automatic Jacobi-value normalization and automatic
two-basic-child swap normalization, this leaves only the two ordinary Jacobi
descendant residuals as recursive frontier inputs.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

namespace
  TSRecolla

/-- Normalize the forward root-swap residual into a strictly higher tail. -/
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
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecolla
      (n := n) factor left right hword := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    normalizer.source_recollection_series hn
      (concreteBasicCommutators.{u} d) hH
      (expandedSwapRaw factor left right hword)
      hlowerWeightPos (by omega)
      (truncated_expanded_source factor left right
        hword hfactorTruncated)
      (by
        intro x hx
        simp only [expandedSwapRaw, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · simpa only [SPFactora.word_neg] using
            hfactorWeight.ge
        · simpa only [expanded_root_factor] using
            hfactorWeight.ge)
      (by
        intro q
        simpa only [hfactorWeight] using
          expanded_raw_series
            factor left right hword q)
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
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecolla
      (n := n) factor left right hword :=
  ofNormalizer hn hH (family.normalizer lowerWeight) factor left right hword
    hfactorWeight hfactorTruncated

end
  TSRecolla

/--
An arbitrary-frontier builder with automatic value-packet normalization.
Only the two ordinary expanded-Jacobi descendants remain recursive.
-/
structure
    TABuildb
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  expandedJacobi :
    JABuild.{u}
      (inputWeight := inputWeight) hn hH
  hinputWeight : 1 ≤ inputWeight

namespace
  TABuildb

open
  TSRecolla

/-- Compile every automatic value-packet route into the arbitrary frontier. -/
noncomputable def expandedFrontierBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TABuildb.{u}
        (inputWeight := inputWeight) hn hH) :
    TEBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  basicChildren :=
    builder.expandedJacobi
      |>.childrenOrientationBuilder
        builder.hinputWeight
  hinputWeight := builder.hinputWeight
  normalizerAbove :=
    fun _lowerWeight strongerWeight _ =>
      builder.expandedJacobi.normalizerFamily.normalizer strongerWeight
  rootSwapResidual :=
    fun _lowerWeight _hnonterminal factor left right hword hfactorWeight
        hfactorTruncated =>
      ofNormalizerFamily hn hH builder.expandedJacobi.normalizerFamily factor
        left right hword hfactorWeight hfactorTruncated

/-- Compile automatic frontier normalization into the existing collector. -/
noncomputable def jacobiCollectionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TABuildb.{u}
        (inputWeight := inputWeight) hn hH) :
    TFBuildc.{u}
      (inputWeight := inputWeight) hn hH :=
  builder.expandedFrontierBuilder
    |>.jacobiCollectionBuilder

end
  TABuildb

namespace TSInput

/--
For canonical Hall families, recursive Jacobi-descendant recollections alone
construct the Claim 5 coordinate polynomials.
-/
theorem
    expandedAutomaticBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TABuildb.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.jacobiFrontierBuilder
    hn hsourceSupported builder.jacobiCollectionBuilder
      builder.hinputWeight

end TSInput
end TCTex
end Towers
