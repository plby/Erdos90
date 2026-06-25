import Towers.Group.Zassenhaus.SemanticallyHigherRecollection
import Towers.Group.Zassenhaus.CanonicalHallRecollection

/-!
# Normalizing concrete basic-reduction residuals directly

The explicit atomic reduction packet for a concrete symbolic Hall-power
factor leaves a raw residual source at the same physical Hall weight.  Its
evaluated product starts one lower-central layer higher.  A semantic
normalizer at the factor-weight stratum therefore recollects the whole raw
residual directly into its strictly higher coordinate tail.

This bypasses Jacobi-tree case analysis whenever a semantic normalizer family
is already available.  It also isolates the genuine circular boundary:
constructing that family without assuming current-stratum normalization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

namespace
  TSRecollb

/--
Normalize the full concrete basic-reduction residual and discard its
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
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    normalizer.source_recollection_series hn
      (concreteBasicCommutators.{u} d) hH
      (basicRawSource factor)
      hlowerWeightPos (by omega)
      (truncated_reduction_source factor
        hfactorTruncated)
      (by
        intro x hx
        simp only [basicRawSource, List.mem_append,
          List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact
            hfactorWeight.ge.trans
              (SPFactora.least_inverse_list
                (least_reduction_factors factor) x hx)
        · exact hfactorWeight.ge)
      (by
        intro q
        simpa only [hfactorWeight] using
          list_reduction_series
            factor q)
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

/-- Use a normalizer family at the factor-weight stratum. -/
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
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  ofNormalizer hn hH (family.normalizer lowerWeight) factor hfactorWeight
    hfactorTruncated

end
  TSRecollb

/--
A Hall-Petresco packet and a semantic normalizer family.  Current-stratum
normalization recollects every concrete basic-reduction residual directly.
-/
structure
    TANorma
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
  hinputWeight : 1 ≤ inputWeight

namespace
  TANorma

open
  TSRecollb

/-- Compile direct residual normalization into the automatic comparison collector. -/
noncomputable def automaticComparisonCollection
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TANorma.{u}
        (inputWeight := inputWeight) hn hH) :
    ACBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  basicResidual :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated =>
      ofNormalizerFamily hn hH builder.normalizerFamily factor hfactorWeight
        hfactorTruncated

end
  TANorma

namespace TSInput

/--
For canonical Hall families, a supplied semantic normalizer family directly
constructs the Claim 5 coordinate polynomials.
-/
theorem
    automaticNormalizationBuilder
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
      TANorma.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.automaticComparisonBuilder
    hn hsourceSupported builder.automaticComparisonCollection
      builder.hinputWeight

end TSInput
end TCTex
end Towers
