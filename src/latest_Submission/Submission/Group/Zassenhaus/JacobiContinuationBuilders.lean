import Submission.Group.Zassenhaus.SignCorrectedSwaps
import Submission.Group.Zassenhaus.SignedCorrectionSemantics
import Submission.Group.Zassenhaus.PolynomialBracketSupport

/-!
# Routed expanded polynomial Jacobi continuation builders

The conjugation around the first expanded-Jacobi descendant is not an
independent recursive obligation.  A sharp signed higher-tail normalizer
routes an ordinary recollection of that descendant through the conjugation.
-/

namespace Submission
namespace TCTex

open CEWord

universe u

/--
A recursive expanded-Jacobi continuation builder whose first descendant is
routed automa through its same-weight conjugation.
-/
structure
    CRBuilda
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  normalizerFamily :
    SNFam
      (n := n) (concreteBasicCommutators.{u} d)
  firstResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecoll
                (n := n) (expandedJacobiFactor factor decomposition)
  secondResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecoll
                (n := n) (expandedJacobiSecond factor decomposition)
  valueResidualInverse :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ExpandedJacobiRecollection
                (n := n) factor decomposition

namespace
  CRBuilda

open
  TCRecolla

/--
Compile the routed continuation builder into the explicit three-piece splice.
-/
noncomputable def splicedCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      CRBuilda.{u}
        (d := d) (n := n) hn) :
    CSBuild
      (d := d) (n := n) hn where
  packet := builder.packet
  secondResidual := builder.secondResidual
  conjugatedFirstResidual :=
    fun lowerWeight hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      first_normalizer_above builder.packet
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
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      CRBuilda.{u}
        (d := d) (n := n) hn) :
    CDBuilda
      (d := d) (n := n) hn :=
  builder.splicedCollectionBuilder
    |>.expandedContinuationBuilder

end
  CRBuilda

end TCTex
end Submission

/-!
# Forward expanded polynomial Jacobi value-residual recollections

The recursive expanded-Jacobi splice uses the inverse orientation of its
value-level residual.  A recursive caller may recollect the forward
orientation: generic signed-source inversion constructs the required inverse
recollection.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

/-- Upward recollection of the forward expanded-Jacobi value residual. -/
structure
    TRRecolla
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  higherSource :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (expandedJacobiRaw factor decomposition)

namespace
  TRRecolla

/-- View a concrete forward value-residual recollection as a generic one. -/
noncomputable def toSourceRecollection
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    {decomposition : ExpandedJacobiDecomposition factor.word}
    (recollection :
      TRRecolla
        (n := n) factor decomposition) :
    SSRecol
      (n := n)
      (lowerWeight := factor.word.weight HEAddres.weight + 1)
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
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    {decomposition : ExpandedJacobiDecomposition factor.word}
    (recollection :
      TRRecolla
        (n := n) factor decomposition) :
    ExpandedJacobiRecollection
      (n := n) factor decomposition :=
  let inverse := recollection.toSourceRecollection.inverse
  {
    higherSource := inverse.higherSource
    higher_source_truncated := inverse.higher_source_truncated
    higher_least_succ :=
      inverse.higher_weight_least
    list_higher_raw := by
      intro e
      simpa only [expandedJacobiSource] using
        inverse.list_higher_raw e
  }

end
  TRRecolla

/--
A routed expanded-Jacobi continuation builder whose value residual is
supplied in the forward orientation.
-/
structure
    EFBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  normalizerFamily :
    SNFam
      (n := n) (concreteBasicCommutators.{u} d)
  firstResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecoll
                (n := n) (expandedJacobiFactor factor decomposition)
  secondResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecoll
                (n := n) (expandedJacobiSecond factor decomposition)
  valueResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecolla
                (n := n) factor decomposition

namespace
  EFBuild

open
  TRRecolla

/-- Compile forward value residuals into the routed continuation builder. -/
noncomputable def routedCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      EFBuild.{u}
        (d := d) (n := n) hn) :
    CRBuilda
      (d := d) (n := n) hn where
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
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      EFBuild.{u}
        (d := d) (n := n) hn) :
    CDBuilda
      (d := d) (n := n) hn :=
  builder.routedCollectionBuilder.splicedCollectionBuilder
    |>.expandedContinuationBuilder

end
  EFBuild

end TCTex
end Submission

/-!
# Normalizing expanded polynomial Jacobi value residuals

The forward expanded-Jacobi value packet is physically supported at the
parent Hall weight, but its evaluated product starts one lower-central layer
higher by the Jacobi identity.  A signed semantic normalizer at the parent
stratum recollects this packet into its strictly higher coordinate tail.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

namespace
  TRRecolla

/--
Normalize the forward expanded-Jacobi value residual and discard its
vanishing active-weight block.
-/
noncomputable def ofNormalizer
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecolla
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
        · simpa only [SPFactor.word_neg] using
            hfactorWeight.ge
        · simpa only [expanded_jacobi_factor] using
            hfactorWeight.ge
        · simpa only [expanded_second_factor] using
            hfactorWeight.ge)
      (by
        intro e
        simpa only [hfactorWeight] using
          list_expanded_series
            factor decomposition e)
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
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecolla
      (n := n) factor decomposition :=
  ofNormalizer hn hH (family.normalizer lowerWeight) factor decomposition
    hfactorWeight hfactorTruncated

end
  TRRecolla

/--
An expanded-Jacobi continuation builder with automatic conjugation routing
and automatic value-residual normalization.
-/
structure
    EABuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  normalizerFamily :
    SNFam
      (n := n) (concreteBasicCommutators.{u} d)
  firstResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecoll
                (n := n) (expandedJacobiFactor factor decomposition)
  secondResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecoll
                (n := n) (expandedJacobiSecond factor decomposition)

namespace
  EABuild

open
  TRRecolla

/-- Compile automatic value-residual normalization into the forward builder. -/
noncomputable def forwardCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      EABuild.{u}
        (d := d) (n := n) hn) :
    EFBuild
      (d := d) (n := n) hn where
  packet := builder.packet
  normalizerFamily := builder.normalizerFamily
  firstResidual := builder.firstResidual
  secondResidual := builder.secondResidual
  valueResidual :=
    fun _lowerWeight _hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      ofNormalizerFamily hn
        (fun s hs hsn =>
          concrete_forms_associated d n s hs hsn)
        builder.normalizerFamily factor decomposition hfactorWeight
          hfactorTruncated

/--
Compile automatic value-residual normalization into the builder consumed by
expanded Jacobi collection.
-/
noncomputable def expandedContinuationBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      EABuild.{u}
        (d := d) (n := n) hn) :
    CDBuilda
      (d := d) (n := n) hn :=
  builder.forwardCollectionBuilder
    |>.expandedContinuationBuilder

end
  EABuild

end TCTex
end Submission

/-!
# Local recursive recollection for expanded polynomial Jacobi roots

An expanded Jacobi root can be recollected once its two ordinary descendants
have been recollected.  The remaining pieces are not recursive obligations:

* a signed semantic normalizer routes the conjugation around the first
  descendant residual;
* the same normalizer family recollects the value-level Jacobi residual;
* the supported Hall-Petresco packet lifts the atomic Jacobi correction.

This file packages that local composition without requiring a global
collection builder for every expanded root.  It is intentionally not
imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

namespace
  TRRecoll

open
  TDRecoll
  TRRecolla

/--
Recollect one expanded Jacobi root from recollections of its two ordinary
descendants.  All nonrecursive packets are supplied by the cutoff packet and
the signed semantic normalizer family.
-/
noncomputable def expanded_normalizer_family
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizerFamily :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (first :
      TRRecoll
        (n := n) (expandedJacobiFactor factor decomposition))
    (second :
      TRRecoll
        (n := n) (expandedJacobiSecond factor decomposition)) :
    TRRecoll
      (n := n) factor :=
  let normalizerAbove :=
    fun strongerWeight _ =>
      normalizerFamily.normalizer strongerWeight
  let valueResidual := (
   TRRecolla.ofNormalizerFamily
      hn
      (fun s hs hsn =>
        concrete_forms_associated d n s hs hsn)
      normalizerFamily factor decomposition hfactorWeight hfactorTruncated)
  let continuation :=
    routed_normalizer_above packet normalizerAbove factor
      decomposition hfactorWeight hfactorTruncated first second
        valueResidual.toInverseRecollection
  expanded_normalizer_above hn
    (fun s hs hsn =>
      concrete_forms_associated d n s hs hsn)
    packet normalizerAbove factor decomposition hfactorWeight hfactorTruncated
      continuation.expandedContinuationRecollection

end
  TRRecoll

end TCTex
end Submission
