import Towers.Group.HallBasic.StandardSequence
import Towers.Group.Zassenhaus.TriangularGHLaw
import Towers.Group.Zassenhaus.GuardedGridCoverage
import Towers.Group.Zassenhaus.InverseUniversalClosure
import Towers.Group.Zassenhaus.CorrectionClosureVocabulary
import Towers.Group.Zassenhaus.ErasedWordSkeleton
import Towers.Group.Zassenhaus.PolynomialConcreteSemantic
import Towers.Group.Zassenhaus.PolynomialConcrete
import Towers.Group.Zassenhaus.Polynomial
import Towers.Group.Zassenhaus.PolynomialBracketSupport
import Towers.Group.Zassenhaus.SignedCorrectionSemantics
import Towers.Group.Zassenhaus.ClassTwo
import Towers.Group.Zassenhaus.CanonicalHallRecollection
import Towers.Group.Zassenhaus.RankedResidual
import Towers.Group.Zassenhaus.GuardedGridInput
import Towers.Group.Zassenhaus.RetainedInsertionCollection
import Towers.Group.Zassenhaus.RestrictedFullCollector
import Towers.Group.Zassenhaus.ClassEndpointFibers
import Towers.Group.Zassenhaus.RestrictedFiniteClosure
import Towers.Group.Zassenhaus.RestrictedSharp
import Towers.Group.Zassenhaus.BlockFormulaSubstitution

open Towers.TCTex

/-!
# Free-truncation collection bound reduced to concrete Hall polynomials

The canonical finite Hall families and their associated-graded basis theorem
remove the Hall-data choice from the final free-truncation collection bound.
At arbitrary cutoff, the remaining inputs are precisely the global power,
product, and inverse Hall-coordinate polynomial packages.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u


/--
For the canonical concrete Hall family, the three global coordinate-
polynomial packages imply the free-truncation collection bound.
-/
theorem
    commutators_collect_poly
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hpower :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d)) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData
            (n := n) (concreteCommutatorsWeight.{u} d) e t)
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    TruncationCollectionBound.{u}
      p d n
        (commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n) := by
  apply free_truncation_data
    hn (concreteCommutatorsWeight.{u} d)
      (fun s hs hsn =>
        concrete_forms_associated
          d n s hs hsn)
  · exact hpower
  · exact hproduct
  · exact hinverse

/--
For the canonical concrete Hall family, the three global coordinate-
polynomial packages produce the existential free-truncation bound.
-/
theorem
    truncation_collection_data
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hpower :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d)) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData
            (n := n) (concreteCommutatorsWeight.{u} d) e t)
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  ⟨commutatorCountBelow
      (concreteCommutatorsWeight.{u} d) n,
    commutators_collect_poly
      hn hpower hproduct hinverse⟩

end TCTex
end Towers

/-!
# Free-truncation bound from selected endpoint Hall-power profiles

The canonical Hall-family reduction consumes the selected operational endpoint
finite-index trace route directly.  At arbitrary cutoff, the remaining explicit
inputs are:

* one aggregate selected-endpoint shape-fiber profile and its ordered law,
* supported symbolic sources for the finitely many low input weights,
* local power-factor normalization recursion, and
* global product and inverse coordinate-polynomial packages.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CRLayer
open
  FIBridge

/--
For the canonical Hall family, selected endpoint finite-index trace profiles
and the remaining global product and inverse polynomial packages imply the
existential free-truncation collection bound.
-/
theorem
    trunc_fiber_profiles
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight)
    (hlistEval :
      EIFiber.SatisfiesTruncEval.{u}
        (d := d) kernel)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (factorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight)
                  (concreteCommutatorsWeight.{u} d) factor)
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      collected_fiber_profiles
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          kernel hlistEval lowWeightSource lowWeightSupported
            factorNormalization
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from selected endpoint residual sources

The selected operational endpoint finite-index trace profile supplies the
Hall-power correction packets.  Intrinsic residual-source recollections then
construct the power-factor singleton normalizations recursively.  This file
threads that sharper power boundary into the canonical Hall-family
free-truncation reduction.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CRLayer
open
  FIBridge

/--
For the canonical Hall family, selected endpoint profiles, intrinsic
Hall-power residual sources, and the global product and inverse polynomial
packages imply the existential free-truncation collection bound.
-/
theorem
    trunc_fin_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight)
    (hlistEval :
      EIFiber.SatisfiesTruncEval.{u}
        (d := d) kernel)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TIBuild
            (n := n) (inputWeight := inputWeight) hn
              (concreteCommutatorsWeight.{u} d)
                (fun r hr hrn =>
                  concrete_forms_associated
                    d n r hr hrn))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    trunc_fiber_profiles
      p d n hn kernel hlistEval lowWeightSource lowWeightSupported
  · intro inputWeight hinputWeight lowerWeight _hnonterminal nextNormalizer
      factor hfactorWeight hfactorTruncated
    exact
      (powerBuilders inputWeight hinputWeight).activeBlockNormalization
        kernel hlistEval hinputWeight nextNormalizer factor hfactorWeight
          hfactorTruncated
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from compatible correction-grid residual sources

This file lifts the operational compatible-grid erased-shape Claim 5 boundary
to the canonical Hall-family free-truncation collection bound.  The
Hall-power side is now stated in terms of overlap-aware scheduler batches,
their signed recollection law, low-weight sourced inputs, and intrinsic
factor residual-source recollections.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  EBList
open
  CRLayer
open
  FIProf

/--
For the canonical Hall family, compatible correction-grid erased-shape
batches, intrinsic Hall-power residual sources, and the global product and
inverse polynomial packages imply the existential free-truncation collection
bound.
-/
theorem
    free_trunc_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (decomposition :
      PCDecompb
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (hlistEval :
      PCDecompb.SatisfiesTruncEval.{u}
        (d := d) decomposition raw)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TIBuild
            (n := n) (inputWeight := inputWeight) hn
              (concreteCommutatorsWeight.{u} d)
                (fun r hr hrn =>
                  concrete_forms_associated
                    d n r hr hrn))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    trunc_fin_builders
      p d n hn
        (decomposition.selectedFullFiber
          raw)
        (decomposition.endpointSatisfiesTrunc
          raw hlistEval)
        lowWeightSource lowWeightSupported powerBuilders
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Canonical Hall collection bound from restricted sharp recursion

The direct restricted-sharp powered and signed collectors reduce arbitrary
cutoff recollection to local recursive builders.  Above the class-two source
band the powered input is automatic.  Below it, retain only the finitely many
supported sourced inputs.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


/--
For the canonical Hall family, local restricted-sharp powered and signed
recursive builders imply the existential free-truncation collection bound.
-/
theorem
    sharp_rec_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          RSRec
            (n := n) (inputWeight := inputWeight) hn
              (concreteCommutatorsWeight.{u} d)
                (forms_associated_below
                  d n))
    (signedBuilder :
      SRBuild
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · intro e inputWeight hinputWeight
    by_cases hclassTwoRange : n ≤ 3 * inputWeight
    · exact
        collected_semantic_below
          hn (concreteCommutatorsWeight.{u} d)
            (forms_associated_below
              d n)
            hinputWeight hclassTwoRange
    · exact
        (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          |>.sharpRecursiveBuilder
            hn
              (lowWeightSupported e inputWeight hinputWeight
                hclassTwoRange)
              (powerBuilders inputWeight hinputWeight) hinputWeight
  · intro e
    exact
      commutators_sharp_rec
        hn e signedBuilder
  · intro e
    exact
      sharp_rec_builder
        hn e signedBuilder

end TCTex
end Towers

/-!
# Canonical Hall collection bound from word expansions and singleton normalizations

The direct restricted-sharp recursive collectors can be constructed from
universal higher-word correction expansions and intrinsic singleton
normalizations.  Package that lower-level interface at the free-truncation
boundary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


/--
For the canonical Hall family, universal correction expansions and singleton
normalizations on the powered and signed sides imply the existential
free-truncation collection bound.
-/
theorem
    singleton_collect_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildd
            (n := n) (inputWeight := inputWeight) hn
              (concreteCommutatorsWeight.{u} d)
                (forms_associated_below
                  d n))
    (signedBuilder :
      RSSingle
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    sharp_rec_builders
      p d n hn lowWeightSource lowWeightSupported
  · intro inputWeight hinputWeight
    exact
      (powerBuilders inputWeight hinputWeight)
        |>.restrictedRecursiveBuilder
  · exact signedBuilder.restrictedRecursiveBuilder

end TCTex
end Towers

/-!
# Canonical Hall collection bound from one cutoff signed-block packet

One cutoff-specific all-integral signed-profile packet supplies both powered
and signed higher-word correction expansions directly.  Package that shared
symbolic input at the free-truncation boundary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CFExp

/--
For the canonical Hall family, one cutoff-specific signed-block Hall-Petresco
packet, sourced low-weight powered inputs, and singleton normalizations on the
powered and signed sides imply the existential free-truncation collection
bound.
-/
theorem
    trunc_singleton_normalizations
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (packet : TAInt.{u} d n)
    (powerFactorNormalization :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
                      TANorm
                        (n := n) (lowerWeight := lowerWeight)
                          (concreteCommutatorsWeight.{u} d) factor)
    (signedFactorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1)
                (concreteCommutatorsWeight.{u} d) →
            ∀ (factor :
                SPFactor
                  (concreteCommutatorsWeight.{u} d) ι),
              factor.word.weight HEAddres.weight = lowerWeight →
                factor.word.weight HEAddres.weight < n →
                  TPActive
                    (n := n) (lowerWeight := lowerWeight)
                      (concreteCommutatorsWeight.{u} d) ι factor) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    singleton_collect_builders
      p d n hn lowWeightSource lowWeightSupported
  · intro inputWeight hinputWeight
    exact
      { correctionExpansionFactory :=
          fun lowerWeight _hterminal =>
            packet.powerSupportedFactory
              (by omega) lowerWeight
        factorNormalization :=
          powerFactorNormalization inputWeight hinputWeight }
  · exact
      { correctionExpansionFactory :=
          fun lowerWeight _hterminal =>
            packet.supportedWordFactory
              (WBForm.chooseNormalizerFamily
                (concreteCommutatorsWeight.{u} d))
              lowerWeight
        factorNormalization := signedFactorNormalization }

end TCTex
end Towers

/-!
# Canonical Hall collection bound from the explicit recipe list-evaluation law

The recursive finite-closure profile construction and singleton recipe-chunk
alignment compile the explicit transversal list-evaluation law to one
cutoff-specific signed-block packet.  This file threads that exact remaining
global symbolic recollection theorem into the free-truncation collection
bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open EPSplit
open
  UCAll

/--
For the canonical Hall family, the explicit transversal list-evaluation law,
sourced low-weight powered inputs, and singleton normalizations imply the
existential free-truncation collection bound.
-/
theorem
    lower_singleton_normalizations
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (hlistEval :
      SatisfiesExplicitRecipe.{u} d n)
    (powerFactorNormalization :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
                      TANorm
                        (n := n) (lowerWeight := lowerWeight)
                          (concreteCommutatorsWeight.{u} d) factor)
    (signedFactorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1)
                (concreteCommutatorsWeight.{u} d) →
            ∀ (factor :
                SPFactor
                  (concreteCommutatorsWeight.{u} d) ι),
              factor.word.weight HEAddres.weight = lowerWeight →
                factor.word.weight HEAddres.weight < n →
                  TPActive
                    (n := n) (lowerWeight := lowerWeight)
                      (concreteCommutatorsWeight.{u} d) ι factor) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  trunc_singleton_normalizations
    p d n hn lowWeightSource lowWeightSupported
      ((explicitRecipePacket
        hlistEval).truncatedAllIntegral)
      powerFactorNormalization signedFactorNormalization

end TCTex
end Towers

/-!
# Canonical Hall collection bound from a finite-closure profile assignment

A universal profile assignment on the finite correction-closure skeleton
compiles to the cutoff signed-block packet consumed by powered and signed
recollection.  This file threads that assignment boundary into the
free-truncation collection bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  UCAll
open
  FCAssign

/--
For the canonical Hall family, one universal profile assignment on the
finite correction closure, sourced low-weight powered inputs, and singleton
normalizations imply the existential free-truncation collection bound.
-/
theorem
    trunc_assignment_normalizations
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (assignment : UPAssign.{u} n 1 1)
    (powerFactorNormalization :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
                      TANorm
                        (n := n) (lowerWeight := lowerWeight)
                          (concreteCommutatorsWeight.{u} d) factor)
    (signedFactorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1)
                (concreteCommutatorsWeight.{u} d) →
            ∀ (factor :
                SPFactor
                  (concreteCommutatorsWeight.{u} d) ι),
              factor.word.weight HEAddres.weight = lowerWeight →
                factor.word.weight HEAddres.weight < n →
                  TPActive
                    (n := n) (lowerWeight := lowerWeight)
                      (concreteCommutatorsWeight.{u} d) ι factor) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  trunc_singleton_normalizations
    p d n hn lowWeightSource lowWeightSupported
      ((assignment.truncAllPacket d
        (by simp) (by simp)).truncatedAllIntegral)
      powerFactorNormalization signedFactorNormalization

end TCTex
end Towers

/-!
# Canonical Hall collection bound from recursive finite-closure profiles

Local source and correction profile builders recursively assign formulas to
the finite correction-closure skeleton.  Once the ordered product identity for
that generated packet is known, the assignment feeds both powered and signed
recollection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open scoped commutatorElement

open
  CRAssign

/--
For the canonical Hall family, recursive finite-closure profile builders,
their ordered all-integral product identity, sourced low-weight powered
inputs, and singleton normalizations imply the existential free-truncation
collection bound.
-/
theorem
    free_trunc_normalizations
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (recursiveKernel : RPKern n 1 1)
    (listEval_eq :
      ∀ {G : Type u} [Group G]
        (left right : G)
        (leftExponent rightExponent : ℤ),
          (((recursiveKernel.signedProfileAssignment
              (by simp) (by simp)).toPackets).map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod =
            ⁅left ^ leftExponent, right ^ rightExponent⁆)
    (powerFactorNormalization :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
                      TANorm
                        (n := n) (lowerWeight := lowerWeight)
                          (concreteCommutatorsWeight.{u} d) factor)
    (signedFactorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1)
                (concreteCommutatorsWeight.{u} d) →
            ∀ (factor :
                SPFactor
                  (concreteCommutatorsWeight.{u} d) ι),
              factor.word.weight HEAddres.weight = lowerWeight →
                factor.word.weight HEAddres.weight < n →
                  TPActive
                    (n := n) (lowerWeight := lowerWeight)
                      (concreteCommutatorsWeight.{u} d) ι factor) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  trunc_assignment_normalizations
    p d n hn lowWeightSource lowWeightSupported
      (recursiveKernel.universalProfileAssignment
        (by simp) (by simp) listEval_eq)
      powerFactorNormalization signedFactorNormalization

end TCTex
end Towers

/-!
# Free-truncation bound from finite-index Hall-power profiles

The canonical Hall-family reduction consumes the finite-index Hall-power
route directly.  At arbitrary cutoff, the remaining explicit inputs are:

* raw and selected-correction finite-index shape-fiber profiles,
* their ordered summed-profile recollection law,
* supported symbolic sources for the finitely many low input weights,
* local power-factor normalization recursion, and
* global product and inverse coordinate-polynomial packages.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CRLayer
open
  ISFiber
open
  RHSplit
open
  RFTransv
open
  TFIdx
open
  SICollec

/--
For the canonical Hall family, finite-index Hall-power profiles and the
remaining global product and inverse polynomial packages imply the
existential free-truncation collection bound.
-/
theorem
    free_fiber_profiles
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (raw :
      PTStab n 1 1)
    (corrections :
      SFProf
        layer (by simp) (by simp))
    (hlistEval :
      EFSplit.SatisfiesTruncEval.{u}
        (d := d)
        (fiberProfileSplit
          (PTStab.idxFiberProfile
            raw (by simp) (by simp))
          corrections))
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (factorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight)
                  (concreteCommutatorsWeight.{u} d) factor)
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      forall_fiber_profiles
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          raw corrections hlistEval lowWeightSource lowWeightSupported
            factorNormalization
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from root-trace concrete Hall-tree residual sources

This file lifts the packet-free concrete Hall-tree root-trace Claim 5
boundary to the canonical Hall-family free-truncation collection bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  RPCrit
open
  CRLayer

/--
For the canonical Hall family, concrete-schedule root-trace permutation,
packet-free concrete Hall-tree residual recollections, and the global product
and inverse packages imply the existential free-truncation collection bound.
-/
theorem
    trunc_collect_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (hlistEval :
      GPPerm.SatisfiesTruncEval.{u}
        (d := d) kernel)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      forall_root_builders
        hn kernel hlistEval lowWeightSource lowWeightSupported
          powerBuilders
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from concrete root-trace permutation residual sources

This file lifts the concrete-schedule root-trace permutation Claim 5
boundary to the canonical Hall-family free-truncation collection bound.  The
Hall-power side is stated in terms of the practical root-trace permutation
criterion, its inherited signed recollection law, finitely many low-weight
sourced inputs, and intrinsic factor residual-source recollections.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  RPCrit
open
  CRLayer

/--
For the canonical Hall family, concrete-schedule root-trace permutation,
intrinsic Hall-power residual sources, and the global product and inverse
polynomial packages imply the existential free-truncation collection bound.
-/
theorem
    free_collect_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (hlistEval :
      GPPerm.SatisfiesTruncEval.{u}
        (d := d) kernel)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuild
            (n := n) (inputWeight := inputWeight) hn
              (concreteCommutatorsWeight.{u} d)
                (fun r hr hrn =>
                  concrete_forms_associated
                    d n r hr hrn))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      coord_collect_builders
        hn (concreteCommutatorsWeight.{u} d)
          (fun r hr hrn =>
            concrete_forms_associated
              d n r hr hrn)
          kernel hlistEval lowWeightSource lowWeightSupported
            powerBuilders
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from guarded-grid Jacobi-only Hall-power collection

The cutoff-aware guarded-grid power collector now receives its semantic
normalizer families from the terminating Jacobi-only ranked residual
recursion.  The signed product and inverse packages are supplied by the
structural supported-basic-children collector driven by the same retained
recipe law.

This file composes those reductions.  It is intentionally not imported by the
existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FTOcc
open
  SOAlign
open
  CRLayer
open
  CCThree
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
Guarded-grid Jacobi-only powered recollection and structural signed
recollection imply the existential free lower-central truncation collection
bound.
-/
theorem
    children_collect_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (schedule :
      OOScheda.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          JCBuild.{u}
            (d := d) (n := n) (inputWeight := inputWeight))
    (signedBuilder :
      TBBuild.{u}
        (d := d) (n := n)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      forall_alignment_builders
        hn hrecipes decomposition hprofileAlignment schedule lowWeightSource
          lowWeightSupported powerBuilders
  · intro e
    exact
      commutators_coeff_builder
        hn e signedBuilder hrecipes
  · intro e
    exact
      commutators_supported_builder
        hn e signedBuilder hrecipes

end TCTex
end Towers

/-!
# Free-truncation bound from fixed-packet structural restarts

Fixed-packet generated structural restart routing supplies the powered outer
residual factory.  Jacobi-only support recursion and guarded-grid collection
then construct the Hall-power polynomials, while the structural signed
collector supplies product and inverse polynomials.

This file composes those reductions.  It is intentionally not imported by
the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FTOcc
open
  SOAlign
open
  CRLayer
open
  CCThree
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
Guarded-grid powered collection from fixed-packet generated structural
restarts and structural signed recollection imply the existential free
lower-central truncation collection bound.
-/
theorem
    trunc_children_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (schedule :
      OOScheda.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TFBuilda.{u}
            (d := d) (n := n) (inputWeight := inputWeight))
    (signedBuilder :
      TBBuild.{u}
        (d := d) (n := n)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    children_collect_builders
      p d n hn hrecipes decomposition hprofileAlignment schedule
        lowWeightSource lowWeightSupported _ signedBuilder
  intro inputWeight hinputWeight
  exact
    (powerBuilders inputWeight hinputWeight)
      |>.jacobiOnlyBuilder

end TCTex
end Towers

/-!
# Free-truncation bound with Jacobi-only powered and signed routing

Exact signed-swap cancellation removes the skew-packet callback from the
polynomial product-and-inverse collector.  Compose that narrower signed
interface with fixed-packet generated structural restarts on the powered
side.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FTOcc
open
  SOAlign
open
  CRLayer
open
  CCThree
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
Fixed-packet powered routing and Jacobi-only signed routing imply the
existential free lower-central truncation collection bound.
-/
theorem
    trunc_only_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (schedule :
      OOScheda.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TFBuilda.{u}
            (d := d) (n := n) (inputWeight := inputWeight))
    (signedBuilder :
      PJBuild.{u}
        (d := d) (n := n)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  exact
    trunc_children_builders
      p d n hn hrecipes decomposition hprofileAlignment schedule
        lowWeightSource lowWeightSupported powerBuilders
        signedBuilder.supportedChildrenBuilder

end TCTex
end Towers

/-!
# Free-truncation bound from local canonical profile alignment

This file lifts the guarded-grid local-profile Claim 5 reduction for
canonical Hall families to the existential free lower-central truncation
collection bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FFCanon
open
  CRLayer
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
For the canonical Hall family, guarded raw-source scheduling, word-local
canonical endpoint-profile agreement, the sorted canonical signed law,
packet-free concrete Hall-tree residual recollections, and the product and
inverse packages imply the existential free-truncation collection bound.
-/
theorem
    trunc_global_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      CanonicalProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (hlistEval :
      SatisfiesGlobalTruncated.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      forall_global_builders
        hn decomposition hprofileAlignment hlistEval lowWeightSource
          lowWeightSupported powerBuilders
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from guarded-grid concrete Hall-tree residual sources

This file lifts the guarded finite-index scheduler Claim 5 boundary with
packet-free concrete Hall-tree residual recollections to the canonical
free-truncation collection bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  PGBridge
open
  PGBridge.GIDecomp
open
  RPCrit
open
  CRLayer
open
  PGSrc

/--
For the canonical Hall family, a guarded finite-index scheduler decomposition,
packet-free concrete Hall-tree residual recollections, and the global product
and inverse packages imply the existential free-truncation collection bound.
-/
theorem
    trunc_residual_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hlistEval :
      GPPerm.SatisfiesTruncEval.{u}
        (d := d)
          (guardedPolyPermutation
            decomposition))
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  trunc_collect_builders
    p d n hn
      (guardedPolyPermutation
        decomposition)
      hlistEval lowWeightSource lowWeightSupported powerBuilders
        hproduct hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from guarded-grid canonical packet alignment

This file lifts the guarded-grid canonical Hall-tree Claim 5 reduction to the
existential free lower-central truncation collection bound.  The generated
signed-law premise is replaced by literal canonical packet alignment and the
canonical recipe-product theorem.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  PGBridge
open
  PGBridge.GIDecomp
open
  RPCrit
open
  CRLayer
open
  CPSplit
open
  PGSrc

/--
For the canonical Hall family, guarded raw-source scheduling, literal
canonical packet alignment, the canonical signed recipe law, packet-free
concrete Hall-tree residual recollections, and the product and inverse
packages imply the existential free-truncation collection bound.
-/
theorem
    global_collect_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (halignment :
      GPPerm.GlobalPacketAlignment.{u}
        (d := d)
          (guardedPolyPermutation
            decomposition))
    (hlistEval :
      SatisfiesRecipeTruncated.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  trunc_residual_builders
    p d n hn decomposition
      ((guardedPolyPermutation
        decomposition)
          |>.satisfies_trunc_recipe
            halignment hlistEval)
      lowWeightSource lowWeightSupported powerBuilders hproduct hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from an ordered retained occurrence schedule

This file lifts the guarded-grid ordered occurrence-schedule Claim 5
reduction for canonical Hall families to the existential free lower-central
truncation collection bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  OOSched
open
  SOAlign
open
  CRLayer
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
For the canonical Hall family, guarded raw-source scheduling, word-local
retained-transversal endpoint-profile agreement, a combined ordered
occurrence schedule, packet-free concrete Hall-tree residual recollections,
and the product and inverse packages imply the existential free-truncation
collection bound.
-/
theorem
    occ_collect_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (schedule :
      COScheda.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      collected_coord_builders
        hn decomposition hprofileAlignment schedule lowWeightSource
          lowWeightSupported powerBuilders
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from retained-transversal profile alignment

This file lifts the guarded-grid retained-transversal Claim 5 reduction for
canonical Hall families to the existential free lower-central truncation
collection bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  SOAlign
open
  CRLayer
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
For the canonical Hall family, guarded raw-source scheduling, word-local
retained-transversal endpoint-profile agreement, the sorted retained signed
law, packet-free concrete Hall-tree residual recollections, and the product
and inverse packages imply the existential free-truncation collection bound.
-/
theorem
    residual_collect_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (hlistEval :
      SatisfiesCoefficientTruncated.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      coord_forall_builders
        hn decomposition hprofileAlignment hlistEval lowWeightSource
          lowWeightSupported powerBuilders
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Free-truncation bound from a cutoff-aware ordered occurrence schedule

This file lifts the guarded-grid cutoff-aware ordered occurrence-schedule
Claim 5 reduction for canonical Hall families to the existential free
lower-central truncation collection bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FTOcc
open
  SOAlign
open
  CRLayer
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
For the canonical Hall family, guarded raw-source scheduling, word-local
retained-transversal endpoint-profile agreement, a cutoff-aware ordered
occurrence schedule, packet-free concrete Hall-tree residual recollections,
and the product and inverse packages imply the existential free-truncation
collection bound.
-/
theorem
    trunc_occ_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (schedule :
      OOScheda.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      forall_trunc_builders
        hn decomposition hprofileAlignment schedule lowWeightSource
          lowWeightSupported powerBuilders
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Canonical Hall collection bound from Hall-Petresco packets

Cutoff Hall-Petresco packets construct the universal higher-word correction
expansions needed by the restricted-sharp collectors.  Package that compilation
at the free-truncation boundary, leaving only sourced low-weight inputs and
semantic singleton recollection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


/--
For the canonical Hall family, cutoff Hall-Petresco packets and singleton
normalizations on the powered and signed sides imply the existential
free-truncation collection bound.
-/
theorem
    trunc_singleton_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          SCBuildb
            (n := n) (inputWeight := inputWeight) hn
              (concreteCommutatorsWeight.{u} d)
                (forms_associated_below
                  d n))
    (signedBuilder :
      RSBuilda
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    singleton_collect_builders
      p d n hn lowWeightSource lowWeightSupported
  · intro inputWeight hinputWeight
    exact
      (powerBuilders inputWeight hinputWeight)
        |>.restrictedSharpExpansion
          hinputWeight
  · exact
      signedBuilder.restrictedSharpChoose
        |>.restrictedSharpExpansion

end TCTex
end Towers

/-!
# Free-truncation bound from cutoff-aware canonical Hall power data

The canonical Hall-basis reduction asks for global power, product, and
inverse coordinate-polynomial packages.  The cutoff-aware guarded-grid power
collector now supplies the power package from semantic normalizer families,
its retained-profile schedule, and finitely many low-weight sourced inputs.

This file composes those two reductions.  It leaves the remaining global
obligations visible: construct the semantic normalizer families and supply
the independent product and inverse polynomial packages.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FTOcc
open
  SOAlign
open
  CRLayer
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
The cutoff-aware retained-transversal canonical Hall-power route, together
with the independent product and inverse packages, implies the existential
free lower-central truncation collection bound.
-/
theorem
    trunc_occ_families
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (schedule :
      OOScheda.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (normalizerFamilies :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          SSNormala
            (n := n) (inputWeight := inputWeight)
              (concreteBasicCommutators.{u} d))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      occ_normalizer_families
        hn decomposition hprofileAlignment schedule lowWeightSource
          lowWeightSupported normalizerFamilies
  · exact hproduct
  · exact hinverse

/--
The same free-truncation reduction can be stated at the recursive semantic
boundary: universal derivation builders generate the normalizer families
required by the cutoff-aware canonical Hall-power route.
-/
theorem
    semantic_derivation_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (schedule :
      OOScheda.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TDBuildb
            (n := n) (inputWeight := inputWeight)
              (concreteBasicCommutators.{u} d))
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    trunc_occ_families
      p d n hn decomposition hprofileAlignment schedule lowWeightSource
        lowWeightSupported
        (fun inputWeight hinputWeight =>
          (builders inputWeight hinputWeight)
            |>.supportedSemanticFamily
              hn (concreteBasicCommutators.{u} d)
                (forms_associated_below
                  d n))
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Canonical Hall collection bound with structural powered and signed descendants

Retained recipe traces supply every correction packet. On both the powered
and signed sides, only rank-zero roots are classified explicitly: recursively
emitted descendants are scheduled through structural two-basic-child Hall
recursion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CCThree

/--
For the canonical Hall family, retained recipe traces, supported low-weight
power sources, and structural powered and signed root routing imply the
existential free-truncation collection bound.
-/
theorem
    free_children_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          CCBuilda.{u}
            (d := d) (n := n) (inputWeight := inputWeight))
    (signedBuilder :
      TBBuild.{u}
        (d := d) (n := n)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      commutators_forall_builders
        hn hrecipes lowWeightSource lowWeightSupported powerBuilders
  · intro e
    exact
      commutators_coeff_builder
        hn e signedBuilder hrecipes
  · intro e
    exact
      commutators_supported_builder
        hn e signedBuilder hrecipes

end TCTex
end Towers

/-!
# Canonical Hall collection bound from retained traces and ranked residuals

Retained recipe traces supply every correction packet. Support-local
Hall-ranked recursion compiles signed and powered outer residual factories and
branch classifications directly to the symbolic recollection polynomials
consumed by the free lower-central truncation collection bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CCThree

/--
For the canonical Hall family, one retained recipe-product law, supported
low-weight power sources, and support-local ranked residual builders imply the
existential free-truncation collection bound.
-/
theorem
    trunc_ranked_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TCBuildb.{u}
            (d := d) (n := n) (inputWeight := inputWeight))
    (signedBuilder :
      PCBuild.{u}
        (d := d) (n := n)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      commutators_poly_builders
        hn hrecipes lowWeightSource lowWeightSupported powerBuilders
  · intro e
    exact
      coeff_collect_builder
        hn e signedBuilder hrecipes
  · intro e
    exact
      poly_collect_builder
        hn e signedBuilder hrecipes

end TCTex
end Towers

/-!
# Canonical Hall collection bound from retained traces and insertion schedules

The retained recipe trace law constructs the powered and signed correction
packets directly.  This file records the resulting canonical arbitrary-cutoff
boundary: only genuinely low-weight powered sources and packet-free reachable
insertion schedules remain.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CCThree

/--
For the canonical Hall family, one retained recipe-product law, supported
low-weight power sources, and packet-free reachable insertion schedules imply
the existential free-truncation collection bound.
-/
theorem
    trunc_reachable_schedules
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerSchedules :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          RIDeriva
            (n := n) (inputWeight := inputWeight)
              (concreteCommutatorsWeight.{u} d))
    (signedSchedule :
      TIDeriva
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      reachable_insertion_schedules
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          hrecipes lowWeightSource lowWeightSupported powerSchedules
  · intro e
    exact
      collected_reachable_insertion
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e hrecipes signedSchedule
  · intro e
    exact
      reachable_insertion_schedule
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e hrecipes signedSchedule

end TCTex
end Towers

/-!
# Canonical Hall collection bound from the retained recipe transversal

The canonical Hall-family reduction consumes the fixed occurrence-preserving
retained recipe trace directly.  At arbitrary cutoff, the remaining explicit
power inputs are its ordered product law, supported symbolic sources for the
finitely many low input weights, and local power-factor normalization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CSAggreg
open
  CCThree

/--
For the canonical Hall family, the ordered retained-recipe trace law and the
remaining global product and inverse polynomial packages imply the
existential free-truncation collection bound.
-/
theorem
    free_truncation_collection
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {kernel : OCShape}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (factorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight)
                  (concreteCommutatorsWeight.{u} d) factor)
    (hproduct :
      ∀ e :
          List
            (HEFam
              (concreteCommutatorsWeight.{u} d)),
        CollectedCoordinateData
          (n := n) (concreteCommutatorsWeight.{u} d) e)
    (hinverse :
      ∀ e :
          HEFam
            (concreteCommutatorsWeight.{u} d),
        CollectedInverseData
          (n := n) (concreteCommutatorsWeight.{u} d) e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      collected_forall_trace
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          (kernel := kernel) hrecipes lowWeightSource lowWeightSupported
            factorNormalization
  · exact hproduct
  · exact hinverse

end TCTex
end Towers

/-!
# Canonical Hall collection bound from retained traces and signed insertion

The retained recipe trace law constructs both the power correction data and
the correction-packet schedule for signed product and inverse recollection.
This file records the resulting canonical arbitrary-cutoff boundary: on the
signed side, only the packet-free reachable insertion schedule remains.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CSAggreg
open
  CCThree

/--
For the canonical Hall family, the retained recipe trace law, power
normalization, and packet-free reachable signed insertion schedule imply the
existential free-truncation collection bound.
-/
theorem
    trunc_insertion_schedule
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {kernel : OCShape}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerFactorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight)
                  (concreteCommutatorsWeight.{u} d) factor)
    (schedule :
      TIDeriva
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    free_truncation_collection
      p d n hn (kernel := kernel) hrecipes lowWeightSource
        lowWeightSupported powerFactorNormalization
  · intro e
    exact
      collected_reachable_insertion
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e hrecipes schedule
  · intro e
    exact
      reachable_insertion_schedule
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e hrecipes schedule

end TCTex
end Towers

/-!
# Canonical Hall collection bound from retained power traces and signed collection

The global Hall product and inverse coordinate-polynomial packages have one
shared recursive signed-semantic source.  This file composes that source with
the retained recipe trace power reduction, so the final arbitrary-cutoff
boundary asks for the reachable signed-semantic builder itself rather than two
separately derived global packages.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CSAggreg
open
  CCThree

/--
For the canonical Hall family, the retained recipe trace power law and one
reachable signed-semantic product/inverse builder imply the existential
free-truncation collection bound.
-/
theorem
    semantic_collect_builder
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {kernel : OCShape}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerFactorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight)
                  (concreteCommutatorsWeight.{u} d) factor)
    (collectionBuilder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    free_truncation_collection
      p d n hn (kernel := kernel) hrecipes lowWeightSource
        lowWeightSupported powerFactorNormalization
  · intro e
    exact
      reachable_semantic_derivation
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e collectionBuilder
  · intro e
    exact
      reachable_derivation_builder
        hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            concrete_forms_associated
              d n s hs hsn)
          e collectionBuilder

end TCTex
end Towers

/-!
# Canonical Hall collection bound from retained power traces and restricted sharp data

The direct restricted-sharp signed collector exposes the low-weight recursive
data still needed for global Hall product and inverse recollection.  Composing
it with the retained recipe trace power reduction gives a canonical
arbitrary-cutoff boundary whose remaining hypotheses are local.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CSAggreg
open
  CCThree

/--
For the canonical Hall family, the retained recipe trace power law and direct
restricted-sharp product/inverse recursion imply the existential
free-truncation collection bound.
-/
theorem
    trunc_sharp_rec
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {kernel : OCShape}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerFactorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight)
                  (concreteCommutatorsWeight.{u} d) factor)
    (collectionBuilder :
      SRBuild
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    free_truncation_collection
      p d n hn (kernel := kernel) hrecipes lowWeightSource
        lowWeightSupported powerFactorNormalization
  · intro e
    exact
      commutators_sharp_rec
        hn e collectionBuilder
  · intro e
    exact
      sharp_rec_builder
        hn e collectionBuilder

end TCTex
end Towers

/-!
# Canonical Hall collection bound from one retained recipe law and residual data

The retained recipe-coefficient product law supplies both the power trace and
the product/inverse correction factories.  After that shared packet is
compiled, the product/inverse side only asks for intrinsic factor-residual
normalization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CSAggreg
open
  CCThree
open
  SRBuild

/--
For the canonical Hall family, one retained recipe-coefficient law, power
residual normalization, and signed factor-residual normalization imply the
existential free-truncation collection bound.
-/
theorem
    trunc_restr_sharp
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {kernel : OCShape}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerFactorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight)
                  (concreteCommutatorsWeight.{u} d) factor)
    (factorResidual :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1)
                (concreteCommutatorsWeight.{u} d) →
            ∀ (factor :
                SPFactor
                  (concreteCommutatorsWeight.{u} d) ι),
              factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPExp
                  (lowerWeight := lowerWeight) hn
                    (concreteCommutatorsWeight.{u} d)
                      (fun r hr hrn =>
                        concrete_forms_associated
                          d n r hr hrn)
                    ι factor) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    trunc_sharp_rec
      p d n hn (kernel := kernel) hrecipes lowWeightSource
        lowWeightSupported powerFactorNormalization
  exact
    recipe_coeff_trace hrecipes factorResidual

end TCTex
end Towers

/-!
# Canonical Hall collection bound from retained traces and singleton normalization

One retained recipe-coefficient product law supplies both the Hall-power trace
and the product/inverse Hall-Petresco packet.  The remaining recursive
normalization callbacks are now stated symmetrically: singleton normalization
for power factors and for signed polynomial factors.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CSAggreg
open
  CCThree

/--
For the canonical Hall family, one retained recipe-coefficient law and local
singleton-normalization callbacks imply the existential free-truncation
collection bound.
-/
theorem
    restr_sharp_singleton
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    {kernel : OCShape}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerFactorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight)
                  (concreteCommutatorsWeight.{u} d) factor)
    (factorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1)
                (concreteCommutatorsWeight.{u} d) →
            ∀ (factor :
                SPFactor
                  (concreteCommutatorsWeight.{u} d) ι),
              factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPActive
                  (n := n) (lowerWeight := lowerWeight)
                    (concreteCommutatorsWeight.{u} d) ι factor) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    free_truncation_collection
      p d n hn (kernel := kernel) hrecipes lowWeightSource
        lowWeightSupported powerFactorNormalization
  · intro e
    exact
      collected_coord_norm
        hn (concreteCommutatorsWeight.{u} d)
          (fun r hr hrn =>
            concrete_forms_associated
              d n r hr hrn)
          e hrecipes factorNormalization
  · intro e
    exact
      collected_coord_coeff
        hn (concreteCommutatorsWeight.{u} d)
          (fun r hr hrn =>
            concrete_forms_associated
              d n r hr hrn)
          e hrecipes factorNormalization

end TCTex
end Towers

/-!
# Canonical Hall collection bound with structural signed descendants

Retained recipe traces supply every correction packet. The powered collector
uses support-local ranked residual builders. On the signed side, only
rank-zero roots are classified explicitly: recursively emitted descendants
are scheduled through the structural two-basic-child Hall recursion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CCThree

/--
For the canonical Hall family, retained recipe traces, supported low-weight
power sources, powered ranked builders, and structural signed root routing
imply the existential free-truncation collection bound.
-/
theorem
    ranked_children_builders
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (powerBuilders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TCBuildb.{u}
            (d := d) (n := n) (inputWeight := inputWeight))
    (signedBuilder :
      TBBuild.{u}
        (d := d) (n := n)) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    truncation_collection_data
      p d n hn
  · exact
      commutators_poly_builders
        hn hrecipes lowWeightSource lowWeightSupported powerBuilders
  · intro e
    exact
      commutators_coeff_builder
        hn e signedBuilder hrecipes
  · intro e
    exact
      commutators_supported_builder
        hn e signedBuilder hrecipes

end TCTex
end Towers

/-!
# Canonical Hall collection bound from one universal Hall-Petresco packet

A universal all-integral Hall-Petresco packet specializes to every
lower-central cutoff and serves both powered and signed recollection.  This
file packages that shared global symbolic input at the free-truncation
boundary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


/--
For the canonical Hall family, one universal Hall-Petresco packet, sourced
low-weight powered inputs, and singleton normalizations on the powered and
signed sides imply the existential free-truncation collection bound.
-/
theorem
    packet_singleton_normalizations
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (packet :
      PFSubsti.UAInt.{u})
    (powerFactorNormalization :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
                      TANorm
                        (n := n) (lowerWeight := lowerWeight)
                          (concreteCommutatorsWeight.{u} d) factor)
    (signedFactorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1)
                (concreteCommutatorsWeight.{u} d) →
            ∀ (factor :
                SPFactor
                  (concreteCommutatorsWeight.{u} d) ι),
              factor.word.weight HEAddres.weight = lowerWeight →
                factor.word.weight HEAddres.weight < n →
                  TPActive
                    (n := n) (lowerWeight := lowerWeight)
                      (concreteCommutatorsWeight.{u} d) ι factor) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    trunc_singleton_builders
      p d n hn lowWeightSource lowWeightSupported
  · intro inputWeight hinputWeight
    exact
      { packet := packet.truncatedAll
        factorNormalization :=
          powerFactorNormalization inputWeight hinputWeight }
  · exact
      { packet := packet.truncatedAll
        factorNormalization := signedFactorNormalization }

end TCTex
end Towers

/-!
# Canonical Hall collection bound from one universal signed-block packet

Signed-profile Hall-Petresco packets are a stronger symbolic language than
positive recipe lists: one universal packet supplies both powered and signed
higher-word correction expansions directly.  Package that shared symbolic
input at the free-truncation boundary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CFExp

/--
For the canonical Hall family, one universal signed-block Hall-Petresco
packet, sourced low-weight powered inputs, and singleton normalizations on the
powered and signed sides imply the existential free-truncation collection
bound.
-/
theorem
    free_singleton_normalizations
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (packet : UAPkt.{u})
    (powerFactorNormalization :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
                      TANorm
                        (n := n) (lowerWeight := lowerWeight)
                          (concreteCommutatorsWeight.{u} d) factor)
    (signedFactorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1)
                (concreteCommutatorsWeight.{u} d) →
            ∀ (factor :
                SPFactor
                  (concreteCommutatorsWeight.{u} d) ι),
              factor.word.weight HEAddres.weight = lowerWeight →
                factor.word.weight HEAddres.weight < n →
                  TPActive
                    (n := n) (lowerWeight := lowerWeight)
                      (concreteCommutatorsWeight.{u} d) ι factor) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    singleton_collect_builders
      p d n hn lowWeightSource lowWeightSupported
  · intro inputWeight hinputWeight
    exact
      { correctionExpansionFactory :=
          fun lowerWeight _hterminal =>
            packet.powerSupportedFactory
              (by omega) lowerWeight
        factorNormalization :=
          powerFactorNormalization inputWeight hinputWeight }
  · exact
      { correctionExpansionFactory :=
          fun lowerWeight _hterminal =>
            packet.truncatedAllIntegral
              |>.supportedWordFactory
                (WBForm.chooseNormalizerFamily
                  (concreteCommutatorsWeight.{u} d))
                lowerWeight
        factorNormalization := signedFactorNormalization }

end TCTex
end Towers

/-!
# Canonical Hall collection bound from one universal signed-block assignment

A universal signed-block profile assignment compiles to the shared
Hall-Petresco packet consumed by both powered and signed recollection.  This
file threads that constructive assignment boundary into the free-truncation
collection bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open UWSkelet

/--
For the canonical Hall family, one universal signed-block profile assignment,
sourced low-weight powered inputs, and singleton normalizations on the powered
and signed sides imply the existential free-truncation collection bound.
-/
theorem
    assignment_singleton_normalizations
    (p d n leftWeight rightWeight : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (powerFactorNormalization :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1)
                      (concreteCommutatorsWeight.{u} d) →
                ∀ (factor :
                    SPFactora
                      (concreteCommutatorsWeight.{u} d)
                        inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
                      TANorm
                        (n := n) (lowerWeight := lowerWeight)
                          (concreteCommutatorsWeight.{u} d) factor)
    (signedFactorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1)
                (concreteCommutatorsWeight.{u} d) →
            ∀ (factor :
                SPFactor
                  (concreteCommutatorsWeight.{u} d) ι),
              factor.word.weight HEAddres.weight = lowerWeight →
                factor.word.weight HEAddres.weight < n →
                  TPActive
                    (n := n) (lowerWeight := lowerWeight)
                      (concreteCommutatorsWeight.{u} d) ι factor) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  free_singleton_normalizations
    p d n hn lowWeightSource lowWeightSupported
      assignment.universalAllPacket
      powerFactorNormalization signedFactorNormalization

end TCTex
end Towers
