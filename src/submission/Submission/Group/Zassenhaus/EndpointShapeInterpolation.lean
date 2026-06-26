import Submission.Group.Zassenhaus.RetainedHistoryFibers
import Submission.Group.Zassenhaus.ClassTwo
import Submission.Group.Zassenhaus.FactorSourceReduction
import Submission.Group.Zassenhaus.RestrictedSharp

/-!
# Claim 5 from cutoff-full endpoint shape-fiber interpolation

At root weights, endpoint recipe-shape fiber interpolation supplies one
natural signed-block packet for the cutoff-full collector.  Once that packet
has an all-integral lift, the existing restricted-sharp singleton collector
constructs the Claim 5 coordinate polynomials.

This file keeps the remaining signed extension and local factor-normalization
obligations explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open
  FSInterp
open
  FPInterp
open CRLayer
open
  CFExp
open
  CFSubsti
open
  UNPkt

namespace
  FPInterp
namespace EFInterp

/--
At root weights, endpoint shape-fiber interpolation supplies the natural
signed-block packet consumed by all-integral lifting.
-/
def truncNaturalPacket
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets) :
    TBPkt.{u} d n :=
  (interpolation.naturalFixedInterpolation
    (by simp) (by simp))
      |>.truncNaturalPacket

@[simp]
lemma packetsTruncNatural
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets) :
    (interpolation.truncNaturalPacket (d := d)).packets =
      packets :=
  rfl

/-- The remaining signed extension of the root endpoint-fiber packet. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets) :
    Prop :=
  TBPkt.AILift.{u}
    (interpolation.truncNaturalPacket (d := d))

end EFInterp
end
  FPInterp

namespace
  SSBuild

/--
Endpoint shape-fiber interpolation and its signed lift supply the generic
restricted-sharp signed-block builder.
-/
def endpointFiberInterpolation
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (lift :
      EFInterp.AILift.{u}
        (d := d) interpolation)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor) :
    SSBuild
      (n := n) (inputWeight := inputWeight) hn H hH where
  packet :=
    lift.truncatedAllIntegral
  factorNormalization :=
    factorNormalization

end
  SSBuild

open
  SSBuild

namespace TSInput

/--
Endpoint shape-fiber interpolation, its signed lift, singleton recollections,
and graded Hall bases construct the Claim 5 coordinate polynomials.
-/
theorem
    fiberInterpolationLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (lift :
      EFInterp.AILift.{u}
        (d := d) interpolation)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSharpSingleton
    hn H hH hsourceSupported
      (endpointFiberInterpolation
        interpolation lift factorNormalization)
      hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Endpoint-interpolation Hall-power collection from residual sources

An endpoint shape-fiber interpolation and its all-integral signed lift supply
the powered adjacent-swap correction packet at every support stratum.
Explicit recollections of the intrinsic residual source of each nonterminal
active factor supply the remaining local input.

This file compiles those inputs to the restricted-sharp recursive collector.
It also packages the quantified Claim 5 boundary: above the automatic
class-two source range no custom input is needed, while the finitely many
lower input weights ask only for supported sourced inputs and intrinsic
factor-residual recollections.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  FPInterp
open
  CRLayer
open
  CFExp
open
  CFSubsti

/--
For one Hall-power input weight, intrinsic factor-residual recollections are
the remaining local input after endpoint interpolation has supplied the
powered correction packets.
-/
structure
    TSBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  factorResidualSource :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor : SPFactora H inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TSSrc
              (lowerWeight := lowerWeight) hn H hH factor

namespace
  TSBuild

/--
Compile endpoint interpolation and intrinsic residual-source recollections to
the direct restricted-sharp recursive collector.
-/
noncomputable def restrictedRecursiveBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (builder :
      TSBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (interpolation :
      EFInterp layer packets)
    (lift :
      EFInterp.AILift.{u}
        (d := d) interpolation)
    (hinputWeight : 1 ≤ inputWeight) :
    RSRec
      (n := n) (inputWeight := inputWeight) hn H hH where
  correctionFactory lowerWeight _hterminal :=
    (lift.truncatedAllIntegral
      |>.powerSupportedFactory
        (by omega) lowerWeight)
      |>.correctionPacketFactory
  factorResidual lowerWeight hterminal _nextNormalizer factor hfactorWeight
      hfactorTruncated :=
    (builder.factorResidualSource lowerWeight hterminal factor hfactorWeight
      hfactorTruncated)
      |>.factorExpansion

/--
The recursively generated semantic normalizer supplies singleton
normalization for every active factor.
-/
noncomputable def activeBlockNormalization
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (builder :
      TSBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (interpolation :
      EFInterp layer packets)
    (lift :
      EFInterp.AILift.{u}
        (d := d) interpolation)
    (hinputWeight : 1 ≤ inputWeight)
    (_nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TANorm
      (n := n) (lowerWeight := lowerWeight) H factor :=
  TANorm.ofNormalizer
    ((builder.restrictedRecursiveBuilder interpolation lift
        hinputWeight)
      |>.semanticCoordinateNormalizer hn H hH lowerWeight)
    factor (by omega) hfactorTruncated

end
  TSBuild

namespace TSInput

/--
Endpoint interpolation, its signed lift, and intrinsic residual-source
recollections construct Claim 5 data for one supported sourced input.
-/
theorem
    coordFiberBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (lift :
      EFInterp.AILift.{u}
        (d := d) interpolation)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TSBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSharpRecursive
    hn H hH hsourceSupported
      (builder.restrictedRecursiveBuilder interpolation lift
        hinputWeight)
      hinputWeight

end TSInput

/--
Endpoint interpolation, its signed lift, finitely many supported low-weight
sources, and intrinsic residual-source recollections construct the complete
quantified Claim 5 power input.
-/
theorem
    forall_endpoint_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (lift :
      EFInterp.AILift.{u}
        (d := d) interpolation)
    (lowWeightSource :
      ∀ (e : HEFam H) (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight) H e)
    (lowWeightSupported :
      ∀ (e : HEFam H) (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuild
            (n := n) (inputWeight := inputWeight) hn H hH) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hclassTwoRange : n ≤ 3 * inputWeight
  · exact
      collected_semantic_below
        hn H hH hinputWeight hclassTwoRange
  · exact
      TSInput.coordFiberBuilder
        hn H hH interpolation lift
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          (builders inputWeight hinputWeight) hinputWeight

/--
The endpoint-interpolation residual-source collector therefore yields the
weight-controlled polynomial degree bound for every Hall coordinate of a
power.
-/
theorem
    interpolation_collect_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (lift :
      EFInterp.AILift.{u}
        (d := d) interpolation)
    (lowWeightSource :
      ∀ (e : HEFam H) (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight) H e)
    (lowWeightSupported :
      ∀ (e : HEFam H) (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuild
            (n := n) (inputWeight := inputWeight) hn H hH)
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    IVMost
      (fun q : ℕ => hallCoordinate hn H hH (u ^ q) i)
      (s / r) := by
  exact
    integer_valued_most
      hn H hH
        (forall_endpoint_builders
          hn H hH interpolation lift lowWeightSource lowWeightSupported
            builders)
        u hu hr hs hsn i

end TCTex
end Submission

/-!
# Claim 5 from uniform endpoint shape-fiber formula packets

The cutoff-full endpoint route reduces scalar collection to one unrestricted
formula packet per retained erased Hall word.  When those packets have
homogeneous presentations, they produce the fixed endpoint-fiber interpolation
consumed by the restricted-sharp singleton collector.

This file packages that composition.  The remaining signed extension and
local factor-normalization obligations stay explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open
  FFInhomo
open
  FPInterp
open CRLayer
open
  CFSubsti
open
  UNPkt

namespace
  FFInhomo
namespace FHPres

/--
The signed extension still needed after uniform endpoint-fiber formula packets
have been presented homogeneously.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      FHPres layer) :
    Prop :=
  EFInterp.AILift.{u}
    (d := d) kernel.fiberProfileInterpolation

end FHPres
end
  FFInhomo

namespace
  SSBuild

/--
Uniform endpoint-fiber packets, homogeneous presentations, and a signed lift
supply the restricted-sharp singleton collection builder.
-/
def endpointHomogeneousPresentation
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {layer : NRLayer n 1 1}
    (kernel :
      FHPres layer)
    (lift :
      FHPres.AILift.{u}
        (d := d) kernel)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor) :
    SSBuild
      (n := n) (inputWeight := inputWeight) hn H hH :=
  endpointFiberInterpolation
    kernel.fiberProfileInterpolation
    lift factorNormalization

end
  SSBuild

open
  SSBuild

namespace TSInput

/--
Uniform endpoint-fiber formula packets with homogeneous presentations, their
signed lift, singleton recollections, and graded Hall bases construct the
Claim 5 coordinate polynomials.
-/
theorem
    fiberHomogeneousLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      FHPres layer)
    (lift :
      FHPres.AILift.{u}
        (d := d) kernel)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.fiberInterpolationLift
    hn H hH kernel.fiberProfileInterpolation
      lift hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from the shallow cutoff-full endpoint shape fibers

At cutoff at most two the cutoff-full endpoint packet is empty.  At cutoff
three its fixed-slot vocabulary is the singleton basic Hall pair and its
profile is the ordinary bilinear Hall-Petresco coefficient.  Both packets have
their all-integral laws without any further symbolic interpolation theorem.

This file discharges their signed lifts and routes the resulting operational
endpoint-fiber packets to the Claim 5 coordinate polynomials.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open
  CTBoundaa
open
  FFInhomo
open
  FLZero
open CRLayer
open NRSubinv
open BRSpec
open
  CPSplit
open
  CLPacket
open
  UCAdapt
open
  FCAssign
open
  CFSubsti
open
  UCSuppor

namespace
  FLZero

/-- Sorting preserves the empty vocabulary below the initial commutator
degree. -/
lemma erased_vocabulary_nil
    {n leftWeight rightWeight : ℕ}
    (hcutoff : n ≤ leftWeight + rightWeight) :
    orderedErasedVocabulary n leftWeight rightWeight = [] := by
  simp [orderedErasedVocabulary,
    shape_vocabulary_nil hcutoff]

/--
The empty endpoint-fiber presentation kernel has its all-integral signed lift.
-/
def endpointFiberLift
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hn : n ≤ 2) :
    FHPres.AILift.{u}
      (d := d)
        (endpointFiberHomogeneous
          layer (by omega)) where
  listEval_eq left right leftExponent rightExponent := by
    change
      ((((endpointFiberHomogeneous
            layer (by omega))
          |>.signedProfileAssignment
          |>.erasedVocabPackets).map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod) =
        ⁅left ^ leftExponent, right ^ rightExponent⁆
    unfold SPAssign.erasedVocabPackets
    have hattach :
        (orderedErasedVocabulary n 1 1).attach = [] := by
      apply Subtype.val_injective.list_map
      simpa only [List.attach_map_subtype_val, List.map_nil] using
        erased_vocabulary_nil
          (show n ≤ 1 + 1 by omega)
    rw [hattach]
    simpa only [List.map_nil, List.prod_nil] using
      (empty_n_two (d := d) hn).listEval_eq
        left right leftExponent rightExponent

end
  FLZero

namespace
  CTBoundaa

/-- Sorting preserves the singleton basic vocabulary in class two. -/
lemma vocabulary_singleton_n
    {n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    orderedErasedVocabulary n 1 1 =
      [CWord.hallPairBase] := by
  rw [orderedErasedVocabulary,
    erased_vocabulary_singleton
      hlow hhigh]
  rfl

/--
The singleton basic endpoint-fiber presentation kernel has its all-integral
signed lift.
-/
def endpointFiberAll
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    FHPres.AILift.{u}
      (d := d)
        (fiberHomogeneousPresentation
          layer hlow hhigh) where
  listEval_eq left right leftExponent rightExponent := by
    have hvocabulary :
        orderedErasedVocabulary n 1 1 =
          [CWord.hallPairBase] :=
      vocabulary_singleton_n
        hlow hhigh
    let basicWord :
        {word // word ∈ orderedErasedVocabulary n 1 1} :=
      ⟨CWord.hallPairBase,
        ordered_erased_vocabulary.mpr
          (base_erased_vocabulary hlow)⟩
    have hattach :
        (orderedErasedVocabulary n 1 1).attach = [basicWord] := by
      apply Subtype.val_injective.list_map
      simpa only [List.attach_map_subtype_val, List.map_singleton, basicWord] using
        hvocabulary
    have hprofile :
        ∀ hword :
            CWord.hallPairBase ∈ erasedShapeVocabulary n 1 1,
          ((fiberHomogeneousPresentation
                layer hlow hhigh
              |>.signedProfileAssignment.profiles
                CWord.hallPairBase hword).value
            leftExponent rightExponent) =
              coefficientValue hallPair leftExponent rightExponent := by
      intro hword
      change
        ((fiberHomogeneousPresentation
              layer hlow hhigh
            |>.presentation CWord.hallPairBase hword).homogeneous.value
              leftExponent rightExponent) =
          coefficientValue hallPair leftExponent rightExponent
      rw [(fiberHomogeneousPresentation
          layer hlow hhigh
        |>.presentation CWord.hallPairBase hword).value_eq]
      change
        (homogeneousFormulaRecipe hallPair).value
            leftExponent rightExponent =
          coefficientValue hallPair leftExponent rightExponent
      exact
        value_homogeneous_recipe
          hallPair leftExponent rightExponent
    change
      ((((fiberHomogeneousPresentation
            layer hlow hhigh)
          |>.signedProfileAssignment
          |>.erasedVocabPackets).map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod) =
        ⁅left ^ leftExponent, right ^ rightExponent⁆
    unfold SPAssign.erasedVocabPackets
    rw [hattach]
    simpa only [List.map_singleton, List.prod_singleton, basicWord, hprofile,
      erased_shape_pair,
      PFSubsti.TAPkt.n_three] using
      (PFSubsti.TAPkt.n_three
        (d := d) hhigh).listEval_eq
        left right leftExponent rightExponent

end
  CTBoundaa

namespace TSInput

/--
Through cutoff three, the operational cutoff-full endpoint shape fibers
construct the Claim 5 coordinate polynomials without a separate signed-lift
hypothesis.
-/
theorem
    fullFiberLow
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn3 : n ≤ 3)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight := by
  by_cases htwo : n ≤ 2
  · exact
      input.fiberHomogeneousLift
        hn H hH
          (endpointFiberHomogeneous
            layer (by omega))
          (endpointFiberLift layer htwo)
          hsourceSupported factorNormalization hinputWeight
  · exact
      input.fiberHomogeneousLift
        hn H hH
          (fiberHomogeneousPresentation
            layer (by omega) hn3)
          (endpointFiberAll
            layer (by omega) hn3)
          hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from recursively assigned cutoff-full endpoint shape-fiber profiles

The cutoff-full collector reduces arbitrary-cutoff symbolic recollection to a
scalar theorem: each fixed erased-word slot has a homogeneous signed profile
whose natural values count the corresponding endpoint recipe-shape fiber.

This file connects counted finite-closure profile assignments, and the recursive
semantic kernels constructing them, directly to the Claim 5 coordinate
polynomials.  The signed extension from natural to integral source exponents and
the local factor-normalization obligations remain explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  FPInterp
open
  RPAssign
set_option linter.style.longLine false in
open RPAssign.RPSem
open CRLayer
open
  CFSubsti
open
  RASem
open
  FCAssign

namespace
  FCAssign
namespace SPAssign

/-- The signed extension still needed after a finite profile assignment has
been proved to count every cutoff-full endpoint recipe-shape fiber. -/
abbrev EndpointFiberLift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (assignment : SPAssign n 1 1)
    (hcounts :
      assignment.CountsFibersCast layer) :
    Prop :=
  EFInterp.AILift.{u}
    (d := d)
      (assignment.fiberProfileInterpolation hcounts)

end SPAssign
end
  FCAssign

namespace
  RPAssign
namespace RPSem

/-- The signed extension still needed after a recursive semantic profile kernel
has propagated an endpoint recipe-shape fiber counting invariant. -/
abbrev EndpointFiberLift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel : RPSem n 1 1)
    (hprofile :
      ∀ word profiles,
        kernel.profileMotive word profiles →
          EndpointRecipeFiber layer word profiles) :
    Prop :=
  EFInterp.AILift.{u}
    (d := d)
      (fiberProfileInterpolation kernel
        (by simp) (by simp) hprofile)

end RPSem
end
  RPAssign

namespace
  SSBuild

/-- A counted cutoff-full endpoint-fiber profile assignment and its signed lift
supply the generic restricted-sharp signed-block builder. -/
def endpointFiberAssignment
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {layer : NRLayer n 1 1}
    (assignment : SPAssign n 1 1)
    (hcounts :
      assignment.CountsFibersCast layer)
    (lift :
      SPAssign.EndpointFiberLift.{u}
        (d := d) assignment hcounts)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor) :
    SSBuild
      (n := n) (inputWeight := inputWeight) hn H hH :=
  endpointFiberInterpolation
    (assignment.fiberProfileInterpolation hcounts)
      lift factorNormalization

end
  SSBuild

namespace TSInput

/-- A counted finite profile assignment, its signed lift, singleton
recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials. -/
theorem
    fiberAssignmentLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (assignment : SPAssign n 1 1)
    (hcounts :
      assignment.CountsFibersCast layer)
    (lift :
      SPAssign.EndpointFiberLift.{u}
        (d := d) assignment hcounts)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.fiberInterpolationLift
    hn H hH
      (assignment.fiberProfileInterpolation hcounts)
      lift hsourceSupported factorNormalization hinputWeight

/--
A recursively constructed homogeneous profile assignment whose propagated
semantic invariant counts cutoff-full endpoint recipe-shape fibers, together
with its signed lift, constructs the Claim 5 coordinate polynomials.
-/
theorem
    recursiveFiberLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel : RPSem n 1 1)
    (hprofile :
      ∀ word profiles,
        kernel.profileMotive word profiles →
          EndpointRecipeFiber layer word profiles)
    (lift :
      RPSem.EndpointFiberLift.{u}
        (d := d) kernel hprofile)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.fiberInterpolationLift
    hn H hH
      (RPAssign.RPSem.fiberProfileInterpolation
        kernel (by simp) (by simp) hprofile)
      lift hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from split retained-correction profiles

The cutoff-full endpoint recipe-shape fibers split into initially retained raw
terms and scheduler-generated retained corrections.  Separate homogeneous
profiles for those two inventories produce the fixed endpoint-fiber
interpolation consumed by the restricted-sharp singleton collector.

This file packages that composition.  The remaining scalar construction is
concentrated in the retained-correction profiles, while the signed extension
and local factor-normalization obligations stay explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open
  FPInterp
open CRLayer
open
  CRSplit

namespace
  CRSplit
namespace EFProf

/--
The signed extension still needed after the raw and retained-correction
inventories have been presented homogeneously.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel : EFProf layer) :
    Prop :=
  EFInterp.AILift.{u}
    (d := d) kernel.fiberProfileInterpolation

/--
The remaining cutoff-specific ordered recollection law for the summed raw and
retained-correction profiles.
-/
def SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel : EFProf layer) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((kernel.signedProfileAssignment
        |>.erasedVocabPackets).map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
The ordered summed-profile recollection law supplies the signed extension.
-/
def allLiftSatisfies
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel : EFProf layer)
    (hlistEval :
      EFProf.SatisfiesTruncEval.{u}
        (d := d) kernel) :
    EFProf.AILift.{u}
      (d := d) kernel where
  listEval_eq := by
    intro left right leftExponent rightExponent
    simpa only [
      EFInterp.packetsTruncNatural
    ] using hlistEval left right leftExponent rightExponent

/--
The signed extension recovers the ordered summed-profile recollection law.
-/
lemma satisfies_trunc_all
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel : EFProf layer)
    (lift :
      EFProf.AILift.{u}
        (d := d) kernel) :
    EFProf.SatisfiesTruncEval.{u}
      (d := d) kernel := by
  intro left right leftExponent rightExponent
  simpa only [
    EFInterp.packetsTruncNatural
  ] using lift.listEval_eq left right leftExponent rightExponent

/--
For a split endpoint-fiber kernel, the remaining signed extension is exactly
the ordered recollection law for its summed profiles.
-/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel : EFProf layer) :
    EFProf.SatisfiesTruncEval.{u}
        (d := d) kernel ↔
      EFProf.AILift.{u}
        (d := d) kernel :=
  ⟨kernel.allLiftSatisfies,
    kernel.satisfies_trunc_all⟩

end EFProf
end
  CRSplit

namespace
  SSBuild

/--
Split retained-correction endpoint profiles and a signed lift supply the
restricted-sharp singleton collection builder.
-/
def endpointFiberProfile
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {layer : NRLayer n 1 1}
    (kernel : EFProf layer)
    (lift :
      EFProf.AILift.{u}
        (d := d) kernel)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor) :
    SSBuild
      (n := n) (inputWeight := inputWeight) hn H hH :=
  endpointFiberInterpolation
    kernel.fiberProfileInterpolation
    lift factorNormalization

/--
The ordered summed-profile recollection law is the direct split-kernel input
for the restricted-sharp singleton collection builder.
-/
def endpointFiberSplit
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {layer : NRLayer n 1 1}
    (kernel : EFProf layer)
    (hlistEval :
      EFProf.SatisfiesTruncEval.{u}
        (d := d) kernel)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor) :
    SSBuild
      (n := n) (inputWeight := inputWeight) hn H hH :=
  endpointFiberProfile kernel
    (kernel.allLiftSatisfies hlistEval)
      factorNormalization

end
  SSBuild

namespace TSInput

/--
Split retained-correction endpoint profiles, their signed lift, singleton
recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials.
-/
theorem
    fiberSplitLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel : EFProf layer)
    (lift :
      EFProf.AILift.{u}
        (d := d) kernel)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.fiberInterpolationLift
    hn H hH kernel.fiberProfileInterpolation
      lift hsourceSupported factorNormalization hinputWeight

/--
Split retained-correction endpoint profiles and their ordered summed-profile
recollection law construct the Claim 5 coordinate polynomials.
-/
theorem
    coordRecipeTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel : EFProf layer)
    (hlistEval :
      EFProf.SatisfiesTruncEval.{u}
        (d := d) kernel)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.fiberSplitLift
    hn H hH kernel
      (kernel.allLiftSatisfies hlistEval)
        hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from retained raw-history and correction-trace profiles

The cutoff-full endpoint shape fibers split into exact retained inverse-history
fibers and scheduler-generated retained corrections.  Homogeneous profiles for
those two inventories, together with the ordered summed-profile recollection
law, feed the restricted-sharp Claim 5 constructor.

This file packages that composition while leaving the arbitrary-cutoff
history-fiber formulas, correction-trace formulas, and ordered recollection law
explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CRLayer
open
  CRSplit
open
  RHSplit

namespace
  RHSplit
namespace EFSplit

/--
The signed extension still needed after raw-history and retained-correction
fibers have been presented homogeneously.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EFSplit layer) :
    Prop :=
  EFProf.AILift.{u}
    (d := d) kernel.endpointRecipeFiber

/--
The remaining ordered recollection law for the summed raw-history and
retained-correction profiles.
-/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EFSplit layer) :
    Prop :=
  EFProf.SatisfiesTruncEval.{u}
    (d := d) kernel.endpointRecipeFiber

end EFSplit
end
  RHSplit

namespace
  SSBuild

/--
Raw-history and retained-correction profiles with their ordered recollection
law supply the restricted-sharp singleton collection builder.
-/
def endpointFiberHistory
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {layer : NRLayer n 1 1}
    (kernel :
      EFSplit layer)
    (hlistEval :
      EFSplit.SatisfiesTruncEval.{u}
        (d := d) kernel)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor) :
    SSBuild
      (n := n) (inputWeight := inputWeight) hn H hH :=
  endpointFiberSplit
    kernel.endpointRecipeFiber hlistEval
      factorNormalization

end
  SSBuild

namespace TSInput

/--
Raw-history and retained-correction profiles with their ordered summed-profile
recollection law construct the Claim 5 coordinate polynomials.
-/
theorem
    coordHistoryTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EFSplit layer)
    (hlistEval :
      EFSplit.SatisfiesTruncEval.{u}
        (d := d) kernel)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordRecipeTrunc
    hn H hH kernel.endpointRecipeFiber hlistEval
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission
