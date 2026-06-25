import Towers.Group.Zassenhaus.CompatibleGridBridge
import Towers.Group.Zassenhaus.GuardedGridCoverage
import Towers.Group.Zassenhaus.CanonicalPacketAlignment
import Towers.Group.Zassenhaus.OrderedRetainedLaw
import Towers.Group.Zassenhaus.InverseUniversalOrbit
import Towers.Group.Zassenhaus.PolynomialOrbitVocabulary
import Towers.Group.Zassenhaus.ErasedShapePrograms
import Towers.Group.Zassenhaus.ClassAutomaticCollection
import Towers.Group.Zassenhaus.BasicTreeReduction
import Towers.Group.Zassenhaus.EndpointInterpolationNormalizer
import Towers.Group.Zassenhaus.CanonicalHallRecollection
import Towers.Group.Zassenhaus.RankedResidual
import Towers.Group.Zassenhaus.FactorSourceReduction
import Towers.Group.Zassenhaus.EndpointShapeInterpolation
import Towers.Group.Zassenhaus.ClassEndpointFibers

/-!
# Selected-endpoint Hall-power collection from residual sources

The selected operational endpoint finite-index trace profile supplies the
powered adjacent-swap correction packet at every support stratum.  Explicit
recollections of the intrinsic residual source of each nonterminal active
factor supply the remaining local input.

This file compiles those two inputs to the restricted-sharp recursive
collector.  In particular, recursive semantic normalization now constructs
the singleton factor normalizations exposed by the selected-endpoint Claim 5
boundary.

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
For one Hall-power input weight, selected-endpoint correction profiles and
explicit intrinsic factor-residual recollections are sufficient for direct
recursive collection.
-/
structure
    TIBuild
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
  TIBuild

/--
Compile selected-endpoint correction profiles and intrinsic residual-source
recollections to the direct restricted-sharp recursive collector.
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
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (builder :
      TIBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight)
    (hlistEval :
      EIFiber.SatisfiesTruncEval.{u}
        (d := d) kernel)
    (hinputWeight : 1 ≤ inputWeight) :
    RSRec
      (n := n) (inputWeight := inputWeight) hn H hH where
  correctionFactory lowerWeight _hterminal :=
    ((kernel.allLiftSatisfies hlistEval
      |>.truncatedAllIntegral)
      |>.powerSupportedFactory
        (by omega) lowerWeight)
      |>.correctionPacketFactory
  factorResidual lowerWeight hterminal _nextNormalizer factor hfactorWeight
      hfactorTruncated :=
    (builder.factorResidualSource lowerWeight hterminal factor hfactorWeight
      hfactorTruncated)
      |>.factorExpansion

/--
The recursive collector generated from selected-endpoint profiles supplies a
singleton normalization for every active factor.
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
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (builder :
      TIBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight)
    (hlistEval :
      EIFiber.SatisfiesTruncEval.{u}
        (d := d) kernel)
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
    ((builder.restrictedRecursiveBuilder kernel hlistEval
        hinputWeight)
      |>.semanticCoordinateNormalizer hn H hH lowerWeight)
    factor (by omega) hfactorTruncated

end
  TIBuild

namespace TSInput

/--
Selected-endpoint profiles and intrinsic residual-source recollections
construct the Claim 5 coordinate-polynomial package for one supported sourced
input, without a separate singleton-normalization premise.
-/
theorem
    coordFinBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight)
    (hlistEval :
      EIFiber.SatisfiesTruncEval.{u}
        (d := d) kernel)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TIBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSharpRecursive
    hn H hH hsourceSupported
      (builder.restrictedRecursiveBuilder kernel hlistEval
        hinputWeight)
      hinputWeight

end TSInput

/--
Selected-endpoint profiles and intrinsic residual-source recollections
construct the complete quantified Claim 5 power input.  Supported sourced
inputs remain explicit only for the finitely many weights below the automatic
class-two source range.
-/
theorem
    forall_profiles_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          TIBuild
            (n := n) (inputWeight := inputWeight) hn H hH) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  apply
    collected_fiber_profiles
      hn H hH kernel hlistEval lowWeightSource lowWeightSupported
  intro inputWeight hinputWeight lowerWeight _hnonterminal nextNormalizer
    factor hfactorWeight hfactorTruncated
  exact
    (builders inputWeight hinputWeight).activeBlockNormalization
      kernel hlistEval hinputWeight nextNormalizer factor hfactorWeight
        hfactorTruncated

/--
The residual-source selected-endpoint collector therefore yields the
weight-controlled polynomial degree bound for every Hall coordinate of a
power.
-/
theorem
    profiles_collect_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
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
          TIBuild
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
        (forall_profiles_builders
          hn H hH kernel hlistEval lowWeightSource lowWeightSupported
            builders)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Claim 5 from compatible correction-grid residual sources

The operational cutoff-full scheduler emits support-compatible correction
grids after overlap subtraction.  Their erased-shape branch lists compile to
the aggregate selected-endpoint profile kernel.  The residual-source
collector then recursively synthesizes singleton factor normalizations.

This file threads those two boundaries together: the remaining arbitrary
cutoff power inputs are the signed recollection law for compatible-grid
batches, finitely many low-weight sourced inputs, and intrinsic factor
residual-source recollections.

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
open
  FIBridge

namespace
  EBList
namespace
  PCDecompb

/--
The compatible-grid signed recollection law is exactly the selected-endpoint
ordered law needed by the residual-source collector.
-/
lemma
    endpointSatisfiesTrunc
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      PCDecompb
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (hlistEval :
      PCDecompb.SatisfiesTruncEval.{u}
        (d := d) decomposition raw) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d)
      (decomposition.selectedFullFiber
        raw) :=
  EIFiber.satisfies_trunc_all
    (decomposition.selectedFullFiber
      raw)
    (decomposition.allLiftSatisfies raw hlistEval)

end
  PCDecompb
end
  EBList

/--
Compatible correction-grid erased-shape batches, their signed recollection
law, and intrinsic residual-source recollections construct the complete
quantified Claim 5 power input.
-/
theorem
    forall_residual_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          TIBuild
            (n := n) (inputWeight := inputWeight) hn H hH) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight :=
  forall_profiles_builders
    hn H hH
      (decomposition.selectedFullFiber
        raw)
      (decomposition.endpointSatisfiesTrunc
        raw hlistEval)
      lowWeightSource lowWeightSupported builders

/--
The operational compatible-grid residual-source collector therefore yields
the weight-controlled polynomial degree bound for every Hall coordinate of a
power.
-/
theorem
    erased_collect_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
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
          TIBuild
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
        (forall_residual_builders
          hn H hH decomposition raw hlistEval lowWeightSource
            lowWeightSupported builders)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Claim 5 from concrete-schedule root-trace permutation residual sources

Root-trace permutation is the compact constructor-level endpoint condition
for the symbolic Hall collector.  It compiles to endpoint interpolation
through structural coalescing.  The generic endpoint-interpolation
residual-source collector then recursively synthesizes singleton factor
normalizations.

Thus the remaining arbitrary-cutoff power inputs are the root-trace signed
recollection law, finitely many low-weight sourced inputs, and intrinsic
factor-residual recollections.

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
Concrete-schedule root-trace permutation, its inherited signed recollection
law, finitely many low-weight sourced inputs, and intrinsic residual-source
recollections construct the complete quantified Claim 5 power input.
-/
theorem
    coord_collect_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (hlistEval :
      GPPerm.SatisfiesTruncEval.{u}
        (d := d) kernel)
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
          (n := n) H e inputWeight :=
  forall_endpoint_builders
    hn H hH kernel.fiberProfileInterpolation
      ((kernel.satisfies_trunc_lift).mp hlistEval)
      lowWeightSource lowWeightSupported builders

/--
The concrete root-trace permutation residual-source collector therefore
yields the weight-controlled polynomial degree bound for every Hall
coordinate of a power.
-/
theorem
    root_collect_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (hlistEval :
      GPPerm.SatisfiesTruncEval.{u}
        (d := d) kernel)
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
        (coord_collect_builders
          hn H hH kernel hlistEval lowWeightSource lowWeightSupported
            builders)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Root-trace Claim 5 boundary from concrete Hall-tree residual sources

The concrete-schedule root-trace permutation criterion supplies endpoint
interpolation and powered adjacent-swap corrections.  The remaining
nonterminal Hall-power input is packet-free: recollect the explicit concrete
Hall-tree reduction residual and its comparison with the semantic active
block.

This file composes those concrete recollections into the intrinsic residual
sources used by the root-trace Claim 5 collector.

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
Root-trace permutation, its signed law, finitely many low-weight sourced
inputs, and packet-free concrete Hall-tree residual recollections construct
the complete quantified Claim 5 power input for canonical Hall families.
-/
theorem
    forall_root_builders
    {d n : ℕ}
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
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  coord_collect_builders
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      kernel hlistEval lowWeightSource lowWeightSupported
        (fun inputWeight hinputWeight => by
          simpa only [concreteBasicCommutators] using
            (builders inputWeight hinputWeight)
              |>.fiberInterpolationBuilder)

end TCTex
end Towers

/-!
# Guarded-grid Claim 5 from local canonical profile alignment

The guarded raw-source scheduler already compiles to one selected endpoint
shape-fiber profile assignment.  If those word-local homogeneous profiles are
the canonical coefficient-sum profiles, then the sorted packet lists agree
literally.  An order-aware signed law for that sorted canonical packet
therefore supplies the all-integral lift consumed by Claim 5.

This file avoids bundling profile agreement and packet-order semantics into
one opaque generated signed-law premise.

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
A guarded finite-index scheduler decomposition, word-local agreement of its
selected endpoint profiles with the canonical coefficient-sum profiles, an
order-aware signed law for the sorted canonical packet, finitely many
low-weight sources, and intrinsic residual recollections construct the
quantified Claim 5 power input.
-/
theorem
    collected_collect_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          (n := n) H e inputWeight :=
  forall_endpoint_builders
    hn H hH
      (decomposition.selectedFullFiber
        |>.fiberProfileInterpolation)
      (allGlobalAlignment
        (decomposition.selectedFullFiber
          |>.fiberProfileInterpolation)
        (ordered_erased_alignment
          (decomposition.selectedFullFiber
            |>.signedProfileAssignment)
          hprofileAlignment)
        hlistEval)
      lowWeightSource lowWeightSupported builders

/--
The local-profile guarded-grid collector yields the weight-controlled
integer-valued polynomial degree bound for every Hall coordinate of a power.
-/
theorem
    poly_global_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
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
        (collected_collect_builders
          hn H hH decomposition hprofileAlignment hlistEval lowWeightSource
            lowWeightSupported builders)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Canonical Hall-tree Claim 5 from local canonical profile alignment

This file specializes the guarded-grid local-profile Claim 5 reduction to the
canonical Hall family and packet-free concrete Hall-tree residual
recollections.

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
For canonical Hall families, guarded raw-source scheduling, word-local
canonical endpoint-profile agreement, the sorted canonical signed law,
finitely many low-weight sources, and packet-free concrete Hall-tree residual
recollections construct the quantified Claim 5 power input.
-/
theorem
    forall_global_builders
    {d n : ℕ}
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
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  collected_collect_builders
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      decomposition hprofileAlignment hlistEval lowWeightSource
        lowWeightSupported
        (fun inputWeight hinputWeight => by
          simpa only [concreteBasicCommutators] using
            (builders inputWeight hinputWeight)
              |>.fiberInterpolationBuilder)

end TCTex
end Towers

/-!
# Claim 5 from guarded raw-source grids and residual sources

The guarded finite-index scheduler decomposition erases to the concrete
generated-program root-trace permutation criterion.  The root-trace
residual-source collector therefore turns the guarded-grid scheduler theorem,
its inherited signed recollection law, finitely many low-weight sourced
inputs, and intrinsic factor residual sources into the quantified Claim 5
power input.

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
A guarded finite-index scheduler decomposition, its inherited signed law,
finitely many low-weight sourced inputs, and intrinsic factor residual-source
recollections construct the complete quantified Claim 5 power input.
-/
theorem
    forall_guarded_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          (n := n) H e inputWeight :=
  coord_collect_builders
    hn H hH
      (guardedPolyPermutation
        decomposition)
      hlistEval lowWeightSource lowWeightSupported builders

end TCTex
end Towers

/-!
# Guarded-grid Claim 5 boundary from concrete Hall-tree residual sources

This file specializes the guarded raw-source grid Claim 5 boundary to the
canonical Hall family and the packet-free concrete Hall-tree residual
decomposition.

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
For canonical Hall families, a guarded finite-index scheduler decomposition,
its signed law, finitely many low-weight sources, and packet-free concrete
Hall-tree residual recollections construct the complete quantified Claim 5
power input.
-/
theorem
    collected_residual_builders
    {d n : ℕ}
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
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  forall_root_builders
    hn
      (guardedPolyPermutation
        decomposition)
      hlistEval lowWeightSource lowWeightSupported builders

end TCTex
end Towers

/-!
# Canonical Hall-tree Claim 5 from guarded-grid packet alignment

This file specializes the guarded raw-source grid Claim 5 boundary to the
canonical Hall family and packet-free concrete Hall-tree residual
recollections.  The generated signed law is discharged by literal alignment
with the global canonical coefficient-sum packet and the canonical
recipe-product theorem.

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
For canonical Hall families, a guarded finite-index scheduler decomposition,
literal canonical packet alignment, the canonical recipe-product law,
finitely many low-weight sourced inputs, and packet-free concrete Hall-tree
residual recollections construct the quantified Claim 5 power input.
-/
theorem
    forall_packet_builders
    {d n : ℕ}
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
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  collected_residual_builders
    hn decomposition
      ((guardedPolyPermutation
        decomposition)
          |>.satisfies_trunc_recipe
            halignment hlistEval)
      lowWeightSource lowWeightSupported builders

end TCTex
end Towers

/-!
# Guarded-grid Claim 5 from canonical packet alignment

The guarded raw-source scheduler supplies a generated root-trace kernel.  Its
signed recollection law follows from literal alignment of the generated
endpoint packet with the global canonical coefficient-sum packet together
with the canonical recipe-product theorem.

This file replaces the opaque generated signed-law hypothesis in the
guarded-grid residual-source collector by those two explicit upstream
obligations.

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
A guarded finite-index scheduler decomposition, literal alignment of its
generated interpolation packet with the canonical coefficient-sum packet,
the canonical signed recipe law, finitely many low-weight sourced inputs, and
intrinsic residual-source recollections construct the quantified Claim 5
power input.
-/
theorem
    collected_global_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          (n := n) H e inputWeight :=
  forall_guarded_builders
    hn H hH decomposition
      ((guardedPolyPermutation
        decomposition)
          |>.satisfies_trunc_recipe
            halignment hlistEval)
      lowWeightSource lowWeightSupported builders

end TCTex
end Towers

/-!
# Guarded-grid Claim 5 from retained-transversal profile alignment

The guarded raw-source scheduler compiles to one selected endpoint profile
assignment.  If those word-local homogeneous profiles agree with the
retained recipe-coefficient transversal, then their sorted packets agree
literally.  The sorted retained-transversal signed law therefore supplies the
all-integral lift consumed by Claim 5.

This is the provenance-preserving guarded-grid reduction for arbitrary
cutoff.

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
A guarded finite-index scheduler decomposition, word-local agreement of its
selected endpoint profiles with the retained recipe-coefficient transversal,
the sorted retained-transversal signed law, finitely many low-weight sources,
and intrinsic residual recollections construct the quantified Claim 5 power
input.
-/
theorem
    collected_forall_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          (n := n) H e inputWeight :=
  forall_endpoint_builders
    hn H hH
      (decomposition.selectedFullFiber
        |>.fiberProfileInterpolation)
      (allLiftAlignment
        (decomposition.selectedFullFiber
          |>.fiberProfileInterpolation)
        (coeff_profile_alignment
          (decomposition.selectedFullFiber
            |>.signedProfileAssignment)
          hprofileAlignment)
        hlistEval)
      lowWeightSource lowWeightSupported builders

/--
The retained-transversal guarded-grid collector yields the weight-controlled
integer-valued polynomial degree bound for every Hall coordinate of a power.
-/
theorem
    poly_collect_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
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
        (collected_forall_builders
          hn H hH decomposition hprofileAlignment hlistEval lowWeightSource
            lowWeightSupported builders)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Guarded-grid Claim 5 from an ordered retained occurrence schedule

The combined ordered occurrence schedule rewrites the powered parent pair
directly to the sorted retained packet followed by the swapped powered
parents.  Its cancellation law supplies the sorted retained-transversal
signed law consumed by cutoff-full interpolation without requiring literal
agreement between inherited and sorted packet orders.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FPInterp
open
  OOSched
open
  SOAlign
open
  CRLayer
open
  CFSubsti
open
  UCSuppor
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
Literal sorted-packet alignment and a combined ordered occurrence schedule
construct the all-integral lift used by Claim 5.
-/
def
    allAlignmentOccurrence
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (hpacketAlignment :
      packets =
        profileRecollectionPackets n)
    (schedule :
      COScheda.{u} d n) :
    EFInterp.AILift.{u}
      (d := d) interpolation :=
  allLiftAlignment
    interpolation hpacketAlignment
      schedule.satisfiesCoefficientTruncated

/--
A guarded finite-index scheduler decomposition, word-local agreement with the
retained transversal, a combined ordered occurrence schedule, finitely many
low-weight sources, and intrinsic residual recollections construct the
quantified Claim 5 power input.
-/
theorem
    forall_collect_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          (n := n) H e inputWeight :=
  collected_forall_builders
    hn H hH decomposition hprofileAlignment
      schedule.satisfiesCoefficientTruncated
      lowWeightSource lowWeightSupported builders

/--
The ordered occurrence-scheduled retained-transversal guarded-grid collector
yields the weight-controlled integer-valued polynomial degree bound for every
Hall coordinate of a power.
-/
theorem
    coord_poly_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
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
        (forall_collect_builders
          hn H hH decomposition hprofileAlignment schedule lowWeightSource
            lowWeightSupported builders)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Canonical Hall-tree Claim 5 from an ordered retained occurrence schedule

This file specializes the guarded-grid ordered occurrence-schedule Claim 5
reduction to the canonical Hall family and packet-free concrete Hall-tree
residual recollections.

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
For canonical Hall families, guarded raw-source scheduling, word-local
retained-transversal endpoint-profile agreement, a combined ordered
occurrence schedule, finitely many low-weight sources, and packet-free
concrete Hall-tree residual recollections construct the quantified Claim 5
power input.
-/
theorem
    collected_coord_builders
    {d n : ℕ}
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
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  forall_collect_builders
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      decomposition hprofileAlignment schedule lowWeightSource
        lowWeightSupported
        (fun inputWeight hinputWeight => by
          simpa only [concreteBasicCommutators] using
            (builders inputWeight hinputWeight)
              |>.fiberInterpolationBuilder)

end TCTex
end Towers

/-!
# Canonical Hall-tree Claim 5 from retained-transversal profile alignment

This file specializes the guarded-grid retained-transversal Claim 5 reduction
to the canonical Hall family and packet-free concrete Hall-tree residual
recollections.

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
For canonical Hall families, guarded raw-source scheduling, word-local
retained-transversal endpoint-profile agreement, the sorted retained signed
law, finitely many low-weight sources, and packet-free concrete Hall-tree
residual recollections construct the quantified Claim 5 power input.
-/
theorem
    coord_forall_builders
    {d n : ℕ}
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
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  collected_forall_builders
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      decomposition hprofileAlignment hlistEval lowWeightSource
        lowWeightSupported
        (fun inputWeight hinputWeight => by
          simpa only [concreteBasicCommutators] using
            (builders inputWeight hinputWeight)
              |>.fiberInterpolationBuilder)

end TCTex
end Towers

/-!
# Guarded-grid Claim 5 from a cutoff-aware ordered occurrence schedule

The cutoff-full collector naturally emits Hall swaps together with certified
identity erasures.  A cutoff-aware ordered occurrence schedule packages that
operational run and still supplies the sorted retained signed law consumed by
the guarded-grid Claim 5 interpolation layer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FPInterp
open
  OOSched
open
  FTOcc
open
  SOAlign
open
  CRLayer
open
  CFSubsti
open
  UCSuppor
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
Literal sorted-packet alignment and a cutoff-aware combined ordered occurrence
schedule construct the all-integral lift used by Claim 5.
-/
def
    allOccSchedule
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (hpacketAlignment :
      packets =
        profileRecollectionPackets n)
    (schedule :
      OOScheda.{u} d n) :
    EFInterp.AILift.{u}
      (d := d) interpolation :=
  allAlignmentOccurrence
    interpolation hpacketAlignment schedule.occurrenceSchedule

/--
A guarded finite-index scheduler decomposition, word-local agreement with the
retained transversal, a cutoff-aware ordered occurrence schedule, finitely
many low-weight sources, and intrinsic residual recollections construct the
quantified Claim 5 power input.
-/
theorem
    collected_trunc_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          (n := n) H e inputWeight :=
  forall_collect_builders
    hn H hH decomposition hprofileAlignment schedule.occurrenceSchedule
      lowWeightSource lowWeightSupported builders

/--
The cutoff-aware ordered occurrence-scheduled retained-transversal guarded
grid collector yields the weight-controlled integer-valued polynomial degree
bound for every Hall coordinate of a power.
-/
theorem
    poly_trunc_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
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
    coord_poly_builders
      hn H hH decomposition hprofileAlignment schedule.occurrenceSchedule
        lowWeightSource lowWeightSupported builders u hu hr hs hsn i

end TCTex
end Towers

/-!
# Canonical Hall-tree Claim 5 from a cutoff-aware ordered occurrence schedule

This file specializes the guarded-grid cutoff-aware ordered
occurrence-schedule Claim 5 reduction to the canonical Hall family and
packet-free concrete Hall-tree residual recollections.

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
For canonical Hall families, guarded raw-source scheduling, word-local
retained-transversal endpoint-profile agreement, a cutoff-aware ordered
occurrence schedule, finitely many low-weight sources, and packet-free
concrete Hall-tree residual recollections construct the quantified Claim 5
power input.
-/
theorem
    forall_trunc_builders
    {d n : ℕ}
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
          TSBuildc.{u}
            (inputWeight := inputWeight) hn
              (forms_associated_below
                d n)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  collected_trunc_builders
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      decomposition hprofileAlignment schedule lowWeightSource
        lowWeightSupported
        (fun inputWeight hinputWeight => by
          simpa only [concreteBasicCommutators] using
            (builders inputWeight hinputWeight)
              |>.fiberInterpolationBuilder)

end TCTex
end Towers

/-!
# Canonical Hall-power input from semantic normalizer families

For the canonical Hall family, semantic normalizer families supply both
concrete Hall-tree residual recollections required by endpoint interpolation.
The cutoff-aware guarded-grid collector therefore produces the complete
quantified Claim 5 power input once its operational schedule, retained-profile
alignment, and finitely many low-weight sourced inputs are available.

This file leaves the circular normalizer-family construction explicit while
removing the lower-level endpoint residual-source builder callbacks.

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
For canonical Hall families, pointwise semantic normalizer families replace
the endpoint residual-source builder callbacks in the cutoff-aware
retained-transversal Claim 5 power boundary.
-/
theorem
    occ_normalizer_families
    {d n : ℕ}
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
              (concreteBasicCommutators.{u} d)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  forall_trunc_builders
    hn decomposition hprofileAlignment schedule lowWeightSource
      lowWeightSupported
      (fun inputWeight hinputWeight =>
        TSBuildc.ofNormalizerFamily
          hn
            (forms_associated_below
              d n)
            (normalizerFamilies inputWeight hinputWeight))

/--
Universal semantic derivation builders provide the pointwise normalizer
families required by the cutoff-aware retained-transversal Claim 5 power
boundary.
-/
theorem
    forall_derivation_builders
    {d n : ℕ}
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
              (concreteBasicCommutators.{u} d)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  occ_normalizer_families
    hn decomposition hprofileAlignment schedule lowWeightSource
      lowWeightSupported
      (fun inputWeight hinputWeight =>
        (builders inputWeight hinputWeight)
          |>.supportedSemanticFamily
            hn (concreteBasicCommutators.{u} d)
              (forms_associated_below
                d n))

end TCTex
end Towers

/-!
# Guarded-grid Hall-power input from Jacobi-only ranked residual collection

The Jacobi-only ranked residual collector constructs semantic normalizer
families by terminating support recursion.  Those families fill both
concrete endpoint residual-source callbacks in the cutoff-aware guarded-grid
collector.  This file records the resulting quantified Claim 5 power input.

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
open
  CCThree
open
  CPSplita

/--
Jacobi-only ranked residual collection supplies the normalizer families
required by the cutoff-aware guarded-grid canonical Hall-power route.
-/
theorem
    forall_alignment_builders
    {d n : ℕ}
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
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          JCBuild.{u}
            (d := d) (n := n) (inputWeight := inputWeight)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  occ_normalizer_families
    hn decomposition hprofileAlignment schedule lowWeightSource
      lowWeightSupported
      (fun inputWeight hinputWeight =>
        (builders inputWeight hinputWeight)
          |>.supportedSemanticFamily
            hn hinputWeight hrecipes)

end TCTex
end Towers

/-!
# Guarded-grid Claim 5 from a retained occurrence schedule

An occurrence schedule proves the retained recipe-product law in its inherited
skeleton order.  If that packet order agrees with sorted cutoff-full vocabulary
order, then the schedule supplies the ordered retained-transversal signed law
and hence the guarded-grid Claim 5 all-integral lift.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FPInterp
open
  SOAlign
open
  CRLayer
open
  CFSubsti
open
  UCSuppor
open
  PTOcc
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp

/--
An occurrence-level retained scheduler supplies the sorted signed law once
the retained skeleton and sorted vocabulary packet orders agree.
-/
theorem
    satisfies_alignment_occ
    {d n : ℕ}
    (horder :
      CoefficientVocabularyAlignment n)
    (schedule :
      COSched.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  satisfies_recipe_trunc
    horder schedule.satisfiesRecipeCoefficient

/--
Literal sorted-packet alignment, retained packet-order alignment, and an
occurrence schedule construct the all-integral lift used by Claim 5.
-/
def
    allAlignmentOcc
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (hpacketAlignment :
      packets =
        profileRecollectionPackets n)
    (horder :
      CoefficientVocabularyAlignment n)
    (schedule :
      COSched.{u} d n) :
    EFInterp.AILift.{u}
      (d := d) interpolation :=
  allLiftAlignment
    interpolation hpacketAlignment
      (satisfies_alignment_occ
        horder schedule)

/--
A guarded finite-index scheduler decomposition, word-local agreement with the
retained transversal, retained packet-order alignment, an occurrence-level
retained scheduler, finitely many low-weight sources, and intrinsic residual
recollections construct the quantified Claim 5 power input.
-/
theorem
    forall_vocab_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (horder :
      CoefficientVocabularyAlignment n)
    (schedule :
      COSched.{u} d n)
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
          (n := n) H e inputWeight :=
  collected_forall_builders
    hn H hH decomposition hprofileAlignment
      (satisfies_alignment_occ
        horder schedule)
      lowWeightSource lowWeightSupported builders

/--
The occurrence-scheduled retained-transversal guarded-grid collector yields
the weight-controlled integer-valued polynomial degree bound for every Hall
coordinate of a power.
-/
theorem
    vocab_collect_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (horder :
      CoefficientVocabularyAlignment n)
    (schedule :
      COSched.{u} d n)
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
        (forall_vocab_builders
          hn H hH decomposition hprofileAlignment horder schedule
            lowWeightSource lowWeightSupported builders)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Selected operational endpoint profiles through cutoff four

Through cutoff four at root weights, the canonical raw-source transversal
has its shallow homogeneous profile and the selected scheduler-correction
trace has zero fibers.  Their sum therefore gives a concrete homogeneous
profile kernel for the aggregate selected operational endpoint trace.

This file packages that aggregate kernel, transports the established shallow
ordered recollection law to it, and exposes the resulting direct Claim 5
constructor.

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
  IFClass
open
  RFTransv
open
  TCThree
open
  TFIdx
open
  FIBridge
open
  FTColleca

namespace
  CTCollec

/--
Through cutoff four, the canonical raw transversal and zero correction
profiles give the aggregate selected operational endpoint trace profile.
-/
noncomputable def
    selectedFiberFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hn4 : n ≤ 4) :
    EIFiber
      layer (by simp) (by simp) :=
  EIFiber.idx_fiber_profile
    (PTStab.idxFiberProfile
      (transversalStabilizationFour
        layer hn4)
      (by simp) (by simp))
    (fiberNFour
      layer hn4)

/--
Through cutoff four, the aggregate selected operational endpoint profiles
satisfy the ordered all-integral recollection law.
-/
lemma
    endpointIdxSatisfies
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hn4 : n ≤ 4) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d)
      (selectedFiberFour
        layer hn4) := by
  exact
    EIFiber.satisfies_trunc_split
      (PTStab.idxFiberProfile
        (transversalStabilizationFour
          layer hn4)
        (by simp) (by simp))
      (fiberNFour
        layer hn4)
      (finIdxSatisfies
        layer hn4)

namespace TSInput

/--
Through cutoff four, the aggregate selected operational endpoint trace
profiles construct Claim 5 coordinate polynomials from any supported sourced
input.
-/
theorem
    coordProfilesFour
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
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
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordTruncEval
    hn H hH
      (selectedFiberFour
        layer hn4)
      (endpointIdxSatisfies
        layer hn4)
      hsourceSupported factorNormalization hinputWeight

end TSInput

/--
Through cutoff four, local factor normalizations promote the selected
operational endpoint finite-index trace route to the complete Claim 5 power
input.
-/
theorem
    profiles_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (factorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1) H →
                ∀ (factor : SPFactora H inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight) H factor) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hOne : inputWeight = 1
  · subst inputWeight
    exact
      TSInput.coordProfilesFour
        (layer := layer) hn hn4 H hH
          (TSInput.classThreeSource
            hn4 e)
          (TSInput.word_least_source
            hn4 e)
          (factorNormalization 1 (by omega)) (by omega)
  · exact
      collected_profiles_below
        hn H hH hinputWeight (by omega)
          (selectedFiberFour
            layer hn4)
          (endpointIdxSatisfies
            layer hn4)
          (factorNormalization inputWeight hinputWeight)

end
  CTCollec
end TCTex
end Towers

/-!
# Hall-coordinate polynomials from selected endpoint profiles

Through cutoff four, the selected operational endpoint finite-index trace
profiles construct the quantified Claim 5 input.  This file records the direct
Hall-coordinate degree consequence.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u


open
  CRLayer
open
  CTCollec

/--
Through cutoff four, selected endpoint finite-index trace profiles and local
factor normalizations yield the weight-controlled polynomial degree bound for
every Hall coordinate of a power.
-/
theorem
    poly_profiles_four
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (factorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1) H →
                ∀ (factor : SPFactora H inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight) H factor)
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
        (profiles_n_four
          (layer := layer) hn hn4 H hH factorNormalization)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Automatic selected-endpoint normalization through cutoff four

The selected operational endpoint finite-index trace route previously exposed
local active-block factor normalization as an input.  Through cutoff four, the
class-three residual-source collector constructs semantic normalizers
recursively at every active stratum.  Normalizing a singleton factor with that
collector supplies the local input automa.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CRLayer
open
  CTCollec

/--
Through cutoff four, the class-three residual-source collector automa
normalizes every active symbolic Hall-power factor.
-/
noncomputable def
    active_normalization_four
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
    ((TSBuilda.automatic_four
        (inputWeight := inputWeight) (H := H) (hH := hH) hn4)
      |>.restrictedRecursiveBuilder hinputWeight
      |>.semanticCoordinateNormalizer hn H hH lowerWeight)
    factor (by omega) hfactorTruncated

/--
Through cutoff four, selected endpoint finite-index trace profiles construct
the complete quantified Claim 5 power input without an additional local
normalization premise.
-/
theorem
    collected_automatic_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1} :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  apply
    profiles_n_four
      (layer := layer) hn hn4 H hH
  intro inputWeight hinputWeight lowerWeight _hnonterminal nextNormalizer
    factor hfactorWeight hfactorTruncated
  exact
    active_normalization_four
      hn hn4 H hH hinputWeight nextNormalizer factor hfactorWeight
        hfactorTruncated

/--
Through cutoff four, the selected endpoint finite-index trace construction
therefore yields the weight-controlled Hall-coordinate polynomial bound
directly.
-/
theorem
    coord_automatic_four
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
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
        (collected_automatic_four
          (layer := layer) hn hn4 H hH)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Automatic phase-aware all-integral parent-pair normalization through cutoff four

Through cutoff four, the shallow signed occurrence schedule fills the three
negative quadrants of the phase-aware parent-pair collector.  The positive
quadrant is constructed automa by the natural cutoff-full collector,
its adjacent compressor, and its fixed-slot padder.

This file carries that sharper operational interface through Claim 5 and the
weight-controlled Hall-coordinate degree theorem.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  RANorm

universe u


open
  CRLayer
open
  PPSched
open
  CTBounda
open
  FIBridge

/--
Through cutoff four, the natural collector and the three shallow signed
quadrants assemble into the phase-aware all-integral parent-pair schedule.
-/
noncomputable def parent_phase_schedules
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hn : n ≤ 4) :
    PPSchedu.{u}
      d n layer
        (idxNFour
          layer hn)
        (coeffNFour
          layer hn) :=
  PPSchedu.parent_occ_schedules
    (idxNFour
      layer hn)
    (coeffNFour
      layer hn)
    (input_parent_schedules hn)

/--
The phase-aware cutoff-four schedule gives the retained-profile selected
endpoint kernel its full signed list-evaluation law.
-/
def
    idx_phase_schedules
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hn : n ≤ 4) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d)
      (idxNFour
        layer hn) :=
  (parent_phase_schedules
      (d := d) layer hn).satisfiesTruncAlignment

namespace TSInput

/--
Through cutoff four, phase-aware all-integral parent-pair schedules construct
the Claim 5 coordinate polynomials.
-/
theorem
    coordAllFour
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
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
    CollectedPolynomialData (n := n) H e inputWeight :=
  PPSched.PPSchedu.TSInput.parentPhaseSchedules
    hn H hH
      (idxNFour
        layer hn4)
      (coeffNFour
        layer hn4)
      (parent_phase_schedules layer hn4)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

/--
Through cutoff four, local factor normalizations promote the phase-aware
parent-pair route to the complete quantified Claim 5 power input.
-/
theorem
    all_schedules_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (factorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1) H →
                ∀ (factor : SPFactora H inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight) H factor) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hOne : inputWeight = 1
  · subst inputWeight
    exact
      TSInput.coordAllFour
        (layer := layer) hn hn4 H hH
          (TSInput.classThreeSource
            hn4 e)
          (TSInput.word_least_source
            hn4 e)
          (factorNormalization 1 (by omega)) (by omega)
  · exact
      collected_profiles_below
        hn H hH hinputWeight (by omega)
          (idxNFour
            layer hn4)
          (idx_phase_schedules
            layer hn4)
          (factorNormalization inputWeight hinputWeight)

/--
Through cutoff four, the phase-aware parent-pair scheduler route constructs
the complete quantified Claim 5 power input automa.
-/
theorem
    all_automatic_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1} :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  apply
    all_schedules_four
      (layer := layer) hn hn4 H hH
  intro inputWeight hinputWeight lowerWeight _hnonterminal nextNormalizer
    factor hfactorWeight hfactorTruncated
  exact
    active_normalization_four
      hn hn4 H hH hinputWeight nextNormalizer factor hfactorWeight
        hfactorTruncated

/--
Through cutoff four, the automatic phase-aware parent-pair scheduler route
gives the weight-controlled Hall-coordinate polynomial degree bound.
-/
theorem
    all_automatic_n
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
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
        (all_automatic_four
          (layer := layer) hn hn4 H hH)
        u hu hr hs hsn i

end
  RANorm
end TCTex
end Towers

/-!
# Automatic operational negative-input parent-pair normalization through cutoff four

Through cutoff four, the retained-profile selected endpoint kernel and the
explicit directed negative-input parent-pair schedules provide the operational
weight-one Claim 5 route.  The class-three residual-source collector
automa supplies every local factor normalization, so this route yields
the complete quantified power input and its Hall-coordinate degree bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CRLayer
open
  CTBounda

/--
Through cutoff four, the directed negative-input parent-pair scheduler route
constructs the complete quantified Claim 5 power input automa.
-/
theorem
    automatic_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1} :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  apply
    schedules_n_four
      (layer := layer) hn hn4 H hH
  intro inputWeight hinputWeight lowerWeight _hnonterminal nextNormalizer
    factor hfactorWeight hfactorTruncated
  exact
    active_normalization_four
      hn hn4 H hH hinputWeight nextNormalizer factor hfactorWeight
        hfactorTruncated

/--
Through cutoff four, the automatic directed negative-input parent-pair
scheduler route gives the weight-controlled Hall-coordinate polynomial degree
bound directly.
-/
theorem
    negative_automatic_four
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
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
        (automatic_n_four
          (layer := layer) hn hn4 H hH)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Automatic semantic-order signed trailing-context collection through cutoff four

Through cutoff four, the retained occurrence schedule and the sorted
retained-packet law construct the sharp signed trailing-context collector
kernel.  This avoids assuming a directed retained-order occurrence transport:
the Claim 5 route only needs equality of the ordered and inherited products.

This file instantiates that sharper kernel at the retained-profile selected
endpoint and carries it through Claim 5 and the Hall-coordinate degree bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  RTNorm

universe u


open
  PPSched
open
  CTBounda
open
  OCKerna
open
  CRLayer
open
  PTOcc
open
  FIBridge

/--
Through cutoff four, the retained occurrence schedule and sorted semantic law
construct the sharp signed trailing-context semantic-order collector kernel.
-/
noncomputable def
    trailing_context_collector
    {d n : ℕ}
    (hn : n ≤ 4) :
    CSCollec.{u}
      d n :=
  CSCollec.occ_coeff_trunc
    (COSched.n_four hn)
    (satisfies_n_four
      hn)

/--
Through cutoff four, the sharp semantic-order collector kernel assembles the
phase-aware all-integral parent-pair schedule.
-/
noncomputable def
    all_parent_four
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hn : n ≤ 4) :
    PPSchedu.{u}
      d n layer
        (idxNFour
          layer hn)
        (coeffNFour
          layer hn) :=
  (trailing_context_collector
      (d := d) hn).allPhaseSchedules
    (idxNFour
      layer hn)
    (coeffNFour
      layer hn)

/--
The sharp semantic-order collector kernel gives the retained-profile selected
endpoint its full signed list-evaluation law through cutoff four.
-/
def
    idx_semantic_collector
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hn : n ≤ 4) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d)
      (idxNFour
        layer hn) :=
  (trailing_context_collector
      (d := d) hn).satisfiesTruncAlignment
    (idxNFour
      layer hn)
    (coeffNFour
      layer hn)

namespace TSInput

/--
Through cutoff four, the sharp semantic-order collector kernel constructs the
Claim 5 coordinate polynomials from a supported sourced input.
-/
theorem
    coordCutoffFour
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
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
    CollectedPolynomialData (n := n) H e inputWeight :=
  CSCollec.TSInput.coordAlignmentCollector
    hn H hH
      (idxNFour
        layer hn4)
      (coeffNFour
        layer hn4)
      (trailing_context_collector hn4)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

/--
Through cutoff four, local factor normalizations promote the sharp semantic
collector-kernel route to the complete quantified Claim 5 power input.
-/
theorem
    collected_forall_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (factorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1) H →
                ∀ (factor : SPFactora H inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight) H factor) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hOne : inputWeight = 1
  · subst inputWeight
    exact
      TSInput.coordCutoffFour
        (layer := layer) hn hn4 H hH
          (TSInput.classThreeSource
            hn4 e)
          (TSInput.word_least_source
            hn4 e)
          (factorNormalization 1 (by omega)) (by omega)
  · exact
      collected_profiles_below
        hn H hH hinputWeight (by omega)
          (idxNFour
            layer hn4)
          (idx_semantic_collector
            layer hn4)
          (factorNormalization inputWeight hinputWeight)

/--
Through cutoff four, the sharp semantic-order collector-kernel route
constructs the complete quantified Claim 5 power input automa.
-/
theorem
    forall_automatic_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1} :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  apply
    collected_forall_four
      (layer := layer) hn hn4 H hH
  intro inputWeight hinputWeight lowerWeight _hnonterminal nextNormalizer
    factor hfactorWeight hfactorTruncated
  exact
    active_normalization_four
      hn hn4 H hH hinputWeight nextNormalizer factor hfactorWeight
        hfactorTruncated

/--
Through cutoff four, the automatic sharp semantic-order collector-kernel
route gives the weight-controlled Hall-coordinate polynomial degree bound.
-/
theorem
    poly_automatic_four
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
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
        (forall_automatic_four
          (layer := layer) hn hn4 H hH)
        u hu hr hs hsn i

end
  RTNorm
end TCTex
end Towers

/-!
# Claim 5 from semantic retained fiber counts and signed trailing contexts

The retained recipe-coefficient assignment need not agree literally with a
selected endpoint profile assignment.  Natural retained endpoint-fiber counts,
an all-integral retained occurrence schedule, and cutoff-aware retained-order
transport already give the selected endpoint interpolation its signed lift.

This file threads that operational semantic collector through the intrinsic
residual-source recursion.  The result is the quantified Claim 5 input and the
weight-controlled Hall-coordinate polynomial degree bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  FPInterp
open
  OOSched
open
  FTOcc
open
  TCBounda
open
  CRLayer
open
  CFSubsti
open
  CTAssigna
open
  FCAssign
open
  PTOcc
open
  FIBridge

namespace
  SPInput

/--
Retained endpoint-fiber counts, an all-integral retained occurrence schedule,
and cutoff-aware retained-order transport give any selected endpoint profile
kernel its signed interpolation lift.
-/
def
    allOccTransport
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      TOTransa.{u} d n) :
    EIFiber.AILift.{u}
      (d := d) kernel :=
  kernel.allLiftSatisfies
    (TCBounda.EIFiber.truncOccTransport
      kernel
      hretained schedule orderedTransport)

/--
The operational semantic retained collector, finitely many supported
low-weight sources, and intrinsic residual recollections construct the complete
quantified Claim 5 power input.
-/
theorem
    forall_counts_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      TOTransa.{u} d n)
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
          (n := n) H e inputWeight :=
  forall_endpoint_builders
    hn H hH kernel.fiberProfileInterpolation
      (allOccTransport
        kernel hretained schedule orderedTransport)
      lowWeightSource lowWeightSupported builders

/--
The operational semantic retained collector yields the weight-controlled
integer-valued polynomial degree bound for every Hall coordinate of a power.
-/
theorem
    counts_collect_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      TOTransa.{u} d n)
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
        (forall_counts_builders
          hn H hH kernel hretained schedule orderedTransport lowWeightSource
            lowWeightSupported builders)
        u hu hr hs hsn i

end
  SPInput
end TCTex
end Towers

/-!
# Semantic retained-profile alignment through cutoff four

Through cutoff four, retained recipe-coefficient profiles count the selected
cutoff-full endpoint fibers on the natural quadrant and the sorted retained
packet satisfies its signed recollection law.  Integral packet extensionality
therefore gives the all-integral list law for any selected endpoint
finite-index profile kernel, without literal equality of profile records.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  SRAligna

universe u


open
  SOAlign
open
  SABounda
open
  CRLayer
open
  FUClass
open
  FIBridge

namespace
  EIFiber

/--
Through cutoff four, every selected endpoint finite-index profile kernel has
its all-integral signed list-evaluation law.  Only natural endpoint-fiber
counting is used to compare its profile syntax with the retained transversal.
-/
def satisfies_alignment_four
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hn : n ≤ 4) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  SABounda.EIFiber.satisfiesFibersCoeff
    kernel
      (signed_n_four
        layer hn)
      (satisfies_n_four
        hn)

end
  EIFiber

namespace TSInput

/--
Through cutoff four, any selected endpoint finite-index profile kernel
constructs the Claim 5 coordinate polynomials through semantic retained-profile
alignment.
-/
theorem
    coordAlignmentFour
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
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
  _root_.Towers.TCTex.TSInput.coordTruncEval
    hn H hH kernel
      (EIFiber.satisfies_alignment_four
        kernel hn4)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  SRAligna
end TCTex
end Towers
