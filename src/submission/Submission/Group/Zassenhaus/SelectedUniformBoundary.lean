import Submission.Group.Zassenhaus.InverseTrace
import Submission.Group.Zassenhaus.RecipeChunkBoundary

/-!
# Claim 5 from selected operational uniform signed recipe packets

An arbitrary-cutoff symbolic Hall collector need not compress its selected
ordered recipes into one packet per conservative closure word.  Such compression
can lose order and distinct block histories.  The honest root output is simply
one selected all-integral recipe packet whose recipes are supported by the
retained finite polynomial-orbit dictionary.

This file packages that minimal occurrence-preserving root certificate.  It can
be built directly from a provenance-carrying uniform signed inverse-schedule
packet when every selected recipe belongs to the conservative retained closure.
The closure certifies support only: it is never substituted for the selected
packet.

The selected packet then compiles through intrinsic residual-source recollection
to the quantified Claim 5 input and the Hall-coordinate polynomial degree bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HACoeff
open
  CSAggreg
open ITSched
open ITSched.PPScheda
open
  UCVocabu
open
  RITrace
open
  ENStab
open
  CABounda
open
  ESLift
open
  PTRecipe
open
  PTSigned
open PFSubsti

/--
One selected operational root packet.  Its ordered recipes remain
occurrence-sensitive and are supported by the retained finite polynomial-orbit
dictionary.
-/
structure SOPkt
    (d n : ℕ) where
  packet :
    TAPkt.{u} d n
  orbitSupported :
    RecipeOrbitSupported n 1 1 packet.recipes

namespace SOPkt

/--
Pointwise membership in the conservative retained closure certifies orbit
support for a selected packet without replacing it by the closure inventory.
-/
noncomputable def retainedClosureRecipes
    {d n : ℕ}
    (packet : TAPkt.{u} d n)
    (hrecipes :
      ∀ recipe ∈ packet.recipes,
        recipe ∈ correctionClosureRecipes n 1 1) :
    SOPkt d n where
  packet := packet
  orbitSupported :=
    recipe_supported_recipes hrecipes

/--
A recipe-chunk-aligned packet is, after forgetting optional compression data,
a selected operational occurrence packet.
-/
noncomputable def recipeChunkAligned
    {d n : ℕ}
    (rootPacket : CAOccur.{u} d n) :
    SOPkt d n where
  packet := rootPacket.packet
  orbitSupported := rootPacket.orbitSupported

/--
A provenance-carrying uniform signed inverse-schedule packet whose selected
recipes are orbit-supported supplies the minimal operational root certificate.
-/
noncomputable def uniformOrbitSupported
    {scheduleKernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (signed : USPkt.{u} scheduleKernel recipes d n)
    (orbitSupported : RecipeOrbitSupported n 1 1 recipes) :
    SOPkt d n where
  packet := signed.truncatedAll
  orbitSupported := by
    simpa only [
      USPkt.recipes_all_packet] using
        orbitSupported

/--
A provenance-carrying uniform signed inverse-schedule packet whose selected
recipes lie in the retained closure supplies the minimal operational root
certificate.
-/
noncomputable def uniformSignedRecipe
    {scheduleKernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (signed : USPkt.{u} scheduleKernel recipes d n)
    (hrecipes :
      ∀ recipe ∈ recipes,
        recipe ∈ correctionClosureRecipes n 1 1) :
    SOPkt d n :=
  uniformOrbitSupported signed
    (recipe_supported_recipes
      hrecipes)

/-- The occurrence-preserving finite polynomial-orbit trace encoded by the
selected root packet. -/
noncomputable def finiteIndexTrace
    {d n : ℕ}
    (rootPacket : SOPkt.{u} d n) :
    List (RetainedOrbitIndex n 1 1) :=
  finIdxAll
    rootPacket.packet rootPacket.orbitSupported

/-- The selected occurrence trace satisfies the all-integral finite-trace
semantic law. -/
lemma satisfiesTruncatedEval
    {d n : ℕ}
    (rootPacket : SOPkt.{u} d n) :
    SatisfiesTruncatedEval.{u}
      (d := d) rootPacket.finiteIndexTrace :=
  satisfies_all_packet
    rootPacket.packet rootPacket.orbitSupported

/-- The selected occurrence trace aligns naturally with every retained
operational endpoint. -/
noncomputable def collectedNaturalAlignment
    {d n : ℕ}
    (rootPacket : SOPkt.{u} d n) :
    SatisfiesOccurrenceAlignment.{u}
      (d := d) (by simp) (by simp) rootPacket.finiteIndexTrace :=
  occurrenceAlignmentSatisfies
    rootPacket.finiteIndexTrace rootPacket.satisfiesTruncatedEval

/-- The selected occurrence trace has the signed extension of its natural
operational endpoint packet. -/
noncomputable def collectedOccurrenceAll
    {d n : ℕ}
    (kernel : OCShape)
    (rootPacket : SOPkt.{u} d n) :
    OccurrenceAllLift kernel rootPacket.finiteIndexTrace
      rootPacket.collectedNaturalAlignment :=
  occurrenceAllSatisfies
    kernel rootPacket.finiteIndexTrace
      rootPacket.satisfiesTruncatedEval

end SOPkt

/--
One selected operational root packet and intrinsic residual-source recollections
for one Hall-power input weight.
-/
structure
    SOBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  rootPacket :
    SOPkt.{u} d n
  factorResidualSource :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor : SPFactora H inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TSSrc
              (lowerWeight := lowerWeight) hn H hH factor

namespace
  SOBuild

/-- Compile the selected operational packet to the direct restricted-sharp
residual-source collector. -/
noncomputable def restrictedSharpPacket
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      SOBuild
        (n := n) (inputWeight := inputWeight) hn H hH) :
    TSBuilda
      (n := n) (inputWeight := inputWeight) hn H hH where
  packet := builder.rootPacket.packet
  factorResidualSource := builder.factorResidualSource

end
  SOBuild

namespace TSInput

/--
One supported sourced input and one selected operational residual builder
construct the integer-valued coordinate polynomials required by Claim 5.
-/
theorem
    coordCollectBuilder
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
    (builder :
      SOBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.sharpCollectionBuilder
    hn H hH hsourceSupported
      builder.restrictedSharpPacket
      hinputWeight

end TSInput

/--
One fixed selected occurrence packet, finitely many supported low-weight
sources, and weight-indexed intrinsic residual recollections construct the
complete quantified Claim 5 power input.
-/
theorem
    forall_occ_sources
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (rootPacket : SOPkt.{u} d n)
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
    (factorResidualSources :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              ∀ (factor : SPFactora H inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TSSrc
                      (lowerWeight := lowerWeight) hn H hH factor) :
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
      TSInput.coordCollectBuilder
        hn H hH
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          { rootPacket := rootPacket
            factorResidualSource :=
              factorResidualSources inputWeight hinputWeight }
          hinputWeight

/--
A provenance-carrying uniform signed inverse-schedule packet supported by the
retained closure supplies the complete quantified Claim 5 power input.
-/
theorem
    forall_recipes_sources
    {scheduleKernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (signed : USPkt.{u} scheduleKernel recipes d n)
    (hrecipes :
      ∀ recipe ∈ recipes,
        recipe ∈ correctionClosureRecipes n 1 1)
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
    (factorResidualSources :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              ∀ (factor : SPFactora H inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TSSrc
                      (lowerWeight := lowerWeight) hn H hH factor) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight :=
  forall_occ_sources
    hn H hH
      (SOPkt.uniformSignedRecipe
        signed hrecipes)
      lowWeightSource lowWeightSupported factorResidualSources

/--
A selected operational occurrence packet and intrinsic residual recollections
yield the weight-controlled integer-valued polynomial degree bound for every
Hall coordinate of a power.
-/
theorem
    selected_occurrence_sources
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (rootPacket : SOPkt.{u} d n)
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
    (factorResidualSources :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              ∀ (factor : SPFactora H inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TSSrc
                      (lowerWeight := lowerWeight) hn H hH factor)
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
        (forall_occ_sources
          hn H hH rootPacket lowWeightSource lowWeightSupported
            factorResidualSources)
        u hu hr hs hsn i

/--
A provenance-carrying uniform signed inverse-schedule packet supported by the
retained closure yields the Hall-coordinate polynomial degree bound.
-/
theorem
    poly_recipes_sources
    {scheduleKernel : PPScheda}
    {recipes : List BRecipe}
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (signed : USPkt.{u} scheduleKernel recipes d n)
    (hrecipes :
      ∀ recipe ∈ recipes,
        recipe ∈ correctionClosureRecipes n 1 1)
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
    (factorResidualSources :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              ∀ (factor : SPFactora H inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TSSrc
                      (lowerWeight := lowerWeight) hn H hH factor)
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
      (s / r) :=
  selected_occurrence_sources
    hn H hH
      (SOPkt.uniformSignedRecipe
        signed hrecipes)
      lowWeightSource lowWeightSupported factorResidualSources
      u hu hr hs hsn i

end TCTex
end Submission
