import Towers.Group.Zassenhaus.PolynomialOrbitVocabulary
import Towers.Group.Zassenhaus.ClassTwo
import Towers.Group.Zassenhaus.RestrictedSharp

/-!
# Claim 5 from operational recipe-chunk-aligned occurrence packets

A symbolic Hall collector must retain an ordered occurrence packet rather than
the entire conservative correction closure.  Same-word recipes may occur more
than once, and their block histories contribute distinct binomial profiles.

This file packages an all-integral ordered recipe packet together with orbit
support, recipe-chunk alignment, and intrinsic residual-source recollections.
The package exposes its occurrence-preserving finite trace, compiles to the
restricted-sharp recursive collector, and yields the quantified Claim 5 input
and Hall-coordinate polynomial degree bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CSAggreg
open
  ACAlign
open
  FCAssign
open UCVocabu
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
A fixed operational root packet, independent of later Hall-power input weights.
Its selected ordered recipes remain occurrence-sensitive, are supported by the
finite polynomial-orbit dictionary, and aggregate chunk-by-chunk to one signed
profile assignment.
-/
structure CAOccur
    (d n : ℕ) where
  assignment :
    SPAssign n 1 1
  packet :
    TAPkt.{u} d n
  orbitSupported :
    RecipeOrbitSupported n 1 1 packet.recipes
  recipeChunkAlignment :
    SPAssign.RCAlign
      assignment packet.recipes

namespace CAOccur

/--
Build a selected root packet from pointwise retained-closure membership.  The
closure remains a support certificate only; its full inventory is not summed.
-/
noncomputable def retainedClosureRecipes
    {d n : ℕ}
    (assignment : SPAssign n 1 1)
    (packet : TAPkt.{u} d n)
    (hrecipes :
      ∀ recipe ∈ packet.recipes,
        recipe ∈ correctionClosureRecipes n 1 1)
    (recipeChunkAlignment :
      SPAssign.RCAlign
        assignment packet.recipes) :
    CAOccur d n where
  assignment := assignment
  packet := packet
  orbitSupported :=
    recipe_supported_recipes hrecipes
  recipeChunkAlignment := recipeChunkAlignment

/-- The occurrence-preserving finite polynomial-orbit trace encoded by a fixed
root packet. -/
noncomputable def finiteIndexTrace
    {d n : ℕ}
    (rootPacket : CAOccur.{u} d n) :
    List (RetainedOrbitIndex n 1 1) :=
  chunkAlignedTrace
    rootPacket.assignment rootPacket.packet rootPacket.orbitSupported
      rootPacket.recipeChunkAlignment

/-- A fixed root packet aligns naturally with every retained operational
endpoint, occurrence-for-occurrence. -/
noncomputable def collectedNaturalAlignment
    {d n : ℕ}
    (rootPacket : CAOccur.{u} d n) :
    SatisfiesOccurrenceAlignment.{u}
      (d := d) (by simp) (by simp) rootPacket.finiteIndexTrace :=
  chunkAlignedAlignment
    rootPacket.assignment rootPacket.packet rootPacket.orbitSupported
      rootPacket.recipeChunkAlignment

/-- A fixed root packet has the signed extension of its natural operational
endpoint packet. -/
noncomputable def collectedOccurrenceAll
    {d n : ℕ}
    (kernel : OCShape)
    (rootPacket : CAOccur.{u} d n) :
    OccurrenceAllLift kernel rootPacket.finiteIndexTrace
      rootPacket.collectedNaturalAlignment :=
  chunkAlignedLift
    kernel rootPacket.assignment rootPacket.packet rootPacket.orbitSupported
      rootPacket.recipeChunkAlignment

/-- A fixed root packet satisfies the all-integral finite-trace semantic law. -/
lemma satisfiesTruncatedEval
    {d n : ℕ}
    (rootPacket : CAOccur.{u} d n) :
    SatisfiesTruncatedEval.{u}
      (d := d) rootPacket.finiteIndexTrace :=
  satisfies_chunk_aligned
    rootPacket.assignment rootPacket.packet rootPacket.orbitSupported
      rootPacket.recipeChunkAlignment

end CAOccur

/--
An operationally meaningful fixed root packet: its ordered recipes are
polynomial-orbit supported and aggregate, chunk-by-chunk, to a signed profile
assignment.  Intrinsic residual-source recollections supply the remaining local
input for Hall-power collection at one input weight.
-/
structure
    TABuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  assignment :
    SPAssign n 1 1
  packet :
    TAPkt.{u} d n
  orbitSupported :
    RecipeOrbitSupported n 1 1 packet.recipes
  recipeChunkAlignment :
    SPAssign.RCAlign
      assignment packet.recipes
  factorResidualSource :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor : SPFactora H inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TSSrc
              (lowerWeight := lowerWeight) hn H hH factor

namespace
  TABuild

/-- Attach input-weight-specific intrinsic residual recollections to one fixed
operational root packet. -/
noncomputable def packet_residual_source
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (rootPacket : CAOccur.{u} d n)
    (factorResidualSource :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          ∀ (factor : SPFactora H inputWeight),
            factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSSrc
                (lowerWeight := lowerWeight) hn H hH factor) :
    TABuild
      (n := n) (inputWeight := inputWeight) hn H hH where
  assignment := rootPacket.assignment
  packet := rootPacket.packet
  orbitSupported := rootPacket.orbitSupported
  recipeChunkAlignment := rootPacket.recipeChunkAlignment
  factorResidualSource := factorResidualSource

/--
Pointwise membership in the conservative retained correction closure is enough
to certify polynomial-orbit support for an ordered selected packet.  The packet
itself remains selected: this does not replace it by the full closure inventory.
-/
noncomputable def retainedClosureRecipes
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (assignment : SPAssign n 1 1)
    (packet : TAPkt.{u} d n)
    (hrecipes :
      ∀ recipe ∈ packet.recipes,
        recipe ∈ correctionClosureRecipes n 1 1)
    (recipeChunkAlignment :
      SPAssign.RCAlign
        assignment packet.recipes)
    (factorResidualSource :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          ∀ (factor : SPFactora H inputWeight),
            factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSSrc
                (lowerWeight := lowerWeight) hn H hH factor) :
    TABuild
      (n := n) (inputWeight := inputWeight) hn H hH :=
  packet_residual_source
    (CAOccur.retainedClosureRecipes
      assignment packet hrecipes recipeChunkAlignment)
    factorResidualSource

/-- The occurrence-preserving finite polynomial-orbit trace encoded by the
ordered recipe packet. -/
noncomputable def finiteIndexTrace
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      TABuild
        (n := n) (inputWeight := inputWeight) hn H hH) :
    List (RetainedOrbitIndex n 1 1) :=
  chunkAlignedTrace
    builder.assignment builder.packet builder.orbitSupported
      builder.recipeChunkAlignment

/-- The packaged trace aligns naturally with every retained operational
endpoint, occurrence-for-occurrence. -/
noncomputable def collectedNaturalAlignment
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      TABuild
        (n := n) (inputWeight := inputWeight) hn H hH) :
    SatisfiesOccurrenceAlignment.{u}
      (d := d) (by simp) (by simp) builder.finiteIndexTrace :=
  chunkAlignedAlignment
    builder.assignment builder.packet builder.orbitSupported
      builder.recipeChunkAlignment

/-- The packaged trace has the signed extension of its natural operational
endpoint packet. -/
noncomputable def collectedOccurrenceAll
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (kernel : OCShape)
    (builder :
      TABuild
        (n := n) (inputWeight := inputWeight) hn H hH) :
    OccurrenceAllLift kernel builder.finiteIndexTrace
      builder.collectedNaturalAlignment :=
  chunkAlignedLift
    kernel builder.assignment builder.packet builder.orbitSupported
      builder.recipeChunkAlignment

/-- The packaged occurrence trace satisfies the fixed-truncation all-integral
semantic law. -/
lemma satisfiesTruncatedEval
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      TABuild
        (n := n) (inputWeight := inputWeight) hn H hH) :
    SatisfiesTruncatedEval.{u}
      (d := d) builder.finiteIndexTrace :=
  satisfies_chunk_aligned
    builder.assignment builder.packet builder.orbitSupported
      builder.recipeChunkAlignment

/-- Forget only the operational certification when compiling to the direct
restricted-sharp residual-source collector. -/
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
      TABuild
        (n := n) (inputWeight := inputWeight) hn H hH) :
    TSBuilda
      (n := n) (inputWeight := inputWeight) hn H hH where
  packet := builder.packet
  factorResidualSource := builder.factorResidualSource

end
  TABuild

namespace TSInput

/--
One supported sourced input and one operational recipe-chunk-aligned residual
builder construct the integer-valued coordinate polynomials required by Claim 5.
-/
theorem
    coordAlignedBuilder
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
      TABuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.sharpCollectionBuilder
    hn H hH hsourceSupported
      builder.restrictedSharpPacket
      hinputWeight

end TSInput

/--
Operational recipe-chunk-aligned packets, finitely many supported low-weight
sources, and intrinsic residual recollections construct the complete quantified
Claim 5 power input.
-/
theorem
    forall_recipe_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          TABuild
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
      TSInput.coordAlignedBuilder
        hn H hH
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          (builders inputWeight hinputWeight) hinputWeight

/--
One fixed operational occurrence packet can be reused at every Hall-power input
weight.  Only intrinsic residual-source recollections remain weight-indexed.
-/
theorem
    collected_occ_sources
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (rootPacket : CAOccur.{u} d n)
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
  forall_recipe_builders
    hn H hH lowWeightSource lowWeightSupported
      (fun inputWeight hinputWeight =>
        TABuild.packet_residual_source
          rootPacket (factorResidualSources inputWeight hinputWeight))

/--
The operational recipe-chunk-aligned residual-source collector yields the
weight-controlled integer-valued polynomial degree bound for every Hall
coordinate of a power.
-/
theorem
    poly_residual_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
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
          TABuild
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
        (forall_recipe_builders
          hn H hH lowWeightSource lowWeightSupported builders)
        u hu hr hs hsn i

/--
One fixed operational occurrence packet and weight-indexed intrinsic residual
recollections yield the Hall-coordinate polynomial degree bound.
-/
theorem
    chunk_aligned_sources
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (rootPacket : CAOccur.{u} d n)
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
        (collected_occ_sources
          hn H hH rootPacket lowWeightSource lowWeightSupported
            factorResidualSources)
        u hu hr hs hsn i

end TCTex
end Towers
