import Towers.Group.Zassenhaus.RetainedHistoryFibers
import Towers.Group.Zassenhaus.CanonicalPacketAlignment
import Towers.Group.Zassenhaus.InverseUniversalClosure
import Towers.Group.Zassenhaus.FiniteIndexProfiles
import Towers.Group.Zassenhaus.OneSourcedInput
import Towers.Group.Zassenhaus.ClassTwo
import Towers.Group.Zassenhaus.TwoSourcedInput
import Towers.Group.Zassenhaus.EndpointShapeInterpolation

/-!
# Claim 5 from the cutoff-full endpoint shape fibers in class three

Above weight three and through cutoff four, the cutoff-full endpoint shape
fibers are counted by the three retained class-three profiles.  The fixed-slot
vocabulary sorts those profiles into operational occurrence order.  This order
may differ from the finite-closure enumeration, but the class-three factors
commute pairwise, so its product has the same all-integral Hall-Petresco law.

This file discharges the signed lift of the operational endpoint-fiber packet
and routes that packet to the Claim 5 coordinate polynomials.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

open
  CCThreeb
open
  FFInhomo
open
  FPInterp
open CRLayer
open NRSubinv
open
  CFSubsti
open
  CTPacket
open
  CTAssigna
open
  FTCollec
open
  FCAssign
open
  UCSuppor

namespace
  CCThreeb

/-- Sorting the finite vocabulary preserves its class-three support list up to
permutation. -/
lemma vocabulary_perm_words
    {n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    List.Perm (orderedErasedVocabulary n 1 1)
      [inverseLeftTriple, CWord.hallPairBase,
        inverseTripleWord] :=
  (List.perm_insertionSort erasedShapeLE
      (erasedShapeVocabulary n 1 1)).trans
    (erased_perm_words hlow hhigh)

/-- The sorted retained-selector packet product is the product of the
corresponding pure class-three factors. -/
lemma
    list_ordered_factor
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    ((((blockProfileAssignment n)
        |>.toSPAssign
        |>.erasedVocabPackets).map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod) =
      ((orderedErasedVocabulary n 1 1).map
        (classThreeFactor left right leftExponent rightExponent)).prod := by
  unfold SPAssign.erasedVocabPackets
  rw [List.map_map]
  simp only [blockProfileAssignment]
  change
    (((orderedErasedVocabulary n 1 1).attach.map fun word =>
      word.1.eval (HPAtom.eval left right) ^
        (retainedRecipeProfiles
          ⟨word.1, ordered_erased_vocabulary.mp word.2⟩).value
          leftExponent rightExponent).prod) =
      ((orderedErasedVocabulary n 1 1).map
        (classThreeFactor left right leftExponent rightExponent)).prod
  rw [List.map_congr_left (fun word _hword =>
    zpow_profiles_factor
      hn left right leftExponent rightExponent
        ⟨word.1, ordered_erased_vocabulary.mp word.2⟩)]
  simpa only [List.map_map, Function.comp_apply] using
    congrArg
      (fun words => (words.map
        (classThreeFactor left right leftExponent rightExponent)).prod)
      (List.attach_map_subtype_val (orderedErasedVocabulary n 1 1))

/--
The sorted retained-selector packet satisfies the all-integral product law in
class three.
-/
lemma list_n_four
    {d n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    ((((blockProfileAssignment n)
        |>.toSPAssign
        |>.erasedVocabPackets).map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod) =
      ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
  rw [
    list_ordered_factor
      hhigh left right leftExponent rightExponent]
  calc
    ((orderedErasedVocabulary n 1 1).map
        (classThreeFactor left right leftExponent rightExponent)).prod =
        ([inverseLeftTriple, CWord.hallPairBase,
          inverseTripleWord].map
            (classThreeFactor left right leftExponent rightExponent)).prod := by
      exact
        (((vocabulary_perm_words hlow hhigh).symm.map
          (classThreeFactor left right leftExponent rightExponent)).prod_eq'
            (pairwise_commute_factor
              hhigh left right leftExponent rightExponent)).symm
    _ = ⁅left ^ leftExponent, right ^ rightExponent⁆ :=
      prod_element_zpow
        hhigh left right leftExponent rightExponent

/--
The class-three endpoint-fiber presentation kernel has the signed extension
required by the fixed-slot Claim 5 route.
-/
def endpointFiberFour
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    FHPres.AILift.{u}
      (d := d)
        (fiberHomogeneousFour
          layer hlow hhigh) where
  listEval_eq left right leftExponent rightExponent := by
    change
      ((((blockProfileAssignment n)
          |>.toSPAssign
          |>.erasedVocabPackets).map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod) =
        ⁅left ^ leftExponent, right ^ rightExponent⁆
    exact
      list_n_four
        hlow hhigh left right leftExponent rightExponent

end
  CCThreeb

namespace TSInput

/--
In class three, the operational cutoff-full endpoint shape fibers construct the
Claim 5 coordinate polynomials without a separate signed-lift hypothesis.
-/
theorem
    fullEndpointFiber
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hclassThree : 3 < n)
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
  input.fiberHomogeneousLift
    hn H hH
      (fiberHomogeneousFour
        layer hclassThree hn4)
      (endpointFiberFour
        layer hclassThree hn4)
      hsourceSupported factorNormalization hinputWeight

/--
Through cutoff four, the operational cutoff-full endpoint shape fibers
construct the Claim 5 coordinate polynomials without a separate signed-lift
hypothesis.
-/
theorem
    fullFiberFour
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
    CollectedPolynomialData (n := n) H e inputWeight := by
  by_cases hn3 : n ≤ 3
  · exact
      input.fullFiberLow
        (layer := layer) hn hn3 H hH hsourceSupported factorNormalization
          hinputWeight
  · exact
      input.fullEndpointFiber
        (layer := layer) hn (by omega) hn4 H hH hsourceSupported
          factorNormalization hinputWeight

end TSInput

end TCTex
end Towers

/-!
# Claim 5 from finite-index cutoff-full shape-fiber profiles

The cutoff-full scheduler endpoint splits into retained inverse-raw
occurrences and selected retained corrections.  Both inventories now have
occurrence-preserving traces over the same fixed finite polynomial-orbit
alphabet.

This file compiles homogeneous fiber profiles for those two finite-index
traces into the existing Claim 5 coordinate-polynomial constructor.  The
ordered summed-profile recollection law remains explicit: finite fiber counts
do not silently prove a noncommutative product identity.

The second adapter specializes the raw side to the canonical retained-source
polynomial-orbit transversal.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


namespace
  SICollec

open
  CRLayer
open
  ISFiber
open
  RHSplit
open
  FIProf
open
  RFTransv
open
  TFIdx

/--
Combine finite-index raw-source and selected scheduler-correction profile
kernels into the endpoint raw-history/correction split consumed by Claim 5.
-/
noncomputable def fiberProfileSplit
    {n : ℕ}
    {layer : NRLayer n 1 1}
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (corrections :
      SFProf
        layer (by simp) (by simp)) :
    EFSplit layer :=
  EFSplit.idx_fiber_profile
    raw corrections

namespace TSInput

/--
Finite-index raw-source and selected scheduler-correction profiles, together
with their ordered summed-profile recollection law, construct the Claim 5
coordinate polynomials.
-/
theorem
    fiberProfileKernels
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (corrections :
      SFProf
        layer (by simp) (by simp))
    (hlistEval :
      EFSplit.SatisfiesTruncEval.{u}
        (d := d)
        (fiberProfileSplit
          raw corrections))
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
  input.coordHistoryTrunc
    hn H hH
      (fiberProfileSplit
        raw corrections)
      hlistEval hsourceSupported factorNormalization hinputWeight

/--
The canonical retained-source polynomial-orbit transversal, selected
scheduler-correction finite-index profiles, and their ordered summed-profile
recollection law construct the Claim 5 coordinate polynomials.
-/
theorem
    coordPolyFiber
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
          (TFIdx.PTStab.idxFiberProfile
            raw (by simp) (by simp))
          corrections))
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
  fiberProfileKernels
    hn H hH
      (TFIdx.PTStab.idxFiberProfile
        raw (by simp) (by simp))
      corrections hlistEval input hsourceSupported factorNormalization
        hinputWeight

end TSInput

end
  SICollec
end TCTex
end Towers

/-!
# Positive-below Claim 5 data from finite-index shape-fiber profiles

In the class-two source range, the canonical retained-raw polynomial-orbit
transversal and selected scheduler-correction finite-index profiles can
consume the native positive-below premise of Claim 5.  Zeroing irrelevant
layers below the requested input weight supplies the explicit sourced input
without changing the collected Hall product.

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
In the class-two source range, finite-index raw and selected-correction
shape-fiber profiles, their ordered summed-profile recollection law, and local
factor normalizations supply the positive-below Claim 5 power package.
-/
theorem
    fiber_profiles_below
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
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
    {e : HEFam H} :
    CollectedPolynomialData
      (n := n) H e inputWeight := by
  intro heBelow
  let e' : HEFam H :=
    HEFam.zeroBelow e inputWeight
  have he'Below :
      ∀ s : ℕ, s < inputWeight → e' s = 0 := by
    intro s hs
    simp [e', hs]
  have he'Product :
      collectedHallProduct (n := n) H e' =
        collectedHallProduct (n := n) H e := by
    simpa [e'] using collected_below_self e heBelow
  rcases
      (SICollec.TSInput.coordPolyFiber
          hn H hH raw corrections hlistEval
          (TSInput.classTwoSource
            hinputWeight hcutoff e' he'Below)
          (TSInput.least_two_source
            hinputWeight hcutoff e' he'Below)
          factorNormalization hinputWeight)
        (fun s _hs hs _hsn => he'Below s hs) with
    ⟨E, hEproduct, hEpolynomial⟩
  refine ⟨E, ?_, hEpolynomial⟩
  intro q
  exact (hEproduct q).trans (congrArg (fun x => x ^ q) he'Product)

end TCTex
end Towers

/-!
# Claim 5 from stabilized retained-raw and correction-trace profiles

The retained raw shape fibers have local homogeneous recipe-chunk profiles at
every natural specialization.  Once those local packets stabilize to fixed
profiles, homogeneous retained-correction profiles and the ordered
summed-profile recollection law construct the Claim 5 coordinate polynomials.

This file packages that composition while keeping the three arbitrary-cutoff
obligations explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CRLayer
open
  CRInv
open
  RHSplit
open
  FUBounda
open
  CFSubsti
open
  UCSuppor

namespace TSInput

/--
Stable retained-raw profiles, retained scheduler-correction profiles, and
their ordered summed-profile recollection law construct the Claim 5
coordinate polynomials.
-/
theorem
    coordPolyProfiles
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (raw : FUProf n 1 1)
    (retainedCorrectionProfiles :
      ∀ word ∈ erasedShapeVocabulary n 1 1,
        HFPkt
          word.pairLeftDegree word.pairRightDegree)
    (retained_correction_cast :
      ∀ (M N : ℕ) word hword,
        (retainedCorrectionProfiles word hword).value (M : ℤ) (N : ℤ) =
          ((((endpointCorrectionInventory layer M N).corrections.filter
            fun term =>
              decide (term.family.recipe.erasedShape = word)).length : ℕ) :
                ℤ))
    (hlistEval :
      EFSplit.SatisfiesTruncEval.{u}
        (d := d)
        (EFSplit.fiber_uniform_profile
          raw retainedCorrectionProfiles
            retained_correction_cast))
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
  input.coordHistoryTrunc
    hn H hH
      (EFSplit.fiber_uniform_profile
        raw retainedCorrectionProfiles
          retained_correction_cast)
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Towers

/-!
# Claim 5 from the retained-raw polynomial-orbit transversal

The retained-raw profile candidate can be chosen concretely: retain one
cutoff-sized dummy source recipe from each polynomial orbit and filter those
representatives by erased Hall shape.  Once that canonical candidate
specializes to the local retained-raw packet, the remaining inputs are the
actual scheduler-correction profiles and the ordered summed-profile
recollection law.

This file threads that sharper interface into the Claim 5 coordinate
polynomial constructor.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CRLayer
open
  CRInv
open
  RHSplit
open
  RFTransv
open
  FUBounda
open
  CFSubsti
open
  UCSuppor

namespace TSInput

/--
The canonical raw source-orbit transversal stabilization theorem, retained
scheduler-correction profiles, and their ordered summed-profile recollection
law construct the Claim 5 coordinate polynomials.
-/
theorem
    coordTransversalProfiles
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (raw :
      PTStab n 1 1)
    (retainedCorrectionProfiles :
      ∀ word ∈ erasedShapeVocabulary n 1 1,
        HFPkt
          word.pairLeftDegree word.pairRightDegree)
    (retained_correction_cast :
      ∀ (M N : ℕ) word hword,
        (retainedCorrectionProfiles word hword).value (M : ℤ) (N : ℤ) =
          ((((endpointCorrectionInventory layer M N).corrections.filter
            fun term =>
              decide (term.family.recipe.erasedShape = word)).length : ℕ) :
                ℤ))
    (hlistEval :
      EFSplit.SatisfiesTruncEval.{u}
        (d := d)
        (EFSplit.fiber_uniform_profile
          raw.fiberUniformProfile
          retainedCorrectionProfiles
            retained_correction_cast))
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
  input.coordPolyProfiles
    hn H hH raw.fiberUniformProfile
      retainedCorrectionProfiles retained_correction_cast
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Towers

/-!
# Claim 5 from uniform retained-raw profiles through cutoff four

Through cutoff four, the retained-recipe profiles count the exact retained
inverse-raw shape fibers and the cutoff scheduler retains no generated
corrections.  The resulting raw-history/correction split has zero correction
profiles.

This file proves the ordered signed recollection law for that split and routes
it through the arbitrary-cutoff split interface to the Claim 5 coordinate
polynomials.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open scoped commutatorElement

open
  CCThreeb
open CRLayer
open
  NRSubinv
open
  CRSplit
open
  RHSplit
open
  FUClass
open
  CFAlg
open
  CPSplit
open
  CTAssigna
open
  FTCollec
open
  FCAssign
open
  UCSuppor

namespace
  FUClass

/--
Sorting the retained-recipe profiles preserves their signed recollection law
through cutoff four.
-/
lemma coefficient_assignment_four
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    ((((blockProfileAssignment n)
        |>.toSPAssign
        |>.erasedVocabPackets).map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod) =
      ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
  by_cases hthree : n ≤ 3
  · have hvocabulary :
        orderedErasedVocabulary n 1 1 =
          erasedShapeVocabulary n 1 1 := by
      unfold orderedErasedVocabulary
      by_cases htwo : n ≤ 2
      · rw [vocabulary_nil_n htwo]
        rfl
      · rw [
          erased_vocabulary_singleton
            (by omega) hthree]
        rfl
    rw [
      CCThreeb.list_ordered_factor
        hn,
      hvocabulary,
      ←
        FTCollec.list_recipe_factor
          hn]
    exact
      (FTCollec.list_recipe_four
          hn left right leftExponent rightExponent)
  · exact
      CCThreeb.list_n_four
          (by omega) hn left right leftExponent rightExponent

/--
The compiled shallow raw-history/correction split satisfies the ordered signed
recollection law.
-/
lemma
    endpointFiberSatisfies
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    EFSplit.SatisfiesTruncEval.{u}
      (d := d)
      (fiberHistoryFour
        layer hhigh) := by
  intro left right leftExponent rightExponent
  simpa only [
    EFSplit.endpointRecipeFiber,
    EFProf.signedProfileAssignment,
    fiberHistoryFour,
    FUBounda.EFSplit.fiber_uniform_profile,
    uniformNFour,
    retainedZeroProfiles,
    FPkt.value_add,
    FPkt.value_zero,
    add_zero] using
    (coefficient_assignment_four
      hhigh left right leftExponent rightExponent)

end
  FUClass

namespace TSInput

/--
Through cutoff four, the uniform retained-raw split constructs the Claim 5
coordinate polynomials without an additional recollection hypothesis.
-/
theorem
    fiberUniformFour
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
  input.coordHistoryTrunc
    hn H hH
      (fiberHistoryFour
        layer hn4)
      (endpointFiberSatisfies
        layer hn4)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Towers

/-!
# Claim 5 from the canonical raw polynomial-orbit transversal through cutoff four

Through cutoff four, the canonical raw source polynomial-orbit transversal has
one representative for every surviving erased Hall shape.  Its profile agrees
with the retained-recipe singleton profile, and the actual cutoff scheduler has
no retained generated corrections.  This file transports the existing shallow
ordered signed recollection law to that canonical orbit profile and feeds it
directly into the arbitrary-cutoff polynomial-orbit Claim 5 adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open scoped commutatorElement

open CRLayer
open
  NRSubinv
open
  CRSplit
open
  RHSplit
open
  RFTransv
open
  TCThree
open
  FUBounda
open
  FUClass
open
  CFAlg
open
  CTAssigna
open
  FCAssign
open
  UCSuppor

namespace
  TCThree

/--
The canonical shallow raw polynomial-orbit profile and zero correction profile
satisfy the ordered signed recollection law.
-/
lemma
    fiberSatisfiesTrunc
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hn : n ≤ 4) :
    EFSplit.SatisfiesTruncEval.{u}
      (d := d)
      (EFSplit.fiber_uniform_profile
        (transversalStabilizationFour
          layer hn).fiberUniformProfile
        retainedZeroProfiles
        (profiles_value_cast layer hn)) := by
  intro left right leftExponent rightExponent
  simp only [
    EFSplit.endpointRecipeFiber,
    EFProf.signedProfileAssignment,
    SPAssign.erasedVocabPackets,
    FUBounda.EFSplit.fiber_uniform_profile,
    PTStab.fiberUniformProfile,
    retainedZeroProfiles,
    List.map_map]
  change
    ((((orderedErasedVocabulary n 1 1).attach.map fun word =>
      word.1.eval (HPAtom.eval left right) ^
        (FPkt.add
          (rawTransversalProfile n 1 1 word.1)
          (FPkt.zero word.1.pairLeftDegree
            word.1.pairRightDegree)).value
              leftExponent rightExponent).prod) =
      ⁅left ^ leftExponent, right ^ rightExponent⁆)
  calc
    _ =
        (((orderedErasedVocabulary n 1 1).attach.map fun word =>
          word.1.eval (HPAtom.eval left right) ^
            (retainedRecipeProfiles
              ⟨word.1, ordered_erased_vocabulary.mp word.2⟩).value
                leftExponent rightExponent).prod) := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro word _hword
      congr 1
      rw [FPkt.value_add, FPkt.value_zero, add_zero]
      exact
        poly_n_four
          hn ⟨word.1, ordered_erased_vocabulary.mp word.2⟩
            leftExponent rightExponent
    _ = ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
      simpa only [
        SPAssign.erasedVocabPackets,
        blockProfileAssignment,
        List.map_map,
        Function.comp_apply] using
        (coefficient_assignment_four
          hn left right leftExponent rightExponent)

end
  TCThree

namespace TSInput

/--
Through cutoff four, the canonical raw source polynomial-orbit transversal
constructs the Claim 5 coordinate polynomials without an additional
recollection hypothesis.
-/
theorem
    coordinateTransversalFour
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
  input.coordTransversalProfiles
    hn H hH
      (transversalStabilizationFour
        layer hn4)
      retainedZeroProfiles
      (profiles_value_cast layer hn4)
      (fiberSatisfiesTrunc
        layer hn4)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Towers

/-!
# Finite-index Claim 5 power package through cutoff four

Through cutoff four, the canonical retained-raw source transversal has the
known shallow profile, and the selected retained-correction finite-index
trace has zero shape-fiber counts.  This file threads those concrete
finite-index kernels through the ordered shallow recollection law and the
Claim 5 power constructor.

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
  RHSplit
open
  RFTransv
open
  TCThree
open
  TFIdx
open
  FUClass
open
  SICollec

namespace
  FTColleca

/--
Through cutoff four, the finite-index raw-transversal and zero-correction
kernels satisfy the ordered summed-profile recollection law.
-/
lemma
    finIdxSatisfies
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hn4 : n ≤ 4) :
    EFSplit.SatisfiesTruncEval.{u}
      (d := d)
      (fiberProfileSplit
        (PTStab.idxFiberProfile
          (transversalStabilizationFour
            layer hn4)
          (by simp) (by simp))
        (fiberNFour
          layer hn4)) := by
  simpa [
    fiberProfileSplit,
    fiberNFour
  ] using
    (fiberSatisfiesTrunc
      (d := d) layer hn4)

namespace TSInput

/--
Through cutoff four, the concrete finite-index raw and correction kernels
construct Claim 5 coordinate polynomials from any supported sourced input.
-/
theorem
    polyProfilesFour
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
  SICollec.TSInput.coordPolyFiber
    hn H hH
      (transversalStabilizationFour
        layer hn4)
      (fiberNFour
        layer hn4)
      (finIdxSatisfies
        layer hn4)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

/--
Through cutoff four, local factor normalizations promote the finite-index
shape-fiber route to the complete Claim 5 power input.
-/
theorem
    forall_profiles_four
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
      TSInput.polyProfilesFour
        (layer := layer) hn hn4 H hH
          (TSInput.classThreeSource
            hn4 e)
          (TSInput.word_least_source
            hn4 e)
          (factorNormalization 1 (by omega)) (by omega)
  · exact
      fiber_profiles_below
        hn H hH hinputWeight (by omega)
          (transversalStabilizationFour
            layer hn4)
          (fiberNFour
            layer hn4)
          (finIdxSatisfies
            layer hn4)
          (factorNormalization inputWeight hinputWeight)

end
  FTColleca
end TCTex
end Towers

/-!
# Arbitrary-cutoff power input from finite-index shape-fiber profiles

The class-two sourced-input constructor is automatic once
`n ≤ 3 * inputWeight`.  For a fixed cutoff, only finitely many lower input
weights lie outside that range.  This file promotes the finite-index
shape-fiber Claim 5 route to the full quantified power-polynomial package
while keeping exactly those genuinely low-weight sourced inputs explicit.

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
Finite-index shape-fiber profiles construct the complete Claim 5 power input
once supported sourced inputs are supplied for the finitely many lower
weights outside the automatic class-two source range.
-/
theorem
    forall_fiber_profiles
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
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
  by_cases hclassTwoRange : n ≤ 3 * inputWeight
  · exact
      fiber_profiles_below
        hn H hH hinputWeight hclassTwoRange raw corrections hlistEval
          (factorNormalization inputWeight hinputWeight)
  · exact
      SICollec.TSInput.coordPolyFiber
        hn H hH raw corrections hlistEval
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          (factorNormalization inputWeight hinputWeight) hinputWeight

end TCTex
end Towers

/-!
# Claim 5 from the selected operational endpoint finite-index trace

The cutoff-full operational collector has one selected occurrence-preserving
finite-index endpoint trace.  Its filtered fibers are exactly the natural
fixed-slot coordinates.  A homogeneous polynomial profile for each fiber
therefore gives the endpoint interpolation package directly.

This file isolates the remaining ordered all-integral law for those aggregate
profiles and threads it into the restricted-sharp Claim 5 constructor.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open scoped commutatorElement

open CRLayer
open
  CFSubsti
open
  FCAssign
open
  FIBridge
open
  FPInterp

namespace
  FIBridge
namespace EIFiber

/--
The signed extension still needed after aggregate selected-endpoint trace
fibers have been presented by homogeneous polynomial profiles.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight) :
    Prop :=
  EFInterp.AILift.{u}
    (d := d) kernel.fiberProfileInterpolation

/--
The ordered all-integral recollection law for the aggregate profiles attached
to the selected operational endpoint finite-index trace.
-/
def SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((kernel.signedProfileAssignment
        |>.erasedVocabPackets).map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/-- The aggregate ordered recollection law supplies its signed lift. -/
def allLiftSatisfies
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight)
    (hlistEval :
      EIFiber.SatisfiesTruncEval.{u}
        (d := d) kernel) :
    EIFiber.AILift.{u}
      (d := d) kernel where
  listEval_eq := by
    intro left right leftExponent rightExponent
    simpa only [
      EFInterp.packetsTruncNatural
    ] using hlistEval left right leftExponent rightExponent

/-- A signed lift recovers the aggregate ordered recollection law. -/
lemma satisfies_trunc_all
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight)
    (lift :
      EIFiber.AILift.{u}
        (d := d) kernel) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel := by
  intro left right leftExponent rightExponent
  simpa only [
    EFInterp.packetsTruncNatural
  ] using lift.listEval_eq left right leftExponent rightExponent

/--
For an aggregate endpoint-trace profile kernel, the signed lift is exactly
its ordered all-integral recollection law.
-/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight) :
    EIFiber.SatisfiesTruncEval.{u}
        (d := d) kernel ↔
      EIFiber.AILift.{u}
        (d := d) kernel :=
  ⟨kernel.allLiftSatisfies,
    kernel.satisfies_trunc_all⟩

end EIFiber
end
  FIBridge

namespace TSInput

/--
Aggregate selected-endpoint finite-index profiles, their ordered all-integral
law, singleton recollections, and graded Hall bases construct Claim 5
coordinate polynomials.
-/
theorem
    coordTruncEval
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
      (kernel.allLiftSatisfies hlistEval)
        hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Towers

/-!
# Positive-below Claim 5 data from selected operational endpoint profiles

In the class-two source range, an aggregate homogeneous profile for the
selected operational endpoint finite-index trace can consume the native
positive-below premise of Claim 5.  Zeroing irrelevant layers below the
requested input weight supplies the explicit sourced input without changing
the collected Hall product.

This file is intentionally not imported by the existing collection proof.
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
In the class-two source range, aggregate selected operational endpoint
profiles, their ordered recollection law, and local factor normalizations
supply the positive-below Claim 5 power package.
-/
theorem
    collected_profiles_below
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {layer : NRLayer n 1 1}
    {hleftWeight : 0 < 1}
    {hrightWeight : 0 < 1}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight)
    (hlistEval :
      EIFiber.SatisfiesTruncEval.{u}
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
              (n := n) (lowerWeight := lowerWeight) H factor)
    {e : HEFam H} :
    CollectedPolynomialData
      (n := n) H e inputWeight := by
  intro heBelow
  let e' : HEFam H :=
    HEFam.zeroBelow e inputWeight
  have he'Below :
      ∀ s : ℕ, s < inputWeight → e' s = 0 := by
    intro s hs
    simp [e', hs]
  have he'Product :
      collectedHallProduct (n := n) H e' =
        collectedHallProduct (n := n) H e := by
    simpa [e'] using collected_below_self e heBelow
  rcases
      (TSInput.coordTruncEval
          hn H hH kernel hlistEval
          (TSInput.classTwoSource
            hinputWeight hcutoff e' he'Below)
          (TSInput.least_two_source
            hinputWeight hcutoff e' he'Below)
          factorNormalization hinputWeight)
        (fun s _hs hs _hsn => he'Below s hs) with
    ⟨E, hEproduct, hEpolynomial⟩
  refine ⟨E, ?_, hEpolynomial⟩
  intro q
  exact (hEproduct q).trans (congrArg (fun x => x ^ q) he'Product)

end TCTex
end Towers

/-!
# Arbitrary-cutoff power input from selected endpoint profiles

The class-two sourced-input constructor is automatic once
`n ≤ 3 * inputWeight`.  For a fixed cutoff, only finitely many lower input
weights lie outside that range.  This file promotes aggregate profiles for the
selected operational endpoint finite-index trace to the full quantified Claim
5 power-polynomial package while keeping exactly those genuinely low-weight
sourced inputs explicit.

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
Selected endpoint finite-index trace profiles construct the complete Claim 5
power input once supported sourced inputs are supplied for the finitely many
lower weights outside the automatic class-two source range.
-/
theorem
    collected_fiber_profiles
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
  by_cases hclassTwoRange : n ≤ 3 * inputWeight
  · exact
      collected_profiles_below
        hn H hH hinputWeight hclassTwoRange kernel hlistEval
          (factorNormalization inputWeight hinputWeight)
  · exact
      TSInput.coordTruncEval
        hn H hH kernel hlistEval
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          (factorNormalization inputWeight hinputWeight) hinputWeight

/--
Selected endpoint finite-index trace profiles therefore yield the
weight-controlled polynomial degree bound for every Hall coordinate of a
power.
-/
theorem
    selected_fiber_profiles
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
        (collected_fiber_profiles
          hn H hH kernel hlistEval lowWeightSource lowWeightSupported
            factorNormalization)
        u hu hr hs hsn i

end TCTex
end Towers
