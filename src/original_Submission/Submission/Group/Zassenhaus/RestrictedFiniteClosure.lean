import Submission.Group.Zassenhaus.InverseUniversalClosure
import Submission.Group.Zassenhaus.PolynomialOrbitVocabulary
import Submission.Group.Zassenhaus.OneSourcedInput
import Submission.Group.Zassenhaus.ClassTwo
import Submission.Group.Zassenhaus.TwoSourcedInput
import Submission.Group.Zassenhaus.SignedBlockStabilization

/-!
# Claim 5 from the canonical summed signed-profile assignment

The canonical finite-correction-closure collector attaches the sum of all
same-word recipe profiles to each retained erased Hall word.  Its flattened
recipe-product theorem is exactly the fixed-truncation summed-profile law
consumed by the restricted-sharp Claim 5 route.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg
open
  CPSplit
open
  CTAssign
open
  ACAlign

namespace TSInput

/--
The canonical flattened recipe-product theorem, singleton recollections, and
graded Hall bases construct the Claim 5 coordinate polynomials.
-/
theorem
    coordPolyAssignment
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (hlistEval :
      SatisfiesRecipeTruncated.{u} d n)
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
  input.coordinateProfileAssignment
    hn H hH (kernel := kernel)
      (canonicalProfileAssignment n 1 1)
      (satisfies_profile_assignment
        hlistEval)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from retained-profile class-three finite-closure packets

Through cutoff four, the provenance-preserving retained selector constructs an
all-integral finite-correction-closure packet.  Feeding this packet into the
restricted-sharp singleton collector produces the Claim 5 coordinate
polynomials from local factor normalizations.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg
open
  FTCollec

namespace TSInput

/--
Through cutoff four, the retained-profile finite-correction-closure packet,
singleton recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials.
-/
theorem
    coordinateClosureProfile
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
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
  input.coordinateAllPacket
    hn H hH (kernel := kernel)
      (packet_n_four (d := d) hn4)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Positive-below Claim 5 data from retained class-three profiles

In the class-two source range, zeroing irrelevant lower layers constructs a
supported source without changing the collected Hall product.  The retained
class-three profile packet can therefore consume the native positive-below
premise of Claim 5.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg

/--
In the class-two source range through cutoff four, the retained-profile packet
and local factor normalizations supply the positive-below Claim 5 package.
-/
theorem
    collected_data_profile
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {kernel : OCShape}
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
      ((TSInput.classTwoSource
        hinputWeight hcutoff e' he'Below)
        |>.coordinateClosureProfile
          hn hn4 H hH (kernel := kernel)
          (TSInput.least_two_source
            hinputWeight hcutoff e' he'Below)
          factorNormalization hinputWeight)
        (fun s _hs hs _hsn => he'Below s hs) with
    ⟨E, hEproduct, hEpolynomial⟩
  refine ⟨E, ?_, hEpolynomial⟩
  intro q
  exact (hEproduct q).trans (congrArg (fun x => x ^ q) he'Product)

end TCTex
end Submission

/-!
# Claim 5 power input from retained class-three profiles

Through cutoff four, the retained-profile packet handles the explicit
weight-one class-three source and every higher positive input weight in the
class-two tail range.  This yields the quantified power-polynomial input
consumed by Claim 5 and its Hall-coordinate degree consequence.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg

/--
Through cutoff four, local factor normalizations promote the retained-profile
packet to the complete Claim 5 power input.
-/
theorem
    collected_forall_profile
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
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
      (TSInput.classThreeSource hn4 e)
        |>.coordinateClosureProfile
          hn hn4 H hH (kernel := kernel)
          (TSInput.word_least_source
            hn4 e)
          (factorNormalization 1 (by omega)) (by omega)
  · exact
      collected_data_profile
        hn hn4 H hH hinputWeight (by omega) (kernel := kernel)
          (factorNormalization inputWeight hinputWeight)

/--
Through cutoff four, the retained-profile route yields the polynomial degree
bound for every Hall coordinate of a power.
-/
theorem
    hall_coordinate_profile
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
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
        (collected_forall_profile
          hn hn4 H hH (kernel := kernel) factorNormalization)
        u hu hr hs hsn i

end TCTex
end Submission

/-!
# Claim 5 from the explicit recipe-coefficient transversal

The explicit recipe-coefficient transversal selects one recursive recipe
witness for each erased Hall word in the deduplicated finite correction
closure.  Once its ordered all-integral product law is proved, the existing
finite-closure Hall-power collector constructs the coordinate polynomials
required by Claim 5.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open EPSplit
open CSAggreg

namespace TSInput

/--
The explicit transversal product law, singleton recollections, and graded
Hall bases construct the Claim 5 coordinate polynomials.
-/
theorem
    coordinateExplicitTransversal
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (hlistEval :
      SatisfiesExplicitRecipe.{u} d n)
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
  input.coordinateAllPacket
    hn H hH (kernel := kernel)
      (explicitRecipePacket
        hlistEval)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from explicit recipe-coefficient transversals at low cutoff

Through cutoff three, the explicit recipe-coefficient transversal product law
is proved directly.  Feeding that law into the finite-closure Hall-power route
constructs the coordinate polynomials required by Claim 5.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open ECLow
open CSAggreg

namespace TSInput

/--
Through cutoff three, the explicit recipe-coefficient transversal constructs
the Claim 5 coordinate polynomials.
-/
theorem
    explicitTransversalLow
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn3 : n ≤ 3)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
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
  input.coordinateExplicitTransversal
    hn H hH (kernel := kernel)
      (satisfies_explicit_three hn3)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Positive-below Claim 5 data from the explicit recipe transversal

In the class-two source range, the explicit powered source is available for
every Hall exponent family whose lower layers vanish.  Zeroing irrelevant
layers below the requested input weight lets the explicit recipe-coefficient
transversal consume the native positive-below premise of Claim 5.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open EPSplit
open CSAggreg

/--
In the class-two source range, the explicit transversal product law and local
factor normalizations supply the positive-below Claim 5 power package.
-/
theorem
    collected_explicit_transversal
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
    {kernel : OCShape}
    (hlistEval :
      SatisfiesExplicitRecipe.{u} d n)
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
      ((TSInput.classTwoSource
        hinputWeight hcutoff e' he'Below)
        |>.coordinateExplicitTransversal
          hn H hH (kernel := kernel) hlistEval
          (TSInput.least_two_source
            hinputWeight hcutoff e' he'Below)
          factorNormalization hinputWeight)
        (fun s _hs hs _hsn => he'Below s hs) with
    ⟨E, hEproduct, hEpolynomial⟩
  refine ⟨E, ?_, hEpolynomial⟩
  intro q
  exact (hEproduct q).trans (congrArg (fun x => x ^ q) he'Product)

end TCTex
end Submission

/-!
# Positive-below Claim 5 data from explicit transversals at low cutoff

Through cutoff three, the explicit recipe-coefficient transversal product law
is already proved.  The positive-below adapter therefore leaves only the local
powered-factor normalization interface required by the Hall-power collector.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open ECLow
open CSAggreg

/--
Through cutoff three, local factor normalizations and the proved explicit
transversal law supply the positive-below Claim 5 power package.
-/
theorem
    explicit_transversal_n
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn3 : n ≤ 3)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    {kernel : OCShape}
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
      (n := n) H e inputWeight :=
  collected_explicit_transversal
    hn H hH hinputWeight (by omega) (kernel := kernel)
      (satisfies_explicit_three hn3)
      factorNormalization

end TCTex
end Submission

/-!
# Low-cutoff Claim 5 power input from the explicit transversal

Through cutoff three, the explicit recipe-coefficient transversal law is
proved.  A family of local powered-factor normalizations therefore supplies
the complete universal power-polynomial input consumed by Claim 5.

This file records both that quantified power input and its direct application
to Hall coordinates of powers.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg

/--
Through cutoff three, a family of local factor normalizations promotes the
proved explicit transversal law to the complete Claim 5 power input.
-/
theorem
    forall_explicit_transversal
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn3 : n ≤ 3)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
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
  exact
    explicit_transversal_n
      hn hn3 H hH hinputWeight (kernel := kernel)
        (factorNormalization inputWeight hinputWeight)

/--
Through cutoff three, the explicit transversal route yields the polynomial
degree bound for every Hall coordinate of a power.
-/
theorem
    explicit_transversal_three
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (hn3 : n ≤ 3)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
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
        (forall_explicit_transversal
          hn hn3 H hH (kernel := kernel) factorNormalization)
        u hu hr hs hsn i

end TCTex
end Submission

/-!
# Arbitrary-cutoff Hall-power input from the retained recipe transversal

The retained recipe transversal is a fixed occurrence-preserving finite trace
at every cutoff.  Once its ordered product law is known, the operational
endpoint adapter constructs Claim 5 from any supported sourced input.

In the class-two source range, zeroing irrelevant lower exponent layers gives
that sourced input automa.  Consequently, only finitely many genuinely
low input weights remain explicit at a fixed cutoff.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CSAggreg
open
  CCThree
open
  ERTransv

/--
In the automatic class-two source range, the ordered retained-recipe product
law and local factor normalizations supply the positive-below Claim 5 power
package.
-/
theorem
    collected_positive_below
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
    {kernel : OCShape}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (factorNormalization :
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
      (ERTransv.TSInput.coordCollectedOcc
          hn H hH (kernel := kernel) hrecipes
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

/--
The retained-transversal ordered product law constructs the full quantified
Claim 5 power input once supported sourced inputs are supplied for the
finitely many input weights below the automatic class-two range.
-/
theorem
    collected_forall_trace
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
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
      collected_positive_below
        hn H hH hinputWeight hclassTwoRange (kernel := kernel) hrecipes
          (factorNormalization inputWeight hinputWeight)
  · exact
      ERTransv.TSInput.coordCollectedOcc
        hn H hH (kernel := kernel) hrecipes
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          (factorNormalization inputWeight hinputWeight) hinputWeight

end TCTex
end Submission
