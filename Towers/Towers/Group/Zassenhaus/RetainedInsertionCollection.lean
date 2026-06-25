import Towers.Group.Zassenhaus.InverseUniversalClosure
import Towers.Group.Zassenhaus.ClassTwo
import Towers.Group.Zassenhaus.TwoSourcedInput
import Towers.Group.Zassenhaus.FormulaChooseSubstitution
import Towers.Group.Zassenhaus.ReachableUniversalReduction

/-!
# Reachable Hall-power collection from retained recipe traces

The retained recipe-coefficient product law supplies the powered correction
packet at every support stratum.  This file compiles that law to the reachable
Hall-power collector, leaving only packet-free insertion schedules and the
genuinely low-weight sourced inputs explicit.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CCThree
open
  CPSplita

namespace
  TDBuild

/--
Compile the retained recipe-coefficient product law to the powered
correction-packet factory at one support stratum.
-/
noncomputable def retainedRecipeFactory
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    TSFtrya
      (n := n) (inputWeight := inputWeight) H lowerWeight :=
  (retainedAllPacket hrecipes
    |>.powerSupportedFactory
      hinputWeight lowerWeight)
    |>.correctionPacketFactory

/--
The retained recipe-coefficient product law fills the custom powered
correction factories in a reachable universal collector.  The only remaining
input is the packet-free reachable insertion schedule.
-/
noncomputable def recipe_coeff_trace
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      RIDeriva
        (n := n) (inputWeight := inputWeight) H) :
    TDBuild
      (n := n) (inputWeight := inputWeight) H where
  correctionFactory lowerWeight _hbelowClassTwoRange :=
    retainedRecipeFactory
      (lowerWeight := lowerWeight) hinputWeight hrecipes
  insert lowerWeight hnonterminal normalizer _factory :=
    schedule.insert lowerWeight hnonterminal normalizer

end
  TDBuild

namespace TSInput

open
  TDBuild

/--
A retained recipe-product law and packet-free reachable insertion schedule
construct the Claim 5 coordinate polynomials for any supported sourced input.
-/
theorem
    coordReachableInsertion
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      RIDeriva
        (n := n) (inputWeight := inputWeight) H) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.reachableDerivationBuilder
    hn H hH hsourceSupported
      (recipe_coeff_trace hinputWeight hrecipes schedule)
      hinputWeight

end TSInput

/--
In the automatic class-two source range, the retained recipe-product law and
a packet-free reachable insertion schedule supply the positive-below Claim 5
power package.
-/
theorem
    collected_insertion_below
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      RIDeriva
        (n := n) (inputWeight := inputWeight) H)
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
      (TSInput.coordReachableInsertion
          hn H hH
          (TSInput.classTwoSource
            hinputWeight hcutoff e' he'Below)
          (TSInput.least_two_source
            hinputWeight hcutoff e' he'Below)
          hinputWeight hrecipes schedule)
        (fun s _hs hs _hsn => he'Below s hs) with
    ⟨E, hEproduct, hEpolynomial⟩
  refine ⟨E, ?_, hEpolynomial⟩
  intro q
  exact (hEproduct q).trans (congrArg (fun x => x ^ q) he'Product)

/--
The retained recipe-product law constructs the full quantified Claim 5 power
input once supported sourced inputs are supplied for the finitely many input
weights below the automatic class-two range and packet-free reachable
insertion schedules are supplied at every positive input weight.
-/
theorem
    reachable_insertion_schedules
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
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
    (schedules :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          RIDeriva
            (n := n) (inputWeight := inputWeight) H) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hclassTwoRange : n ≤ 3 * inputWeight
  · exact
      collected_insertion_below
        hn H hH hinputWeight hclassTwoRange hrecipes
          (schedules inputWeight hinputWeight)
  · exact
      TSInput.coordReachableInsertion
        hn H hH
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          hinputWeight hrecipes (schedules inputWeight hinputWeight)

end TCTex
end Towers
