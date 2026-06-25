import Towers.Group.Zassenhaus.ResidualBasicChildren

/-!
# Global concrete Hall-power collection through retained-right recursion

The closed retained-right Hall-tree resolver constructs Claim 5 coordinate
polynomials for one supported sourced input.  This file threads that structural
resolver through the explicit class-two source and the low-weight source
boundary, obtaining the quantified powered-polynomial package.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CCThree

/--
In the automatic class-two source range, retained recipe coefficients and a
packet-free reachable insertion schedule route through the closed
retained-right Hall-tree resolver.
-/
theorem
    insertion_positive_below
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      RIDeriva
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d))
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)} :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight := by
  intro heBelow
  let e' :
      HEFam
        (concreteCommutatorsWeight.{u} d) :=
    HEFam.zeroBelow e inputWeight
  have he'Below :
      ∀ s : ℕ, s < inputWeight → e' s = 0 := by
    intro s hs
    simp [e', hs]
  have he'Product :
      collectedHallProduct
          (n := n) (concreteCommutatorsWeight.{u} d) e' =
        collectedHallProduct
          (n := n) (concreteCommutatorsWeight.{u} d) e := by
    simpa [e'] using collected_below_self e heBelow
  rcases
      (TSInput.reachableInsertionSchedule
          hn
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
Retained recipe coefficients, supported low-weight sources, and packet-free
reachable insertion schedules construct the global concrete Hall-power
coordinate polynomials through the closed retained-right Hall-tree resolver.
-/
theorem
    forall_reachable_schedules
    {d n : ℕ}
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
    (schedules :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          RIDeriva
            (n := n) (inputWeight := inputWeight)
              (concreteCommutatorsWeight.{u} d)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hclassTwoRange : n ≤ 3 * inputWeight
  · exact
      insertion_positive_below
        hn hinputWeight hclassTwoRange hrecipes
          (schedules inputWeight hinputWeight)
  · exact
      TSInput.reachableInsertionSchedule
        hn
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          hinputWeight hrecipes (schedules inputWeight hinputWeight)

end TCTex
end Towers
