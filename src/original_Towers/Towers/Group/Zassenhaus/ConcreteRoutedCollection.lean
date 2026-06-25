import Towers.Group.Zassenhaus.Jacobi
import Towers.Group.Zassenhaus.RootFrontierCollection

/-!
# Routed symbolic recollection at every concrete Jacobi frontier

This module combines the expanded-Jacobi continuation route with the
expanded-root frontier route.  Recursive callers supply:

* ordinary recollections of the two Jacobi descendants;
* forward recollections of the next-stratum Jacobi value packet;
* inverse recollections of the canonical two-basic-child swap packet; and
* forward recollections of the generic expanded-root swap packet.

All conjugation routing, source inversion, and orientation dispatch are
compiled internally.  The resulting builder feeds the existing Claim 5
coordinate-polynomial collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open HEWord

universe u

/-- Recursive data after all concrete Jacobi-frontier routing is compiled. -/
structure
    RFBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  expandedJacobi :
    EJBuild.{u}
      (inputWeight := inputWeight) hn hH
  hinputWeight : 1 ≤ inputWeight
  basicChildrenInverse :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right : HallTree (FreeGenerator.{u} d))
          (hleftBasic : left.IsBasic)
          (hrightBasic : right.IsBasic)
          (htree : tree factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TIRecoll
                (n := n) factor left right hleftBasic hrightBasic htree
  rootSwapResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecolla
                (n := n) factor left right hword

namespace
  RFBuild

/-- Compile routed expanded continuations into two-basic-child orientation. -/
noncomputable def childrenOrientationBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      RFBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    JOBuild.{u}
      (inputWeight := inputWeight) hn hH where
  expandedJacobi :=
    builder.expandedJacobi
      |>.expandedContinuationBuilder
        builder.hinputWeight
  swapValueInverse :=
    builder.basicChildrenInverse

/-- Compile all routed cases into the expanded-root frontier builder. -/
noncomputable def expandedFrontierBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      RFBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    TEBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  basicChildren :=
    builder.childrenOrientationBuilder
  hinputWeight := builder.hinputWeight
  normalizerAbove :=
    fun _lowerWeight strongerWeight _ =>
      builder.expandedJacobi.normalizerFamily.normalizer strongerWeight
  rootSwapResidual := builder.rootSwapResidual

/-- Compile all routed cases into the arbitrary Jacobi-frontier collector. -/
noncomputable def jacobiCollectionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      RFBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    TFBuildc.{u}
      (inputWeight := inputWeight) hn hH :=
  builder.expandedFrontierBuilder
    |>.jacobiCollectionBuilder

end
  RFBuild

namespace TSInput

/--
For canonical Hall families, routed recursive Jacobi data constructs the
Claim 5 coordinate polynomials.
-/
theorem
    routedJacobiBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      RFBuild.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.jacobiFrontierBuilder
    hn hsourceSupported builder.jacobiCollectionBuilder
      builder.hinputWeight

end TSInput
end TCTex
end Towers
