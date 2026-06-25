# Milne ANT correspondence

The Lean implementations originally followed the chapter layout of J. S. Milne's
*Algebraic Number Theory* notes (`ANT.tex`). They now live in topic-oriented modules under
`Towers/AlgebraicNumberTheory/`.

Declaration namespaces remain `Towers.AlgebraicNumberTheory.Milne` for API compatibility;
only the module organization changed. The few `.lean` files left below this directory are
forwarding imports required by code outside `AlgebraicNumberTheory/`, which was outside the
permitted edit scope for this migration. They contain no implementations.

`Towers.AlgebraicNumberTheory.All` is the neutral umbrella for the moved development, while
`Towers.AlgebraicNumberTheory.Milne` remains a compatibility umbrella.

## Solutions appendix

The solutions appendix repeats the exercises from the body of ANT rather than
introducing a second set of declarations.  In source order, its mathematical
content is located as follows.

| ANT solution | Current topic module |
|---|---|
| 0-1 | `Quadratic/IntegralElements.lean` and `Quadratic/QuadraticIntegerRings.lean` |
| 0-2 | `Quadratic/Examples/SqrtNegFiveIdeals.lean` |
| 1-1 | `CommutativeAlgebra/Localization/SaturatedSubmonoids.lean` |
| 2-1 | `Quadratic/Examples/SqrtFiveFactorization.lean` |
| 2-2 | `IntegralClosure/MonicPolynomialFactorization.lean` |
| 2-3 | `Discriminant/InseparableExtension.lean` |
| 2-4 | `Quadratic/Examples/SqrtNegThreeIdeal.lean` |
| 2-5 | `IntegralClosure/UnitAdjoinIntersection.lean` |
| 2-6 | `Quadratic/Examples/BiquadraticNonmonogenic.lean` |
| 2-7 | `IntegralClosure/IntegralClosureFacts.lean` |
| 2-8 | `CommutativeAlgebra/Localization/ResidueField.lean` |
| 3-1 | `DedekindDomain/Examples/BivariatePolynomialNotDedekind.lean` |
| 3-2 | `Quadratic/Examples/QuadraticAndBiquadraticIntegerRings.lean` |
| 3-3 | `Quadratic/Examples/PrimeRepresentations.lean` |
| 3-4 | `DedekindDomain/Examples/CuspidalCubicNotDedekind.lean` |
| 4-1 | `CommutativeAlgebra/Examples/PrimeIdealZeroContraction.lean` |
| 4-2 | `Ramification/TowerFormulas.lean` |
| 4-3 | `Ramification/Examples/CubicSplittingPatterns.lean` |
| 4-4 | Computational class-group examples; intentionally omitted |
| 4-5 | `ClassGroup/Principalization.lean` |
| 4-6 | `ClassGroup/Examples/CubicClassNumberOne.lean` |
| 4-7 | `Quadratic/Examples/SqrtNegFiveUnramifiedBiquadratic.lean`; the last Hilbert-class-field identification is delegated to class field theory, as in ANT |
| 5-1 | `Units/BoundedSingleEmbeddingCounterexample.lean` |
| 5-2 | `Quadratic/ContinuedFractions/Sqrt67Pell.lean` |
| 5-3 | `Quadratic/Examples/GaussianNonintegralNormOne.lean` |
| 6-1 | `NumberFields/Examples/CubicX3Sub3XAdd1.lean` and `NumberFields/Examples/CubicX3Sub3XAdd1IntegralClosure.lean` |
| 6-2 | `Cyclotomic/MaximalRealRingOfIntegers.lean` |
| 6-3 | `Cyclotomic/PrimePowerAutomorphismGroups.lean` |
| 7-1 | `LocalFields/FinitePlaceApproximation.lean` |
| 7-2 | `LocalFields/UltrametricBallsAndSeries.lean` |
| 7-3 | `LocalFields/SevenAdicSquares.lean` |
| 7-4 | `LocalFields/UniversalPadicQuadraticRoot.lean` and `LocalFields/SevenAdicNewtonApproximation.lean` |
| 7-5 | `LocalFields/TwoAdicSquareClasses.lean` |
| 7-6 | `LocalFields/MultiquadraticDegree.lean` and `LocalFields/MultiquadraticDegreeGamma.lean` |
| 7-7 | `LocalFields/PadicAlgebraicClosureRootsOfUnity.lean` |
| 7-8 | `LocalFields/LocallyReducibleIrreduciblePolynomial.lean` and `LocalFields/NewtonPolygonIrreducibilityCounterexample.lean` |
| 8-1 | `Completions/TwoAdicCubicFactorization.lean` |
| 8-2 | `Completions/HigherRamificationCoefficient.lean`; see the corrected statement in the Chapter 8 coverage notes below |
| 8-3 | PARI computation; intentionally omitted |
| 8-4 | `GlobalFields/RationalFunctionProductFormula.lean` |

## Two-hour examination

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Appendix.ExaminationFive` | `Towers.AlgebraicNumberTheory.LocalFields.ThreeAdicCyclicCubic` |
| `Towers.AlgebraicNumberTheory.Milne.Appendix.ExaminationFour` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegFiveIrreducibleCube` |
| `Towers.AlgebraicNumberTheory.Milne.Appendix.ExaminationOneB` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.Sqrt29NonmaximalOrder` |
| `Towers.AlgebraicNumberTheory.Milne.Appendix.ExaminationSix` | `Towers.AlgebraicNumberTheory.Galois.TrivialUnramifiedExtensionInertia` |
| `Towers.AlgebraicNumberTheory.Milne.Appendix.ExaminationThree` | `Towers.AlgebraicNumberTheory.Cyclotomic.EighthIntermediateFields` |
| `Towers.AlgebraicNumberTheory.Milne.Appendix.ExaminationTwo` | `Towers.AlgebraicNumberTheory.NumberFields.RadicalExtensions.XPowerMinusTwo` |
| `Towers.AlgebraicNumberTheory.Milne.Appendix.ExaminationTwoPlaces` | `Towers.AlgebraicNumberTheory.NumberFields.RadicalExtensions.XPowerMinusTwoPlaces` |
| `Towers.AlgebraicNumberTheory.Milne.Appendix.TwoHourExamination` | `Towers.AlgebraicNumberTheory.NumberFields.Examples.IntegralComplexEighthRoot` |

## Chapter1

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.ChineseRemainder` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.ChineseRemainder` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.FiniteProducts` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.FiniteProducts` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.InseparableTensor` | `Towers.AlgebraicNumberTheory.FieldTheory.TensorProduct.InseparableTensor` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.IntegerLocalizations` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Localization.IntegerLocalizations` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.LocalizationIdeals` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Localization.LocalizationIdeals` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.Nakayama` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Nakayama` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.Noetherian` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Noetherian` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.PrimeIdealExamples` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Examples.PrimeIdealsZMod42` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.PrimeIdealsAtTwo` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Localization.PrimeIdealsAtTwo` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.PrimeIdealsAwayFortyTwo` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Localization.PrimeIdealsAwayFortyTwo` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.PrimeIdealsAwayTwo` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Localization.PrimeIdealsAwayTwo` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.SaturatedSubmonoids` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Localization.SaturatedSubmonoids` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.SeparableTensorProduct` | `Towers.AlgebraicNumberTheory.FieldTheory.TensorProduct.SeparableTensorProduct` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.TensorMatrices` | `Towers.AlgebraicNumberTheory.LinearAlgebra.TensorProduct.TensorMatrices` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter1.TensorNoninjective` | `Towers.AlgebraicNumberTheory.LinearAlgebra.TensorProduct.TensorNoninjective` |

## Chapter2

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.CubicIntegralBasisExamples` | `Towers.AlgebraicNumberTheory.NumberFields.Examples.CubicIntegralBasisExamples` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.DedekindCubicExample` | `Towers.AlgebraicNumberTheory.NumberFields.Examples.DedekindCubicExample` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.DiscriminantBasisCriterion` | `Towers.AlgebraicNumberTheory.Discriminant.DiscriminantBasisCriterion` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.DiscriminantChangeOfGenerators` | `Towers.AlgebraicNumberTheory.Discriminant.DiscriminantChangeOfGenerators` |
| Exercise 2-1 | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtFiveFactorization` |
| Exercise 2-2 | `Towers.AlgebraicNumberTheory.IntegralClosure.MonicPolynomialFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.Exercise2_3` | `Towers.AlgebraicNumberTheory.Discriminant.InseparableExtension` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.Exercise2_4` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegThreeIdeal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.Exercise2_5` | `Towers.AlgebraicNumberTheory.IntegralClosure.UnitAdjoinIntersection` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.Exercise2_6` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.BiquadraticNonmonogenic` |
| Exercise 2-7 | `Towers.AlgebraicNumberTheory.IntegralClosure.IntegralClosureFacts` |
| Exercise 2-8 | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Localization.ResidueField` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.FiniteIndexDiscriminant` | `Towers.AlgebraicNumberTheory.Discriminant.FiniteIndexDiscriminant` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.IntegralClosureFacts` | `Towers.AlgebraicNumberTheory.IntegralClosure.IntegralClosureFacts` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.IntegralClosureLattice` | `Towers.AlgebraicNumberTheory.IntegralClosure.IntegralClosureLattice` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.IntegralCoordinates` | `Towers.AlgebraicNumberTheory.IntegralClosure.IntegralCoordinates` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.IntegralCriterion` | `Towers.AlgebraicNumberTheory.IntegralClosure.IntegralCriterion` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.IntegralElements` | `Towers.AlgebraicNumberTheory.IntegralClosure.IntegralElements` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.IntegralTraceNorm` | `Towers.AlgebraicNumberTheory.TraceNorm.IntegralTraceNorm` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.MinpolyIntegral` | `Towers.AlgebraicNumberTheory.IntegralClosure.MinpolyIntegral` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.NumberFieldDiscriminant` | `Towers.AlgebraicNumberTheory.Discriminant.NumberFieldDiscriminant` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.PolynomialDiscriminantExamples` | `Towers.AlgebraicNumberTheory.Discriminant.PolynomialDiscriminantExamples` |
| Example 2.39 (quintic integral basis) | `Towers.AlgebraicNumberTheory.NumberFields.Examples.QuinticIntegralBasis` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.PolynomialInIntegralElements` | `Towers.AlgebraicNumberTheory.IntegralClosure.PolynomialInIntegralElements` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.PowerBasisDiscriminant` | `Towers.AlgebraicNumberTheory.Discriminant.PowerBasisDiscriminant` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.QuadraticIntegerRings` | `Towers.AlgebraicNumberTheory.Quadratic.QuadraticIntegerRings` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.SeparableDiscriminant` | `Towers.AlgebraicNumberTheory.Discriminant.SeparableDiscriminant` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.SqrtFiveFactorization` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtFiveFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.SqrtFiveNotIntegrallyClosed` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtFiveNotIntegrallyClosed` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.SqrtNegFiveNonfreeIdeal` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegFiveNonfreeIdeal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.SqrtNegThree` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegThree` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.SqrtNegThreeIdeal` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegThreeIdeal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.Stickelberger` | `Towers.AlgebraicNumberTheory.Discriminant.Stickelberger` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.SymmetricFunctionTheorem` | `Towers.AlgebraicNumberTheory.Symmetric.IntegralSymmetricFunctions` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.SymmetricPolynomialIntegralClosure` | `Towers.AlgebraicNumberTheory.IntegralClosure.SymmetricPolynomialIntegralClosure` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.TraceDualLattice` | `Towers.AlgebraicNumberTheory.Discriminant.TraceDualLattice` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.TraceNormFormulas` | `Towers.AlgebraicNumberTheory.TraceNorm.TraceNormFormulas` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter2.UnitAdjoinIntersection` | `Towers.AlgebraicNumberTheory.IntegralClosure.UnitAdjoinIntersection` |

## Chapter3

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.Approximation` | `Towers.AlgebraicNumberTheory.Ideals.Approximation` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.CyclicQuotientCoordinates` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.CyclicQuotientCoordinates` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.CyclicQuotientLift` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.CyclicQuotientLift` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DVRFractionalIdeals` | `Towers.AlgebraicNumberTheory.Ideals.DVRFractionalIdeals` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DVRQuotientAnnihilator` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.DVRQuotientAnnihilator` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DedekindEquivalentConditions` | `Towers.AlgebraicNumberTheory.DedekindDomain.DedekindEquivalentConditions` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DedekindLocalizations` | `Towers.AlgebraicNumberTheory.DedekindDomain.DedekindLocalizations` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DedekindModules` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.DedekindModules` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DeterminantLattice` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.DeterminantLattice` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DeterminantLine` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.DeterminantLine` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DiscreteValuationRings` | `Towers.AlgebraicNumberTheory.Valuations.DiscreteValuationRings` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DiscreteValuations` | `Towers.AlgebraicNumberTheory.Valuations.DiscreteValuations` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DiscriminantModIdeal` | `Towers.AlgebraicNumberTheory.Ramification.DiscriminantModIdeal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.DiscriminantProduct` | `Towers.AlgebraicNumberTheory.Ramification.DiscriminantProduct` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.EisensteinRamification` | `Towers.AlgebraicNumberTheory.Ramification.EisensteinRamification` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.EisensteinTotalRamification` | `Towers.AlgebraicNumberTheory.Ramification.EisensteinTotalRamification` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.EllipticCurveClassGroup` | `Towers.AlgebraicNumberTheory.ClassGroup.EllipticCurveClassGroup` |
| External class-group realization results before Example 3.22 | `Towers.AlgebraicNumberTheory.ClassGroup.Universality` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.Exercise3_1` | `Towers.AlgebraicNumberTheory.DedekindDomain.Examples.BivariatePolynomialNotDedekind` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.Exercise3_2` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.QuadraticAndBiquadraticIntegerRings` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.Exercise3_3` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.PrimeRepresentations` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.Exercise3_4` | `Towers.AlgebraicNumberTheory.DedekindDomain.Examples.CuspidalCubicNotDedekind` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.ExteriorAnnihilatorInvariant` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.ExteriorAnnihilatorInvariant` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.FactorizationInExtensions` | `Towers.AlgebraicNumberTheory.Ramification.FactorizationInExtensions` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.FiniteClassGroupLocalization` | `Towers.AlgebraicNumberTheory.ClassGroup.FiniteClassGroupLocalization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.FractionalIdealFreeAbelian` | `Towers.AlgebraicNumberTheory.Ideals.FractionalIdealFreeAbelian` |
| Fractional-ideal preliminaries before Example 3.19 | `Towers.AlgebraicNumberTheory.Ideals.FractionalIdealBasics` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.FractionalIdealLocalization` | `Towers.AlgebraicNumberTheory.Ideals.FractionalIdealLocalization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.GaussianPrimeSplitting` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.GaussianPrimeSplitting` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.IdealFactorization` | `Towers.AlgebraicNumberTheory.Ideals.IdealFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.IdealGenerationCorollaries` | `Towers.AlgebraicNumberTheory.Ideals.IdealGenerationCorollaries` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.IntegralClosureDedekind` | `Towers.AlgebraicNumberTheory.DedekindDomain.IntegralClosureDedekind` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorKernel` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorKernel` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorLastStep` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorLastStep` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorPresentationUniqueness` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorPresentationUniqueness` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorPseudobasis` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorPseudobasis` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorPseudobasisExistence` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorPseudobasisExistence` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorPseudobasisInduction` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorPseudobasisInduction` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorPseudobasisRecursive` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorPseudobasisRecursive` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorPseudobasisStep` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorPseudobasisStep` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorRankRecursionHelpers` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorRankRecursionHelpers` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorTheorem` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorTheorem` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorTheoremFull` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorTheoremFull` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorsAssembly` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorsAssembly` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorsCRT` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorsCRT` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorsDVR` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorsDVR` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorsGlobalQuotient` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorsGlobalQuotient` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorsLocal` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorsLocal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorsPadding` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorsPadding` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorsQuotient` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorsQuotient` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorsRankPadding` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorsRankPadding` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.InvariantFactorsUniqueness` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.InvariantFactorsUniqueness` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.KummerDedekindFactorization` | `Towers.AlgebraicNumberTheory.Ramification.KummerDedekindFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.LocalizationQuotientPowers` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.LocalizationQuotientPowers` |
| Note after Proposition 3.6 | `Towers.AlgebraicNumberTheory.DedekindDomain.NonnoetherianLocalDVR` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.PrimePowerTorsionDecomposition` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.PrimePowerTorsionDecomposition` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.PrincipalIdealCriteria` | `Towers.AlgebraicNumberTheory.Ideals.PrincipalIdealCriteria` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.PseudobasisGlobal` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.PseudobasisGlobal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.QuadraticPrimeFactorization` | `Towers.AlgebraicNumberTheory.Quadratic.PrimeFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.QuotientPowerLinearEquiv` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.QuotientPowerLinearEquiv` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.RamificationDiscriminant` | `Towers.AlgebraicNumberTheory.Ramification.RamificationDiscriminant` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.RankSizedInvariantFactorsLocal` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.RankSizedInvariantFactorsLocal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.ReducedDiscriminant` | `Towers.AlgebraicNumberTheory.Ramification.ReducedDiscriminant` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.StableCancellation` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.StableCancellation` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.TorsionElementaryDivisors` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.TorsionElementaryDivisors` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.TorsionInvariantFactors` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.TorsionInvariantFactors` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter3.TorsionLocalization` | `Towers.AlgebraicNumberTheory.DedekindDomain.Modules.TorsionLocalization` |

## Chapter4

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.ArithmeticGeometricMean` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.ArithmeticGeometricMean` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.BinaryQuadraticForms` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.BinaryQuadraticForms` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Blichfeldt` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.Blichfeldt` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.ClassNumberFinite` | `Towers.AlgebraicNumberTheory.ClassGroup.ClassNumberFinite` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.ConvexBodyIntegral` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.ConvexBodyIntegral` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.ConvexBodyVolume` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.ConvexBodyVolume` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.CubicClassNumberExample` | `Towers.AlgebraicNumberTheory.ClassGroup.Examples.CubicClassNumberExample` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Exercise4_1` | `Towers.AlgebraicNumberTheory.CommutativeAlgebra.Examples.PrimeIdealZeroContraction` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Exercise4_2` | `Towers.AlgebraicNumberTheory.Ramification.TowerFormulas` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Exercise4_3` | `Towers.AlgebraicNumberTheory.Ramification.Examples.CubicSplittingPatterns` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Exercise4_4` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.ClassNumbersNeg23Neg47` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Exercise4_5` | `Towers.AlgebraicNumberTheory.ClassGroup.Principalization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Exercise4_6` | `Towers.AlgebraicNumberTheory.ClassGroup.Examples.CubicClassNumberOne` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Exercise4_7` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegFiveUnramifiedBiquadratic` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.FormClassToNarrowClass` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.FormClassToNarrowClass` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.FormIdealClass` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.FormIdealClass` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.FormIdealEquivalence` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.FormIdealEquivalence` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.FormIdealNarrowEquivalence` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.FormIdealNarrowEquivalence` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.FormToIdeal` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.FormToIdeal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.FourSquaresApplication` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.FourSquaresApplication` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.IdealFormInverse` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.IdealFormInverse` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.IdealLatticeMinkowski` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.IdealLatticeMinkowski` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.IdealNormCompatibility` | `Towers.AlgebraicNumberTheory.Ideals.IdealNormCompatibility` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.IdealNormForms` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.IdealNormForms` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.ImaginaryQuadraticNarrowClass` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.ImaginaryQuadraticNarrowClass` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.LatticeCovolume` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.LatticeCovolume` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.LatticeCriteria` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.LatticeCriteria` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.MinkowskiClassBound` | `Towers.AlgebraicNumberTheory.ClassGroup.MinkowskiClassBound` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.MinkowskiConvexBody` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.MinkowskiConvexBody` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.NarrowClassGroup` | `Towers.AlgebraicNumberTheory.ClassGroup.NarrowClassGroup` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.NarrowIdealNormClass` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.NarrowIdealNormClass` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.NarrowIntegralRepresentative` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.NarrowIntegralRepresentative` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.NoUnramifiedExtensionQ` | `Towers.AlgebraicNumberTheory.ClassGroup.NoUnramifiedExtensionQ` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.NumericalIdealNorm` | `Towers.AlgebraicNumberTheory.Ideals.NumericalIdealNorm` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.OrientedIdealBases` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.OrientedIdealBases` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.OrientedIdealBasisExistence` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.OrientedIdealBasisExistence` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.PositiveLeadingCoefficient` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.PositiveLeadingCoefficient` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.PositiveLeadingIdealBasis` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.PositiveLeadingIdealBasis` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.QuadraticClassGroupExamples` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.ClassGroups` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.QuadraticFieldFormSetup` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.QuadraticFieldFormSetup` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.QuadraticFormParameters` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.QuadraticFormParameters` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.QuadraticIdealFormMap` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.QuadraticIdealFormMap` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.QuadraticTotalPositivity` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.QuadraticTotalPositivity` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.QuinticClassNumberExample` | `Towers.AlgebraicNumberTheory.ClassGroup.Examples.QuinticClassNumberExample` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.SqrtTwoNonLattice` | `Towers.AlgebraicNumberTheory.GeometryOfNumbers.SqrtTwoNonLattice` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Theorem4_29` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.NarrowClassGroupEquiv` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Theorem4_29Forms` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.ProperPrimitiveClasses` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter4.Theorem4_29Gaussian` | `Towers.AlgebraicNumberTheory.Quadratic.Forms.GaussianClassCorrespondence` |

## Chapter5

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.BoundedAlgebraicIntegers` | `Towers.AlgebraicNumberTheory.Units.BoundedAlgebraicIntegers` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.BoundedConjugates` | `Towers.AlgebraicNumberTheory.Units.BoundedConjugates` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.CMFieldPresentation` | `Towers.AlgebraicNumberTheory.Units.CMFieldPresentation` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.CMUnitIndex` | `Towers.AlgebraicNumberTheory.Units.CMUnitIndex` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.ContinuedFractionExpansion` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.ContinuedFractionExpansion` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.CubicDiscriminantBound` | `Towers.AlgebraicNumberTheory.NumberFields.Examples.CubicDiscriminantBound` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.CubicUnitExample` | `Towers.AlgebraicNumberTheory.NumberFields.Examples.CubicUnitExample` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.Exercise5_1` | `Towers.AlgebraicNumberTheory.Units.BoundedSingleEmbeddingCounterexample` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.Exercise5_2` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.Sqrt67Pell` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.Exercise5_3` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.GaussianNonintegralNormOne` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.FixedNormIdeals` | `Towers.AlgebraicNumberTheory.Units.FixedNormIdeals` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.GlobalKronecker` | `Towers.AlgebraicNumberTheory.Units.GlobalKronecker` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.LogUnitLattice` | `Towers.AlgebraicNumberTheory.Units.LogUnitLattice` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.NegativeOffDiagonalMatrix` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.NegativeOffDiagonalMatrix` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.NonintegralNormOne` | `Towers.AlgebraicNumberTheory.Units.NonintegralNormOne` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.PeriodicContinuedFractions` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.PeriodicContinuedFractions` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.QuadraticContinuedFractionFundamentalUnit` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.QuadraticContinuedFractionFundamentalUnit` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.QuadraticContinuedFractionMinimality` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.QuadraticContinuedFractionMinimality` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.QuadraticContinuedFractionUnits` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.QuadraticContinuedFractionUnits` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.QuadraticNegativeUnitGenerator` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.QuadraticNegativeUnitGenerator` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.QuadraticPellExamples` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.QuadraticPellExamples` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.QuadraticPeriodicForward` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.QuadraticPeriodicForward` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.QuadraticUnitExamples` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.QuadraticUnitExamples` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.QuadraticUnitSuborder` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.QuadraticUnitSuborder` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.RationalSUnitExample` | `Towers.AlgebraicNumberTheory.Units.RationalSUnitExample` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.RealFieldRootsOfUnity` | `Towers.AlgebraicNumberTheory.Units.RealFieldRootsOfUnity` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.Regulator` | `Towers.AlgebraicNumberTheory.Units.Regulator` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.RootsOfUnity` | `Towers.AlgebraicNumberTheory.Units.RootsOfUnity` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.SUnits` | `Towers.AlgebraicNumberTheory.Units.SUnits` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.Sqrt94ContinuedFraction` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.Sqrt94ContinuedFraction` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.Sqrt94PellMinimality` | `Towers.AlgebraicNumberTheory.Quadratic.ContinuedFractions.Sqrt94PellMinimality` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter5.UnitTheorem` | `Towers.AlgebraicNumberTheory.Units.UnitTheorem` |

## Chapter6

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.CompositumIntegers` | `Towers.AlgebraicNumberTheory.Cyclotomic.CompositumIntegers` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.CyclotomicDiscriminantFormula` | `Towers.AlgebraicNumberTheory.Cyclotomic.CyclotomicDiscriminantFormula` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.CyclotomicIntersection` | `Towers.AlgebraicNumberTheory.Cyclotomic.CyclotomicIntersection` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.CyclotomicMaximalReal` | `Towers.AlgebraicNumberTheory.Cyclotomic.CyclotomicMaximalReal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.CyclotomicPolynomialExamples` | `Towers.AlgebraicNumberTheory.Cyclotomic.CyclotomicPolynomialExamples` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.CyclotomicUnits` | `Towers.AlgebraicNumberTheory.Cyclotomic.CyclotomicUnits` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.CyclotomicUnitsTwoPower` | `Towers.AlgebraicNumberTheory.Cyclotomic.CyclotomicUnitsTwoPower` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.Exercises.Exercise6_1` | `Towers.AlgebraicNumberTheory.NumberFields.Examples.CubicX3Sub3XAdd1` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.Exercises.Exercise6_1_Finish` | `Towers.AlgebraicNumberTheory.NumberFields.Examples.CubicX3Sub3XAdd1IntegralClosure` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.Exercises.Exercise6_2` | `Towers.AlgebraicNumberTheory.Cyclotomic.MaximalRealRingOfIntegers` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.Exercises.Exercise6_3` | `Towers.AlgebraicNumberTheory.Cyclotomic.PrimePowerAutomorphismGroups` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.FermatAuxiliary` | `Towers.AlgebraicNumberTheory.Fermat.FermatAuxiliary` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.FermatFactorization` | `Towers.AlgebraicNumberTheory.Fermat.FermatFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.FermatFirstCase` | `Towers.AlgebraicNumberTheory.Fermat.FermatFirstCase` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.FermatFirstCaseTheorem` | `Towers.AlgebraicNumberTheory.Fermat.FermatFirstCaseTheorem` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.FermatPairwiseCoprime` | `Towers.AlgebraicNumberTheory.Fermat.FermatPairwiseCoprime` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.FermatPrimitiveReduction` | `Towers.AlgebraicNumberTheory.Fermat.FermatPrimitiveReduction` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.FermatSmallCases` | `Towers.AlgebraicNumberTheory.Fermat.FermatSmallCases` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.GeneralCyclotomic` | `Towers.AlgebraicNumberTheory.Cyclotomic.GeneralCyclotomic` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.PairwisePowerFactors` | `Towers.AlgebraicNumberTheory.Fermat.PairwisePowerFactors` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.PrimePowerCyclotomic` | `Towers.AlgebraicNumberTheory.Cyclotomic.PrimePowerCyclotomic` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.PrimePowerCyclotomicSign` | `Towers.AlgebraicNumberTheory.Cyclotomic.PrimePowerCyclotomicSign` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter6.PrimitiveRootPowers` | `Towers.AlgebraicNumberTheory.Cyclotomic.PrimitiveRootPowers` |

## Chapter7

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.AbsoluteValueExamples` | `Towers.AlgebraicNumberTheory.LocalFields.AbsoluteValueExamples` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.AbsoluteValueRing` | `Towers.AlgebraicNumberTheory.LocalFields.AbsoluteValueRing` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.AbsoluteValueTopology` | `Towers.AlgebraicNumberTheory.LocalFields.AbsoluteValueTopology` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.AdicCompletionQuotients` | `Towers.AlgebraicNumberTheory.LocalFields.AdicCompletionQuotients` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.ArbitraryPlaceClassification` | `Towers.AlgebraicNumberTheory.LocalFields.ArbitraryPlaceClassification` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.ArchimedeanPlaceClassification` | `Towers.AlgebraicNumberTheory.LocalFields.ArchimedeanPlaceClassification` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.CompactValuationSubsets` | `Towers.AlgebraicNumberTheory.LocalFields.CompactValuationSubsets` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.CompleteDVRHenselian` | `Towers.AlgebraicNumberTheory.LocalFields.CompleteDVRHenselian` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.CompleteDiscreteExtension` | `Towers.AlgebraicNumberTheory.LocalFields.CompleteDiscreteExtension` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.CompletionUniversal` | `Towers.AlgebraicNumberTheory.LocalFields.CompletionUniversal` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.DiscreteAbsoluteValueRing` | `Towers.AlgebraicNumberTheory.LocalFields.DiscreteAbsoluteValueRing` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.EquivalentAbsoluteValues` | `Towers.AlgebraicNumberTheory.LocalFields.EquivalentAbsoluteValues` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_1` | `Towers.AlgebraicNumberTheory.LocalFields.FinitePlaceApproximation` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_2` | `Towers.AlgebraicNumberTheory.LocalFields.UltrametricBallsAndSeries` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_3` | `Towers.AlgebraicNumberTheory.LocalFields.SevenAdicSquares` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_4a` | `Towers.AlgebraicNumberTheory.LocalFields.UniversalPadicQuadraticRoot` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_4b` | `Towers.AlgebraicNumberTheory.LocalFields.SevenAdicNewtonApproximation` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_5` | `Towers.AlgebraicNumberTheory.LocalFields.TwoAdicSquareClasses` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_6` | `Towers.AlgebraicNumberTheory.LocalFields.MultiquadraticDegree` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_7` | `Towers.AlgebraicNumberTheory.LocalFields.PadicAlgebraicClosureRootsOfUnity` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_8a` | `Towers.AlgebraicNumberTheory.LocalFields.LocallyReducibleIrreduciblePolynomial` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.Exercise7_8b` | `Towers.AlgebraicNumberTheory.LocalFields.NewtonPolygonIrreducibilityCounterexample` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Exercises.TestGamma` | `Towers.AlgebraicNumberTheory.LocalFields.MultiquadraticDegreeGamma` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.FiniteExtensionClasses` | `Towers.AlgebraicNumberTheory.LocalFields.FiniteExtensionClasses` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.FiniteExtensionsFixedDegree` | `Towers.AlgebraicNumberTheory.LocalFields.FiniteExtensionsFixedDegree` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.FiniteFieldUnramifiedExample` | `Towers.AlgebraicNumberTheory.LocalFields.FiniteFieldUnramifiedExample` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.FiniteProductFormula` | `Towers.AlgebraicNumberTheory.LocalFields.FiniteProductFormula` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.FunctionFieldProductFormula` | `Towers.AlgebraicNumberTheory.LocalFields.FunctionFieldProductFormula` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.HenselFactorUniqueness` | `Towers.AlgebraicNumberTheory.LocalFields.HenselFactorUniqueness` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.HenselFactorization` | `Towers.AlgebraicNumberTheory.LocalFields.HenselFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.HenselFiniteFactorization` | `Towers.AlgebraicNumberTheory.LocalFields.HenselFiniteFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.KrasnerLemma` | `Towers.AlgebraicNumberTheory.LocalFields.KrasnerLemma` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.LocalDegreeFormula` | `Towers.AlgebraicNumberTheory.LocalFields.LocalDegreeFormula` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.LocalFieldClassification` | `Towers.AlgebraicNumberTheory.LocalFields.LocalFieldClassification` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.LocalNormFormula` | `Towers.AlgebraicNumberTheory.LocalFields.LocalNormFormula` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.LocalPolynomialBezoutDegree` | `Towers.AlgebraicNumberTheory.LocalFields.LocalPolynomialBezoutDegree` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.LocalPolynomialCoprime` | `Towers.AlgebraicNumberTheory.LocalFields.LocalPolynomialCoprime` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.LocalUnramifiedDecomposition` | `Towers.AlgebraicNumberTheory.LocalFields.LocalUnramifiedDecomposition` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.LogarithmicValuation` | `Towers.AlgebraicNumberTheory.LocalFields.LogarithmicValuation` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.NewtonPolygon` | `Towers.AlgebraicNumberTheory.LocalFields.NewtonPolygon` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.NewtonRootLifting` | `Towers.AlgebraicNumberTheory.LocalFields.NewtonRootLifting` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.NonarchimedeanCriterion` | `Towers.AlgebraicNumberTheory.LocalFields.NonarchimedeanCriterion` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.NonarchimedeanPlaceClassification` | `Towers.AlgebraicNumberTheory.LocalFields.NonarchimedeanPlaceClassification` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.NondiscreteAlgebraicClosure` | `Towers.AlgebraicNumberTheory.LocalFields.NondiscreteAlgebraicClosure` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.NondiscreteValueGroup` | `Towers.AlgebraicNumberTheory.LocalFields.NondiscreteValueGroup` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.NumberFieldProductFormula` | `Towers.AlgebraicNumberTheory.LocalFields.NumberFieldProductFormula` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.OpenIdealQuotient` | `Towers.AlgebraicNumberTheory.LocalFields.OpenIdealQuotient` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.Ostrowski` | `Towers.AlgebraicNumberTheory.LocalFields.Ostrowski` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PadicApproximations` | `Towers.AlgebraicNumberTheory.LocalFields.PadicApproximations` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PadicCauchyExample` | `Towers.AlgebraicNumberTheory.LocalFields.PadicCauchyExample` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PadicComplexAlgebraicClosure` | `Towers.AlgebraicNumberTheory.LocalFields.PadicComplexAlgebraicClosure` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PadicDigitExpansion` | `Towers.AlgebraicNumberTheory.LocalFields.PadicDigitExpansion` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PadicExamples` | `Towers.AlgebraicNumberTheory.LocalFields.PadicExamples` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PadicExponentialValuation` | `Towers.AlgebraicNumberTheory.LocalFields.PadicExponentialValuation` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PadicGlobalization` | `Towers.AlgebraicNumberTheory.LocalFields.PadicGlobalization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PadicInverseLimit` | `Towers.AlgebraicNumberTheory.LocalFields.PadicInverseLimit` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PlaceExtension` | `Towers.AlgebraicNumberTheory.LocalFields.PlaceExtension` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PlacesClassification` | `Towers.AlgebraicNumberTheory.LocalFields.PlacesClassification` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PolynomialStability` | `Towers.AlgebraicNumberTheory.LocalFields.PolynomialStability` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.PositiveCharacteristicNonarchimedean` | `Towers.AlgebraicNumberTheory.LocalFields.PositiveCharacteristicNonarchimedean` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.RamificationGroups` | `Towers.AlgebraicNumberTheory.LocalFields.RamificationGroups` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.RationalProductFormula` | `Towers.AlgebraicNumberTheory.LocalFields.RationalProductFormula` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.RestrictionNontrivial` | `Towers.AlgebraicNumberTheory.LocalFields.RestrictionNontrivial` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.TeichmullerLifts` | `Towers.AlgebraicNumberTheory.LocalFields.TeichmullerLifts` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.TeichmullerResidueRoots` | `Towers.AlgebraicNumberTheory.LocalFields.TeichmullerResidueRoots` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.TotallyRamifiedEisenstein` | `Towers.AlgebraicNumberTheory.LocalFields.TotallyRamifiedEisenstein` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.UltrametricConsequences` | `Towers.AlgebraicNumberTheory.LocalFields.UltrametricConsequences` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.UniformizerExpansion` | `Towers.AlgebraicNumberTheory.LocalFields.UniformizerExpansion` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.UniformizerSeries` | `Towers.AlgebraicNumberTheory.LocalFields.UniformizerSeries` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.UnramifiedExtensions` | `Towers.AlgebraicNumberTheory.LocalFields.UnramifiedExtensions` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.UnramifiedResidueLift` | `Towers.AlgebraicNumberTheory.LocalFields.UnramifiedResidueLift` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.ValuationRingCompactness` | `Towers.AlgebraicNumberTheory.LocalFields.ValuationRingCompactness` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.WeakApproximation` | `Towers.AlgebraicNumberTheory.LocalFields.WeakApproximation` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.WeakApproximationCompletion` | `Towers.AlgebraicNumberTheory.LocalFields.WeakApproximationCompletion` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter7.WeakApproximationCompletions` | `Towers.AlgebraicNumberTheory.LocalFields.WeakApproximationCompletion` |

## Chapter8

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.AdicCompletionBaseChange` | `Towers.AlgebraicNumberTheory.Completions.AdicCompletionBaseChange` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.AdicCompletionChineseRemainder` | `Towers.AlgebraicNumberTheory.Completions.AdicCompletionChineseRemainder` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.AdicCompletionDenseEquiv` | `Towers.AlgebraicNumberTheory.Completions.AdicCompletionDenseEquiv` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.AdicCompletionIntegersComplete` | `Towers.AlgebraicNumberTheory.Completions.AdicCompletionIntegersComplete` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.AdicCompletionLocalEquiv` | `Towers.AlgebraicNumberTheory.Completions.AdicCompletionLocalEquiv` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.AdicCompletionLocalRing` | `Towers.AlgebraicNumberTheory.Completions.AdicCompletionLocalRing` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.AdicCompletionPower` | `Towers.AlgebraicNumberTheory.Completions.AdicCompletionPower` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.ChebotarevDensity` | `Towers.AlgebraicNumberTheory.Density.ChebotarevDensity` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.ChebotarevExamples` | `Towers.AlgebraicNumberTheory.Density.ChebotarevExamples` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompletedDifferentProductBound` | `Towers.AlgebraicNumberTheory.Completions.CompletedDifferentProductBound` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompletedDifferentSelectedSemilocalBound` | `Towers.AlgebraicNumberTheory.Completions.CompletedDifferentSelectedSemilocalBound` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompletedDifferentSemilocalBound` | `Towers.AlgebraicNumberTheory.Completions.CompletedDifferentSemilocalBound` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompletedLocalExponentCompatibility` | `Towers.AlgebraicNumberTheory.Completions.CompletedLocalExponentCompatibility` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompletedValuationRingExtension` | `Towers.AlgebraicNumberTheory.Completions.CompletedValuationRingExtension` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompletionFactorization` | `Towers.AlgebraicNumberTheory.Completions.CompletionFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompletionNormTrace` | `Towers.AlgebraicNumberTheory.Completions.CompletionNormTrace` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompletionTensorDecomposition` | `Towers.AlgebraicNumberTheory.Completions.CompletionTensorDecomposition` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompositumDegreeCriterion` | `Towers.AlgebraicNumberTheory.Galois.CompositumDegreeCriterion` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CompositumSplittingPrimes` | `Towers.AlgebraicNumberTheory.Galois.CompositumSplittingPrimes` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CubicChebotarevDensities` | `Towers.AlgebraicNumberTheory.Density.CubicChebotarevDensities` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.CyclotomicQuadraticFrobenius` | `Towers.AlgebraicNumberTheory.Galois.CyclotomicQuadraticFrobenius` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DecompositionGroup` | `Towers.AlgebraicNumberTheory.Galois.DecompositionGroup` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DecompositionGroupTower` | `Towers.AlgebraicNumberTheory.Galois.DecompositionGroupTower` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DecompositionInertiaFields` | `Towers.AlgebraicNumberTheory.Galois.DecompositionInertiaFields` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DedekindCyclePartition` | `Towers.AlgebraicNumberTheory.Galois.DedekindCyclePartition` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DedekindPermutationCycles` | `Towers.AlgebraicNumberTheory.Galois.DedekindPermutationCycles` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DedekindRootReduction` | `Towers.AlgebraicNumberTheory.Galois.DedekindRootReduction` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DedekindTheorem` | `Towers.AlgebraicNumberTheory.Galois.DedekindTheorem` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionAdicRecovery` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionAdicRecovery` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionBasis` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionBasis` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionCommonDenominator` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionCommonDenominator` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionConcrete` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionConcrete` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionDescent` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionDescent` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionFractionRingBridge` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionFractionRingBridge` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionPureTensorLocalization` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionPureTensorLocalization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionSemilocalImage` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionSemilocalImage` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionSemilocalRecovery` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionSemilocalRecovery` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionTrace` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionTrace` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionTraceDualBaseChange` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionTraceDualBaseChange` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentCompletionTransport` | `Towers.AlgebraicNumberTheory.Completions.DifferentCompletionTransport` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DifferentLocalization` | `Towers.AlgebraicNumberTheory.Completions.DifferentLocalization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.DihedralQuarticChebotarev` | `Towers.AlgebraicNumberTheory.Density.DihedralQuarticChebotarev` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.Example8_25` | `Towers.AlgebraicNumberTheory.Galois.QuinticX5SubXSub1` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.Example8_25GaloisGroup` | `Towers.AlgebraicNumberTheory.Galois.QuinticX5SubXSub1GaloisGroup` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.Example8_27` | `Towers.AlgebraicNumberTheory.Galois.SymmetricGroupPolynomialConstruction` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.Example8_27GaloisGroup` | `Towers.AlgebraicNumberTheory.Galois.SymmetricGroupPolynomialGaloisGroup` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.Exercises.Exercise8_1` | `Towers.AlgebraicNumberTheory.Completions.TwoAdicCubicFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.Exercises.Exercise8_2` | `Towers.AlgebraicNumberTheory.Completions.HigherRamificationCoefficient` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.Exercises.Exercise8_4` | `Towers.AlgebraicNumberTheory.GlobalFields.RationalFunctionProductFormula` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.FiniteFieldIrreducibleFactors` | `Towers.AlgebraicNumberTheory.Galois.FiniteFieldIrreducibleFactors` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.FractionRingProductLattice` | `Towers.AlgebraicNumberTheory.Completions.FractionRingProductLattice` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.FrobeniusElement` | `Towers.AlgebraicNumberTheory.Galois.FrobeniusElement` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.FrobeniusFactorCyclePartition` | `Towers.AlgebraicNumberTheory.Galois.FrobeniusFactorCyclePartition` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.FrobeniusPermutationCycles` | `Towers.AlgebraicNumberTheory.Galois.FrobeniusPermutationCycles` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.GaloisOrbitFactorization` | `Towers.AlgebraicNumberTheory.Galois.GaloisOrbitFactorization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.GlobalField` | `Towers.AlgebraicNumberTheory.GlobalFields.GlobalField` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.GlobalProductFormula` | `Towers.AlgebraicNumberTheory.GlobalFields.GlobalProductFormula` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.HermiteEmbeddedFiniteness` | `Towers.AlgebraicNumberTheory.GlobalFields.HermiteEmbeddedFiniteness` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.HermiteFiniteness` | `Towers.AlgebraicNumberTheory.GlobalFields.HermiteFiniteness` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.LocalCompletionDegreeBound` | `Towers.AlgebraicNumberTheory.Completions.LocalCompletionDegreeBound` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.LocalDifferentTowerBound` | `Towers.AlgebraicNumberTheory.Completions.LocalDifferentTowerBound` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.LocalDifferentUniformExponent` | `Towers.AlgebraicNumberTheory.Completions.LocalDifferentUniformExponent` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.LocalNormProduct` | `Towers.AlgebraicNumberTheory.Completions.LocalNormProduct` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.LocalizedDifferentUniformBound` | `Towers.AlgebraicNumberTheory.Completions.LocalizedDifferentUniformBound` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.NormTraceProduct` | `Towers.AlgebraicNumberTheory.Completions.NormTraceProduct` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.NormalizedExtension` | `Towers.AlgebraicNumberTheory.Completions.NormalizedExtension` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.OddCyclePowerSwap` | `Towers.AlgebraicNumberTheory.Galois.OddCyclePowerSwap` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.PermutationCycleTransport` | `Towers.AlgebraicNumberTheory.Galois.PermutationCycleTransport` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.PermutationGroupCriterion` | `Towers.AlgebraicNumberTheory.Galois.PermutationGroupCriterion` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.PiBaseLocalization` | `Towers.AlgebraicNumberTheory.Completions.PiBaseLocalization` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.PlaceFactorCorrespondence` | `Towers.AlgebraicNumberTheory.Completions.PlaceFactorCorrespondence` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.PrimeIdealNaturalDensity` | `Towers.AlgebraicNumberTheory.Density.PrimeIdealNaturalDensity` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.ProductDifferent` | `Towers.AlgebraicNumberTheory.Completions.ProductDifferent` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.QuarticChebotarevDensities` | `Towers.AlgebraicNumberTheory.Density.QuarticChebotarevDensities` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.QuarticSmallGroupDensities` | `Towers.AlgebraicNumberTheory.Density.QuarticSmallGroupDensities` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.RealPrimeCycleType` | `Towers.AlgebraicNumberTheory.Galois.RealPrimeCycleType` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.Remark8_3` | `Towers.AlgebraicNumberTheory.Galois.FinitePlacesAndReducedFactors` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.Remark8_40` | `Towers.AlgebraicNumberTheory.Galois.ReduciblePolynomialLocalRoots` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.ResolventCoefficientDescent` | `Towers.AlgebraicNumberTheory.Galois.ResolventCoefficientDescent` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.ResolventFactorDescent` | `Towers.AlgebraicNumberTheory.Galois.ResolventFactorDescent` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.ResolventGaloisGroup` | `Towers.AlgebraicNumberTheory.Galois.ResolventGaloisGroup` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalAtPrime` | `Towers.AlgebraicNumberTheory.Completions.SemilocalAtPrime` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalAtPrimeModule` | `Towers.AlgebraicNumberTheory.Completions.SemilocalAtPrimeModule` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalCompletionAssembly` | `Towers.AlgebraicNumberTheory.Completions.SemilocalCompletionAssembly` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalCompletionCommonDenominator` | `Towers.AlgebraicNumberTheory.Completions.SemilocalCompletionCommonDenominator` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalCompletionCoordinateAlgebra` | `Towers.AlgebraicNumberTheory.Completions.SemilocalCompletionCoordinateAlgebra` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalCompletionCoordinateCompatibility` | `Towers.AlgebraicNumberTheory.Completions.SemilocalCompletionCoordinateCompatibility` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalCompletionCoordinateDescent` | `Towers.AlgebraicNumberTheory.Completions.SemilocalCompletionCoordinateDescent` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalCompletionCoordinateMap` | `Towers.AlgebraicNumberTheory.Completions.SemilocalCompletionCoordinateMap` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalCompletionFactor` | `Towers.AlgebraicNumberTheory.Completions.SemilocalCompletionFactor` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalCompletionMap` | `Towers.AlgebraicNumberTheory.Completions.SemilocalCompletionMap` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalFractionFieldSetup` | `Towers.AlgebraicNumberTheory.Completions.SemilocalFractionFieldSetup` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalLowerLocalSetup` | `Towers.AlgebraicNumberTheory.Completions.SemilocalLowerLocalSetup` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalTotalQuotient` | `Towers.AlgebraicNumberTheory.Completions.SemilocalTotalQuotient` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalTotalQuotientAlgebra` | `Towers.AlgebraicNumberTheory.Completions.SemilocalTotalQuotientAlgebra` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SemilocalTotalQuotientCompatibility` | `Towers.AlgebraicNumberTheory.Completions.SemilocalTotalQuotientCompatibility` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.SplittingPrimeDensity` | `Towers.AlgebraicNumberTheory.Density.SplittingPrimeDensity` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.TotallyRamifiedDifferentBound` | `Towers.AlgebraicNumberTheory.Completions.TotallyRamifiedDifferentBound` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.TransitiveCycleSwap` | `Towers.AlgebraicNumberTheory.Galois.TransitiveCycleSwap` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.UnramifiedExtensionFiniteness` | `Towers.AlgebraicNumberTheory.GlobalFields.UnramifiedExtensionFiniteness` |
| `Towers.AlgebraicNumberTheory.Milne.Chapter8.UnramifiedExtensionFinitenessFinal` | `Towers.AlgebraicNumberTheory.GlobalFields.UnramifiedExtensionFinitenessFinal` |

## Introduction

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.Introduction.SqrtNegFive` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegFive` |
| `Towers.AlgebraicNumberTheory.Milne.Introduction.SqrtNegFiveIdeals` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegFiveIdeals` |
| `Towers.AlgebraicNumberTheory.Milne.Introduction.SqrtNegFiveTwentyOne` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegFiveTwentyOne` |
| `Towers.AlgebraicNumberTheory.Milne.Introduction.SqrtNegFiveTwentyOneIdeals` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegFiveTwentyOneIdeals` |
| Pairwise principal products in the `21` example | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtNegFiveTwentyOnePrincipalProducts` |
| `Towers.AlgebraicNumberTheory.Milne.Introduction.SqrtTwoUnits` | `Towers.AlgebraicNumberTheory.Quadratic.Examples.SqrtTwoUnits` |
| Carlitz's half-factorial theorem | `Towers.AlgebraicNumberTheory.Factorization.HalfFactorial` |

## TestArch

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.TestArch` | `Towers.AlgebraicNumberTheory.Completions.RealPlaceFactorRoundtrip` |

## TestLocalQuotient

| Former module | Current topic module |
|---|---|
| `Towers.AlgebraicNumberTheory.Milne.TestLocalQuotient` | `Towers.AlgebraicNumberTheory.LocalFields.InertiaResidueGaloisEquiv` |

## Coverage Notes

The tables above record the mechanical module move.  The following notes
record the mathematical assembly points where one ANT result is spread over
several topic modules.

### Introduction

- Carlitz's characterization of class-number-two number rings is stated in
  `Factorization/HalfFactorial.lean`.  The file defines irreducible
  factorizations modulo associates and the half-factorial property.  Besides
  the class-number-one result, it proves the unconditional forward half of
  Carlitz's theorem: any Dedekind domain whose class group has cardinality two
  is half-factorial, hence so is the ring of integers of every class-number-two
  number field.  The proof assigns weight two to principal prime ideals and
  weight one to nonprincipal prime ideals, proves every irreducible has weight
  two, and compares factorization lengths.  ANT cites the converse without
  proof; the exact equivalence remains exposed honestly as an explicit
  proposition rather than introduced as an axiom.
- The intermediate class-group claim in the `21` example is completed in
  `Quadratic/Examples/SqrtNegFiveTwentyOnePrincipalProducts.lean`: any two
  of the four displayed nonprincipal prime ideals have principal product.
  The proof derives the general `ℤ[√-5]` statement from the class group's
  cardinality two, rather than checking the ten products separately.

### Chapter 1

- Proposition 1.1 now has explicit binary-product wrappers in
  `CommutativeAlgebra/FiniteProducts.lean`, including both the coordinate
  decomposition of every ideal and the classification of prime ideals.
  `CommutativeAlgebra/Localization/LocalizationIdeals.lean` likewise records
  both assertions of Example 1.13(a): localization at a prime is local and
  the extended prime is its unique maximal ideal.  Theorem 1.14's statement
  that all simultaneous solutions form one coset of the product ideal is
  explicit in `CommutativeAlgebra/ChineseRemainder.lean`.
- The inseparability discussion after Example 1.19 is completed in
  `FieldTheory/TensorProduct/InseparableTensor.lean`.  Besides the source's
  explicit `x^p` obstruction, the intrinsic theorem proves that `K tensor_k K`
  is nonreduced for every finite inseparable extension `K/k`.  Its proof uses
  the repeated factor of an inseparable minimal polynomial; this avoids the
  source's overly strong suggestion that every inseparable extension directly
  supplies an element outside `k` whose `p`th power lies in `k`.

### Chapter 2

- Example 2.10(a)'s two concrete cases are explicit in
  `IntegralClosure/IntegralClosureFacts.lean`: both `ℤ` and the Gaussian
  integers are principal ideal rings, and both are integrally closed by the
  proved unique-factorization criterion of Proposition 2.9.
- Example 2.10(b) is now completed algebraically across
  `Quadratic/Examples/SqrtNegThree.lean` and
  `Eisenstein/Euclidean.lean`.  The former proves the displayed distinct
  irreducible factorizations in `ℤ[√-3]` and constructs its proper embedding
  into the Eisenstein integers, sending `√-3` to `2ω - 1`.  The latter
  constructs an explicit Euclidean quotient by rounding the two rational
  Eisenstein coordinates and proves the strict norm decrease.  Consequently
  the Eisenstein integers are a principal ideal ring, are integrally closed,
  and are the integral closure of `ℤ` in their fraction field.  Clearing a
  factor of two proves that this fraction field is canonically isomorphic to
  the fraction field of `ℤ[√-3]`, matching the field equality printed by
  Milne.
- Remark 2.31(a)'s inseparable normalization-finiteness assertion is stated
  exactly as `PolynomialIntegralClosureFiniteTheorem` in
  `IntegralClosure/PolynomialFiniteExtension.lean`.  Milne gives no proof;
  Mathlib currently supplies the trace-dual theorem only for separable
  extensions.  Accordingly the arbitrary finite-extension result is exposed
  as an explicit source-delegated proposition rather than an axiom.
- Remark 2.31(b)'s unproved existence of a number-field extension with a
  nonfree relative ring of integers is recorded literally as
  `NonfreeRelativeRingOfIntegersTheorem` in
  `IntegralClosure/NonfreeRelativeRingOfIntegers.lean`.  The concrete module
  counterexample in part (c), by contrast, is proved unconditionally in
  `Quadratic/Examples/SqrtNegFiveNonfreeIdeal.lean`.
- The Lubin--Tate block inserted in the current `ANT.tex` immediately after
  Remark 2.17 is recorded in `FormalGroups/LubinTateInsert.lean`.  The
  underlying unconditional proofs already live in
  `ClassFieldTheory/Chapter1/Section2`: Example 2.18 identifies the
  p-adic binomial series `(1+T)^a - 1` with the canonical scalar
  endomorphism of the multiplicative Lubin--Tate law, Remark 2.19 proves the
  uniformizer, faithfulness, and canonical-isomorphism assertions, Summary
  2.20 gives existence and uniqueness of the formal group law, and Exercise
  2.21 constructs the unique inverse series with linear coefficient `-1`.
  The externally referenced logarithm assertions in the following Notes are
  exposed as the explicit propositions `FormalGroupLogarithmTheorem` and
  `FormalGroupLogarithmLinearizesEndomorphisms`, without adding axioms.
- Example 2.38 is completed in
  `NumberFields/Examples/DedekindCubicExample.lean`.  For
  `f = X^3 + X^2 - 2X + 8`, it proves irreducibility and polynomial
  discriminant `-2012`, constructs the integral basis
  `{1, alpha, (alpha^2 - alpha) / 2}`, identifies the full integer ring as
  `Z[alpha, (alpha^2 - alpha) / 2]`, computes field discriminant `-503` and
  index `[O_K : Z[alpha]] = 2`, and proves Dedekind's full
  nonmonogenicity conclusion by showing that every cubic index form is even.
- Example 2.39 is completed in
  `NumberFields/Examples/QuinticIntegralBasis.lean`: the discriminant of
  `X^5 - X - 1` is `2869 = 19 * 151`, its first five powers form an integral
  basis, and the full ring of integers is generated by the chosen root.
- Example 2.46's basis `1, (1 + √m) / 2` is realized by
  `quadraticRingOfIntegersBasis` in
  `Quadratic/Forms/QuadraticFieldFormSetup.lean`; the accompanying basis
  theorem identifies its two vectors with the standard half-integral
  quadratic-order basis.  The surrounding Hermite-normal-form algorithm is
  computational material and is intentionally omitted.
- The explicit PARI examples and the row-reduction/Hermite-normal-form
  algorithm in the section following Proposition 2.43 are computational
  material and are intentionally outside this development's scope.

### Chapter 3

- The assertions surrounding Example 3.1 are explicit across
  `Valuations/DiscreteValuationRings.lean` and
  `DedekindDomain/Modules/DVRQuotientAnnihilator.lean`: nonzero elements and
  ideals have unique unit-times-power and prime-power normal forms, the
  exponent detects units, and the maximal annihilator in `A/(c)` occurs
  exactly at the penultimate power and is generated by the represented
  quotient `c/b`.
- The two-part note after Proposition 3.6 is recorded in
  `DedekindDomain/NonnoetherianLocalDVR.lean`.  The finite-character local-to-
  global noetherian criterion is proved by patching generators at the finitely
  many maximal ideals containing a fixed nonzero ideal element.  Milne gives
  no construction or proof of the counterexample existence assertion, so its
  exact statement is exposed as `NonnoetherianLocallyDVRDomainTheorem`, not
  added as an axiom.
- The fractional-ideal preliminaries and Example 3.19 are explicit in
  `Ideals/FractionalIdealBasics.lean` and `Ideals/DVRFractionalIdeals.lean`.
  Besides finite generation, common denominators, and principal
  multiplication, the latter proves the literal unique normal forms for both
  nonzero fraction-field elements and nonzero fractional ideals using integer
  powers of a fixed uniformizer or maximal ideal.
- The external assertions before Example 3.22 are recorded in
  `ClassGroup/Universality.lean`: Gauss's unbounded elementary `2`-subgroups
  in quadratic class groups and Claborn's realization of every abelian group
  as a Dedekind-domain class group are exposed as propositions rather than
  axioms.  The finite-character and tensor-product claims surrounding
  Theorem 3.31 are proved directly.
- The inseparable strengthening following Theorem 3.29 is exposed as
  `IntegralClosureDedekindFiniteExtensionTheorem` in
  `DedekindDomain/IntegralClosureDedekind.lean`.  Milne delegates this harder
  noetherianity theorem to Janusz; the separable theorem stated and proved as
  Theorem 3.29 remains unconditional.
- Theorem 3.35 is available in its literal number-field generality in
  `Ramification/RamificationDiscriminant.lean`.  The base Dedekind domain need
  not be finite over `ℤ`: `DedekindDomain/NumberFieldOverrings.lean` proves
  unconditionally that every nonzero prime quotient is finite when the
  fraction field is a number field, by identifying the relevant DVR
  localization with that of the ring of integers.
- Example 3.22 is in `ClassGroup/EllipticCurveClassGroup.lean`.  The
  coordinate ring is proved Dedekind: maximal ideals are identified with
  complex points, and the nonvanishing of a partial derivative makes the
  localized maximal ideal principal and hence its localization a DVR.  Its
  class group is proved uncountable.  The analytic identification with
  `C / Lambda` is cited by ANT from algebraic geometry and is not formalized.
- Example 3.26(a) is in `Valuations/MeromorphicFunctionField.lean` for a
  connected open subset of `C`: meromorphic functions modulo codiscrete
  equality form a field, order at a point descends to an additive valuation,
  and the valuation is normalized by a proof of surjectivity onto
  `WithTop Z`.  The algebraic examples 3.26(b)--(c) are in
  `Valuations/DiscreteValuations.lean`.
- Proposition 3.28 is in `Ideals/Approximation.lean`.  Besides the equivalent
  congruence formulation, it now exports Milne's literal strict inequalities
  for the normalized integer-valued prime valuations, including negative
  integer bounds without an extra sign hypothesis.
- Remark 3.39(a)'s lower bound is in
  `Ramification/RamificationDiscriminant.lean`.  The exact tame local formula
  is proved in `Completions/TotallyRamifiedDifferentBound.lean`: for a totally
  ramified finite extension of DVRs whose ramification degree is a unit in the
  base DVR, the different is exactly the `(e - 1)`st power of the upstairs
  maximal ideal.  Its public theorem constructs an Eisenstein uniformizer and
  proves monogenicity internally.  The displayed global sum equality is not
  assembled: it requires the general local different-exponent theorem after
  passing through the unramified/totally ramified decomposition and then
  transporting exponents through completion.  ANT delegates precisely this
  result to Serre, III.6; Mathlib currently has no packaged tame-ramification
  predicate or general tame finite-DVR different formula.
- Remark 3.43's fixed-prime Kummer--Dedekind conclusion is in
  `Ramification/KummerDedekindFactorization.lean`.  It assumes only that the
  chosen prime is coprime to the contraction of the conductor of `A[alpha]`
  in the integral closure, and gives the prime-factor bijection, the explicit
  ideals `(p, G(alpha))`, and their multiplicities without assuming
  `A[alpha] = B`.  This conductor condition is the canonical local-index
  hypothesis used by Mathlib's Kummer--Dedekind API.  For the printed
  `ℤ`/number-field situation, `not_dvd_exponent_of_discriminant_ratio`
  derives this condition from
  `D(1, alpha, ..., alpha^(m-1)) = a * disc(B/ℤ)` and `p ∤ a`, using the
  index--discriminant identity and the fact that the index annihilates the
  quotient by `ℤ[alpha]`.
- Example 3.44, including the radicand congruent to one modulo four, is in
  `Quadratic/PrimeFactorization.lean`; its statements use the full
  half-integral maximal order rather than `Z[sqrt(m)]`.
- Theorem 3.41's general residue-ring isomorphism and inertia-degree clause
  are in `Ramification/KummerDedekindFactorization.lean`.  They apply over an
  arbitrary integrally closed base and identify the quotient attached to a
  reduced irreducible factor with the corresponding polynomial quotient over
  the base residue field; the existing number-field specialization is a
  corollary-level convenience, not an extra hypothesis on the general result.

### Chapter 4

- Proposition 4.1 is in `Ideals/IdealNormCompatibility.lean`.  In the
  Galois conjugate formula, the stabilizer cardinality is obtained by
  comparing orbit--stabilizer with the unconditional ramification
  fundamental identity.  Thus the public statement does not require the
  residue-field extension to be separable.
- Remark 4.18's intermediate form of Minkowski's argument is in
  `GeometryOfNumbers/Blichfeldt.lean`.  It assumes only that a set contains
  half the difference of each pair of its points, rather than replacing that
  condition by the stronger convexity-and-symmetry hypotheses.
- Lemma 4.22 is proved in `GeometryOfNumbers/ConvexBodyVolume.lean` both for
  an arbitrary positive-dimensional pair `(r,s)` and for the signature of a
  number field.  The generic statement lives on `R^r x C^s`, so the calculus
  result itself no longer depends on realizing the signature arithmetically.
- Lemma 4.23's recursive induction is connected in
  `GeometryOfNumbers/ConvexBodyIntegral.lean` to the actual multidimensional
  Lebesgue integral over the closed simplex `Z(t)`.  The public Gamma formula
  now has Milne's set integral, rather than only the auxiliary iterated-list
  integral, on its left-hand side.
- Exercise 4-7 is in
  `Quadratic/Examples/SqrtNegFiveUnramifiedBiquadratic.lean`.  The integer
  ring, ramified rational primes and their indices, relative unramifiedness,
  class number two, abelianity, and the final concrete numerical/unramified
  criterion are proved.  The identification with the Hilbert class field is
  left to Remark 4.11/class field theory, as in the source; the Lean
  predicate is deliberately not presented as a replacement definition of a
  Hilbert class field.
- Theorem 4.29 is assembled in `Quadratic/Forms/NarrowClassGroupEquiv.lean`.
  For negative discriminant its target is the positive-definite component of
  the proper primitive form classes; for positive discriminant it is the full
  proper primitive indefinite component.  This positivity/orientation split
  corrects the printed statement's otherwise over-broad target.

### Chapter 5

- Example 5.3 is in `Units/RootsOfUnity.lean`.  In addition to the
  necessary restriction on roots of unity in a fixed quadratic field, the
  cyclotomic degree statement is now an iff:
  `finrank Q (CyclotomicField m Q) <= 2` exactly when `m` divides `4` or
  `6`.  The type-varying existential statement is also packaged: every
  positive `m` with `φ(m) <= 2` occurs in a quadratic number field.  The
  proof uses the fourth- and sixth-cyclotomic fields and takes powers of
  their primitive roots, so it includes the degree-one cases `m = 1, 2`.
  `Units/ImaginaryQuadraticRootsOfUnity.lean` assembles the complementary
  fixed-field classification.  For every squarefree `d < 0` other than
  `-1` and `-3`, the roots of unity in the full ring of integers of the
  coordinate field `Q(sqrt d)` are literally the set `{1, -1}`.  Separate
  fixed-model theorems give the complete four-element Gaussian and
  six-element Eisenstein lists.  This formulation avoids treating the
  informal, type-varying field isomorphisms as Lean equalities.
- Exercise 5-2 is completed in
  `Quadratic/ContinuedFractions/Sqrt67Pell.lean`.  Its continued-fraction and
  Pell analysis is now transported across an explicit identification of the
  full integer ring of `Q(sqrt 67)` with `Z[sqrt 67]`; every integer-ring unit
  is, up to sign, a power of `48842 + 5967 sqrt 67`.
- The unit-theoretic part of Example 5.14 is proved in
  `NumberFields/Examples/CubicUnitExample.lean`, through the identification
  of `-alpha^-1` as a fundamental unit and the description of every unit.
  The subsequent class-group computation is not formalized: the source
  leaves generation by `(2, 1 + alpha)`, the sixth-power identity, and the
  nonprincipality of its square to unshown computations (and treats the
  cube only by a sketched residue calculation).  It is therefore recorded
  as a skipped computational part of the example, not exported as a
  theorem with those conclusions as hypotheses.

### Chapter 6

- Theorem 6.4(c)'s ideal factorization is assembled literally in
  `Cyclotomic/GeneralCyclotomic.lean`: `(p)` is the product of the distinct
  primes above `p`, each with exponent `p^k (p - 1)`, under the displayed
  factorization `n = p^(k+1) m` with `p` not dividing `m`.
- The conductor-`23` class-number example is developed in
  `Cyclotomic/ConductorTwentyThreeClassNumber.lean`.  The quadratic Gauss-sum
  identity constructs an explicit embedding
  `Q(sqrt(-23)) -> Q(zeta_23)`.  The tower formula makes the relative degree
  `11`; since the quadratic base has class number `3`, the ideal-norm argument
  proves unconditionally that `Q(zeta_23)` has nontrivial class group.
- Proposition 6.7 is assembled without an exported CM-field hypothesis in
  `Cyclotomic/CyclotomicUnits.lean` and
  `Cyclotomic/CyclotomicUnitsTwoPower.lean`.  The public prime-power theorem
  covers every conductor `p^r > 2`, constructs the cyclotomic CM structure
  internally, and dispatches to the proved odd-prime and two-power cases.
- Exercise 6-1 is completed in
  `NumberFields/Examples/CubicX3Sub3XAdd1IntegralClosure.lean`.  The quotient
  by `(alpha + 1)` has three elements, the congruence argument proves
  `O_K = Z[alpha]`, the field discriminant is `81`, and the resulting
  Minkowski bound and primality of `(2)` prove that `O_K` is a PID.
- Exercise 6-2 is in `Cyclotomic/MaximalRealRingOfIntegers.lean`.  Its public
  cyclotomic theorem constructs the automatic number-field and CM-field
  structures internally and identifies the maximal-real integer ring with
  `Z[zeta + zeta^-1]`, equivalently `Z[2 cos(2 pi / m)]`.
- Exercise 6-3 is in `Cyclotomic/PrimePowerAutomorphismGroups.lean`; the odd
  prime-power and two-power relative automorphism groups are proved cyclic.
- Theorem 6.8 is assembled in
  `Fermat/FermatPrimitiveReduction.lean`.  Its public theorem assumes only
  that the ambient field is the `p`th cyclotomic extension; for odd `p` the
  required CM-field instance is constructed internally from the cyclotomic
  structure, so no additional CM hypothesis is exported.

### Chapter 7

- Proposition 7.6 is in `LocalFields/DiscreteAbsoluteValueRing.lean` with
  Milne's literal topology: the maximal ideal is principal exactly when
  `|K^x|` has the discrete topology.  This equivalence includes the trivial
  absolute value; under the necessary nontriviality hypothesis it is also
  equivalent to the valuation ring being a discrete valuation ring.
- Remark 7.7 is completed in `LocalFields/NondiscreteValueGroup.lean`: for
  the canonical algebraic closure of `Q_p`, the norm range on nonzero
  elements is exactly `{p^q | q in Q}`.  The forward inclusion follows from
  the spectral norm and the reverse inclusion from explicit algebraic roots;
  in particular the nonzero value group is not discrete.
- Remark 7.17 is in
  `GlobalFields/RationalFunctionProductFormula.lean`.  The product formula is
  proved directly for `k(T)` over a finite field.  For a finite extension,
  the finite-place support is regrouped over the base places and the
  7.16-style local norm identity transfers the already-proved base formula;
  the additive, algebraically-closed-constant form is packaged in parallel.
  This is the same input to which ANT delegates the general case.
- The completion discussion after Remark 7.24 is in
  `LocalFields/CompletionUniversal.lean`.  Besides the universal property,
  uniqueness, and density, it now proves from discreteness of `|K^x|` that
  the full value range is closed and hence that completion introduces no new
  values: `|Khat| = |K|`.  In `LocalFields/AdicCompletionQuotients.lean`,
  Lemma 7.25 is stated with the literal completed ideal: for finitely
  generated `I`, the reduction kernel is `(I Rhat)^n`, giving the
  source-oriented equivalence `R / I^n ~= Rhat / (I Rhat)^n`.
- Proposition 7.26 is in `LocalFields/UniformizerExpansion.lean`.  Integral
  elements have unique convergent digit expansions, and arbitrary field
  elements now use the least pole-clearing power of the uniformizer, removing
  the former leading-zero ambiguity and giving a unique canonical Laurent
  digit sequence.
- Example 7.29 is completed in
  `LocalFields/PadicExponentialValuation.lean`: it proves the exact valuation
  formula for `x^n / n!`, the sharp termwise criterion
  `ord_p(x) > 1 / (p - 1)`, and the equivalent summability criterion.  The
  converse uses the `n = p^k` subsequence, and the boundary case `p = 2`
  explicitly excludes valuation one.
- Remark 7.37 has a proved unit-resultant specialization in
  `LocalFields/HenselFactorization.lean`: its literal resultant-square norm
  bound forces equality after residue reduction, the mapped resultant proves
  coprimality, and Hensel lifting gives monic factors of the prescribed
  degrees.  The stronger nonunit-resultant estimate cited by ANT is not
  available in Mathlib and is not claimed by this specialization.
- Remark 7.41 is in `LocalFields/PadicComplexAlgebraicClosure.lean`: the
  completion of an algebraically closed characteristic-zero ultrametric
  normed field is algebraically closed, and the completed algebraic closure
  of `Q_p` is the concrete corollary.  Mathlib's dense-completion theorem does
  not yet provide the corresponding positive-characteristic generalization.
- Proposition 7.44 is in `LocalFields/NewtonPolygon.lean`.  Its exposed lower
  face at slope `s` is defined by the coefficient indices attaining the
  weighted Gauss norm at radius `exp (-s)`, with horizontal length given by
  the difference of the extreme indices.  Face lengths add under
  multiplication, a linear factor contributes one exactly at its root's
  value, and consequently the base face length equals the number of roots of
  that value in a splitting extension.  The characteristic-zero
  algebraic-closure theorem also proves that each root-value stratum descends
  to a polynomial over the base field, constructing the Galois structure
  internally and exporting no finite-dimensional splitting-field assumption.
- Example 7.45 is completed in
  `LocalFields/TwoAdicCubicSplitting.lean`: the displayed cubic is proved
  irreducible over `Q`, Hensel lifting constructs three roots in `Q_2` with
  additive valuations `0`, `1`, and `2`, and the polynomial is proved to
  split completely over both `Z_2` and `Q_2`.
- Proposition 7.50 is split between `LocalFields/UnramifiedResidueLift.lean`
  (existence) and `LocalFields/UnramifiedExtensions.lean` (order reflection,
  inverse reduction/lift laws, uniqueness, uniqueness up to algebra
  equivalence, and passage to fraction fields), with the literal embedded
  intermediate-field packaging in
  `LocalFields/MaximalUnramifiedExtension.lean`.  The result is packaged as
  an order isomorphism between finite formally unramified valuation
  subalgebras and finite separable residue intermediate fields, and also as
  an order isomorphism directly between finite unramified intermediate
  fields in the chosen algebraic closure and those residue fields.  Equal
  degrees over a finite residue field imply the required residue-field
  equivalence internally.  The converse `residue Galois -> field Galois` in
  part (b) is proved by lifting all distinct residue roots, proving that the
  integral minimal polynomial splits, and deducing normality of the fraction
  field extension.
- Corollaries 7.51--7.52 use
  `LocalFields/MaximalUnramifiedExtension.lean` and
  `LocalFields/LocalUnramifiedDecomposition.lean`.  The directed union of all
  finite formally unramified valuation rings now generates an actual
  intermediate field in the ambient fraction field.  It is the least field
  containing every finite unramified stage, and a finitely generated
  subfield lies in it exactly when it lies in one such stage.  For finite
  ambient residue degree, the maximal finite unramified subalgebra has the
  full residue image and the extension above it is totally ramified.  The
  prime-to-residue-characteristic roots-of-unity description in Corollary
  7.51 is an equality over a complete base DVR with finite residue field,
  even in a possibly infinite integral ambient algebra: the directed union
  of finite unramified stages is exactly the algebra generated by all roots
  of unity whose orders are units in the base.  Corollary 7.52 now has a named
  `K^un` inside a chosen algebraic closure and the same finite-subfield
  characterization.  Under the intended Henselian-DVR, perfect-fraction-field,
  and fixed-local-prolongation hypotheses, this is also packaged intrinsically:
  a finite embedded intermediate field is unramified exactly when it is
  contained in `K^un`.  The proof identifies its intrinsic integral model,
  proves that model is Dedekind and module-finite, and descends unramifiedness
  from a finite stage using unramifiedness at the maximal ideal.
  Its residue-algebraic-closure assertion is proved for every chosen maximal
  ideal of the integral closure above the base maximal ideal, which records
  the chosen prolongation of the valuation without assuming the entire
  integral closure is local.
- Example 7.54's finite-field input is in
  `LocalFields/FiniteFieldUnramifiedExample.lean`: for every positive `n` it
  constructs a finite formally unramified stage whose residue extension has
  degree `n`, and its embedded fraction field is proved to have degree `n`
  over the base fraction field.  Under the natural adic-completeness
  hypothesis, the lifted field is Galois with cyclic group; its canonical
  Frobenius reduces to `x |-> x^(#k)` and generates the group.
  `LocalFields/TeichmullerSplitting.lean` proves the full splitting-field
  assertion for `X^(q^n) - X`.  A Teichmuller lift of a primitive residue
  element generates the unramified valuation ring by residue-image
  uniqueness, and fraction-field surjectivity then shows that the same root
  generates the lifted field.
- Proposition 7.55 is in `LocalFields/TotallyRamifiedEisenstein.lean`.  Its
  final field-generator theorem now assumes only total ramification: an
  upstairs uniformizer has Eisenstein minimal polynomial and generates the
  fraction-field extension, with no exported separability or perfect-field
  assumptions.
- Theorem 7.58(a) is completed in `LocalFields/RamificationGroups.lean`.
  Inertia fixes every formally unramified integral stage pointwise; comparing
  residue degree with the inertia index identifies its fixed field with the
  fraction field of the maximal unramified stage.  This field is then proved
  greatest among the finite unramified intermediate fields.
- Propositions 7.60--7.63 are in `LocalFields/KrasnerLemma.lean`,
  `LocalFields/PolynomialStability.lean`, and
  `LocalFields/PadicGlobalization.lean`.  In the characteristic-zero
  algebraic-closure setting, normality and the Galois structure are now
  constructed internally for Krasner's lemma and the full nearby-root and
  root-field stability theorem.
- Remark 7.49 is in `LocalFields/LocalFieldClassification.lean`.  The
  positive-characteristic Laurent-series classification is assembled as a
  ring equivalence and a homeomorphism.  The final local-field statements
  assume only a nontrivially normed ultrametric locally compact field of
  characteristic `p`: completeness, the discrete valuation-ring property,
  and finiteness of the residue field are derived from local compactness.
  The equivalence maps the Laurent-series valuation ring onto the original
  valuation ring and identifies the two valuations up to heterogeneous
  valuation equivalence; the model fields are locally compact exactly for
  finite coefficient fields.  In characteristic zero, the
  restricted rational norm is proved nontrivial and Ostrowski supplies the
  unique prime `p`; completion then constructs a continuous injection
  `Q_p -> K`, and `K` is finite-dimensional for the induced algebra
  structure.  This is deliberately a continuous algebra rather than a
  `NormedAlgebra`: the original absolute value may be a positive power of the
  normalized `p`-adic one.  In the archimedean case the same completion
  method constructs a continuous real embedding, proves finite dimension,
  and concludes that the field is ring-isomorphic to `R` or `C`, with no
  preexisting real algebra structure.
- Remark 7.65 combines `LocalFields/FiniteExtensionClasses.lean`,
  `LocalFields/FiniteExtensionsFixedDegree.lean`, and
  `LocalFields/LocalUnramifiedDecomposition.lean`.  The unramified degree is
  proved to divide the total degree, unramified extensions with equal finite
  residue degree are isomorphic, and the abstract divisor-indexed cover is
  constructed from the unramified-degree invariant rather than assumed
  separately.  For actual fields embedded in one algebraic closure, the
  divisor-indexed theorem now proves each fiber finite from Proposition 7.64
  over the chosen unramified base and transports it back to the original base
  by restriction of scalars; the intrinsically decomposed family has a
  no-cover finiteness theorem.  The maximal-unramified construction packages
  total ramification and degree divisibility together.  The abstract maximal
  unramified DVR is identified with the norm-defined ring `𝒪[K_U]` by proving
  that both are the integral closure of the base valuation ring; Eisenstein
  polynomials and their evaluations are transported across this equivalence.
  Proposition 7.50 then identifies the canonical unramified fraction field
  literally with the selected normal degree-`m` base inside the fixed
  algebraic closure.  Finally,
  `embeddedLocalExtensionsOfFixedDegree_finite` places every degree-`n`
  embedded local extension in one of the finitely many divisor-indexed
  Eisenstein families, without assuming the former family-cover hypothesis.
  The final theorem
  `embeddedLocalExtensionsOfFixedDegree_finite_unconditional` has no
  selected-base, compatibility, or ambient nonarchimedean hypothesis.  The
  norm valuation ring of the chosen algebraic closure is proved Henselian and
  its residue field an algebraic closure of the base residue field.  This
  supplies each degree-`m` unramified base internally via Proposition 7.50
  and Example 7.54, while ultrametricity supplies nonarchimedeanness.

### Chapter 8

- Proposition 8.1 is in `Completions/PlaceFactorCorrespondence.lean`.  Its
  finite and archimedean place/factor correspondence now assumes only a
  finite separable extension, with no exported number-field structures.
- Exercise 8-2 is in `Completions/HigherRamificationCoefficient.lean`.  Its
  positive-index additive coefficient law is proved, and its arithmetic
  specialization gives an injection from each actual number-field quotient
  `G_i / G_(i+1)` for `i > 0` into the additive residue-field group.  The
  literal printed
  iff is false when `G_0 = G_1` (in particular for an unramified extension),
  so Lean proves the corrected statement: level-zero additivity is equivalent
  to triviality of the tame quotient, and obtains the printed iff under a
  nontrivial tame-quotient hypothesis.

- Propositions 8.1--8.2 are in `Completions/PlaceFactorCorrespondence.lean`
  and `Completions/CompletionTensorDecomposition.lean`.  The nonarchimedean
  statements have the book's generality.  The actual-completion archimedean
  product now also assumes only finite dimensionality and separability, not
  number-field structures.  Corollary 8.4's norm and trace comparison in
  `Completions/CompletionNormTrace.lean` has the same generality.
- Remark 8.3 is split between the Hensel power assertion and the
  finite-place/reduced-factor correspondence in
  `Galois/FinitePlacesAndReducedFactors.lean`.  An explicit commuting
  comparison with completed factors is not yet packaged; Mathlib's normalized
  finite places and exact extensions of a fixed absolute value use different
  powers of equivalent absolute values.
- Propositions 8.10--8.13 are in `Galois/DecompositionGroup.lean`,
  `Galois/DecompositionInertiaFields.lean`, and
  `Galois/DecompositionGroupTower.lean`.  Proposition 8.13(b) is assembled as
  an equality between the image of the upstairs stabilizer in `G/H` and the
  set of quotient elements whose representatives preserve the `H`-orbit of
  the prime.  This is the exact group-action content of the downstairs
  decomposition group without requiring a separate descended quotient-action
  instance.
- Propositions 8.14--8.17 are in `Galois/FrobeniusElement.lean`, including
  conjugation, the residue-degree power in a tower, restriction to a Galois
  intermediate field, and the compositum splitting criterion.  Examples
  8.18--8.19 are in `Galois/CyclotomicQuadraticFrobenius.lean`; besides the
  global Frobenius actions and quadratic reciprocity, this includes both the
  modulo-eight criterion for the Legendre symbol of `2` and ANT's displayed
  formula `(2/p) = (-1)^((p^2-1)/8)`.  For `p` not dividing the chosen
  cyclotomic level `n`, primes above `p` are proved unramified with residue degree
  `orderOf (p : ZMod n)`; the source's converse needs the usual conductor
  qualification because `Q(zeta_(2m)) = Q(zeta_m)` for odd `m`.
- Theorem 8.20 has coefficient descent and the stabilizer identification in
  `Galois/ResolventCoefficientDescent.lean`,
  `Galois/ResolventFactorDescent.lean`, and
  `Galois/ResolventGaloisGroup.lean`.  Irreducibility of the descended factor
  is the van der Waerden result cited without proof by ANT.
- Proposition 8.21 through Remark 8.29 are covered by the orbit-factor,
  Dedekind-cycle, real-place, permutation-group, and finite-field modules in
  `Galois/`.  In particular, `Galois/FiniteFieldIrreducibleFactors.lean`
  proves the noncomputational content of the `F_5` example in Remark 8.29:
  every distinct monic-irreducible factorization of `X^125-X` has five
  linear factors and forty cubic factors.  The PARI commands are omitted.
- Examples 8.25 and 8.27 include the final polynomial-Galois-group
  identifications in `Galois/QuinticX5SubXSub1GaloisGroup.lean` and
  `Galois/SymmetricGroupPolynomialGaloisGroup.lean`.  The required cycles are
  derived from the displayed modular factorizations rather than assumed, and
  the general Example 8.27 theorem now concludes `Gal(f) ~= S_n` directly.
- Definition 8.30 and the formalized consequences of Chebotarev in 8.32--8.40
  are in
  `Density/` and `Galois/CompositumDegreeCriterion.lean`, with the analytic
  Theorem 8.31 exposed as the explicit hypothesis
  `ChebotarevDensityTheorem`.  Remark 8.33 now has a qualitative uniform norm
  bound realizing every Frobenius conjugacy class that occurs; effective
  Chebotarev would make this bound computable from arithmetic data.  The
  cubic and quartic density tables are proved at the Frobenius-cycle level,
  and the cyclotomic and quadratic density statements, splitting-field
  criteria, finite/density-zero exceptional-set variants, and the reducible
  polynomial in Remark 8.40(d) are included.
  `Density/GassmannEquivalentFactorizations.lean` formalizes the mechanism in
  Remark 8.40(c): Gassmann-equivalent finite actions and subgroups have equal
  degrees and permutation characters, and Gassmann-equivalent polynomial root
  actions have identical factor-degree multisets at every prime away from the
  two discriminants.  The existence of a nonconjugate Gassmann pair realized
  over `Q` is not constructed; ANT supplies no example or proof there.
  For Remark 8.40(e),
  `Galois/NonsolvableGlobalLocalObstruction.lean` proves that every finite
  decomposition group in a nonsolvable Galois number field is proper, and
  derives this unconditionally from an identification with `S_n` for
  `n >= 5`.  `Completions/PrimitivePolynomialLocalReducibility.lean` proves
  that a proper completion-place stabilizer forces the minimal polynomial of
  a primitive element to become reducible over the corresponding completion.
  Together these give the claimed reducibility at every finite prime.  The
  same obstruction file proves the infinite-place case from the fact that an
  irreducible real polynomial has degree at most two.  Thus only the cited
  construction of such global `S_n`-extensions remains external, as in ANT.
  Example 8.34 is now stated in
  its literal arithmetic-progression form: the arithmetic Frobenius at a
  chosen prime above `p` maps to `[p]` under the cyclotomic Galois
  equivalence, its fibers are the rational congruence classes, and
  Chebotarev gives density `1 / phi(n)`.  For Examples 8.36--8.37,
  `Galois/DedekindFactorDegreePartition.lean` now assembles the rootwise
  Dedekind cycles into the full permutation partition, including fixed points,
  and identifies it with the normalized irreducible-factor degrees.
  `Density/PolynomialFactorizationDensities.lean` defines the literal prime
  sets by those degree multisets and proves their Chebotarev density as the
  proportion of Galois elements with the corresponding root partition.  It
  proves that the inseparable-reduction primes divide the nonzero polynomial
  discriminant and hence form a finite set, rewrites the conjugacy-class sum
  as an element count, and transports that count across an explicitly
  equivalent permutation representation.
  `Density/PolynomialFactorizationExampleDensities.lean` specializes this
  bridge to every named cubic and quartic action in the two examples and
  proves all of the displayed numerical rows for the literal factor-degree
  multisets.  `CommutativeAlgebra/RationalPolynomialIntegralModel.lean`
  clears denominators for an arbitrary nonzero polynomial in `Q[X]`, after
  passing to its monic associate and scaling its roots, and produces a monic
  integral polynomial of the same degree; it also proves that the rational
  primes dividing the chosen scaling denominator form a finite set.  The
  local algebra in
  `CommutativeAlgebra/ScaleRootsFactorization.lean` proves that scaling roots
  by a unit preserves irreducibility and the complete multiset of normalized
  factor degrees.  `CommutativeAlgebra/RationalPolynomialReduction.lean`
  defines the unscaled residue polynomial attached to the integral model and
  proves, away from the denominator primes, that it has exactly the same
  irreducible-factor degrees as the integral model.  The printed
  discriminant-based classification in Example 8.37 is incomplete under its
  literal hypothesis "no linear factor":
  `Density/QuarticSmallGroupDensities.lean` gives the omitted faithful `V₄`
  action on two quadratic orbits, proves it has no global fixed point, and
  exhibits an odd transposition.  Thus it belongs on the nonsquare side (as
  happens for `(X^2-2)(X^2-3)`).  The tables for every group action actually
  listed by ANT remain proved.
  Example 8.41 delegates its class-field-theory classification exactly as ANT
  does.
- Theorem 8.42 is closed in
  `GlobalFields/UnramifiedExtensionFinitenessFinal.lean`; Theorem 8.43 uses
  Mathlib's bounded-discriminant Hermite theorem.
- Exercise 8-1 is completed in
  `Completions/TwoAdicCubicFactorization.lean`, including the three 2-adic
  extensions and both discriminant divisibility conclusions.  Exercise 8-2
  is covered, with its necessary correction, in
  `Completions/HigherRamificationCoefficient.lean`.  Exercise 8-3 is omitted
  as the requested computational Galois-group problem.  Exercise 8-4 is in
  `GlobalFields/RationalFunctionProductFormula.lean`, which proves both the
  additive order identity and the normalized multiplicative product formula.
