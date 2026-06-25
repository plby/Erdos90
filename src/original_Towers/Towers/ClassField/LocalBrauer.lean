import Towers.ClassField.LocalBrauer.RingMulComm
import Towers.ClassField.LocalBrauer.RealNumbers
import Towers.ClassField.LocalBrauer.RealCrossedProduct
import Towers.ClassField.LocalBrauer.RealH2
import Towers.ClassField.LocalBrauer.RealBrauerGroup
import Towers.ClassField.LocalBrauer.LocalField
import Towers.ClassField.LocalBrauer.LocalFieldOrder
import Towers.ClassField.LocalBrauer.FieldAdicOrder
import Towers.ClassField.LocalBrauer.FieldNormExtension
import Towers.ClassField.LocalBrauer.FiniteLocalExtension
import Towers.ClassField.LocalBrauer.FiniteExtensionOrder
import Towers.ClassField.LocalBrauer.FiniteExtensionNorm
import Towers.ClassField.LocalBrauer.FiniteExtensionData
import Towers.ClassField.LocalBrauer.SpectralIntegerClosure
import Towers.ClassField.LocalBrauer.SpectralIntegerTower
import Towers.ClassField.LocalBrauer.LocalDivisionAlgebra
import Towers.ClassField.LocalBrauer.DivisionSubfieldDegree
import Towers.ClassField.LocalBrauer.DivisionAlgebraNorm
import Towers.ClassField.LocalBrauer.DivisionAbsoluteValue
import Towers.ClassField.LocalBrauer.AlgebraAbsoluteValue
import Towers.ClassField.LocalBrauer.DivisionAlgebraOrder
import Towers.ClassField.LocalBrauer.DivisionOrderDenominator
import Towers.ClassField.LocalBrauer.DivisionAlgebraRamification
import Towers.ClassField.LocalBrauer.RamificationIndex
import Towers.ClassField.LocalBrauer.DivisionIdealPowers
import Towers.ClassField.LocalBrauer.DivisionIdealProduct
import Towers.ClassField.LocalBrauer.DivisionAlgebraIntegers
import Towers.ClassField.LocalBrauer.DivisionIntegers
import Towers.ClassField.LocalBrauer.DivisionAlgebraIntegrality
import Towers.ClassField.LocalBrauer.DivisionIntegerModule
import Towers.ClassField.LocalBrauer.DivisionResidueField
import Towers.ClassField.LocalBrauer.DivisionResidueExtension
import Towers.ClassField.LocalBrauer.ResidueDegreeBound
import Towers.ClassField.LocalBrauer.ResidueGeneratorSubfield
import Towers.ClassField.LocalBrauer.DivisionDegreeFormula
import Towers.ClassField.LocalBrauer.UnramifiedMaximalSubfield
import Towers.ClassField.LocalBrauer.DivisionAlgebraStructure
import Towers.ClassField.LocalBrauer.DivisionAlgebraInvariant
import Towers.ClassField.LocalBrauer.CyclicCarryCocycle
import Towers.ClassField.LocalBrauer.UnramifiedExtensionExistence
import Towers.ClassField.LocalBrauer.UnramifiedExtensionGalois
import Towers.ClassField.LocalBrauer.UnramifiedIntermediateField
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedTower
import Towers.ClassField.LocalBrauer.FiniteFieldRestriction
import Towers.ClassField.LocalBrauer.CanonicalRamification
import Towers.ClassField.LocalBrauer.SpectralUnramifiedOrder
import Towers.ClassField.LocalBrauer.UnramifiedBrauerCofinality
import Towers.ClassField.LocalBrauer.IntegralModelUniqueness
import Towers.ClassField.LocalBrauer.IntegralGeneratorReduction
import Towers.ClassField.LocalBrauer.IntegralModelFrobenius
import Towers.ClassField.LocalBrauer.GenericFrobeniusSplitting
import Towers.ClassField.LocalBrauer.CofinalityUnconditional
import Towers.ClassField.LocalBrauer.UnramifiedNormSurjectivity
import Towers.ClassField.LocalBrauer.UnramifiedNormOrder
import Towers.ClassField.LocalBrauer.CanonicalNormData
import Towers.ClassField.LocalBrauer.PrincipalNormApproximation
import Towers.ClassField.LocalBrauer.SpectralNormData
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedData
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedFrobenius
import Towers.ClassField.LocalBrauer.CanonicalFrobeniusRestriction
import Towers.ClassField.LocalBrauer.UnitH2
import Towers.ClassField.LocalBrauer.CyclicH2
import Towers.ClassField.LocalBrauer.CohomologyTransport
import Towers.ClassField.LocalBrauer.UnramifiedH2
import Towers.ClassField.LocalBrauer.UnramifiedFiniteInvariant
import Towers.ClassField.LocalBrauer.FiniteInvariantCompatibility
import Towers.ClassField.LocalBrauer.LocalInvariantTorsion
import Towers.ClassField.LocalBrauer.InvariantTorsionLimit
import Towers.ClassField.LocalBrauer.InvariantLimitAssembly
import Towers.ClassField.LocalBrauer.BrauerCofinalLimit
import Towers.ClassField.LocalBrauer.InvariantAssembly
import Towers.ClassField.LocalBrauer.CanonicalCarryInflation
import Towers.ClassField.LocalBrauer.CyclicCarryRestriction
import Towers.ClassField.LocalBrauer.ConcreteInflationBasic
import Towers.ClassField.LocalBrauer.ConcreteInflationComparison
import Towers.ClassField.LocalBrauer.GaloisCarryRestriction
import Towers.ClassField.LocalBrauer.ConcreteInflationMorita
import Towers.ClassField.LocalBrauer.CyclicFiniteStrictification
import Towers.ClassField.LocalBrauer.CanonicalInvariantAssembly
import Towers.ClassField.LocalBrauer.CanonicalUnconditional
import Towers.ClassField.LocalBrauer.CanonicalCarryUnconditional
import Towers.ClassField.LocalBrauer.FiniteExtensionRamification
import Towers.ClassField.LocalBrauer.InvariantBaseChange
import Towers.ClassField.LocalBrauer.FiniteRelativeCardinality
import Towers.ClassField.LocalBrauer.H2Cardinality
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedRelative
import Towers.ClassField.LocalBrauer.DivisionOrder
import Towers.ClassField.LocalBrauer.CanonicalCarryMul

/-!
# Milne, Class Field Theory, Chapter IV, Section 4

This section computes Brauer groups of special fields.

`Theorem41` records Wedderburn's little theorem from Mathlib and its
finite-field Brauer consequence. `RealNumbers` proves that Hamilton's
quaternions form a four-dimensional central simple real algebra.
`RCProduc` constructs Milne's explicit factor set for
`Complex/Real`, proves it is a normalized multiplicative `2`-cocycle, and
identifies its crossed product with Hamilton's quaternions.
`RealH2` proves directly that `H²(Gal(Complex/Real), Complexˣ)` is cyclic of
order two, with Milne's factor set as its nonzero class. `RealBrauerGroup`
transports this calculation to `Br(Real)`, identifies the nonzero class with
Hamilton's algebra, and proves that every central simple real algebra is a
matrix algebra over either `Real` or the Hamilton quaternions.
`LocalField` records the discrete value group, ring of integers, finite
residue field, and ultrametric valuation supplied by Mathlib's
`IsNonarchimedeanLocalField` API. `LocalFieldAdicOrder` identifies its
normalized order with the normalized adic order on the valuation DVR.
`LocalFieldNormExtension` packages the
spectral norm and proves that the local absolute value extends uniquely to
every finite commutative field extension. `FLExt` equips such
an extension with its canonical spectral topology and proves that it is again
a nonarchimedean local field; `FiniteLocalExtensionOrder` proves that its
normalized order is invariant under all base-field automorphisms.
`FiniteLocalExtensionNorm` proves that the field norm preserves the canonical
valuation integers and constructs the resulting continuous norm map on
integer-unit groups.
`FiniteLocalExtensionNormData` packages those results into the local norm
data used by successive approximation, reducing its remaining input to the
residue norm and the principal-unit corrections supplied by trace
surjectivity. `SpectralIntegerIntegralClosure` identifies the spectral
valuation integers with the integral closure of the base valuation ring.
`LocalDivisionAlgebra` proves
Milne's degree bound for commutative subfields and for the subfield generated
by one element inside a finite-dimensional central division algebra;
`DivisionSubfieldDegree` strengthens the bound to divisibility by the degree
of the division algebra.
`DivisionAlgebraNorm` constructs the determinant-root absolute-value
candidate, proves its multiplicative and scalar-extension laws, and proves
the determinant tower formula on commutative subfields.
`DivisionAlgebraAbsoluteValue` identifies that candidate with the spectral
norm on every one-generated subfield and uses this to prove the full
ultrametric inequality. `LocalDivisionAlgebraAbsoluteValue` specializes the
result to a unique nonarchimedean extension of the absolute value from a
local field to every finite-dimensional division algebra.
`LocalDivisionAlgebraOrder` constructs the normalized rational additive
valuation on the whole division algebra, proves its ultrametric inequality,
and shows that it extends the normalized integer order on the center.
`DivisionAlgebraOrderDenominator` proves Milne's sharper assertion that, for
an algebra of dimension `n²`, all nonzero orders lie in `(1/n)ℤ`.
`DivisionAlgebraRamification` identifies the full value group as `(1/e)ℤ`
for a positive divisor `e` of `n`.
`RamificationIndex` packages this generator as `ramificationIndex K D` and
records the arithmetic consequence of the later identity `ef = n²`.
`DivisionAlgebraIdealPowers` proves the API-native form of Milne's ideal
classification: every nonzero two-sided ideal is the principal ideal of a
least-order element, equivalently an order-threshold ideal.
`DivisionAlgebraIdealProduct` supplies the missing multiplication API for
two-sided ideals, proves that every nonzero ideal is a power of the maximal
ideal, and establishes Milne's identity `P^e = ϖ_K O_D`.
`DivisionAlgebraIntegers` constructs the noncommutative ring of integers and
its maximal two-sided ideal, proves the unit criterion, and makes the residue
quotient into a division ring.
`LocalDivisionAlgebraIntegers` identifies these two objects with the
nonnegative and positive loci of the additive order.
`DivisionAlgebraIntegrality` proves that the integer ring consists exactly of
the elements integral over the valuation ring of the center.
`DivisionIntegerModule` proves that this ring is a finite free lattice over
the base integer ring, with rank equal to the dimension of the division
algebra over its center.
`DivisionResidueField` proves that this quotient is finite by compactness of
the unit ball, and then applies Wedderburn's little theorem to make it a field.
`LocalDivisionResidueExtension` constructs the embedding of the base residue
field, proves the residue extension finite-dimensional, and defines its
residue degree.
`ResidueDegreeBound` proves Milne's inequality `f ≤ n` by lifting a primitive
residue generator and reducing its integral minimal polynomial.
`ResidueGeneratorSubfield` proves that, once `f = n`, such a lift generates a
maximal commutative subfield which splits the division algebra.
`DivisionAlgebraDegreeFormula` carries out Milne's filtration argument and
proves `[D : K] = ef`: the successive quotients by powers of the maximal
ideal all have the cardinality of the division residue field, while finite
freeness of `O_D` over `O_K` computes the final scalar quotient.
`UnramifiedMaximalSubfield` strengthens this by retaining the integral
minimal polynomial and proving that the corresponding integer algebra is
formally unramified and unramified at its maximal ideal.
`LocalDivisionAlgebraStructure` combines the degree formula with `e,f ≤ n`,
proves `e = f = n`, and obtains an unramified maximal commutative subfield
which splits the division algebra.
`LocalDivisionAlgebraInvariant` defines the implementer order in `ℚ/ℤ`,
proves independence from the Skolem--Noether implementer under the
unramified integral-order condition, and proves invariance under algebra
isomorphism.
`LocalInvariantTorsion` identifies the subgroup of `ℚ/ℤ` killed by `n` with
`ZMod n`, by sending `m` to `m/n` modulo integers.
`LocalInvariantTorsionLimit` proves that the direct limit of these subgroups
along the cofinal factorial degrees is the whole local invariant group.
`CanonicalUnramifiedRelativeBrauer` identifies every canonical degree-`n`
relative Brauer group with `ZMod n`, proves every class killed by `n` lies in
it, and identifies its order-`n` classes as coprime powers of the carry class.
`LocalDivisionBrauerOrder` proves that the period of a local central division
algebra equals its degree, that equality of period and degree forces a central
simple algebra to be a division algebra, and that the division degree divides
the degree of every finite splitting field.
`Example42` constructs the cyclic carry cocycle, proves its two multiplication
rules, the coefficient-twisting rule, Milne's relation `e₁ⁿ = π`, and the
resulting order calculation `ord(e₁) = 1/n`.
`UnramifiedExtensionExistence` constructs an unramified extension of every
positive degree from a separable irreducible residue polynomial.
`UnramifiedExtensionGalois` refines the construction using a Hensel factor of
`X^(q^n)-X`, proves that its fraction field is Galois and cyclic, and lifts
arithmetic Frobenius to a generator of order `n`.
`UnramifiedIntermediateField` embeds each such extension in a fixed separable
closure while retaining its degree and cyclic Galois structure.
`CanonicalUnramifiedTower` generates canonical levels by the roots of
`X^(q^n)-X`, proves divisibility nesting, proves that the level has degree
exactly `n` and cyclic Galois group, and packages the factorial tower used by
the direct limit.
`FiniteFieldFrobeniusRestriction` proves the Frobenius power law in a tower
of finite fields and its naturality through reduction-induced Galois
equivalences. `CanonicalUnramifiedFrobenius` defines arithmetic Frobenius on
each canonical level as the unique lift of residue Frobenius and proves that
it generates the Galois group.
`CanonicalUnramifiedRamification` proves that an unramified finite local DVR
model has ramification index one and derives the resulting restriction
formula for normalized adic order.
`SpectralUnramifiedOrder` transports finite freeness, formal unramifiedness,
and that order formula from an integral model to the spectral integers.
`UnramifiedBrauerCofinality` proves that uniqueness of finite unramified
extensions is the only remaining input needed for Brauer cofinality: from
that statement it derives, via the division representative and its
unramified maximal splitting subfield, that every Brauer class is split at a
factorial canonical level.
`UnramifiedIntegralModelUniqueness` proves that the field generated by an
integral unramified model is its fraction field, derives separability after
localization, and identifies it with the canonical level once the canonical
Frobenius polynomial is shown to split there.
`UnramifiedIntegralGeneratorReduction` proves that reduction of the integral
minimal polynomial of a primitive generator is irreducible and separable and
retains the full field degree.
`UnramifiedIntegralModelFrobenius` proves the adic completeness and Henselian
infrastructure for finite free unramified integral models.
`GenericUnramifiedFrobeniusSplitting` applies Teichmuller lifting to split
`X^(q^n)-X` in every such model, independently of its presentation.
`UnramifiedBrauerCofinalityUnconditional` combines these results to prove
uniqueness of finite unramified extensions and unconditional cofinality of
the factorial canonical tower for splitting Brauer classes.
`UnramifiedNormSurjectivity` proves unit-norm surjectivity from the residue
norm and trace identities by successive approximation and compactness.
`UnramifiedNormOrder` derives the normalized-order formula for field norms
from ramification index one and invariance under the Galois action.
`CanonicalUnramifiedNormData` proves the residue norm and Galois-product
identities, while `UnramifiedPrincipalNormApproximation` carries out the
trace-one correction on every positive principal-unit layer.
`SpectralUnramifiedNormData` transports these facts to spectral integers,
and `CanonicalUnramifiedLocalData` supplies the resulting norm and order data
at every canonical level. `UnramifiedUnitH2` then proves Milne's explicit
vanishing `H²(Gal(L/K), O_L^x) = 0` for those levels.
`CyclicH2`, `CohomologyTransport`, and `UnramifiedCyclicH2` identify the
relative Brauer group at an unramified cyclic degree-`n` level with `ZMod n`,
with the carry crossed product as generator.
`UnramifiedFiniteInvariant` identifies this relative Brauer group with the
`n`-torsion subgroup of `ℚ/ℤ` and sends the carry class to `1/n`.
`UnramifiedFiniteInvariantCompatibility` proves the factorial torsion
inclusion formula and reduces compatibility of all finite-level invariants to
the concrete inflation formula for the carry class.
`CanonicalUnramifiedCarryInflation` constructs coherent cyclic coordinates
on the canonical factorial tower. `ConcreteInflationBasic` defines cochain
inflation, `ConcreteInflationComparison` proves the carry-power calculation,
and `ConcreteInflationMorita` identifies cochain inflation with abstract
Brauer inflation through the standard Morita bimodule.
`LocalInvariantLimitAssembly` proves the formal last step: any compatible
family of these finite-level identifications assembles to `ℚ/ℤ`.
`BrauerCofinalLimit` identifies the direct limit of any cofinal monotone
sequence of relative Brauer groups with the absolute Brauer group.
`LocalBrauerInvariantAssembly` composes these two direct-limit results into
the resulting equivalence `Br(K) ≃ (ℚ/ℤ)` and records its finite-level formula.
`CanonicalLocalInvariantAssembly` packages the unconditional arithmetic
finite invariants. `CIStrict` gives a second,
purely cyclic proof of transition compatibility, and
`CanonicalLocalInvariantUnconditional` uses it with Brauer cofinality to
construct an unconditional equivalence `Br(K) ≃ (ℚ/ℤ)`.
`CanonicalCarryInvariantUnconditional` strengthens this to the original
carry-normalized finite invariants: it proves their compatibility using the
explicit carry cocycle and Morita comparison, assembles them to
`Br(K) ≃ (ℚ/ℤ)`, and sends the canonical degree-`n` carry class to `1/n`.
`Remark44` records that this invariant is a homomorphism, computes the
invariant of the `i`-th power of the carry crossed product as `i/n`, proves
coprime carry powers are division algebras, and classifies every local central
division algebra as the base field or a canonical coprime carry crossed product,
with exponents unique modulo `n`. It also reduces the splitting and polynomial
root claims in part (c) to the cited Chapter III base-change formula.
`FiniteLocalExtensionRamification` proves that normalized order in an
arbitrary finite extension, equipped with its spectral local-field structure,
scales by the ramification index, and for finite separable extensions proves
that the ramification index times the residue degree is the field degree.
`LocalInvariantBaseChange` packages formula (29), proves that it composes
through a field tower, and exposes its canonical spectral-topology form.
`FiniteLocalRelativeBrauerCardinality` gives the universe-polymorphic,
relative-only consequence: formula (29) identifies the relative Brauer group
with the degree-torsion subgroup of `ℚ/ℤ` and computes its cardinality.
`FiniteLocalH2Cardinality` proves that formula (29) identifies the relative
Brauer group with the degree-torsion subgroup of `ℚ/ℤ`. It upgrades this to
an explicit equivalence between categorical `H²(Gal(L/K), Lˣ)` and
`ZMod [L : K]`, constructs the finite local fundamental class, proves that it
generates `H²`, and obtains the cardinality input required by Tate's
construction of local reciprocity.
`CyclicCarryRestriction` proves that the standard carry cocycle restricts
unchanged to the cyclic subgroup obtained by multiplying indices by the
subgroup index. `GaloisCarryRestriction` transports this calculation to
finite Galois cohomology and, through the Mackey--Morita restriction square,
to relative Brauer groups.
`Remark44` uses that form to derive the splitting and polynomial-root claims
without a Galois hypothesis. Proving formula (29) itself now requires
arithmetic-Frobenius-normalized cyclic coordinates for the canonical
unramified towers over both fields and their compatibility under base change.
-/
