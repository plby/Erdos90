import Towers.ClassField.UnramifiedCohom.UnitsModuloPrincipal
import Towers.ClassField.UnramifiedCohom.PrincipalUnits
import Towers.ClassField.UnramifiedCohom.FiniteFieldNorms
import Towers.ClassField.UnramifiedCohom.FiniteFieldTraces
import Towers.ClassField.UnramifiedCohom.CohomologicalReduction
import Towers.ClassField.UnramifiedCohom.Approximation
import Towers.ClassField.UnramifiedCohom.ValAddCarry
import Towers.ClassField.LocalClass.RegularLatticeCore
import Towers.ClassField.LocalClass.EquivariantExponentialTransfer
import Towers.ClassField.LocalClass.FiniteTrivialInt
import Towers.ClassField.LocalClass.Cardinality
import Towers.ClassField.LocalClass.LocalInvariantCorestriction
import Towers.ClassField.LocalClass.FundamentalClassCompatibility
import Towers.ClassField.LocalReciprocity.FiniteIndexCore
import Towers.ClassField.LocalReciprocity.DualityConclusion
import Towers.ClassField.LocalReciprocity.SubgroupHilbert90
import Towers.ClassField.LocalReciprocity.TateZeroQuotient
import Towers.ClassField.LocalReciprocity.LocalUnitsRep
import Towers.ClassField.LocalReciprocity.ArtinTowerCompatibility
import Towers.ClassField.LocalReciprocity.GlobalBrauer
import Towers.ClassField.LocalReciprocity.TransportedProduct
import Towers.ClassField.LocalReciprocity.Functoriality
import Towers.ClassField.LocalReciprocity.UniversePolymorphicArtin
import Towers.ClassField.LocalReciprocity.CyclotomicComparison
import Towers.ClassField.HilbertSymbols.QuadraticHilbert
import Towers.ClassField.HilbertSymbols.QuadraticSquareClasses
import Towers.ClassField.HilbertSymbols.NormCriterion
import Towers.ClassField.HilbertSymbols.KummerNormCriterion
import Towers.ClassField.HilbertSymbols.FiniteCharacter
import Towers.ClassField.HilbertSymbols.NondegeneracyCore
import Towers.ClassField.HilbertSymbols.Nondegeneracy
import Towers.ClassField.HilbertSymbols.PairingTheoreticCore
import Towers.ClassField.HilbertSymbols.FiniteCyclicExtension
import Towers.ClassField.LocalExistence.IsDivisibleSubgroup
import Towers.ClassField.LocalExistence.ClosedImagesKernels
import Towers.ClassField.LocalExistence.CompactNormFibers
import Towers.ClassField.LocalExistence.FiniteNormRoots
import Towers.ClassField.LocalExistence.SeparatingNormFamily
import Towers.ClassField.LocalExistence.ValuationClassification
import Towers.ClassField.LocalExistence.FinalCompactness
import Towers.ClassField.LocalExistence.FinalGroupArgument
import Towers.ClassField.LocalExistence.LocalExistence
import Towers.ClassField.LocalExistence.ConcreteLocalExistence

/-!
# Milne, Class Field Theory, Chapter III

Section 1 studies the cohomology of unramified extensions.  The local
`Section1.Proposition11` proves the complete cohomological reduction in
Proposition III.1.1: for a finite cyclic action, vanishing of `H¹` and
surjectivity of the norm imply vanishing in every Tate range represented by
the project. The remaining specialization to local units is precisely the
valuation splitting and unit-norm surjectivity inputs described below.
`Section1.Proposition12Approximation` formalizes the inductive heart of
Proposition III.1.2: an initial norm lift modulo the first unit filtration and
a one-layer correction at each stage give norm approximations modulo every
finite layer. Passing to an actual norm still requires compatibility of the
local norm with those quotient maps and convergence of the infinite product.
The continuous-cohomology Corollary 1.6 and the invariant-map results 1.7 and
1.8 still depend on the continuous-cochain comparison described in Chapter
II, Section 4. `Section1.Proposition19` resumes the finite algebra in
Proposition III.1.9: it constructs Milne's normalized cyclic carry factor set,
proves its cocycle identity, and proves the displayed norm product is the
chosen uniformizer. Identifying this calculation with the full Tate boundary
composite requires the unavailable uniform Tate functor.
`Section1.Lemma13Units` proves the first isomorphism of Lemma III.1.3:
reduction identifies the units modulo `1 + mathfrak m` with the units of the
residue field. `Section1.Lemma13PrincipalUnits` proves its second, purely
local-ring part: for `m > 0`, subtraction of one identifies successive
principal-unit quotients with `mathfrak m^m / mathfrak m^(m+1)`, and when
the maximal ideal is nonzero and principal it identifies this quotient with
the additive residue field.

`Section1.Lemma14` records the norm-surjectivity assertion for finite residue
field extensions, and `Section1.Lemma15` records positive-degree additive
cohomology vanishing together with trace surjectivity.  Mathlib does not yet
provide a uniform integer-indexed Tate-cohomology theory, so the all-degree
Tate formulations in Lemmas III.1.4 and III.1.5 are represented by these
ordinary-cohomology and norm/trace consequences.

Propositions III.1.1 and III.1.2 additionally require the complete local-field
unit filtration, its completeness, and compatibility of the field norm with
the successive quotient maps.  The invariant-map and fundamental-class
results later in Section 1 require continuous cohomology comparison and cup
product infrastructure not currently exported by Mathlib.

Section 2 extends the invariant theorem to ramified extensions.  The local
`Section2.Lemma23` clears a common denominator in a normal basis, constructs
its integral Galois-stable lattice, identifies that lattice with the regular
representation, proves it is open when the valuation integers are integral
over the base domain, and proves positive-degree cohomology vanishing.
`Section2.Lemma24` proves the categorical final step of Milne's next lemma:
any Galois-equivariant exponential isomorphism transports that vanishing to
the corresponding principal-unit subgroup. Constructing the required local
exponential/logarithm equivalence is not presently supported by Mathlib.
Theorem III.2.1 and Lemmas III.2.2, III.2.4, and III.2.6 additionally depend on
local-field invariant maps, exponential/logarithm on principal units, higher
inflation-restriction, or Galois invariance of the chosen valuation.
`Section2.Lemma25` proves the unconditional numerical part of Lemma III.2.5:
for a finite cyclic group, the Herbrand quotient of the trivial integral
representation is exactly the order of the group. The remaining passage from
the additive lattice to local units needs the missing equivariant local
exponential and logarithm. `Section2.Lemma26Cardinality` proves the finite
exact-sequence inequality `|B| ≤ |A||C|` used in Lemma III.2.6's induction;
the local application still requires higher inflation-restriction and the
solvability theorem for local Galois groups.

Section 3 constructs the local Artin map from Tate's theorem and the local
fundamental class. `Section3.Theorem31SourceStatement` now gives the finite
norm-residue isomorphism unconditionally: direct local `H²` cardinality at
the base and every fixed field supplies Tate's hypotheses.
`Section3.SubgroupHilbert90` proves the remaining subgroupwise Hilbert 90 by
the twisted-trace argument, and `Section3.TateZeroNormQuotient` identifies
degree zero with `Kˣ / N_{L/K}(Lˣ)`. `Section3.LocalTowerCompatibility` proves both tower
diagrams by explicit left- and right-coset cocycle calculations.
`Section3.Lemma33` proves compatibility under quotient restriction by the
corrected character argument through Proposition III.3.6, packages the
canonical finite Artin maps as a compatible reciprocity family, and
assembles their inverse limit in the abelianized absolute Galois group.  It
then identifies every finite abelian subextension with a finite level of
that inverse system and instantiates Corollary I.1.2, yielding the full local
norm correspondence for the assembled Artin map.  Proving Frobenius
normalization remains.
`Section3.Theorem35Core` nevertheless proves the final
group-theoretic step in the Galois case of norm limitation: nested norm
subgroups of the same finite index are equal. `Section3.Lemma37` proves the
final duality step in Lemma III.3.7: `ℚ / ℤ`-valued characters separate the
elements of an abelian group, so equality of every character value implies
that the Artin image is the asserted integer power of Frobenius.
`Section3.Proposition36` proves Proposition III.3.6 itself: the finite local
Artin map is adjoint to cup product with the character boundary.  The proof
reduces at each Artin symbol to its generated cyclic subgroup and combines
the explicit cyclic carry calculation with projection and
restriction--corestriction.
`Section3.PadicCyclotomicLocalArtinComparison` places that cohomological map
in the concrete prime-power cyclotomic Lubin--Tate root fields.  It proves
unconditionally that the uniformizer `p` has trivial Artin image, transports
this formula and the fixed quotient-unit orbit to every cyclotomic field
model, and shows that the sole remaining unit comparison is literally
equivalent to one explicit norm-residue equation.  The elementwise
degree-minus-two API now rewrites that equation as the cyclic product of the
canonical local fundamental cocycle.

Section 4 develops the Hilbert symbol. `Section4.QuadraticHilbert` formalizes
the elementary algebraic core of Milne's special case `K = ℚ_p`, `n = 2`: the
defining conic condition is symmetric, is unchanged by multiplying either
coefficient by a nonzero square, and for a nonsquare first coefficient is
equivalent to the quadratic norm equation. That equation is identified with
the norm formula in `QuadraticAlgebra K a 0`. The file also defines the resulting
`{±1}`-valued quadratic indicator and proves its symmetry, square invariance,
basic unit identities, and norm-equation criterion. Bilinearity and local
nondegeneracy of this particular conic indicator remain separate from the
general Kummer--Artin construction below.
`Section4.QuadraticSquareClasses` proves that the indicator is well-defined
on `Kˣ` modulo nonzero squares in both variables and remains symmetric there.
`Section4.NormCriterion` proves the cyclic representation-theoretic core
of Step 1's boxed equivalence: under the period isomorphism, a class vanishes
exactly when its invariant representative belongs to the norm image.
`Section4.KummerNormCriterion` proves the Kummer field-theory input used in Step 2 and
Theorem III.4.4(d): the relevant splitting field is cyclic Galois of degree
`n`, with an explicit generator acting on the chosen root by multiplication
by the primitive root of unity.
`Section4.Proposition43FiniteCharacter` proves Proposition III.4.3 at every
finite abelian level: Proposition III.3.6 turns vanishing of the cup pairing
into vanishing on all finite local Artin symbols, and their surjectivity forces
the finite character to be zero. `Section4.Proposition43Density` also records
the corresponding abstract dense-image argument.
`Section4.Theorem44Core` proves the kernel argument in Theorem III.4.4:
skew-symmetry transports left nondegeneracy to right nondegeneracy.
`Section4.Theorem44Nondegeneracy` supplies the substantive Kummer argument.
For every power class it constructs its cyclic multiradical extension,
factors local reciprocity through the power-class quotient, and combines
Artin surjectivity with the perfect Kummer pairing to prove the left kernel
trivial. In characteristic zero it constructs the full Kummer--Artin Hilbert
pairing, proves bilinearity, and proves both kernels trivial.
`Section4.Proposition41` proves the abstract pairing-theoretic deduction and
its quadratic specialization. `DDensit.PolarDirichletBridge` now
gives the literal characteristic-zero local-field result for positive `n`:
it bundles every one-class Kummer field as a cyclic extension of degree
dividing `n`, applies the universal norm hypothesis and the Kummer norm
criterion, and uses right nondegeneracy to force an `n`th power.

Section 5 proves the local existence theorem. `Section5.Remark52` formalizes
the preliminary abstract finite-index observations: divisible subgroups lie
in every finite-index subgroup, finite intersections and the relevant
subgroup products retain finite index, and the final subgroup containment
holds. `Section5.ClosedNormImagesCompactKernels` proves Step 1's topological argument that
an open homomorphic image is closed and a closed kernel inside a compact unit
set is compact. `Section5.CompactNormFibers` proves Step 2's full filtered
compact-fiber image equality. `Section5.FiniteNormRoots` proves Step 3's
filtered finite-root intersection and norm-of-a-power calculation.
`Section5.SeparatingNormFamily` proves Step 4's final subgroup-lattice
argument, while `Section5.ValuationSubgroupClassification` classifies finite-index
subgroups containing the valuation kernel as inverse images of `nℤ`, with
`n > 0`. `Section5.FinalCompactness` proves the final compact-unit extraction
of a candidate norm group, and `Section5.Theorem51Final` assembles Milne's
last subgroup argument under the three norm-family closure properties.
`Section5.Theorem51` completes the source-facing theorem: a directed compact
family produces a norm preimage lying in every finite Galois relative norm
subgroup, the full Kummer extension forces that preimage to be an `n`th
power, and its norm supplies the roots proving divisibility of the common
finite-abelian norm subgroup.
`Section5.ConcreteLocalExistence` connects these abstract arguments to the
actual family of finite abelian norm groups.  It proves that every
finite-index subgroup containing the local units is a canonical unramified
norm group, proves that the common finite-abelian norm subgroup lies in the
local units, and derives the full Local Existence Theorem from local
reciprocity and divisibility of that common norm subgroup.  Corollary I.1.2
now supplies the norm correspondence internally.
-/
