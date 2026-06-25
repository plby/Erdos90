import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Towers.ClassField.CohomologyOps.IndMkOne
import Towers.ClassField.CohomologyOps.BotEquivFun
import Towers.ClassField.CohomologyOps.RegularCoefficientTwist
import Towers.ClassField.CohomologyOps.InjectiveModuleVanishing
import Towers.ClassField.CohomologyOps.ZeroCoinducedSucc
import Towers.ClassField.CohomologyOps.DimensionShiftingIso
import Towers.ClassField.CohomologyOps.ExtensionsSecondCohomology
import Towers.ClassField.CohomologyOps.NormalizedRepresentation
import Towers.ClassField.CohomologyOps.IsCocycle
import Towers.ClassField.CohomologyOps.ConnectingCocycle
import Towers.ClassField.CohomologyOps.HilbertNinetyCoboundary
import Towers.ClassField.CohomologyOps.CyclicHilbert
import Towers.ClassField.CohomologyOps.AdditiveRepresentation
import Towers.ClassField.CohomologyOps.GroupFiniteIso
import Towers.ClassField.CohomologyOps.Arbitrary
import Towers.ClassField.CohomologyOps.TimesTwoInt
import Towers.ClassField.CohomologyOps.FunctorialMapsGroup
import Towers.ClassField.CohomologyOps.QuotientActionSubgroup
import Towers.ClassField.CohomologyOps.DegreeZero
import Towers.ClassField.CohomologyOps.Corestriction
import Towers.ClassField.CohomologyOps.RestrictionZero
import Towers.ClassField.CohomologyOps.AllDegrees
import Towers.ClassField.CohomologyOps.ProjectiveComparison
import Towers.ClassField.CohomologyOps.RestrictionCompatibility
import Towers.ClassField.CohomologyOps.NatCardNsmul
import Towers.ClassField.CohomologyOps.FiniteGroupModule
import Towers.ClassField.CohomologyOps.InjPrimaryComponent
import Towers.ClassField.CohomologyOps.InflationRestrictionOne
import Towers.ClassField.CohomologyOps.AcyclicInflation
import Towers.ClassField.CohomologyOps.RestrictedCoinducedAcyclic
import Towers.ClassField.CohomologyOps.ShortComplexMap
import Towers.ClassField.CohomologyOps.NoPositiveOne
import Towers.ClassField.CohomologyOps.VanishingH1
import Towers.ClassField.CohomologyOps.DimensionShiftModule
import Towers.ClassField.TateCohomology.ProjectiveModuleVanishing
import Towers.ClassField.TateCohomology.IntegralGroupRing
import Towers.ClassField.TateCohomology.AddEquivAbelianization
import Towers.ClassField.Shifting.LowTateCohomology
import Towers.ClassField.Shifting.NormExactSequence
import Towers.ClassField.Shifting.BottomToTrivial
import Towers.ClassField.Shifting.AdditiveHomZero
import Towers.ClassField.Shifting.TateZero
import Towers.ClassField.Shifting.Rational
import Towers.ClassField.Shifting.RationalAllDegrees
import Towers.ClassField.Shifting.SubgroupCorestrictionInt
import Towers.ClassField.Shifting.GroupPeriodicityOdd
import Towers.ClassField.Shifting.CyclicTateShape
import Towers.ClassField.Shifting.FiniteCardUnit
import Towers.ClassField.Shifting.GeneratorSub
import Towers.ClassField.Shifting.KernelImageComplex
import Towers.ClassField.Shifting.SubsingletonLinearEquiv
import Towers.ClassField.Shifting.SolvableGroup
import Towers.ClassField.Shifting.SylowDetection
import Towers.ClassField.Shifting.SolvablePositive
import Towers.ClassField.Shifting.InducedCover
import Towers.ClassField.Shifting.NormTransitivity
import Towers.ClassField.Shifting.SolvableTateZero
import Towers.ClassField.Shifting.TateShift
import Towers.ClassField.Shifting.TateCover
import Towers.ClassField.Shifting.TransportAlongEquivalences
import Towers.ClassField.Shifting.TateCoverClosure
import Towers.ClassField.Shifting.SolvableNegOne
import Towers.ClassField.Shifting.TateLowerShift
import Towers.ClassField.Shifting.TateZeroTransfer
import Towers.ClassField.Shifting.AllDegrees
import Towers.ClassField.Shifting.RestrictionGenerator
import Towers.ClassField.Shifting.SplittingModule
import Towers.ClassField.Shifting.LowDegreeSequence
import Towers.ClassField.Shifting.DoubleShift
import Towers.ClassField.Shifting.Exceptional
import Towers.ClassField.Shifting.Augmentation
import Towers.ClassField.Shifting.AugmentationH1
import Towers.ClassField.Shifting.ShapiroNaturality
import Towers.ClassField.Shifting.BoundaryFormula
import Towers.ClassField.Shifting.BoundaryIso
import Towers.ClassField.Shifting.AssemblingShifts
import Towers.ClassField.Shifting.ZeroResTop
import Towers.ClassField.Shifting.RegularTensor
import Towers.ClassField.Shifting.TensorExact
import Towers.ClassField.Shifting.ExceptionalShift
import Towers.ClassField.Shifting.ExceptionalTateTransport
import Towers.ClassField.Shifting.TensorAcyclicity
import Towers.ClassField.Shifting.AssemblingTensorShift
import Towers.ClassField.Shifting.Recorded
import Towers.ClassField.Shifting.CyclicCupPeriodicity
import Towers.ClassField.Shifting.FundamentalClassEquiv
import Towers.ClassField.ProfiniteCohom.FilteredColimitExact
import Towers.ClassField.ProfiniteCohom.FixedOpenNormal
import Towers.ClassField.ProfiniteCohom.Cochains
import Towers.ClassField.ProfiniteCohom.CochainFactorization
import Towers.ClassField.Homological.ExtendedSnakeLemma
import Towers.ClassField.Homological.KernelCokernelComp
import Towers.ClassField.Homological.BaerOfDivisible
import Towers.ClassField.Homological.ModulesPIDInjectives
import Towers.ClassField.Homological.AdjointLeftExact
import Towers.ClassField.Homological.InjectiveResolutionComparison
import Towers.ClassField.Homological.RightZeroIso
import Towers.ClassField.Homological.ExtendInjectiveResolutions
import Towers.ClassField.Homological.ResolutionExtensionHomotopy
import Towers.ClassField.Homological.LongHomologySegment
import Towers.ClassField.Homological.RightIsoSelf
import Towers.ClassField.Homological.ProjectiveExtComparison
import Towers.ClassField.Homological.RepresentationsProjectives
import Towers.ClassField.Homological.GroupCohomologyPresentation
import Towers.ClassField.Homological.EnoughInjectives

/-!
# Milne, Class Field Theory, Chapter II

Mathlib already contains most of Chapter II, Section 1's foundations.
`Rep.equivalenceModuleMonoidAlgebra` identifies `G`-modules with modules over
the group ring and supplies the abelian category.  `Representation.coind` is
Milne's function-valued induced module (usually called coinduction in modern
terminology), with the restriction/coinduction adjunction and exactness.
`Section1.Remark13` proves Milne's finite-group induced-module trace is
surjective by constructing the explicit vector supported at the identity;
`Section1.Remark13ab` identifies coinduction from the trivial subgroup with
the regular representation tensored with the coefficient module and proves
that its restriction to a subgroup is again regular after regrouping along
a right transversal.
`Section1.Remark14` constructs the tensor-twisting isomorphism that identifies
the regular tensor a trivial underlying module with the diagonal tensor
action, including its formula on basis tensors.
`Section1.Statement17` proves the positive-degree vanishing for injective
coefficients by splitting the canonical embedding into a coinduced module
and applying Shapiro's lemma. `Section1.Corollary112` records the same Shapiro
vanishing for modules coinduced from the trivial subgroup.
`Section1.Remark113` proves the general connecting-map dimension-shifting
isomorphism and specializes it to the canonical short exact sequence
`0 -> M -> M_* -> M_dagger -> 0`.

Group cohomology, its inhomogeneous cochain complex, zeroth cohomology as
invariants, the long exact sequence, Shapiro's lemma, low-degree cocycles and
coboundaries, and the cyclic-group calculation are in the imported
`GroupCohomology` modules.  Noether's and Hilbert's Theorem 90 are in
`GroupCohomology.Hilbert90`. `Section1.Remark119` proves that every degree-two
class has a normalized cocycle representative by subtracting a constant
coboundary. `Section1.Example120` adds Milne's explicit iteration formula for
crossed homomorphisms. `Section1.Remark121` constructs the lifted cochain and
factored differential representing the connecting homomorphism.
`Section1.Proposition122` and `Section1.Corollary123` give the cohomological and
cyclic forms of Hilbert 90. `Section1.Proposition124` proves
the positive-degree vanishing for the additive Galois module of a finite
Galois extension using a normal basis and Shapiro's lemma.
`Section1.Proposition125` supplies the finite-product consequence of Milne's
product theorem, including the displayed binary direct-sum formula, while
`Section1.Proposition125Arbitrary` proves the full arbitrary-product statement
by comparing the degreewise cochain product and passing to homology.
`Section1.Remark126` gives a pointwise-surjective morphism of parallel pairs
whose induced map on equalizers is not surjective, exhibiting the failure of
exactness for inverse limits.
`Section1.Example127` constructs the compatible maps giving Shapiro evaluation,
restriction, inflation, and inner conjugation, and proves by Milne's
dimension-shifting induction that inner conjugation acts trivially in every
degree. `Section1.Remark128` constructs the resulting action on subgroup
cohomology and descends it to an actual representation of the quotient group.

`Section1.Example129` constructs corestriction in degree zero as the
transversal norm and proves independence of the transversal;
`Section1.Example129Corestriction` constructs cohomological corestriction in
every degree from inverse Shapiro and the finite-index coinduction trace.
`Section1.Proposition130` proves `Cor ∘ Res = (G : H)` in degree zero.  The
coefficient identity underlying the all-degree formula is proved in
`Section1.Proposition130AllDegrees`. `Section1.BarRestriction` constructs the
explicit subgroup map of bar resolutions, and
`Section1.ProjectiveResolutionComparison` transports its comparison homotopy
through linear-Yoneda cochains and `Ext`. Using these constructions,
`Section1.RestrictionShapiroCompatibility` proves that Mathlib's
inhomogeneous-cochain restriction is the Shapiro restriction and proves the
all-degree restriction--corestriction formula for the actual restriction map.
`Section1.Corollary131` proves that the order of a finite group annihilates its
positive-degree cohomology, and `Section1.Corollary132` proves finiteness for
finitely generated abelian coefficients. `Section1.ShapiroInjPrimary` proves the
book's Sylow primary-component injectivity for the actual restriction map.
`Section1.Proposition134` records the degree-one inflation-restriction
sequence, including injectivity of inflation and exactness at `H¹(G,M)`.
`Section1.RestrictedCoinducedAcyclic` proves that the canonical coinduced
dimension-shift module stays acyclic after restriction to an arbitrary
subgroup. Using this, `Section1.Proposition134Full` proves the complete
higher-degree inflation-restriction theorem under exactly Milne's
lower-degree vanishing hypothesis. `Section1.Proposition134Acyclic`
constructs the inflation/invariants adjunction and proves, by injective
dimension shifting, that `Hⁿ(G/H,M^H) ≅ Hⁿ(G,M)` in every positive degree
when the positive cohomology of `H` vanishes. Cup products remain unavailable.
`Section1.Remark135` records the actual exact initial Hochschild--Serre edge
sequence in degree one. `Section1.Example136` applies the full
inflation--restriction theorem in degree two under the Hilbert--90 vanishing
hypothesis, proving exactness and injectivity with the actual maps.
`Section1.Lemma137` proves the underlying-module splitting
`A_* ≃ A ⊕ A_†` used in Milne's dimension-shifting construction.

Mathlib's `GroupHomology` modules cover Section 2's definition, low degrees,
functoriality, long exact sequence, Shapiro lemma, and finite cyclic groups.
`Section2.Statement22` proves positive-degree homology vanishes for a
projective coefficient representation by splitting its induced-module cover.
`Section2.Lemma26` constructs the integral group-ring augmentation ideal and
proves the canonical equivalence `G^ab ≃ I_G / I_G^2`.
`Section2.Proposition27` specializes Mathlib's computation of `H₁` with
trivial coefficients to the canonical isomorphism `H₁(G, ℤ) ≃ Gᵃᵇ`.

Mathlib has no uniform Tate-cohomology functor. `Section3.Basic` constructs
the norm from coinvariants to invariants and defines Milne's exceptional
groups `H_T⁰` and `H_T⁻¹`; positive cohomology and negative homology remain
available separately through the imported ordinary theories.
`Section3.NormExactSequence` proves the displayed five-term sequence from
`H_T⁻¹` through coinvariants, invariants, and `H_T⁰` is exact.
`Section3.Proposition31` proves all exposed pieces of the induced-module
vanishing theorem: positive cohomology, degrees zero and minus one, and
positive homology. `Section3.Lemma33`
proves `H¹(G, ℤ) = 0`, while `Section3.Lemma33TateZero` identifies
`H_T⁰(G, ℤ)` with `ZMod |G|`; together these formalize Lemma 3.3(b).
`Section3.Lemma33Rational` proves the exceptional-degree cases of Lemma
3.3(a): the rational norm is bijective, so `H_T⁻¹` and `H_T⁰` vanish.
`Section3.Lemma33RationalAllDegrees` uses the source's averaging argument to
prove rational cohomology vanishes in every positive degree and then applies
the long exact sequence of `0 -> ℤ -> ℚ -> ℚ/ℤ -> 0` to construct the
canonical isomorphism `Hom(G, ℚ/ℤ) ≃ H²(G, ℤ)` from Lemma 3.3(c).
`Section3.Proposition32` proves that degree `-2` corestriction corresponds to
the inclusion-induced map on abelianizations, as in Proposition 3.2(a).
`Section3.Proposition34` proves two-periodicity for cyclic groups in positive
cohomological degrees, throughout the negative homological range, and across
the exceptional Tate degrees `0` and `-1`.
`Section3.Remark35CyclicCupPeriodicity` packages these ranges into one
unconditional two-shift for every integral `G`-module and proves that its
positive and degree-zero maps are cup product with the cyclic period class.
`Section3.Proposition36` defines
the Herbrand quotient, proves all three definedness implications in a short
exact sequence, and proves its multiplicativity using the exact hexagon of
the two-periodic cyclic Tate complex. `Section3.Lemma37` proves the
alternating-cardinality identity for arbitrary finite exact chains of finite
groups. `Section3.Proposition38` proves that every finite module has Herbrand
quotient one, and `Section3.Corollary39` proves that a homomorphism with finite
kernel and cokernel preserves both definedness and the value of the quotient.
`Section3.Theorem310Cyclic` proves the cyclic case of Theorem 3.10 in every
Tate range represented by the project: positive cohomology, degrees `0` and
`-1`, and positive homology. `Section3.Theorem310SolvableGroup` proves the
group-theoretic reduction for the solvable induction: a finite nontrivial
solvable group has a proper normal subgroup of strictly smaller order with
cyclic quotient. `Section3.Theorem310Transfer` proves the final
Sylow-detection step for ordinary cohomology: Shapiro restriction followed by
corestriction is multiplication by the subgroup index, so vanishing on all
Sylow subgroups implies vanishing on the ambient finite group. Completing the
intervening solvable induction is carried out in
`Section3.Theorem310SolvablePositive`, first for solvable groups and then for
arbitrary finite groups by Sylow detection. Thus Theorem 3.10 is complete in
all positive ordinary-cohomology degrees. `Section3.Theorem310InducedCover`
constructs Milne's induced short exact sequence and its positive-degree
dimension shifts after restriction to every subgroup. `Section3.Theorem310Norm`
proves transitivity of the norm across a normal subgroup, and
`Section3.Theorem310SolvableTateZero` uses it to complete the solvable case in
Tate degree zero. `Section3.Theorem310TateShift` packages the norm as a natural
transformation, applies the snake lemma to construct the cross-exceptional
shift `H_T⁻¹(G,X₃) ≅ H_T⁰(G,X₁)` for a short exact sequence whose
middle term vanishes in the two exceptional degrees.
`Section3.Theorem310TateCover` transports the exceptional vanishing across the
explicit restricted-induced-module isomorphism and specializes the shift to
Milne's cover as `H_T⁻¹(H,A) ≅ H_T⁰(H,A')`.
`Section3.Theorem310TateCoverClosure` proves from the low-degree exact sequence
that the cover kernel again has vanishing first and second cohomology over each
subgroup; `Section3.Theorem310Equiv` identifies this subgroup formulation with
arbitrary injective restrictions. `Section3.Theorem310SolvableNegOne` then
completes the solvable case in Tate degree minus one and, using the exceptional
`H₁ ≅ H_T⁻¹` boundary and the repeated positive-homology dimension shifts
from `Section3.Theorem310TateLowerShift`, in every negative Tate degree. Thus
the full solvable case is complete. `Section3.Theorem310TateZeroTransfer`
extends Sylow detection to Tate degree zero by proving that corestriction sends
a subgroup norm to the full group norm. Finally,
`Section3.Theorem310AllDegrees` repeats the cover argument over an arbitrary
finite group and proves Theorem 3.10 in every Tate range represented by the
project, with exactly Milne's hypothesis on literal subgroups.
`Section3.Theorem311RestrictionGenerator` formalizes the finite-order argument
beginning Tate's Theorem 3.11: the corestriction-restriction index formula
forces the restriction of the chosen degree-two generator to generate every
subgroup's degree-two cohomology.
`Section3.Theorem311SplittingModule` constructs the splitting module attached
to a normalized two-cocycle as `C ⊕ I_G`, verifies Milne's twisted action
formula directly from the cocycle identity, proves
`0 -> C -> C(φ) -> I_G -> 0` short exact, and proves that the chosen class
becomes zero in `H²(G,C(φ))`.
`Section3.Theorem311Augmentation` constructs and proves exact the augmentation
sequence `0 -> I_G -> ℤ[G] -> ℤ -> 0`, and computes the required
cohomological and homological acyclicity after restriction to every subgroup.
`Section3.Theorem311AugmentationH1` proves that the class of `h ↦ h - 1`
generates `H¹(H,I_G)` and is annihilated by `|H|`.
`Section3.Theorem311ShapiroNaturality` proves that Shapiro restriction is
natural in the coefficient module. `Section3.Theorem311BoundaryFormula`
evaluates the splitting boundary on the canonical augmentation cocycle, and
`Section3.Theorem311BoundaryIso` combines naturality, exactness, and the
finite-order calculation to prove that boundary is an isomorphism for every
subgroup.
`Section3.Theorem311Acyclic` formalizes the next long-exact-sequence step:
if `H¹(C) = 0`, `H²(I_G) = 0`, and the boundary
`H¹(I_G) -> H²(C)` is an isomorphism, then the splitting module has
vanishing first and second cohomology, both for the whole group and after
restriction to every subgroup.
`Section3.Theorem311DoubleShift` formalizes the final splice in all ordinary
positive cohomology and positive homology degrees: two adjacent short exact
sequences with acyclic middle terms give the required two-degree shift.
`Section3.Theorem311Exceptional` supplies the two exceptional inputs for
trivial integral coefficients: Tate degree minus one vanishes, while degree
zero is identified with `H²(G,C)` by the chosen generator.
`Section3.Theorem311Assemble` combines the two coefficient sequences into
equivalences in every Tate range represented by the project.
`Section3.Theorem311` is the unconditional range-wise statement of Theorem
3.11 under Milne's hypotheses, attached only to the chosen generator.
`Section3.Remark312RegularTensor` begins Remark 3.12 by identifying
the restricted diagonal module `ℤ[G] ⊗ M` with a module induced from the
trivial subgroup, and proves its Tate acyclicity in every represented range.
`Section3.Remark312TensorExact` proves that both halves of Tate's four-term
sequence remain short exact after tensoring with an arbitrary `G`-module;
the proof uses explicit underlying abelian-group retractions, so this step
does not require a flatness assumption.
`Section3.Remark312ExceptionalShift` proves the missing low-degree boundary
`H_T⁰(X₃) ≅ H¹(X₁)`, and `Section3.Remark312TateIso` proves that
representation isomorphisms transport both exceptional Tate groups.
`Section3.Remark312Acyclic` packages Tate acyclicity and records the standard
tensor-acyclicity and torsion-free Tor facts used without proof in Milne's
remark.  These are axioms because Mathlib's currently minimal categorical
`Tor` API has no Tor symmetry, flat-vanishing theorem, long exact sequence,
or connection to group cohomology. `Section3.Remark312Assemble` proves the
six-range splice from those inputs, and `Section3.Remark312` gives Remark
3.12 with exactly Milne's `Tor₁ᶻ(M,C)=0` hypothesis.
Remark 3.13 cannot yet be stated faithfully: Mathlib's group-cohomology API
does not currently define the cup product used there. `Section3.Example314`
formalizes the algebraic content of Example 3.14 by constructing the
fundamental-class isomorphism from `Gᵃᵇ` to degree-zero Tate cohomology and
its inverse, the abstract Artin map.  The local-field interpretation is left
to the later chapters where the required local fundamental class is proved.

`Section4.Lemma41` proves that filtered colimits of modules preserve exact
sequences and supplies the canonical comparison identifying the homology of
a filtered colimit of complexes with the filtered colimit of their homology.
Mathlib's continuous cohomology and profinite-group APIs cover Section 4's
basic definitions. `Section4.FixedByOpenNormal` proves that every element of
a discrete continuous profinite action is fixed by an open normal subgroup.
`Section4.Proposition42Cochains` then formalizes Milne's full cochain-level
compactness argument: a continuous cochain has finite image and explicitly
descends to a function on `(G/N)^r` with values in `M^N`.  The induced
cohomology comparison is not yet available because Mathlib explicitly leaves
the equivalence between its homogeneous continuous cochains and the usual
finite-arity continuous cochains as a TODO. `Section4.Proposition44Cochains`
proves the analogous cochain factorization through one stage of a directed
union of coefficient submodules.

The Appendix's general homological algebra is largely in Mathlib.
`Appendix.LemmaA1` exposes the extended snake lemma, including its two
endpoint extensions, and `Appendix.LemmaA2` exposes the exact
kernel-cokernel sequence of a composite. `Appendix.PropositionA3` proves
Baer's characterization that a module over a principal ideal domain is
injective exactly when it is divisible. `Appendix.PropositionA4` records
that modules over a principal ideal domain have enough injectives (using
Mathlib's stronger theorem for modules over any ring), and
`Appendix.PropositionA5` proves directly from the adjunction that a functor
with an exact left adjoint preserves injective objects. `Appendix.LemmaA6`
constructs injective resolutions and their comparison maps,
`Appendix.RemarkA7` identifies the zeroth right-derived functor of a left
exact functor with the functor itself, and `Appendix.PropositionA8` constructs
extensions to injective resolutions and proves their induced cohomology maps
are independent of the extension. `Appendix.LemmasA9A10` proves the sharper
comparison results Milne cites: an arbitrary exact augmented cochain
resolution maps to an injective resolution, and any two extensions are
homotopic; no injectivity is imposed on the source resolution.
`Appendix.PropositionA11` exposes exactness
and functoriality of every six-object window in the long exact homology
sequence, the engine underlying Milne's derived-functor sequence. Mathlib does
not yet provide the horseshoe construction connecting this to arbitrary
`Functor.rightDerived`, nor the cohomological-delta-functor uniqueness invoked
in Remark A.12; `Appendix.RemarkA12` records the available degree-zero and
injective-vanishing characterizations. `Appendix.PropositionA13` canonically
compares projective- and injective-resolution computations of Ext through
derived-category Ext. Finally, `Appendix.ExampleA14` and
`Appendix.RemarkA15` identify group cohomology with Ext from the trivial
representation and with the cohomology computed from any projective
resolution, Milne's formula (25). The local
`Appendix.EnoughInjectives` instance transfers enough injectives to `Rep k G`
through its equivalence with modules over the group ring.
-/
