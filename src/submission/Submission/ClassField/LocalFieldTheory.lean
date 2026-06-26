import Submission.ClassField.LocalFields.NormSubgroups
import Submission.ClassField.NormCorrespondence.SubgroupOpenClosed
import Submission.ClassField.LocalFields.ArchimedeanPlaces
import Submission.ClassField.NormCorrespondence.FiniteIndexOpen
import Submission.ClassField.NormCorrespondence.LocalStatements
import Submission.ClassField.NormCorrespondence.LocalStatement
import Submission.ClassField.NormCorrespondence.ExistenceConsequences
import Submission.ClassField.NormCorrespondence.Statement
import Submission.ClassField.NormCorrespondence.Main
import Submission.ClassField.NormCorrespondence.OpenIndexSubgroup
import Submission.ClassField.NormCorrespondence.UnramifiedFrobenius
import Submission.ClassField.NormCorrespondence.PrincipalUnitQuotients
import Submission.ClassField.NormCorrespondence.StandardOpenSubgroups
import Submission.ClassField.NormCorrespondence.UnramifiedNormGroups
import Submission.ClassField.NormCorrespondence.TotalAndUnramified
import Submission.ClassField.NormCorrespondence.PrimeElementsGenerate
import Submission.ClassField.NormCorrespondence.LocalUniqueness
import Submission.ClassField.NormCorrespondence.LubinTateGeneration
import Submission.ClassField.NormCorrespondence.FiniteLevelArgument
import Submission.ClassField.NormCorrespondence.GroupClassification
import Submission.ClassField.NormCorrespondence.ExistenceLubinTate
import Submission.ClassField.FormalGroups.CompositionalInverse
import Submission.ClassField.FormalGroups.PowerEvalAdic
import Submission.ClassField.FormalGroups.IdempotentSeries
import Submission.ClassField.FormalGroups.FormalGroupLaw
import Submission.ClassField.FormalGroups.FormalGroupEvaluation
import Submission.ClassField.FormalGroups.AdicSubstitutionEvaluation
import Submission.ClassField.FormalGroups.AdicFormalGroup
import Submission.ClassField.FormalGroups.AdicGroupHom
import Submission.ClassField.FormalGroups.AdicHomRing
import Submission.ClassField.FormalGroups.LubinTateExamples
import Submission.ClassField.FormalGroups.Homomorphisms
import Submission.ClassField.FormalGroups.HomGroupRing
import Submission.ClassField.FormalGroups.LubinTateSeries
import Submission.ClassField.FormalGroups.LubinTateIntertwiner
import Submission.ClassField.FormalGroups.LubinLinearApproximation
import Submission.ClassField.FormalGroups.LubinBaseApproximation
import Submission.ClassField.FormalGroups.LubinCorrectionUnits
import Submission.ClassField.FormalGroups.LubinHomogeneousCorrection
import Submission.ClassField.FormalGroups.LubinTateFiltration
import Submission.ClassField.FormalGroups.LubinDegreeCorrection
import Submission.ClassField.FormalGroups.LubinTateApproximants
import Submission.ClassField.FormalGroups.SubstitutionCongruence
import Submission.ClassField.FormalGroups.LubinPerturbationLower
import Submission.ClassField.FormalGroups.LubinTatePerturbation
import Submission.ClassField.FormalGroups.LubinApproximationLimit
import Submission.ClassField.FormalGroups.StableLimit
import Submission.ClassField.FormalGroups.LubinTateUniqueness
import Submission.ClassField.FormalGroups.LubinIntertwinerPredicate
import Submission.ClassField.FormalGroups.LubinIntertwinerExistence
import Submission.ClassField.FormalGroups.LubinIntertwinerUniqueness
import Submission.ClassField.FormalGroups.UniqueTateIntertwiner
import Submission.ClassField.FormalGroups.LubinIntertwinerComposition
import Submission.ClassField.FormalGroups.LubinIntertwinerOperations
import Submission.ClassField.FormalGroups.GroupLawConstructor
import Submission.ClassField.FormalGroups.LawBaseChange
import Submission.ClassField.FormalGroups.LubinGroupLaw
import Submission.ClassField.FormalGroups.CyclotomicPowerSeries
import Submission.ClassField.FormalGroups.PAdicIntegers
import Submission.ClassField.FormalGroups.LubinTateHomomorphism
import Submission.ClassField.FormalGroups.LubinIntertwinerArithmetic
import Submission.ClassField.FormalGroups.LubinTateIsomorphism
import Submission.ClassField.FormalGroups.LubinEndomorphismRing
import Submission.ClassField.FormalGroups.PowerSeriesUnary
import Submission.ClassField.FormalGroups.LubinTateRemarks
import Submission.ClassField.FormalGroups.FirstVariable
import Submission.ClassField.LubinTate.UnramifiedCyclotomic
import Submission.ClassField.LubinTate.CyclotomicRootsModule
import Submission.ClassField.LubinTate.AdicEvaluation
import Submission.ClassField.LubinTate.AdicModule
import Submission.ClassField.LubinTate.RelativeAdicModule
import Submission.ClassField.LubinTate.TorsionSeries
import Submission.ClassField.LubinTate.NatCompX
import Submission.ClassField.LubinTate.RootValuation
import Submission.ClassField.LubinTate.AdicTorsion
import Submission.ClassField.LubinTate.CyclotomicTorsion
import Submission.ClassField.LubinTate.TorsionKernel
import Submission.ClassField.LubinTate.PolynomialSurjectivity
import Submission.ClassField.LubinTate.AlgebraicConsequences
import Submission.ClassField.LubinTate.BallModel
import Submission.ClassField.LubinTate.AevalAlgEquiv
import Submission.ClassField.LubinTate.RingUnitsCard
import Submission.ClassField.LubinTate.FiniteLevelExtensions
import Submission.ClassField.LubinTate.RootField
import Submission.ClassField.LubinTate.RootFieldTower
import Submission.ClassField.LubinTate.RootFieldAdic
import Submission.ClassField.LubinTate.RootFieldRamification
import Submission.ClassField.LubinTate.RootGaloisAction
import Submission.ClassField.LubinTate.PadicCyclotomic
import Submission.ClassField.LubinTate.AmbientGaloisAction
import Submission.ClassField.LubinTate.InfiniteAutomorphism
import Submission.ClassField.LubinTate.AmbientNorm
import Submission.ClassField.LubinTate.FiniteSubextension
import Submission.ClassField.LubinTate.EvalPolynomialMap
import Submission.ClassField.LubinTate.LocalArtinMap
import Submission.ClassField.LubinTate.AmbientCompositum
import Submission.ClassField.LubinTate.ResidueFieldBase
import Submission.ClassField.LubinTate.Subfield
import Submission.ClassField.LubinTate.SemilinearIntertwiningError
import Submission.ClassField.LubinTate.SemilinearConjugate
import Submission.ClassField.LubinTate.FrobeniusReduction
import Submission.ClassField.LubinTate.UnaryBridge
import Submission.ClassField.LubinTate.IntertwinerConjugation
import Submission.ClassField.LubinTate.Independence
import Submission.ClassField.LubinTate.WittFrobeniusDifference
import Submission.ClassField.LubinTate.PadicWittSemilinear
import Submission.ClassField.LubinTate.PadicUniformizerChange
import Submission.ClassField.LubinTate.PadicBasic
import Submission.ClassField.LubinTate.PadicRootAmbient
import Submission.ClassField.LubinTate.PadicRootDVR
import Submission.ClassField.LubinTate.PadicRootAction
import Submission.ClassField.LubinTate.PadicUniformizerRoot
import Submission.ClassField.LubinTate.CyclotomicResidueDegree
import Submission.ClassField.LubinTate.PadicGaloisAction
import Submission.ClassField.Ramification.UnitMulAdd
import Submission.ClassField.Ramification.LubinLowerBreak
import Submission.ClassField.Ramification.SubgroupEquivMap
import Submission.ClassField.Ramification.UpperRamification
import Submission.ClassField.Ramification.LubinValueInteger
import Submission.ClassField.Ramification.FilteredGroupRigidity
import Submission.ClassField.Ramification.DescentFiniteStage
import Submission.ClassField.Ramification.FiniteGroupSplitting
import Submission.ClassField.Ramification.FiveSubOne
import Submission.ClassField.LocalCohomology

/-!
# Milne, Class Field Theory, Chapter I

The local reciprocity and local existence theorems (1.1 and 1.4) have faithful
statements in `Section1.LocalReciprocityStatement` and
`Section1.MainTheoremStatements`.  The forward implication in local existence
is proved from local reciprocity in `Section1.LocalExistenceConsequences`.
`Section1.Corollary12Statement` states all five parts of Corollary 1.2 using
the actual compositum and intersection of subextensions, and
`Section1.IntermediateField` proves them from the finite-level reciprocity
isomorphisms, including the fixed-field construction for every supergroup of
a norm group.  Thus Theorem 1.1 implies the full local norm correspondence.
`Section1.localOpenEquivalence` derives the complete open-subgroup correspondence of
Corollary 1.5 from Corollary 1.2 and local existence (and proves that this
correspondence implies local existence).  Proving local reciprocity and the
remaining divisibility input in the reverse implication of local existence
remain.
`Section1.Lemma13` formalizes all of Lemma 1.3: the local unit subgroup `U_K`
is open, the norm on the compact integer-unit group is continuous, its range
is `Nm(L^x) inter U_K = Nm(U_L)`, and every finite-index norm subgroup of a
finite Galois local extension is open.
-/

-- Section 1.6 is formalized in `Archimedean`, including the classification of
-- finite-index subgroups of `ℝˣ`.  Section 1.7 is complete in
-- `Section1.FiniteIndexOpen`: the inverse function theorem makes every
-- nonzero power map locally surjective at one in a complete
-- characteristic-zero normed field, and hence every finite-index subgroup of
-- its multiplicative group is open.  The finite residue-field Frobenius
-- statement underlying 1.8 is in
-- `Section1.UnramifiedFrobenius`; constructing the maximal unramified extension
-- and identifying its Galois group with `Zhat` still needs infinite Galois
-- infrastructure.  The principal-unit neighborhood basis and the p-group
-- assertion about its successive quotients in 1.9 are
-- `Section1.principal_unit_basis` and
-- `Section1.principal_p_group`;
-- `Section1.standard_open_subgroup` proves the standard-subgroup
-- cofinality step used in the local existence argument.  The canonical
-- unramified degree-`n` extension is bundled in
-- `Section1.canonicalUnramifiedSubextension`, and its norm group is proved to
-- be exactly `{x | n ∣ ord_K(x)}`; this unconditionally realizes the
-- unramified valuation factor in the local existence construction.  These
-- canonical levels also satisfy the intrinsic spectral-integer
-- unramifiedness predicate used in the statement of local reciprocity.
-- the conductor assertions and Sections 1.10--1.11 depend on local
-- reciprocity and infinite Galois theory.  `Section1.TotalAndUnramified`
-- records the numerical total-versus-unramified obstruction used in 1.12.
-- `standardOpenSubgroupInfOrderModKerLe` proves Theorem 1.13: under local existence, the two
-- characterizing clauses of local reciprocity determine the Artin map
-- uniquely.  Its proof uses the finite-level compositum argument from the
-- text, canonical unramified Frobenius, and the maximal-abelian inverse limit.
-- `Section1.lubinArtinUniqueness` proves Claim 1.14 from exactly the componentwise facts
-- used in the text: both maps fix every finite Lubin--Tate level, agree on the
-- maximal unramified field, and those fields generate the common target.
-- `Section1.localNormClassification` proves the Local Kronecker--Weber conclusion from the
-- finite hypotheses constructed in the text: condition (d) gives containment
-- of each standard subgroup in a finite compositum norm group, the displayed
-- degree computation forces equality, and these levels are cofinal among all
-- finite abelian subextensions.
-- `Section1.existence_standard_levels` formalizes the following
-- paragraph: every open finite-index subgroup contains one of these standard
-- norm groups, so Corollary 1.2(e) makes it a norm group as well.
-- Exercise 1.16 additionally needs a
-- local-field norm/valuation compatibility theorem not presently available.

-- Lemma 2.1(a), associativity of substitution, is
-- `PowerSeries.subst_comp_subst_apply`; Lemma 2.1(b), including the recursive
-- construction and uniqueness of the two-sided compositional inverse, is in
-- `CompositionalInverse`.  The substitution-idempotent argument proving the
-- identity assertion in Remark 2.4(b) is in `IdempotentSeries`.  The
-- formal-group-law structure and the additive and multiplicative examples
-- from Definition 2.3 and Example 2.5 are developed locally because Mathlib
-- does not package them yet.

-- Remark 2.2 is proved in `Remark22` for a complete ideal-adic ring, and hence
-- for a complete DVR equipped with its maximal-ideal-adic topology.  The
-- convergence and ideal-closure assertion for evaluating a formal group law
-- on the maximal ideal after Remark 2.4 is in `FormalGroupEvaluation`, together
-- with the evaluated additive and multiplicative formulas from Examples
-- 2.5(a,b). `AdicSubstitutionEvaluation` proves that evaluation commutes with
-- substitution in the actual adic topology; `AdicFormalGroup` consequently
-- packages the ideal as an `AddCommGroup`, and `AdicFormalGroupHom` and
-- `AdicFormalGroupHomRing` evaluate formal homomorphisms, isomorphisms, and
-- endomorphism rings functorially. The elliptic-curve formal group in Example
-- 2.5(c) remains outside the local formal-group-law wrapper.

-- Definition 2.6, Example 2.7, and identity/composition of formal-group
-- homomorphisms are in `Homomorphisms`.  `HomGroupRing` proves Lemma 2.8 in
-- full: `Hom(F,G)` is an abelian group under the target law and `End(F)` is a
-- ring under composition.  Definition 2.9 and Examples 2.10(a,b) are in
-- `LubinTateSeries`.

-- `LubinTateIntertwiner` proves the finite-residue-field Frobenius congruence
-- and coefficientwise uniformizer divisibility used in Lemma 2.11.  Its
-- degree-one starting form is packaged in `LubinTateLinearApproximation`.  The
-- initial intertwining error is proved to have order at least two in
-- `LubinTateBaseApproximation`.  The correction denominator is proved to be a
-- unit times the uniformizer in
-- `LubinTateCorrectionUnits`; `LubinTateHomogeneousCorrection` assembles
-- coefficientwise divisibility into a unique quotient by that denominator,
-- while `LubinTateFiltration` restricts it to the required homogeneous degree.
-- `LubinTateDegreeCorrection` chooses that quotient, `LTApprox`
-- builds Milne's successive sequence, `LubinTatePerturbation` proves that each
-- correction raises the error order, and `LubinTateApproximationLimit`
-- assembles the exact coefficientwise limit with the prescribed linear part.
-- `LubinTateIntertwinerUniqueness` carries out the least-degree argument, and
-- `UniqueLubinTateIntertwiner` packages the resulting existence-and-uniqueness theorem.
-- Thus Lemma 2.11 is complete.  `LubinTateIntertwinerComposition` and
-- `LubinTateIntertwinerOperations` supply the substitution algebra used next;
-- `LubinTateFormalGroupLaw` proves Proposition 2.12, including identity,
-- commutativity, associativity, the inverse constructed through
-- `FLConstr`, the endomorphism equation, and uniqueness.
-- `Example213` proves the cyclotomic endomorphism identity, and
-- `Example213Padic` proves the actual `K = Q_p` specialization: the series is
-- Lubin--Tate over `ℤ_[p]` and its canonical law is the multiplicative law.
-- `LubinTateHomomorphism` proves Proposition 2.14;
-- `LubinTateIntertwinerArithmetic`, `LubinTateIsomorphism`, and
-- `LubinTateEndomorphismRing` prove Proposition 2.15 and Corollaries 2.16--2.17,
-- including the faithful ring map into the endomorphism ring. `Example218`
-- defines Milne's p-adic binomial series, proves its constant and linear
-- coefficients and its agreement with ordinary powers at natural exponents,
-- proves the full substitution identity for arbitrary `a : ℤ_[p]` by
-- coefficientwise continuity and density, and identifies it with `[a]_f`.
-- `LubinTateRemarks` records Remark 2.19 and the assertions collected in
-- Summary 2.20. `FormalGroupLawBaseChange` transports formal group laws and
-- their homomorphism and endomorphism rings along a coefficient ring map;
-- this is the relative-algebra interface needed to evaluate the law in a
-- finite extension ring.

-- Exercise 2.21 is proved independently by a coefficientwise successive
-- approximation, showing that the inverse axiom follows from the two identity
-- axioms and that the inverse begins with `-X`.

-- The finite residue-field argument at the start of Section 3 is in
-- `Section3.UnramifiedCyclotomic`: prime-to-characteristic roots are separable,
-- Frobenius on a primitive root is controlled by `q^f modulo m`, and a root
-- generating the residue extension gives the stated least residue degree and
-- cardinality.  Lifting this to the unramified local-field extension and
-- forming its infinite union still need a maximal-unramified-extension API.
-- `Section3.AdicEvaluation` nevertheless constructs the convergent values
-- `F_f(alpha,beta)` and `[a]_f(alpha)` in every complete adic local domain;
-- `AdicLubinTateModule` proves that these operations make the ideal an actual
-- module over the coefficient ring and that the canonical change of
-- Lubin--Tate series is a linear equivalence. `RelativeAdicLubinTateModule`
-- base-changes a law over `A` to a complete adic `A`-algebra `B`, constructs
-- its `A`-module of points, proves that `pi^n` acts by the mapped `n`-fold
-- iterate, and identifies its torsion kernels with the corresponding zero
-- loci. `AdicTorsion` restricts the absolute equivalence to every level of
-- torsion. `TorsionSeries` formalizes
-- the compositional iteration underlying Remark 3.1, while `Remark31` proves
-- that a monic degree-`q` polynomial has monic `n`-fold iterate of degree
-- `q^n`. `RootValuation` proves that polynomial Lubin--Tate iterates are
-- distinguished and that every root has valuation less than one in any
-- field carrying an extending valuation. `AdicTorsion` also identifies the
-- level-`n` torsion kernel in the complete adic model with the zero locus of
-- the evaluated `n`-fold iterate. `Example32` proves
-- `f^(n)(T) = (1+T)^(p^n)-1`, identifies its zero
-- set with the `p^n`-th roots of unity by `alpha |-> 1+alpha`, and bundles the
-- correspondence between formal addition and multiplication as a group
-- isomorphism. `Lemma33` constructs
-- the exact kernel tower from Lemma 3.3, proves `|M_n| = q^n`, lifts compatible
-- cyclic generators, and identifies `M_n ≃ A/(pi^n)`. `Proposition34` proves
-- `End_A(A/I) ≃ A/I` and `Aut_A(A/I) ≃ (A/I)^x` and specializes them to those
-- torsion kernels. `Proposition34Polynomial` proves that the basic
-- Lubin--Tate polynomial has exactly `q` distinct roots in an algebraically
-- closed field and is surjective on the valuation-open unit ball.
-- `Proposition34BallModel` isolates the exact ambient coordinate model and,
-- from it, proves surjectivity by `pi`, all torsion cardinalities, and the
-- module, endomorphism-ring, and automorphism-group conclusions of Proposition
-- 3.4. Constructing that coordinate model directly from convergent evaluation
-- in an algebraic closure remains the analytic frontier. `Lemma35` proves the
-- formal power-series equivariance statement under the complete
-- linear-topology hypotheses used by Mathlib's convergent evaluation API and
-- discharges convergence for inputs in any complete adic ideal. `Theorem36`
-- proves the intrinsic DVR
-- counts `|A/(pi^n)| = q^n` and `|(A/(pi^n))^x| = (q-1)q^(n-1)`, transfers the
-- latter to the automorphism group of both the abstract torsion kernel and the
-- open-ball model, proves that every reduced level polynomial is Eisenstein,
-- computes the degree of the field generated by any root, packages Milne's
-- Galois cardinality squeeze, identifies the reduced polynomial with the
-- minimal polynomial, and proves unconditionally that the uniformizer
-- coefficient is a norm. `Summary37` records the abstract cardinality squeeze
-- and packages the concrete finite-level conclusion: exact degree, generation
-- by the primitive root, Galoisness, total ramification, the quotient-unit
-- Galois group, its abelianity, and the uniformizer norm.
-- `LubinTateRootField` constructs the reduced-polynomial `AdjoinRoot`
-- unconditionally, records the actual residue cardinality in its datum,
-- proves its degree and generator statements, shows that the root has exact
-- torsion level, matches the quotient-unit cardinality, and proves the
-- uniformizer norm assertion. `LubinTateRootFieldAdic` equips this field with
-- its spectral local-field structure, places the distinguished root in the
-- maximal ideal of the complete spectral integer ring, proves that the
-- resulting relative adic point has exact annihilator `(pi^(n+1))`, and
-- constructs the faithful quotient-unit orbit. A degree count proves that
-- this orbit exhausts the roots of the reduced polynomial; the polynomial is
-- separable and splits in the distinguished root field, so that field is
-- Galois. Composing the root orbit with the `AdjoinRoot` universal property
-- gives an explicit equivalence of types between quotient units and field
-- automorphisms, with the asserted formula on the distinguished root.
-- `LubinTateRootFieldGaloisAction` proves that this equivalence respects
-- multiplication, completing the Galois-group identification and abelianity
-- assertion in Theorem 3.6(b) for the distinguished root field.
-- `PadicCyclotomicLubinTate` specializes this construction to
-- `(1+X)^p-1`, identifies its reduced root fields with the prime-power
-- cyclotomic extensions of `Q_p`, and supplies the standard finite quotient
-- coordinates. `PadicCyclotomicLubinTateGaloisAction` then proves that the
-- generic quotient-unit orbit is the direct cyclotomic action and that
-- taking inverse units gives the convention used in Example 3.13(b).
-- `LubinTateRootFieldRamification` applies the unconditional integral-closure
-- Eisenstein theorem to prove the full ideal-theoretic total ramification
-- assertion in Theorem 3.6(a), and proves that the distinguished primitive
-- root generates the maximal ideal of the spectral integer ring. Together
-- with the degree calculation above and the norm theorem in
-- `LubinTateRootField`, this completes all three clauses of Theorem 3.6 and
-- the finite-level uniformizer assertion of Summary 3.7 for the concrete
-- distinguished root field.
-- `LubinTateRootFieldTower` constructs the canonical embeddings between all
-- finite root fields; the successor map sends `pi_(n+1)` to `f(pi_(n+2))`,
-- and every successive relative degree is `q`. In a common ambient field it
-- defines the nested torsion-root fields, their infinite supremum `K_pi`, and
-- proves that the carrier of `K_pi` is exactly their directed union. It also
-- separates the full torsion zero locus from its primitive reduced factor,
-- proves that both generate the same finite-level field, and recursively
-- extends the abstract root-field embeddings into one algebraic closure. The
-- resulting primitive roots satisfy `f(pi_(n+2)) = pi_(n+1)` on the nose; the
-- range of every coherent embedding is the corresponding concrete torsion
-- field, and the resulting abstract-to-concrete equivalences commute with
-- both successor maps. The transported primitive root generates its complete
-- finite level and determines every automorphism of that level.
-- `LubinTateAmbientGaloisAction` transports the explicit quotient-unit action
-- to these concrete fields, retaining Milne's formula on the coherent
-- primitive root. It also constructs the quotient-unit reduction maps between
-- consecutive levels and proves that the finite actions can be chosen as a
-- simultaneous compatible family. `LubinTateInfiniteAutomorphism` glues this
-- compatible family into the induced action by base units on the infinite
-- union, completing the inverse-limit unit action in Summary 3.7.
-- `LubinTateAmbientNorm` transports the uniformizer-norm calculation to the
-- concrete finite torsion fields, while `LubinTateFiniteSubextension` embeds
-- each root field into the separable closure and proves the trivial finite
-- Lubin--Tate restriction used in Claim 1.14.
-- `Example38`
-- proves the cyclotomic identities from Example 3.8: the `n`-fold iterate at
-- `ζ - 1` is `ζ^(p^n)-1`, compatible roots of unity give compatible tower
-- generators, adjoining `ζ - 1` gives the same field as adjoining `ζ`, and
-- the standard cyclotomic Galois equivalence has the asserted action on this
-- translated generator.
-- `LocalArtinMap` proves the unique decomposition `a = u*pi^m`, packages it as
-- a multiplicative equivalence, and glues commuting unit and Frobenius actions
-- into the homomorphism prescribed in the text, including Milne's inverse-unit
-- sign convention. `Theorem39` defines the actual compositum `K_pi*K^un`
-- inside a fixed algebraic closure, expresses it as the supremum of the finite
-- composita, and records the exact field-independence proposition. Constructing
-- its Galois-valued Artin map and proving both independence clauses still
-- require arithmetic Frobenius on `K^un`, gluing it to the infinite unit
-- action, and the completed-unramified valuation ring used in Proposition
-- 3.10.
-- `Lemma311` proves the algebraically
-- closed residue-field base cases used in Lemma 3.11: surjectivity of
-- `x ↦ x^(p^n)-x` and the corresponding multiplicative equation on nonzero
-- elements. The lifting through all valuation-ring quotients and the inverse
-- limit remains dependent on that unavailable unramified-completion setup.
-- `Lemma312` isolates Lemma 3.12's topological argument: any subfield that is
-- the common fixed field of continuous endomorphisms is closed, proves the
-- Galois intermediate-field form, and specializes it to every intermediate
-- field of `PadicAlgCl p` using invariance of the spectral norm.
-- `Proposition310` proves Step 1 abstractly and with its full recursive proof:
-- surjectivity of `sigma-1` and an eigenunit produce a power series `theta`
-- with the prescribed linear term and exact equation `sigma theta = theta ∘ u`.
-- It also proves the formal cancellation `(sigma theta) ∘ [u⁻¹] = theta` used
-- in Theorem 3.9. `Proposition310Step2` proves the formal algebra of Step 2:
-- the conjugated series has zero constant term and linear coefficient `u*pi`,
-- the Frobenius-twisted inverse identity holds, and the conjugated series is
-- fixed by Frobenius. It also packages the fixed coefficient subring and
-- proves the complete generic `[1]_{g,h}` adjustment, including preservation
-- of the semilinear equation, linear term, inverse, and exact conjugacy to `g`.
-- `Proposition310Reduction` proves the characteristic-`p` Frobenius identity
-- and the full reduction `h(T) = T^q` after passage to the residue field.
-- `Proposition310UnaryBridge` identifies the ordinary and `Fin 1`-indexed
-- presentations of unary power series, converts exact intertwining equations
-- in both directions, and realizes the canonical `[1]_{g,h}` and its inverse
-- as ordinary power series for the final Step 2 adjustment.
-- `Proposition310Transport` supplies the proof Milne leaves to the reader in
-- Steps 3--4: conjugation transports the Lemma 2.11 predicate, and uniqueness
-- identifies the transported binary law and every scalar endomorphism with
-- the canonical ones for `g`; ordinary-power-series wrappers connect these
-- conclusions directly to the output of Steps 1--2.
-- `Proposition310Independence` continues with the proof immediately after
-- Proposition 3.10: mutually inverse series evaluate to an equivalence of an
-- adic ideal, exact conjugacy restricts it to the torsion zero loci, the two
-- chains of generator inclusions imply equality of the adjoined fields, and
-- the inverse-unit cancellation is proved after convergent evaluation.
-- Instantiating these results with the completed unramified valuation ring,
-- identifying its fixed coefficients with the base ring, and constructing
-- the actual completed-unramified torsion fields and composita remain.
-- `Example313` identifies the residue degree as the multiplicative order of
-- `p` modulo `n`, proves the Frobenius action and its exponent kernel, and in
-- the `p`-power case constructs the reduction of p-adic units, its inverse
-- cyclotomic action, exact congruence kernel, and the cyclotomic degree under
-- irreducibility. Identifying these actions with the local Artin map still
-- requires the missing local cyclotomic bridge.

-- Section 4's general lower ramification filtration, normality, eventual
-- triviality, uniformizer criterion, and inertia/residue quotient are already
-- proved in Milne's `ExistenceTheorem.RamificationGroups`. The specialization of that
-- filtration to the ambient fields `K_{pi,n}` in Proposition 4.1 still needs
-- the finite-level action and uniformizer formulas transported from the
-- abstract root-field models to those intermediate fields.
-- `Proposition41` proves the unconditional core of Milne's proof: the
-- one-step valuation-unit factorization, its iteration to exponent `q^i`, and
-- the exact lower ramification break following from a uniformizer-difference
-- formula. `Example42`
-- proves the remaining Herbrand-function arithmetic: consecutive lower
-- breaks `q^i-1` have length `(q-1)q^i`, so their upper numbers are precisely
-- `i` as asserted in Example 4.2 and Example 4.7.
-- `Proposition43` packages the resulting restriction of reciprocity as an
-- equivalence onto the upper ramification subgroup. `UpperRamification`
-- defines the integer-point Herbrand function, lower and upper jumps, the
-- Hasse--Arf integrality property, and quotient-compatibility interface;
-- `Example47` proves integrality at every Lubin--Tate breakpoint.
-- The unconditional quotient-compatibility theorem of Proposition 4.4 and
-- the general Hasse--Arf theorem require substantial ramification theory not
-- currently present in Mathlib. The local Kronecker--Weber theorem and the
-- concrete Lubin--Tate field statements additionally need restriction maps
-- and Galois compatibility across the new torsion-field tower. `Lemma49Group`
-- index-rigidity argument and the separated-filtration conclusion used in
-- Lemma 4.9. `Lemma410` proves the finite-coefficient descent statement from
-- its footnote: every finite subset of a monotone union of intermediate
-- fields lies in one stage. `Lemma411Group` proves the finite-abelian core of
-- Lemma 4.11: an element whose order equals the exponent generates a direct
-- factor, a lift of a cyclic quotient generator complements the restriction
-- kernel, and complementary Galois subgroups have fixed fields whose
-- compositum is the whole extension. Its finite-Galois wrapper gives exactly
-- this compositum equality for a normal intermediate field. Corollary 4.12
-- remains at the concrete
-- Lubin--Tate field frontier. `Example413` records the example's
-- small numerical facts and proves its final group-theoretic obstruction: a
-- cyclic group of order four is not a product of two cyclic groups of order
-- two. Lemma 4.17 is already Milne's
-- `inertia_subgroup_top` in `Appendix.ExaminationSix`.

-- Appendix A.1--A.4 is covered by `Mathlib.FieldTheory.Galois.Infinite`:
-- fixing subgroups are closed, intermediate fields are recovered as fixed
-- fields, and finite intermediate extensions correspond to open subgroups.
-- `AppendixA` adds the arbitrary-subgroup clause of Theorem A.4: a subgroup
-- and its topological closure have the same fixed field, and that closure is
-- the full subgroup fixing the field.
-- Proposition A.3 and Remark A.9 are in
-- `Mathlib.FieldTheory.Galois.Profinite`, including compactness and the
-- continuous equivalence with the inverse limit of finite Galois groups.
-- The profinite completion of a group is provided by
-- `ProfiniteGrp.profiniteCompletion`, while adic-completion inverse systems
-- and their exactness are developed in `Mathlib.RingTheory.AdicCompletion`.
-- The fully general formulation of Proposition A.8 for arbitrary inverse
-- systems of finite abelian groups is not currently exposed as a single
-- Mathlib theorem.
