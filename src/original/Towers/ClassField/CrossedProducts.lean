import Towers.ClassField.CrossedProducts.EndRestrictScalars
import Towers.ClassField.CrossedProducts.Centralizer
import Towers.ClassField.CrossedProducts.IsMaximalCommutative
import Towers.ClassField.CrossedProducts.SubalgebraField
import Towers.ClassField.CrossedProducts.TensorEquivLeft
import Towers.ClassField.CrossedProducts.SplitNonemptyHom
import Towers.ClassField.CrossedProducts.LeCentralizer
import Towers.ClassField.CrossedProducts.SeparableNotField
import Towers.ClassField.CrossedProducts.TensorRightCongr
import Towers.ClassField.CrossedProducts.CocycleConstruction
import Towers.ClassField.CrossedProducts.CocycleRepresentatives
import Towers.ClassField.CrossedProducts.ConjugatorsIndependent
import Towers.ClassField.CrossedProducts.UniquenessFactorSet
import Towers.ClassField.CrossedProducts.NormalizedCocycle
import Towers.ClassField.CrossedProducts.CrossedProduct
import Towers.ClassField.CrossedProducts.CrossedProductGalois
import Towers.ClassField.CrossedProducts.FieldEmbeddingMul
import Towers.ClassField.CrossedProducts.Classification
import Towers.ClassField.CrossedProducts.GaloisSubfieldAlgebra
import Towers.ClassField.CrossedProducts.CohomologousProducts
import Towers.ClassField.CrossedProducts.CrossedProductBrauer
import Towers.ClassField.CrossedProducts.FixedDimensionInjectivity
import Towers.ClassField.CrossedProducts.MulApply
import Towers.ClassField.CrossedProducts.BimoduleInfrastructure
import Towers.ClassField.CrossedProducts.CohomologyClass
import Towers.ClassField.CrossedProducts.Multiplicative2Comparison
import Towers.ClassField.CrossedProducts.CohomologyRestriction
import Towers.ClassField.CrossedProducts.MultiplicativeHComparison
import Towers.ClassField.CrossedProducts.GaloisRestriction
import Towers.ClassField.CrossedProducts.Injectivity
import Towers.ClassField.CrossedProducts.Cohomology
import Towers.ClassField.CrossedProducts.BrauerRestriction
import Towers.ClassField.CrossedProducts.RelativeGroupMono
import Towers.ClassField.CrossedProducts.IsMulCoboundary

/-!
# Milne, Class Field Theory, Chapter IV, Section 3

This section begins the study of splitting fields of central simple algebras.

`Theorem31` proves the centralizer theorem: the centralizer of a simple
subalgebra is simple, its dimension is complementary to that of the
subalgebra, and taking the centralizer twice recovers the subalgebra.
`Corollary33` treats the central-subalgebra case and identifies the ambient
algebra with the tensor product of the subalgebra and its centralizer.
`Corollary34` characterizes maximal commutative simple subalgebras by being
self-centralizing and by the square of their dimension.
`Corollary35` specializes this to division algebras, first proving that every
commutative finite-dimensional subalgebra is a field and then recovering the
square-root degree criterion for maximal subfields.
`Corollary36` proves the splitting-field criterion: a finite extension splits
a central simple algebra exactly when it embeds with square-root degree into a
central simple algebra in the same Brauer class.  It also proves directly that
an embedded subfield of square-root degree splits the ambient algebra.
`Corollary37` specializes the criterion to central division algebras: a field
of the degree of the algebra splits it exactly when it embeds in it.
`Proposition38` proves that every finite-dimensional central division algebra
contains a maximal subfield separable over its centre.  Its enlargement step
uses `Lemma39`, the Jacobson--Noether theorem that a nontrivial central
division algebra contains a noncentral separable element.
`Corollary310` proves that every Brauer class is split by a finite Galois
extension in a fixed separable closure, and records Milne's union formula for
the relative Brauer subgroups.
`CocycleConstruction` formalizes equations (39)--(40): associativity makes a
factor set into a multiplicative 2-cocycle, and rescaling the chosen
representatives changes it by a multiplicative 2-coboundary.
`CocycleRepresentatives` uses Skolem--Noether to choose normalized
representatives for an embedded finite Galois field, proves equations
(38)--(40), and constructs their normalized multiplicative 2-cocycle.
`Lemma312` proves that the conjugating representatives are an `L`-basis of the
ambient algebra, using a normal-basis generator and eigenvectors with distinct
eigenvalues; it also specializes this basis to the chosen normalized
representatives.
`Theorem311` proves the uniqueness step in Theorem 3.11: two algebras with
Galois-indexed bases satisfying the same scalar-twisting and factor-set
relations are isomorphic as `k`-algebras.
`NormalizedCocycle` proves that every multiplicative `2`-cocycle is
cohomologous to a normalized one. `CProduc` constructs the associated
associative twisted group algebra and its standard `L`-basis.
`CrossedProductGalois` equips it with its base-field algebra structure,
embeds the coefficient field, proves equations (39)--(40), and computes its
dimension over the coefficient field. `Lemma313` proves that the resulting
Galois crossed product is central simple over the base field.
`Theorem311Classification` proves that every central simple algebra of the
required square dimension containing `L` is recovered from its normalized
factor set. `CohomologousCrossedProducts` proves that cohomologous normalized
cocycles give isomorphic crossed products, completing the constructive
classification in Theorem 3.11. `Theorem311Statement` bundles Milne's
`A(L/k)` and proves the literal surjectivity-and-fibers formulation.
`CrossedProductBrauer` packages crossed products as central simple algebras,
computes their base-field dimension, and proves that `L` splits them.
`Theorem314` proves Milne's fixed-dimension injectivity step and the
surjectivity of crossed products onto Brauer classes split by `L`.
`Lemma315` constructs the pointwise product of normalized factor sets and
states the exact Brauer-equivalence assertion for its crossed product and the
tensor product of the two original crossed products. `Lemma315Proof` develops
Milne's tensor bimodule, constructs its commuting left and right actions, and
proves by simplicity and a dimension count that the combined action is the
full endomorphism algebra.  This proves the asserted Brauer equivalence.
`CohomologyClass` gives normalized multiplicative cocycles and their quotient
the expected abelian-group structures. `CohomologyRestriction` constructs
restriction on normalized cocycles and on `H²`, with identity and composition
laws, while `GaloisCohomologyRestriction` specializes it to field towers.
`MultiplicativeH2Comparison` identifies this normalized multiplicative
presentation with Mathlib's categorical degree-two group cohomology.
`MultiplicativeH2RestrictionComparison` proves that this identification is
natural for restriction to subgroups with the induced coefficient action.
`BrauerCohomologyRestriction` constructs scalar extension on relative Brauer
groups, proves its tower law, and compares it with Galois-cohomology
restriction by an explicit Morita bimodule.
`Theorem311Injectivity` proves that
isomorphic crossed products have cohomologous factor sets, using
Skolem--Noether. `Theorem314Cohomology` therefore descends crossed products to
a canonical group isomorphism `H²(L/k) ≃* Br(L/k)`.
`Corollary316` constructs compatible finite-level inflation maps, defines
absolute multiplicative `H²` as their directed limit, and proves the canonical
isomorphism `Br(k) ≃* H²(kᵃˡ/k)`. `Corollary317` proves directly that the
order of a finite group kills every multiplicative degree-two cocycle class,
transports this to finite-Galois relative Brauer groups, and proves that
`Br(k)` is torsion.  The extension-degree bound there is currently formalized
for Galois extensions; the arbitrary finite-extension case needs the missing
Brauer corestriction, including its purely inseparable form.
-/
