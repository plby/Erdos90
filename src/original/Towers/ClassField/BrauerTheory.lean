import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Towers.ClassField.SimpleAlgebras.FirstAxis
import Towers.ClassField.SimpleAlgebras.NaturalMatrixModule
import Towers.ClassField.SimpleAlgebras.CompositionFactor
import Towers.ClassField.SimpleAlgebras.PrefixSum
import Towers.ClassField.SimpleAlgebras.SSupGenerators
import Towers.ClassField.SimpleAlgebras.ClosureProperties
import Towers.ClassField.SimpleAlgebras.MapIsotypicComponent
import Towers.ClassField.SimpleAlgebras.RegularModuleEndomorphisms
import Towers.ClassField.SimpleAlgebras.TwoSidedIdeal
import Towers.ClassField.SimpleAlgebras.DivisionAlgebraRing
import Towers.ClassField.SimpleAlgebras.StandardQuaternionRing
import Towers.ClassField.SimpleAlgebras.ScalarMatrixCommutes
import Towers.ClassField.SimpleAlgebras.DoubleCentralizer
import Towers.ClassField.SimpleAlgebras.MatrixDivisionAlgebra
import Towers.ClassField.SimpleAlgebras.AlgebraSemisimpleRing
import Towers.ClassField.SimpleAlgebras.PairwiseModulesIsomorphic
import Towers.ClassField.SimpleAlgebras.LeftIdealsIsomorphic
import Towers.ClassField.SimpleAlgebras.LinearEquivFin
import Towers.ClassField.SimpleAlgebras.NaturalRightMul
import Towers.ClassField.BrauerGroups
import Towers.ClassField.CrossedProducts
import Towers.ClassField.LocalBrauer
import Towers.ClassField.BrauerDimension

/-!
# Milne, Class Field Theory, Chapter IV

Chapter IV develops Brauer groups from the structure theory of finite
dimensional algebras.

Most of Section 1's general module theory is already present in Mathlib.
`Mathlib.RingTheory.FiniteLength` supplies composition series and the
Jordan-Hölder theorem. `Mathlib.RingTheory.SimpleModule.Basic` identifies
semisimple modules with complemented submodule lattices, proves closure under
submodules and quotients, develops isotypic components and Schur's lemma, and
contains the Jacobson-density form of Milne's double-centralizer lemma.
`Mathlib.RingTheory.SimpleModule.WedderburnArtin` proves the finite algebra form
of the Wedderburn-Artin theorem and that finite-dimensional simple algebras are
semisimple. `AlgEquiv.moduleEndSelf` gives
`End_A(A) ≃ₐ Aᵐᵒᵖ`, and `Mathlib.Algebra.Central.Matrix` computes matrix
centres.

The local files formalize the concrete calculations not already packaged by
those APIs. `Section1.Example11` classifies invariant subspaces for Milne's
Jordan, distinct-diagonal, and scalar `2×2` matrices, while
`Section1.NaturalMatrixModule` proves the final simple-action example.
`Section1.Theorem12` specializes finite-length theory to Milne's
finite-dimensional algebra modules, proving existence with simple successive
quotients and the full Jordan--Holder uniqueness statement.
`Section1.Corollary13` constructs composition series from two finite internal
direct-sum decompositions into simple modules and extracts the permutation
matching their summands.
`Section1.Corollaries15_16` records the two standard characterizations of
semisimplicity and proves closure under arbitrary sums, submodules, and
quotients.
`Section1.Proposition17` formalizes functoriality and the independent spanning
decomposition by isotypic components, and identifies fully invariant
submodules with sums of those components.
`Section1.Statement18` identifies the endomorphism algebra of the left regular
module with the opposite algebra by evaluation at one.
`Section1.Proposition19` identifies the regular module's isotypic components
with the minimal nonzero two-sided ideals and proves the independent
decomposition of every two-sided ideal.
`Section1.Example110` proves that division algebras are simple and their finite
modules have finite bases. `Section1.NaturalMatrixModule` also proves that a
full matrix algebra over a division algebra is simple. `Section1.Proposition14`
proves Milne's stronger generator-preserving complement statement: a module
spanned by a specified family of simple submodules has complements formed from
an independent subfamily of that same family.

`Section1.Example112` treats the standard quaternion division algebra over an
ordered field and proves its simplicity. `Section1.Example113` computes the
centralizers of scalar and diagonal matrices and the centre of a full matrix
algebra. `Section1.Theorem114` packages Mathlib's Jacobson-density theorem as
Milne's double-centralizer isomorphism. `Section1.Theorem117` and
`Section1.Proposition118` specialize Wedderburn--Artin and semisimplicity to
Milne's finite-dimensional hypotheses. `Section1.Theorem119` proves the three
characterizations of simple semisimple algebras, and `Section1.Corollary120`
and `Section1.Corollary121` prove the resulting classification of minimal left
ideals and finite modules. Finally, `Section1.Corollary122` computes the
endomorphism algebra of the natural matrix module and proves uniqueness of the
matrix size and coefficient division algebra in an Artin--Wedderburn
presentation under the book's finite-dimensional hypothesis.

Section 2 develops tensor products and the Brauer group. Mathlib already
contains the elementary matrix tensor equivalences and the underlying quotient
definition of the Brauer group. The local development proves the tensor-product
centralizer formula, the primordial-element argument, simplicity of tensor
products with a central factor, closure of central simple algebras under tensor
product, and the canonical equivalence
`A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Module.End k A`. It also proves Skolem--Noether and
its inner-automorphism corollaries, and identifies the central division
algebra representative of a Brauer class uniquely up to isomorphism. The
Brauer quotient is given its tensor-product commutative group structure. The
algebraically closed and finite-field examples are formalized as triviality of
Mathlib's Brauer quotient. Scalar extension is shown to preserve central
simplicity and to induce the expected group homomorphism on Brauer groups;
the relative Brauer group is its kernel. This yields the square-dimension
theorem for central simple algebras, and every central simple algebra is shown
to have a finite splitting field inside a fixed algebraic closure.

Section 3 starts the centralizer theory used to recognize splitting fields.
It proves Milne's double-centralizer theorem for simple subalgebras, the
tensor decomposition attached to a central simple subalgebra, and the
self-centralizer/dimension/maximal-commutativity characterizations for
subfields. It constructs Galois crossed products, presents multiplicative
degree-two cohomology by normalized cocycles, and descends crossed products to
an isomorphism of abelian groups `H²(L/k) ≃* Br(L/k)`.  Milne's sketched
tensor-bimodule argument in Lemma 3.15 is formalized using commuting actions,
simplicity, and the dimension comparison with a full endomorphism algebra.
Compatible inflation maps give the direct-limit isomorphism
`Br(k) ≃* H²(kᵃˡ/k)`.  The finite-Galois exponent bound and torsion of the
full Brauer group are also proved.

Section 4 begins the computations for special fields. It records
Wedderburn's little theorem and the resulting triviality of the Brauer
quotient of a finite field, and formalizes Hamilton's quaternions as a
four-dimensional central simple real algebra. It computes
`H²(Gal(Complex/Real), Complexˣ)` and `Br(Real)` as cyclic groups of order
two, identifies the nonzero class with Hamilton's algebra, and proves that
every central simple real algebra is a matrix algebra over either `Real` or
the Hamilton quaternions. It also records the commutative local-field
valuation infrastructure currently available in Mathlib, proves unique
extension of the absolute value to finite commutative extensions, and proves
the square-root degree bound for commutative subfields of a central division
algebra. The determinant of left multiplication is then used to construct
and uniquely characterize the nonarchimedean absolute value on every
finite-dimensional division algebra over a local field. Its valuation ring,
normalized rational additive valuation, maximal two-sided ideal, and residue
field are constructed as well; finiteness of the residue field follows from
compactness, and the valuation values are proved to lie in `(1/n)ℤ` for an
algebra of dimension `n²`; more precisely, the value group is `(1/e)ℤ` for a
positive divisor `e` of `n`. Every nonzero two-sided ideal is classified by
an order threshold, the integer ring is identified with the elements integral
over the valuation ring of the center, and the finite residue extension and
its degree are constructed; the residue degree is proved to be at most `n`.

Section 5 connects the complement theory with Mathlib's semisimple-module
and Artin-Wedderburn APIs, including the finite product, centralizer, algebra
decomposition, and finite module decomposition statements.
The central-simple scalar-extension case of Proposition 5.6 is included as
well.
-/
