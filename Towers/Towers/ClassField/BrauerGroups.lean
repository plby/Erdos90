import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.SimpleRing.Field
import Towers.ClassField.BrauerGroups.TensorMatrixEquiv
import Towers.ClassField.BrauerGroups.MatrixAlgEquiv
import Towers.ClassField.BrauerGroups.CentralizerInfCentralizers
import Towers.ClassField.BrauerGroups.AlgebraCenterField
import Towers.ClassField.BrauerGroups.BasisSupport
import Towers.ClassField.BrauerGroups.CentralTensor
import Towers.ClassField.BrauerGroups.CentralMatrix
import Towers.ClassField.BrauerGroups.TensorProductCentral
import Towers.ClassField.BrauerGroups.MulLeftBijective
import Towers.ClassField.BrauerGroups.SkolemNoether
import Towers.ClassField.BrauerGroups.SimpleSubalgebraInner
import Towers.ClassField.BrauerGroups.AlgEquivInner
import Towers.ClassField.BrauerGroups.BrauerGroup
import Towers.ClassField.BrauerGroups.CentralDivisionCSA
import Towers.ClassField.BrauerGroups.CentralSimpleClosed
import Towers.ClassField.BrauerGroups.ScalarExtensionCentral
import Towers.ClassField.BrauerGroups.FinrankSimpleSquare
import Towers.ClassField.BrauerGroups.BaseChangeBrauer
import Towers.ClassField.BrauerGroups.BaseChangeTower
import Towers.ClassField.BrauerGroups.BrauerTrivialClass
import Towers.ClassField.BrauerGroups.IsSplitBy
import Towers.ClassField.BrauerGroups.RelativeBrauerGroup

/-!
# Milne, Class Field Theory, Chapter IV, Section 2

This section constructs the Brauer group from central simple algebras.

`Example21` specializes and combines Mathlib's `matrixEquivTensor` and
`Matrix.kroneckerTMulAlgEquiv` to prove both forms of Milne's first matrix
tensor example. `Example22` uses `Matrix.kroneckerAlgEquiv` and finite-index
reindexing for the product-of-sizes formula. `Corollary24` transports
Mathlib's `IsSimpleRing.isField_center` to the algebra centre.

The local files prove the first results not already packaged by those APIs.
`Proposition23` computes the centralizer of a tensor product of subalgebras
and deduces the corresponding formula for centres.
`Proposition25` develops support-minimal (primordial) vectors over a division
ring and proves that they span any subspace. `Lemma27` proves Milne's
ideal-generation lemma and its key division-algebra consequence.
`Proposition26` combines that lemma with Artin--Wedderburn and explicit matrix
tensor equivalences to prove simplicity of tensor products when one factor is
central. `Corollary28` proves that tensor products of central simple algebras
are central simple, and `Corollary29` identifies `A ⊗ Aᵐᵒᵖ` with the
endomorphism algebra of the underlying vector space and hence with a full
matrix algebra. `Theorem210` proves Skolem--Noether by classifying
finite-dimensional representations of a simple algebra; `Corollary211` and
`Corollary212` give the subalgebra and automorphism forms. `BrauerGroup`
packages Mathlib's quotient interface and proves its tensor-product
commutative group structure, with opposite algebras as inverses.
`Remark213` proves that every class has a central division-algebra
representative and that two such representatives are Brauer equivalent
exactly when they are isomorphic. `Example214` proves that
the Brauer quotient is trivial for algebraically closed and finite fields;
Milne's real, local-field, and number-field examples are deferred to the later
sections where their classification theorems are proved. `Proposition215`
proves that scalar extension preserves central simple algebras, and
`Corollary216` deduces that the dimension of a finite-dimensional central
simple algebra over its centre is a square. `BaseChangeBrauer` proves that
scalar extension descends to a group homomorphism `Br(k) → Br(K)` and defines
Milne's relative Brauer group `Br(K/k)` as its kernel. `BrauerTrivialClass`
identifies the identity class with full matrix algebras, and
`RelativeBrauerGroup` proves that kernel membership is exactly splitting by
`K`.
`Proposition217` then proves that every such algebra is split by a finite
extension contained in a fixed algebraic closure.

Mathlib's `Mathlib.Algebra.BrauerGroup.Defs` defines central simple algebras
(`CSA`), Brauer equivalence, and the underlying quotient type `BrauerGroup`.
The local `BrauerGroup` file supplies the same-universe abelian group structure
needed here.
`Mathlib.Algebra.Azumaya.Basic` supplies the canonical map
`AlgHom.mulLeftRight`; `Corollary29` proves directly that it is bijective in
the finite-dimensional central-simple case.
-/
