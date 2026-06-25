import Submission.ClassField.QuadraticForms.OrthogonalDecomposition
import Submission.ClassField.QuadraticForms.Symmetry
import Submission.ClassField.QuadraticForms.Cancellation
import Submission.ClassField.QuadraticForms.QOrthogonal
import Submission.ClassField.QuadraticForms.EquivalentPlace
import Submission.ClassField.QuadraticForms.Archimedean
import Submission.ClassField.QuadraticForms.QuadraticHilbert
import Submission.ClassField.QuadraticForms.HilbertInvariants
import Submission.ClassField.QuadraticForms.AbstractSymbol
import Submission.ClassField.QuadraticForms.DiagonalInvariance
import Submission.ClassField.QuadraticForms.BasesDifferAdjacent
import Submission.ClassField.QuadraticForms.SquareClass
import Submission.ClassField.QuadraticForms.LocalEquivalenceData
import Submission.ClassField.QuadraticForms.PairingNondegenerate
import Submission.ClassField.QuadraticForms.RealOrPlace
import Submission.ClassField.QuadraticForms.QuadraticHasseSign
import Submission.ClassField.QuadraticForms.ThreeSquares

/-!
# Chapter VIII, Section 6: classification of quadratic forms

The files imported here follow the section linearly.  They formalize Proposition 6.1, the
reflection and ambient-isometry complement step used in Proposition 6.2, the complete
algebraically closed and real classifications,
the elementary conic identities of Lemma 6.5, the abstract Hilbert-symbol algebra behind the
Hasse invariant calculations, and the obstruction direction of Proposition 6.14.

The following arithmetic or substantial linear-algebra bridges remain explicit:

* Proposition 6.2 is derived from the missing Witt-extension step, while its
  exact source statement and the ambient-complement argument are complete;
* Theorem 6.3 has its exact all-completions statement and is reduced to
  Theorem 3.5, Proposition 6.2, the rank induction, and the nonsingular
  reduction;
* Proposition 6.9 now has the exact four rank cases over the actual
  square-class quotient; its remaining bridges are the local Hilbert pairing,
  ternary simultaneous-pairing argument, and the rank-at-least-four input;
* Theorem 6.10's invariant induction is complete in the diagonal square-class
  model; Proposition 6.11 additionally has an actual local-field wrapper with
  nonzero coefficients, concrete square-class discriminant, and concrete
  quadratic Hilbert signs;
* Theorem 6.12 and Lemma 6.13 use actual number-field completions and local
  Hilbert signs; their global product-formula and idelic realization inputs
  remain explicit;
* the converse direction of the Gauss--Legendre three-squares theorem.

No axioms standing in for these results are introduced.
-/
