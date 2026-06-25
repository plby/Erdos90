import Submission.ClassField.Reciprocity.DecompositionGroups
import Submission.ClassField.Reciprocity.Reciprocity
import Submission.ClassField.Reciprocity.ArtinMapStatements
import Submission.ClassField.Reciprocity.LocalFactorsQ
import Submission.ClassField.Reciprocity.RationalUniqueness
import Submission.ClassField.Reciprocity.RestrictedFactorFamily
import Submission.ClassField.Reciprocity.FiniteProductContinuity
import Submission.ClassField.Reciprocity.FiniteRestrictionTopology
import Submission.ClassField.Reciprocity.FiniteIndependence

/-!
# Milne, Class Field Theory, Chapter V, Section 5

This section records the group-theoretic independence of the decomposition
group in Lemma 5.1, the exact quotient-group algebra behind Theorem 5.3, and
concrete statements of Proposition 5.2 and Theorems 5.3 and 5.5 using the
completed local and global idele norms.
For Lemma 5.9, it packages the available local identifications over `Q`:
finite places correspond to rational primes, their completions are `Q_p`, and
the unique infinite completion is `R`.  It also proves the arithmetic
uniqueness step, both for reduced numerator/denominator prime-unit conditions
and directly from vanishing of every finite `p`-adic valuation.

The arithmetic proofs of the central results remain beyond the current
library:

* Proposition 5.2 is proved by assembling the normalized finite-layer local
  Artin products through the inverse limit of finite abelian subextensions;
* the stated arithmetic global reciprocity law, idelic existence
  theorem, norm correspondence, and global Hilbert-symbol product formula in
  Theorems 5.3--5.5 and Corollary 5.6 are not yet proved;
* the full topological-group equivalence of Lemma 5.9 requires assembling the
  finite support of local valuations into a rational principal idèle, together
  with compatibility between `padicValRat` and Mathlib's restricted-product
  adic completions.

No axioms or assumptions named as these class-field-theory theorems are
introduced here; their statements are definitions of propositions.
-/
