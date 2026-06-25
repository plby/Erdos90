import Submission.ClassField.LocalGlobalPowers
import Submission.ClassField.GrunwaldWang
import Submission.ClassField.HasseNorm
import Submission.ClassField.GlobalClass
import Submission.ClassField.HigherReciprocity
import Submission.ClassField.QuadraticForms
import Submission.ClassField.ChebotarevDensity
import Submission.ClassField.FunctionFieldProspectus
import Submission.ClassField.NumberFieldCohomology
import Submission.ClassField.ArtinLSeries

/-!
# Chapter VIII: complements

The Grunwald--Wang statement and the new global Brauer statements use a common
type of finite and infinite number-field places.  Section 4 states the full
exact sequence of Theorem 4.2, including injectivity, exactness at the local
direct sum, and surjectivity of the invariant sum.  It also states Corollary
4.3 in two forms: the single-completion form for finite Galois extensions, and
the correct arbitrary-extension form in which the local relative group is the
kernel of restriction to all completions above a base place.  The least common
multiple `n₀` is characterized by its divisibility universal property.

Constructing the canonical placewise localization and invariant-sum maps,
and proving local-invariant compatibility under scalar extension, remain the
principal prerequisites for proving these exact sequences.
-/
