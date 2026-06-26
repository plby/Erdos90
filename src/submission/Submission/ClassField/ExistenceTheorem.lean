import Submission.ClassField.ExistenceOutline
import Submission.ClassField.IdeleCohomology
import Submission.ClassField.HerbrandQuotients
import Submission.ClassField.NormIndex
import Submission.ClassField.CyclicIdeles
import Submission.ClassField.KummerNormIndex
import Submission.ClassField.CyclotomicBrauer
import Submission.ClassField.ReciprocityExistence
import Submission.ClassField.NormLimitation
import Submission.ClassField.KummerTheory

/-!
# Chapter VII: global class field theory, proofs

Section 2 constructs Galois conjugation between arbitrary absolute-value
completions, proves its identity and composition laws, and carries out the
continuous completion-product action of Lemma 2.1 for all extensions of a
fixed place.  The action preserves the product ring structure and satisfies
the required formula on the diagonal copy of the global field, while fixing
the diagonal copy of the completed base field.  Its induced action on the
unit group is packaged as the integral representation used in Propositions
2.2 and 2.3, and its additive coinduced-module identification is proved.
The generic passage from a coordinatewise action to a restricted-product
representation is also proved.  `IAData` states the remaining
arithmetic action directly on the actual idele group, including place
transport, continuity, and Milne's coordinate formula.  Proposition 2.3's
Shapiro step and the local Hilbert 90 input are proved, while Proposition
2.5(b) and Corollary 2.6 are stated against that representation.

Section 7 packages the finite-support localization map to a direct sum and
states Theorem 7.1 using localization coordinates that are literally Brauer
scalar extension.  Its long-exact-sequence injection is proved, and
`RelativeCohomologicalData` gives the exact arithmetic interface
linking the actual idele action, the local decomposition, and the Brauer
comparison square.
Section 8 states both clauses of Theorem 8.1 and both squares of Lemma 8.5's
cup-product diagram.  The implications in Lemma 8.5 are proved once those
cup-product maps and their local-invariant comparison are supplied; the
cyclic-cyclotomic reduction of Lemma 8.6 is also proved abstractly.

The main remaining arithmetic work is to construct the finite- and
infinite-place transports in `IAData`, prove the idele
cohomology direct-sum theorem, prove finite support of Brauer scalar-extension
localizations, and prove the local cup-product/invariant formula of
Proposition III.3.6.  Appendix A now states the full Kummer correspondence
with actual intermediate fields and radical subgroups; multiradical Kummer
theory and descent remain to be proved.
-/
