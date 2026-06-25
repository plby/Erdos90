import Towers.ClassField.HigherReciprocity.PowerResidue
import Towers.ClassField.HigherReciprocity.PowerHenselCriterion
import Towers.ClassField.HigherReciprocity.PowerSymbolLaws
import Towers.ClassField.HigherReciprocity.QuadraticEquivalences
import Towers.ClassField.HigherReciprocity.PowerReciprocity
import Towers.ClassField.HigherReciprocity.SkewPairing
import Towers.ClassField.HigherReciprocity.CubicReciprocity
import Towers.ClassField.HigherReciprocity.Wieferich
import Towers.ClassField.HigherReciprocity.FurtwanglerConclusion
import Towers.ClassField.HigherReciprocity.PrimitiveFermatSolution
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Chapter VIII, Section 5: higher reciprocity laws

The opening quadratic material is already in Mathlib:

* `legendreSym.eq_pow` is Euler's criterion in the congruence form used here;
* `legendreSym.quadratic_reciprocity` is the quadratic reciprocity law;
* `legendreSym.at_neg_one` and `legendreSym.at_two` are its two supplements.

`Section5.PowerResidue` formalizes Statements 5.1 and the finite-field
equivalence in 5.2 as the exact sequence for a power map on a finite cyclic
group. `Section5.Statement52Hensel` proves the remaining equivalence with
being an `n`th power in the completion, including the integrality of a field
root. `Section5.Theorem511PowerReciprocity` proves the Power Recip Law
from exactly 5.7, 5.8, and 5.10. `Section5.FurtwanglerConclusion` records
Furtwängler's theorem and proves its arithmetic conclusion from the one
missing cyclotomic Hilbert-symbol trace calculation. `Section5.Wieferich`
formalizes the parity step, and `Section5.PrimitiveFermatSolution`
performs the primitive-solution reduction and derives the exact source
formulation of Corollary 5.15. `Section5.Example513CubicReciprocity` proves
the elementary Eisenstein arithmetic and derives the literal cubic
reciprocity and supplementary laws from only the explicit local
Hilbert-symbol values at the prime above three.

The remaining numbered assertions require interfaces not currently present:

* Statements 5.3--5.5 now have explicit Artin-action, numerator-congruence,
  and ray-class-factorization formulations; the first two elementary
  deductions are proved from prime factorization data;
* Example 5.6 has the exact equivalence between the four-variable quaternion
  norm form, the conic, and the quadratic norm equation.  Its remaining
  matrix-algebra clause, and the symbol-algebra/Brauer inputs to Statements
  5.7--5.10, remain explicit, while Theorem 5.11's deduction from those
  statements is complete;
* Proposition 5.12's uniqueness from the cyclotomic power-class generators
  and relations (a)--(c) is complete; constructing the local pairing and
  checking those explicit relations remains;
* the local bridge isolated in Example 5.13 and the remaining bridge in
  Theorem 5.14 require explicit computation of the cyclotomic Hilbert symbol
  at the prime above `p`;
* Exercise 5.16 is the cubic-reciprocity criterion and is not presently
  available in Mathlib or the Milne development.

The intensive explicit Hilbert-symbol computation following Theorem 5.11 is
also intentionally omitted, as requested.
-/
