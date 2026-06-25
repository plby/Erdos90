import Submission.ClassField.EulerProducts.PartialZeta
import Submission.ClassField.Examples.SqrtNegFive

/-!
# Chapter VI, Section 2, Example 2.13

The rational specialization is the displayed numerical identity.  For
`ℚ(√-5)`, the Submission ANT development supplies the class-number computation
and the ramification of `2`; the two residue-field square calculations used
in the text are checked directly below.  A packaged quadratic Artin character
on positive integers is not yet connected to these APIs, so the four-term
character sum is recorded only as its resulting arithmetic evaluation rather
than being assigned an artificial character definition.
-/

namespace Submission.CField.EProduc

open Submission.CField.Examples
open Submission.NumberTheory

/-- Example 2.13(a): for `K = ℚ`, the numerical residue formula reads
`1 = 2 / 2`. -/
theorem rational_residue_identity :
    (1 : ℚ) = 2 / 2 := by
  norm_num

/-- Example 2.13(b): the field `ℚ(√-5)` has class number two. -/
theorem identity_sqrt_five :
    CNOne.negativeQuadraticNumber (-5) (by norm_num) = 2 :=
  sqrt_five_number

/-- The rational prime `2` ramifies in `ℚ(√-5)`, as used in the
quadratic-character class-number calculation. -/
theorem sqrt_neg_ramifies :
    (QOrd.rootIdeal (-5) 0 2 (-1)).IsPrime ∧
      QOrd.rootIdeal (-5) 0 2 (-1) *
          QOrd.rootIdeal (-5) 0 2 (-1) =
        Ideal.span {(2 : QOrd (-5) 0)} :=
  Submission.CField.Examples.sqrt_neg_ramifies

/-- The two congruences displayed in Example 2.13(b): `-5` is a square
modulo both `3` and `7`. -/
theorem sqrt_five_congruences :
    (-5 : ZMod 3) = 1 ^ 2 ∧ (-5 : ZMod 7) = 3 ^ 2 := by
  decide

/-- The final four-term numerical evaluation in the `ℚ(√-5)` example. -/
theorem sqrt_displayed_sum :
    ((1 + 1 + 1 + 1 : ℚ) / 2) = 2 := by
  norm_num

end Submission.CField.EProduc
