import Mathlib.Algebra.Quaternion
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Chapter IV, Example 1.12

Milne's standard example is the quaternion algebra `H(-1,-1)`.  Mathlib denotes this by
`Quaternion k` (notation `ℍ[k]`).  Over an ordered field its norm gives inverses, so it is a
division algebra and therefore a simple ring.

The broader assertion that every `H(a,b)` is either a division algebra or a matrix algebra
requires the usual characteristic restriction; the unqualified statement is false in
characteristic two.
-/

namespace Submission.CField.SAlgebr

open scoped Quaternion

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- The standard quaternion algebra `H(-1,-1)` over an ordered field is a division algebra. -/
example : DivisionRing ℍ[k] := inferInstance

/-- Example IV.1.12: the standard quaternion algebra is simple. -/
theorem standard_quaternion_simple : IsSimpleRing ℍ[k] := inferInstance

end Submission.CField.SAlgebr
