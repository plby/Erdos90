import Mathlib.NumberTheory.SumFourSquares

/-!
# Milne, Algebraic Number Theory, Remark 4.20

Milne's first application of the convex-body theorem is Lagrange's four-squares theorem.  We record
both the multiplicative identity used to reduce to primes and the resulting theorem for all natural
numbers.
-/

namespace Submission.NumberTheory.Milne

/-- The four-squares identity displayed in Remark 4.20. -/
theorem euler_squares_identity
    {R : Type*} [CommRing R] (a b c d A B C D : R) :
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) =
      (a * A - b * B - c * C - d * D) ^ 2 +
      (a * B + b * A + c * D - d * C) ^ 2 +
      (a * C - b * D + c * A + d * B) ^ 2 +
      (a * D + b * C - c * B + d * A) ^ 2 := by
  simpa using (euler_four_squares a b c d A B C D).symm

/-- Remark 4.20: every natural number is a sum of four squares. -/
theorem four_squares (n : ℕ) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

end Submission.NumberTheory.Milne
