import Submission.ClassField.Examples.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Class Field Theory, Exercise 0.11

Quadratic reciprocity describes the splitting primes of a quadratic field by
congruence conditions.  For a squarefree radicand `d`, an odd prime `q` away
from `d` splits in the quadratic order precisely when `(d / q) = 1`.  The
Jacobi-symbol form of quadratic reciprocity shows that this value depends only
on `q` modulo `4 * |d|`.
-/

namespace Submission.CField.Examples

open Ideal
open Submission.NumberTheory
open scoped NumberTheorySymbols

/-- The explicit two-prime factorization expressing that an odd rational prime
splits in the integral-coordinate quadratic order `Z[sqrt(d)]`. -/
def OddSplitsQuadratic (d : ℤ) (q : ℕ) : Prop :=
  ∃ a : ℤ,
    (QOrd.rootIdeal d 0 q a).IsPrime ∧
    (QOrd.rootIdeal d 0 q (-a)).IsPrime ∧
    QOrd.rootIdeal d 0 q a ≠
      QOrd.rootIdeal d 0 q (-a) ∧
    QOrd.rootIdeal d 0 q a *
        QOrd.rootIdeal d 0 q (-a) =
      span {(q : QOrd d 0)}

private theorem root_rational_prime
    (d : ℤ) (q : ℕ) [Fact q.Prime] (a : ℤ) :
    ¬QOrd.rootIdeal d 0 q a ≤
      span {(q : QOrd d 0)} := by
  intro hle
  have homega :
      QuadraticAlgebra.omega - (a : QOrd d 0) ∈
        span {(q : QOrd d 0)} :=
    hle (subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))))
  rw [Ideal.mem_span_singleton] at homega
  obtain ⟨z, hz⟩ := homega
  have him := congrArg QuadraticAlgebra.im hz
  have hdiv : (q : ℤ) ∣ 1 := by
    refine ⟨z.im, ?_⟩
    simpa [QuadraticAlgebra.im_mul, mul_comm] using him
  exact (Fact.out : Nat.Prime q).not_dvd_one (by exact_mod_cast hdiv)

/-- Away from `2d`, an odd rational prime splits in `Z[sqrt(d)]` exactly when
the associated Legendre symbol is one. -/
theorem odd_splits_legendre
    (d : ℤ) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (hqd : ¬(q : ℤ) ∣ d) :
    OddSplitsQuadratic d q ↔ legendreSym q d = 1 := by
  constructor
  · intro hsplit
    have hd0 : (d : ZMod q) ≠ 0 := by
      intro hd
      exact hqd ((ZMod.intCast_zmod_eq_zero_iff_dvd d q).mp hd)
    rcases legendreSym.eq_one_or_neg_one q hd0 with hleg | hleg
    · exact hleg
    · exfalso
      have hspanPrime : (span {(q : QOrd d 0)}).IsPrime :=
        Submission.NumberTheory.Milne.odd_inert_legendre
          d q hleg
      obtain ⟨a, -, -, -, hproduct⟩ := hsplit
      have hmul :
          QOrd.rootIdeal d 0 q a *
              QOrd.rootIdeal d 0 q (-a) ≤
            span {(q : QOrd d 0)} :=
        le_of_eq hproduct
      rcases hspanPrime.mul_le.mp hmul with hleft | hright
      · exact root_rational_prime d q a hleft
      · exact root_rational_prime d q (-a) hright
  · exact
      Submission.NumberTheory.Milne.splits_legendre_sym
        d q hq2 hqd

/-- The quadratic character attached to `d` is constant on odd prime residue
classes modulo `4 * |d|`. -/
theorem legendre_sym_abs
    (d : ℤ) {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    (hqr : q ≡ r [MOD 4 * d.natAbs]) :
    legendreSym q d = legendreSym r d := by
  calc
    legendreSym q d = J(d | q) := jacobiSym.legendreSym.to_jacobiSym q d
    _ = J(d | q % (4 * d.natAbs)) :=
      jacobiSym.mod_right d (Nat.Prime.odd_of_ne_two (Fact.out : Nat.Prime q) hq2)
    _ = J(d | r % (4 * d.natAbs)) := congrArg (jacobiSym d) hqr
    _ = J(d | r) :=
      (jacobiSym.mod_right d
        (Nat.Prime.odd_of_ne_two (Fact.out : Nat.Prime r) hr2)).symm
    _ = legendreSym r d := (jacobiSym.legendreSym.to_jacobiSym r d).symm

/-- Exercise 0.11: for odd primes away from a squarefree radicand `d`, the
splitting condition is determined by the residue class modulo `4 * |d|`. -/
theorem odd_splits_mod
    (d : ℤ) {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    (hqd : ¬(q : ℤ) ∣ d) (hrd : ¬(r : ℤ) ∣ d)
    (hqr : q ≡ r [MOD 4 * d.natAbs]) :
    OddSplitsQuadratic d q ↔
      OddSplitsQuadratic d r := by
  rw [odd_splits_legendre d q hq2 hqd,
    odd_splits_legendre d r hr2 hrd,
    legendre_sym_abs d hq2 hr2 hqr]

end Submission.CField.Examples
