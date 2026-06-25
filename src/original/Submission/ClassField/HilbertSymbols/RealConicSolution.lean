import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Sqrt
import Submission.NumberTheory.Locals.NumberFieldFormula
import Submission.ClassField.HilbertSymbols.QuadraticSquareClasses
import Submission.ClassField.LocalBrauer.RealBrauerGroup
import Submission.ClassField.KummerTheory.PowerClasses

/-!
# Milne, Class Field Theory, Remark III.4.8

The quadratic Hilbert symbol over `ℝ` is concrete: it is `-1` exactly when
both arguments are negative.  This file proves that formula directly from
Milne's conic definition, together with bimultiplicativity and
nondegeneracy on real square classes.

For a number field, the source also asserts the Hilbert-symbol product
formula over all finite and infinite places.  The repository has the
normalized product formula for absolute values, but not the local Hilbert
symbols at number-field completions nor the Brauer-reciprocity theorem that
their invariants sum to zero.  The exact product assertion is therefore
packaged below without adding it as a hypothesis.
-/

namespace Submission.CField.HSymbol

open scoped BigOperators
open NumberField
open Submission.CField.KTheory

noncomputable section

/-- Over the real numbers, Milne's quadratic conic has a nontrivial point
exactly when at least one coefficient is nonnegative. -/
theorem real_nontrivial_conic (a b : ℝ) :
    NontrivialQuadraticConic a b ↔ 0 ≤ a ∨ 0 ≤ b := by
  constructor
  · rintro ⟨x, y, z, hne, hxy⟩
    by_contra h
    push Not at h
    have hx2 : x ^ 2 = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hy2 : y ^ 2 = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hz2 : z ^ 2 = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hx : x = 0 := sq_eq_zero_iff.mp hx2
    have hy : y = 0 := sq_eq_zero_iff.mp hy2
    have hz : z = 0 := sq_eq_zero_iff.mp hz2
    rcases hne with hx' | hy' | hz'
    · exact hx' hx
    · exact hy' hy
    · exact hz' hz
  · rintro (ha | hb)
    · refine ⟨1, 0, √a, Or.inl one_ne_zero, ?_⟩
      simp [Real.sq_sqrt ha]
    · refine ⟨0, 1, √b, Or.inr (Or.inl one_ne_zero), ?_⟩
      simp [Real.sq_sqrt hb]

/-- The real quadratic Hilbert symbol on nonzero real numbers. -/
noncomputable def realQuadraticSymbol (a b : ℝˣ) : ℤˣ :=
  quadraticHilbertSign (a : ℝ) (b : ℝ)

/-- The classical sign formula: `(a,b)_∞ = -1` precisely when both `a` and
`b` are negative. -/
theorem real_quadratic_symbol (a b : ℝˣ) :
    realQuadraticSymbol a b = -1 ↔
      (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
  rw [realQuadraticSymbol,
    hilbert_sign_neg,
    real_nontrivial_conic]
  constructor
  · intro h
    exact ⟨lt_of_not_ge (fun ha => h (Or.inl ha)),
      lt_of_not_ge (fun hb => h (Or.inr hb))⟩
  · rintro ⟨ha, hb⟩ (ha' | hb')
    · exact (not_lt_of_ge ha') ha
    · exact (not_lt_of_ge hb') hb

/-- Equivalently, the real symbol is the elementary sign table. -/
theorem real_symbol_ite (a b : ℝˣ) :
    realQuadraticSymbol a b =
      if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then -1 else 1 := by
  classical
  by_cases h : (a : ℝ) < 0 ∧ (b : ℝ) < 0
  · rw [if_pos h]
    exact (real_quadratic_symbol a b).2 h
  · rw [if_neg h]
    rw [realQuadraticSymbol,
      hilbert_sign_one,
      real_nontrivial_conic]
    by_cases ha : (a : ℝ) < 0
    · exact Or.inr (le_of_not_gt fun hb => h ⟨ha, hb⟩)
    · exact Or.inl (le_of_not_gt ha)

/-- The real symbol is multiplicative in its first variable. -/
theorem real_symbol_left (a b c : ℝˣ) :
    realQuadraticSymbol (a * b) c =
      realQuadraticSymbol a c *
        realQuadraticSymbol b c := by
  rw [real_symbol_ite,
    real_symbol_ite,
    real_symbol_ite]
  by_cases hc : (c : ℝ) < 0
  · rcases lt_or_gt_of_ne a.ne_zero with ha | ha <;>
      rcases lt_or_gt_of_ne b.ne_zero with hb | hb
    all_goals
      simp [Units.val_mul, hc, ha, hb,
        not_lt_of_ge ha.le, not_lt_of_ge hb.le, mul_neg_iff]
  · simp [Units.val_mul, hc]

/-- The real symbol is multiplicative in its second variable. -/
theorem real_symbol_right (a b c : ℝˣ) :
    realQuadraticSymbol a (b * c) =
      realQuadraticSymbol a b *
        realQuadraticSymbol a c := by
  unfold realQuadraticSymbol
  rw [quadratic_sign_comm (a : ℝ) ((b * c : ℝˣ) : ℝ),
    quadratic_sign_comm (a : ℝ) (b : ℝ),
    quadratic_sign_comm (a : ℝ) (c : ℝ)]
  exact real_symbol_left b c a

/-- The real symbol is nondegenerate: a unit pairing trivially with every
real unit is positive, hence a square. -/
theorem quadratic_hilbert_symbol
    (b : ℝˣ) (hb : ∀ a : ℝˣ, realQuadraticSymbol a b = 1) :
    0 < (b : ℝ) := by
  by_contra h
  have hbneg : (b : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt h) b.ne_zero
  let a : ℝˣ := Units.mk0 (-1 : ℝ) (by norm_num)
  have ha : (a : ℝ) < 0 := by simp [a]
  have hneg := (real_quadratic_symbol a b).2 ⟨ha, hbneg⟩
  rw [hb a] at hneg
  norm_num at hneg

/-- Remark III.4.8's Hilbert symbol with its literal source domain
`ℝˣ/ℝˣ² × ℝˣ/ℝˣ²`. -/
noncomputable def realHilbertSymbol :
    QuadraticSquareClass ℝ → QuadraticSquareClass ℝ → ℤˣ :=
  hilbertSignSquare

@[simp]
theorem real_symbol_mk (a b : ℝˣ) :
    realHilbertSymbol
        (QuotientGroup.mk a) (QuotientGroup.mk b) =
      realQuadraticSymbol a b :=
  rfl

/-- The real square-class Hilbert symbol is multiplicative in its first
variable. -/
theorem hilbert_symbol_square
    (a b c : QuadraticSquareClass ℝ) :
    realHilbertSymbol (a * b) c =
      realHilbertSymbol a c *
        realHilbertSymbol b c := by
  induction a using QuotientGroup.induction_on with
  | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
          induction c using QuotientGroup.induction_on with
          | _ c =>
              simpa using real_symbol_left a b c

/-- The real square-class Hilbert symbol is multiplicative in its second
variable. -/
theorem real_symbol_square
    (a b c : QuadraticSquareClass ℝ) :
    realHilbertSymbol a (b * c) =
      realHilbertSymbol a b *
        realHilbertSymbol a c := by
  induction a using QuotientGroup.induction_on with
  | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
          induction c using QuotientGroup.induction_on with
          | _ c =>
              simpa using real_symbol_right a b c

/-- The real square-class Hilbert symbol has trivial right kernel. -/
theorem real_hilbert_symbol
    (b : QuadraticSquareClass ℝ)
    (hb : ∀ a, realHilbertSymbol a b = 1) :
    b = 1 := by
  induction b using QuotientGroup.induction_on with
  | _ b =>
      have hb' : ∀ a : ℝˣ, realQuadraticSymbol a b = 1 := by
        intro a
        simpa using hb (QuotientGroup.mk a)
      have hpos : 0 < (b : ℝ) := quadratic_hilbert_symbol b hb'
      let u : ℝˣ := Units.mk0 (Real.sqrt (b : ℝ)) (Real.sqrt_pos.2 hpos).ne'
      apply (QuotientGroup.eq_one_iff _).2
      apply Subgroup.mem_square.mpr
      refine ⟨u, ?_⟩
      ext
      simpa [u, pow_two] using (Real.sq_sqrt hpos.le).symm

/-- The combined type of finite and infinite places of a number field. -/
abbrev NumberFieldPlace (K : Type*) [Field K] [NumberField K] :=
  FinitePlace K ⊕ InfinitePlace K

/-- **Remark III.4.8, number-field product formula (exact assertion).**
For a family of local Hilbert symbols, the product over all places is one.
The finitary product also records the assertion that all but finitely many
local symbols are trivial. -/
def NumberHilbertFormula
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ)
    (localHilbertSymbol : NumberFieldPlace K →
      PowerClassGroup K n → PowerClassGroup K n → rootsOfUnity n K) : Prop :=
  ∀ a b : PowerClassGroup K n,
    (∏ᶠ v : NumberFieldPlace K, localHilbertSymbol v a b) = 1

end

end Submission.CField.HSymbol
