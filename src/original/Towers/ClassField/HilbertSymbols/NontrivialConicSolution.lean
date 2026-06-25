import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Sqrt
import Towers.NumberTheory.Locals.NumberFieldFormula
import Towers.ClassField.HilbertSymbols.QuadraticSquareClasses
import Towers.ClassField.LocalBrauer.RealBrauerGroup
import Towers.ClassField.KummerTheory.PowerClasses

/-!
# Milne, Class Field Theory, Remark III.4.8

This file gives a self-contained formalization of the real quadratic Hilbert
symbol on `ℝˣ/ℝˣ²`.  It also records the exact all-places product formula
asserted for number fields and arbitrary `n`.  The latter remains a statement:
the project has the product formula for normalized absolute values, but not
the local Hilbert symbols at every completion or the global Brauer reciprocity
theorem needed to prove it.
-/

namespace Towers.CField.HSymbol.NCSoluti

open scoped BigOperators
open NumberField
open Towers.CField.BGroups
open Towers.CField.LBrauer
open Towers.CField.KTheory

noncomputable section

/-- Over `ℝ`, the conic `z² = ax² + by²` has a nonzero solution exactly when
at least one coefficient is nonnegative. -/
theorem quadratic_conic_solution (a b : ℝ) :
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
    have hx : x = 0 := eq_zero_of_pow_eq_zero hx2
    have hy : y = 0 := eq_zero_of_pow_eq_zero hy2
    have hz : z = 0 := eq_zero_of_pow_eq_zero hz2
    rcases hne with hx' | hy' | hz'
    · exact hx' hx
    · exact hy' hy
    · exact hz' hz
  · rintro (ha | hb)
    · refine ⟨1, 0, √a, Or.inl one_ne_zero, ?_⟩
      simp [Real.sq_sqrt ha]
    · refine ⟨0, 1, √b, Or.inr (Or.inl one_ne_zero), ?_⟩
      simp [Real.sq_sqrt hb]

/-- The real quadratic Hilbert symbol on representatives. -/
noncomputable def symbol (a b : ℝˣ) : ℤˣ :=
  quadraticHilbertSign (a : ℝ) (b : ℝ)

/-- The real Hilbert symbol is `-1` exactly when both inputs are negative. -/
theorem symbol_neg_one (a b : ℝˣ) :
    symbol a b = -1 ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
  rw [symbol, hilbert_sign_neg,
    quadratic_conic_solution]
  constructor
  · intro h
    exact ⟨lt_of_not_ge (fun ha => h (Or.inl ha)),
      lt_of_not_ge (fun hb => h (Or.inr hb))⟩
  · rintro ⟨ha, hb⟩ (ha' | hb')
    · exact (not_lt_of_ge ha') ha
    · exact (not_lt_of_ge hb') hb

/-- The elementary sign table for the real Hilbert symbol. -/
theorem symbol_eq_ite (a b : ℝˣ) :
    symbol a b = if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then -1 else 1 := by
  classical
  by_cases h : (a : ℝ) < 0 ∧ (b : ℝ) < 0
  · rw [if_pos h]
    exact (symbol_neg_one a b).2 h
  · rw [if_neg h, symbol, hilbert_sign_one,
      quadratic_conic_solution]
    by_cases ha : (a : ℝ) < 0
    · exact Or.inr (le_of_not_gt fun hb => h ⟨ha, hb⟩)
    · exact Or.inl (le_of_not_gt ha)

/-- Multiplicativity in the first argument. -/
theorem symbol_mul_left (a b c : ℝˣ) :
    symbol (a * b) c = symbol a c * symbol b c := by
  rw [symbol_eq_ite, symbol_eq_ite, symbol_eq_ite]
  by_cases hc : (c : ℝ) < 0
  · rcases lt_or_gt_of_ne a.ne_zero with ha | ha
    · rcases lt_or_gt_of_ne b.ne_zero with hb | hb
      · have hab : 0 < (a : ℝ) * (b : ℝ) := mul_pos_of_neg_of_neg ha hb
        simp [Units.val_mul, hc, ha, hb, not_lt_of_ge hab.le]
      · have hab : (a : ℝ) * (b : ℝ) < 0 := mul_neg_of_neg_of_pos ha hb
        have hnb : ¬(b : ℝ) < 0 := not_lt_of_ge hb.le
        simp [Units.val_mul, hc, ha, hnb, hab]
    · rcases lt_or_gt_of_ne b.ne_zero with hb | hb
      · have hab : (a : ℝ) * (b : ℝ) < 0 := mul_neg_of_pos_of_neg ha hb
        have hna : ¬(a : ℝ) < 0 := not_lt_of_ge ha.le
        simp [Units.val_mul, hc, hna, hb, hab]
      · have hab : 0 < (a : ℝ) * (b : ℝ) := mul_pos ha hb
        have hna : ¬(a : ℝ) < 0 := not_lt_of_ge ha.le
        have hnb : ¬(b : ℝ) < 0 := not_lt_of_ge hb.le
        simp [Units.val_mul, hc, hna, hnb, not_lt_of_ge hab.le]
  · simp [Units.val_mul, hc]

/-- Multiplicativity in the second argument. -/
theorem symbol_mul_right (a b c : ℝˣ) :
    symbol a (b * c) = symbol a b * symbol a c := by
  unfold symbol
  rw [quadratic_sign_comm (a : ℝ) ((b * c : ℝˣ) : ℝ),
    quadratic_sign_comm (a : ℝ) (b : ℝ),
    quadratic_sign_comm (a : ℝ) (c : ℝ)]
  exact symbol_mul_left b c a

/-- A representative pairing trivially with every real unit is positive. -/
theorem symbol_right_positive
    (b : ℝˣ) (hb : ∀ a : ℝˣ, symbol a b = 1) :
    0 < (b : ℝ) := by
  by_contra h
  have hbneg : (b : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt h) b.ne_zero
  let a : ℝˣ := Units.mk0 (-1 : ℝ) (by norm_num)
  have ha : (a : ℝ) < 0 := by simp [a]
  have hneg := (symbol_neg_one a b).2 ⟨ha, hbneg⟩
  rw [hb a] at hneg
  norm_num at hneg

/-- Remark III.4.8's real Hilbert symbol on its literal source domain. -/
noncomputable def squareClassSymbol :
    QuadraticSquareClass ℝ → QuadraticSquareClass ℝ → ℤˣ :=
  hilbertSignSquare

@[simp]
theorem square_symbol_mk (a b : ℝˣ) :
    squareClassSymbol (QuotientGroup.mk a) (QuotientGroup.mk b) =
      symbol a b :=
  rfl

theorem square_symbol_left (a b c : QuadraticSquareClass ℝ) :
    squareClassSymbol (a * b) c =
      squareClassSymbol a c * squareClassSymbol b c := by
  induction a using QuotientGroup.induction_on with
  | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
          induction c using QuotientGroup.induction_on with
          | _ c => simpa using symbol_mul_left a b c

theorem square_symbol_right (a b c : QuadraticSquareClass ℝ) :
    squareClassSymbol a (b * c) =
      squareClassSymbol a b * squareClassSymbol a c := by
  unfold squareClassSymbol
  calc
    hilbertSignSquare a (b * c) =
        hilbertSignSquare (b * c) a :=
      hilbert_sign_comm _ _
    _ = hilbertSignSquare b a *
        hilbertSignSquare c a :=
      square_symbol_left b c a
    _ = hilbertSignSquare a b *
        hilbertSignSquare a c := by
      rw [hilbert_sign_comm b a,
        hilbert_sign_comm c a]

/-- The real Hilbert pairing has trivial right kernel on square classes. -/
theorem square_symbol_kernel
    (b : QuadraticSquareClass ℝ)
    (hb : ∀ a, squareClassSymbol a b = 1) :
    b = 1 := by
  induction b using QuotientGroup.induction_on with
  | _ b =>
      have hb' : ∀ a : ℝˣ, symbol a b = 1 := by
        intro a
        simpa using hb (QuotientGroup.mk a)
      have hpos : 0 < (b : ℝ) := symbol_right_positive b hb'
      let u : ℝˣ := Units.mk0 (Real.sqrt (b : ℝ)) (Real.sqrt_pos.2 hpos).ne'
      apply (QuotientGroup.eq_one_iff _).2
      apply Subgroup.mem_square.mpr
      refine ⟨u, ?_⟩
      ext
      simpa [u, pow_two] using (Real.sq_sqrt hpos.le).symm

/-- The Brauer class selected by the real Hilbert sign: the split class for
symbol `1`, and Hamilton's quaternion class for symbol `-1`. -/
noncomputable def brauerClassSymbol (a b : ℝˣ) : BrauerGroup ℝ :=
  if symbol a b = -1 then brauerClass ℝ hamiltonCSA else 1

/-- Both negative inputs select the unique nontrivial real Brauer class. -/
theorem brauer_symbol_hamilton (a b : ℝˣ) :
    brauerClassSymbol a b = brauerClass ℝ hamiltonCSA ↔
      (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
  rw [← symbol_neg_one]
  by_cases h : symbol a b = -1
  · simp [brauerClassSymbol, h]
  · simp [brauerClassSymbol, h, hamilton_brauer_ne.symm]

/-- The combined type of finite and infinite places of a number field. -/
abbrev NumberFieldPlace (K : Type*) [Field K] [NumberField K] :=
  FinitePlace K ⊕ InfinitePlace K

/-- **Remark III.4.8, number-field product formula (exact assertion).**
For every `n`, the product of the local Hilbert symbols over all places is
one.  `finprod` also encodes that only finitely many local factors are
nontrivial. -/
def NumberHilbertFormula
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ)
    (localHilbertSymbol : NumberFieldPlace K →
      PowerClassGroup K n → PowerClassGroup K n → rootsOfUnity n K) : Prop :=
  ∀ a b : PowerClassGroup K n,
    (∏ᶠ v : NumberFieldPlace K, localHilbertSymbol v a b) = 1

end

end Towers.CField.HSymbol.NCSoluti
