import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Class Field Theory, Chapter I, Lemma 3.11: residue-field base case

Milne begins the proof of Lemma 3.11 by observing that, over an algebraic
closure of the residue field, `x ↦ x^q - x` is surjective.  This file proves
that assertion for `q = p^n`, and records the analogous multiplicative
equation used for units.  Passing from these residue-field statements through
all infinitesimal quotients and then to the completed inverse limit requires
the maximal unramified extension, which is not yet available in Mathlib.
-/

namespace Towers.CField.LTate

open Polynomial

noncomputable section

/-- In characteristic `p`, subtraction from the `p^n`-power Frobenius is an
additive homomorphism. -/
def frobeniusSubHom
    (k : Type*) [CommRing k] (p n : ℕ) [Fact p.Prime] [CharP k p] : k →+ k where
  toFun x := x ^ (p ^ n) - x
  map_zero' := by simp [(Fact.out : p.Prime).ne_zero]
  map_add' x y := by
    rw [add_pow_char_pow]
    ring

@[simp]
theorem frobenius_sub_hom
    (k : Type*) [CommRing k] (p n : ℕ) [Fact p.Prime] [CharP k p] (x : k) :
    frobeniusSubHom k p n x = x ^ (p ^ n) - x :=
  rfl

/-- The residue-field surjectivity in the first exact sequence of Lemma 3.11:
over an algebraically closed field of characteristic `p`, every element is
`x^(p^n) - x` for some `x`, provided `n > 0`. -/
theorem frobenius_pow_surjective
    (k : Type*) [Field k] [IsAlgClosed k]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hn : n ≠ 0) :
    Function.Surjective (frobeniusSubHom k p n) := by
  intro y
  let P : k[X] := X ^ (p ^ n) - X - C y
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hnatDegree : P.natDegree = p ^ n := by
    rw [show P = (X ^ (p ^ n) - X : k[X]) - C y by rfl,
      natDegree_sub_C, FiniteField.X_pow_card_pow_sub_X_natDegree_eq k hn hp]
  have hdegreePos : 0 < P.degree := by
    rw [← natDegree_pos_iff_degree_pos, hnatDegree]
    exact pow_pos (Nat.zero_lt_of_lt hp) n
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root P hdegreePos.ne'
  refine ⟨x, ?_⟩
  apply sub_eq_zero.mp
  simpa [P, IsRoot.def] using hx

/-- In an extension of a finite field, the fixed points of the cardinality
power map are exactly the elements of the base field.  This is the kernel
identification in the residue-field exact sequence used in Lemma 3.11. -/
theorem self_range_algebra
    (k L : Type*) [Field k] [Fintype k] [Field L] [Algebra k L] (x : L) :
    x ^ Fintype.card k = x ↔ x ∈ Set.range (algebraMap k L) := by
  let P : k[X] := X ^ Fintype.card k - X
  have hcard : 1 < Fintype.card k := Fintype.one_lt_card
  have hP0 : P ≠ 0 := by
    simpa [P] using FiniteField.X_pow_card_sub_X_ne_zero k hcard
  have hsplit : P.Splits := by
    rw [splits_iff_card_roots]
    simp [P, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq k hcard]
  constructor
  · intro hx
    apply hsplit.mem_range_of_isRoot hP0
    simpa [P, IsRoot.def, sub_eq_zero] using hx
  · rintro ⟨y, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

/-- The multiplicative residue-field calculation parallel to
`frobenius_pow_surjective`: every nonzero `y` has a nonzero solution of
`x^(p^n) / x = y`. -/
theorem frobenius_pow_div
    (k : Type*) [Field k] [IsAlgClosed k]
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) {y : k} (hy : y ≠ 0) :
    ∃ x : k, x ≠ 0 ∧ x ^ (p ^ n) / x = y := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hq : 1 < p ^ n := Nat.one_lt_pow hn hp
  have hsub : 0 < p ^ n - 1 := Nat.sub_pos_of_lt hq
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hsub
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    apply hy
    simpa [hsub.ne'] using hx.symm
  refine ⟨x, hx0, ?_⟩
  have hsucc : p ^ n - 1 + 1 = p ^ n := Nat.sub_add_cancel hq.le
  rw [← hsucc, pow_succ, mul_div_cancel_right₀ _ hx0, hx]

end

end Towers.CField.LTate
