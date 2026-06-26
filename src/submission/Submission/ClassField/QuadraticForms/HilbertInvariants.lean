import Mathlib

/-!
# Class field theory, Chapter VIII, Section 6: Hilbert-symbol invariants

The local Hilbert symbol is not yet constructed in the Submission local-field
development.  This file isolates the exact algebraic properties used in
Milne's Lemma 6.5 and in the calculations of Remarks 6.6 and Propositions
6.7, 6.9, and 6.11.  Consequently every result applies immediately to the
local Hilbert symbol once that construction is available.

The coefficient group is written multiplicatively.  In the intended
application it is the square-class group of a local field, `negOne` is the
class of `-1`, and the value group is `{+1,-1}`.

The following arithmetic inputs remain unavailable and are therefore not
asserted here:

* construction and nondegeneracy of the Hilbert symbol for every
  nonarchimedean local field;
* the local classification theorem 6.10 and the existence part of
  Proposition 6.11;
* the Hasse--Minkowski completion bridge used earlier in the chapter;
* the global realization theorem 6.12 and Lemma 6.13, which additionally
  require the global product formula and idelic class field theory.
-/

namespace Submission.CField.QForms

variable (G μ : Type*) [CommGroup G] [CommGroup μ]

/-- The algebraic interface to the quadratic Hilbert symbol used in Section 6. -/
structure AHSym where
  /-- The symbol, bimultiplicative in its two arguments. -/
  symbol : G →* (G →* μ)
  /-- The distinguished square class of `-1`. -/
  negOne : G
  /-- Every value of the symbol has order dividing two. -/
  value_sq : ∀ a b, symbol a b ^ 2 = 1
  /-- The quadratic Hilbert symbol is symmetric. -/
  symmetric : ∀ a b, symbol a b = symbol b a
  /-- The identity `(a, -a) = 1`. -/
  self_neg : ∀ a, symbol a (negOne * a) = 1
  /-- The square class of `-1` has order dividing two. -/
  negOne_sq : negOne ^ 2 = 1

namespace AHSym

variable {G μ}

variable (h : AHSym G μ)

@[simp] theorem map_one_left (b : G) : h.symbol 1 b = 1 := by
  simp

@[simp] theorem map_one_right (a : G) : h.symbol a 1 = 1 := by
  exact map_one (h.symbol a)

@[simp] theorem map_mul_left (a b c : G) :
    h.symbol (a * b) c = h.symbol a c * h.symbol b c := by
  rw [map_mul]
  rfl

@[simp] theorem map_mul_right (a b c : G) :
    h.symbol a (b * c) = h.symbol a b * h.symbol a c := by
  exact map_mul (h.symbol a) b c

theorem value_inv_eq (a b : G) : (h.symbol a b)⁻¹ = h.symbol a b := by
  calc
    (h.symbol a b)⁻¹ = (h.symbol a b)⁻¹ * 1 := (mul_one _).symm
    _ = (h.symbol a b)⁻¹ * (h.symbol a b * h.symbol a b) := by
      rw [← pow_two, h.value_sq]
    _ = h.symbol a b := by group

@[simp] theorem map_sq_left (a b : G) : h.symbol (a ^ 2) b = 1 := by
  rw [map_pow]
  exact h.value_sq a b

@[simp] theorem map_sq_right (a b : G) : h.symbol a (b ^ 2) = 1 := by
  rw [map_pow]
  exact h.value_sq a b

/-- Lemma 6.5(a): multiplication by squares does not change the symbol. -/
theorem mul_sq (a b c d : G) :
    h.symbol (a * c ^ 2) (b * d ^ 2) = h.symbol a b := by
  rw [h.map_mul_left a (c ^ 2) (b * d ^ 2), h.map_sq_left c (b * d ^ 2), mul_one,
    h.map_mul_right a b (d ^ 2), h.map_sq_right a d, mul_one]

/-- Lemma 6.5(c): symmetry, inversion, and equality agree for quadratic values. -/
theorem symmetric_inv (a b : G) :
    h.symbol b a = (h.symbol a b)⁻¹ ∧ (h.symbol a b)⁻¹ = h.symbol a b := by
  exact ⟨(h.symmetric a b).symm.trans (h.value_inv_eq a b).symm, h.value_inv_eq a b⟩

/-- The standard identity `(a,a)=(-1,a)`, deduced from `(a,-a)=1`. -/
theorem self_neg_one (a : G) : h.symbol a a = h.symbol h.negOne a := by
  have hprod : h.symbol a h.negOne * h.symbol a a = 1 := by
    simpa only [map_mul_right] using h.self_neg a
  have hinv : h.symbol a a = (h.symbol a h.negOne)⁻¹ := by
    calc
      h.symbol a a = 1 * h.symbol a a := (one_mul _).symm
      _ = ((h.symbol a h.negOne)⁻¹ * h.symbol a h.negOne) * h.symbol a a := by
        simp
      _ = (h.symbol a h.negOne)⁻¹ *
          (h.symbol a h.negOne * h.symbol a a) := by group
      _ = (h.symbol a h.negOne)⁻¹ := by rw [hprod, mul_one]
  rw [hinv, h.value_inv_eq]
  exact h.symmetric a h.negOne

/-- The discriminant of a diagonal list, as a square class. -/
def discriminant (coeffs : List G) : G := coeffs.prod

/-- Serre's epsilon invariant of a diagonal list. -/
def epsilon : List G → μ
  | [] => 1
  | a :: as => (as.map fun b => h.symbol a b).prod * epsilon as

/-- Milne's Hasse invariant of a diagonal list, including the diagonal pairs. -/
def hasse : List G → μ
  | [] => 1
  | a :: as => h.symbol a a * (as.map fun b => h.symbol a b).prod * hasse as

@[simp] theorem discriminant_nil : discriminant ([] : List G) = 1 := rfl

@[simp] theorem discriminant_cons (a : G) (as : List G) :
    discriminant (a :: as) = a * discriminant as := rfl

@[simp] theorem epsilon_nil : h.epsilon [] = 1 := rfl

@[simp] theorem epsilon_cons (a : G) (as : List G) :
    h.epsilon (a :: as) = (as.map fun b => h.symbol a b).prod * h.epsilon as := rfl

@[simp] theorem hasse_nil : h.hasse [] = 1 := rfl

@[simp] theorem hasse_cons (a : G) (as : List G) :
    h.hasse (a :: as) =
      h.symbol a a * (as.map fun b => h.symbol a b).prod * h.hasse as := rfl

theorem prod_symbol_right (a : G) (as : List G) :
    (as.map fun b => h.symbol a b).prod = h.symbol a as.prod := by
  induction as with
  | nil => simp
  | cons b bs ih => simp [ih]

/-- Remark 6.6: `S(q) = epsilon(q) * (-1, d(q))`. -/
theorem hasse_epsilon_discriminant (coeffs : List G) :
    h.hasse coeffs =
      h.epsilon coeffs * h.symbol h.negOne (discriminant coeffs) := by
  induction coeffs with
  | nil => simp
  | cons a as ih =>
      rw [hasse_cons, epsilon_cons, discriminant_cons, ih, h.map_mul_right,
        h.self_neg_one]
      ac_rfl

/-- The epsilon invariant of an orthogonal sum of diagonal forms. -/
theorem epsilon_append (xs ys : List G) :
    h.epsilon (xs ++ ys) =
      h.epsilon xs * h.epsilon ys *
        h.symbol (discriminant xs) (discriminant ys) := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.cons_append, epsilon_cons, ih, epsilon_cons,
        discriminant_cons, h.map_mul_left]
      rw [List.map_append, List.prod_append, h.prod_symbol_right a as,
        h.prod_symbol_right a ys]
      ac_rfl

/-- The Hasse invariant of an orthogonal sum of diagonal forms. -/
theorem hasse_append (xs ys : List G) :
    h.hasse (xs ++ ys) =
      h.hasse xs * h.hasse ys *
        h.symbol (discriminant xs) (discriminant ys) := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.cons_append, hasse_cons, ih, hasse_cons,
        discriminant_cons, h.map_mul_left]
      rw [List.map_append, List.prod_append, h.prod_symbol_right a as,
        h.prod_symbol_right a ys]
      ac_rfl

/-- Proposition 6.9(b), algebraic calculation for a binary diagonal form. -/
theorem binary_scaled_symbol (a b c : G) :
    h.symbol (a * b) (a * c) =
      h.symbol a (h.negOne * (b * c)) * h.symbol b c := by
  rw [h.map_mul_left a b (a * c), h.map_mul_right a a c,
    h.map_mul_right b a c, h.self_neg_one, h.symmetric b a,
    h.map_mul_right a h.negOne (b * c), h.map_mul_right a b c,
    h.symmetric h.negOne a]
  ac_rfl

/-- Proposition 6.11(a): the rank-one constraint on the Hasse invariant. -/
theorem hasse_singleton (d : G) : h.hasse [d] = h.symbol h.negOne d := by
  simp [h.self_neg_one]

/-- Proposition 6.11(b): a binary diagonal form of discriminant `-1` has
Hasse invariant `(-1,-1)`. -/
theorem hasse_pair_discriminant {a b : G} (hab : a * b = h.negOne) :
    h.hasse [a, b] = h.symbol h.negOne h.negOne := by
  simp only [hasse, List.map, List.prod_cons, List.prod_nil, mul_one]
  rw [mul_assoc, h.symmetric a b, ← h.map_mul_right b a b, hab, h.symmetric b h.negOne,
    h.self_neg_one a, ← h.map_mul_right h.negOne a b, hab]

/-- The rank-two construction used in Proposition 6.11 has the prescribed discriminant
when square classes have exponent two. -/
theorem discriminant_pair_self (a d : G) (ha : a ^ 2 = 1) :
    discriminant [a, a * d] = d := by
  simp only [discriminant, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc]
  simpa [pow_two] using congrArg (fun x : G => x * d) ha

/-- Adding one diagonal coefficient gives the discriminant recursion used in Theorem 6.10. -/
theorem discriminant_append_singleton (coeffs : List G) (a : G) :
    discriminant (coeffs ++ [a]) = discriminant coeffs * a := by
  simp [discriminant]

/-- Adding one diagonal coefficient gives the Hasse-invariant recursion used in Theorem 6.10. -/
theorem hasse_append_singleton (coeffs : List G) (a : G) :
    h.hasse (coeffs ++ [a]) =
      h.hasse coeffs * h.symbol a a * h.symbol a (discriminant coeffs) := by
  rw [h.hasse_append]
  simp [h.symmetric]

end AHSym

end Submission.CField.QForms
