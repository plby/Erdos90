import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic

/-!
# Forward recursions

Cant--Eick Section 3 repeatedly reduces a missing Hall polynomial to a
forward recursion `f(x+1) = f(x) + g(x)` with a known initial value.  The
paper solves those recursions with Bernoulli numbers; this file records the
abstract finite-sum solution and its uniqueness.
-/

namespace Submission
namespace CantEick

open scoped BigOperators
open Polynomial

variable {R : Type*}

/-- The finite-sum solution of `f(x+1) = f(x) + g(x)` with value `f₀` at `0`. -/
def forwardAntiderivative [AddCommMonoid R] (f₀ : R) (g : ℕ → R) (x : ℕ) : R :=
  f₀ + ∑ i ∈ Finset.range x, g i

@[simp]
lemma forwardAntiderivative_zero [AddCommMonoid R] (f₀ : R) (g : ℕ → R) :
    forwardAntiderivative f₀ g 0 = f₀ := by
  simp [forwardAntiderivative]

lemma forwardAntiderivative_succ [AddCommMonoid R] (f₀ : R) (g : ℕ → R) (x : ℕ) :
    forwardAntiderivative f₀ g (x + 1) =
      forwardAntiderivative f₀ g x + g x := by
  simp [forwardAntiderivative, Finset.sum_range_succ, add_comm, add_left_comm]

/-- A function solves a forward recursion with specified initial value. -/
def SolvesForwardRecursion [Add R] [OfNat R 0]
    (f : ℕ → R) (f₀ : R) (g : ℕ → R) : Prop :=
  f 0 = f₀ ∧ ∀ x, f (x + 1) = f x + g x

lemma forwardAntiderivative_solves [AddCommMonoid R] (f₀ : R) (g : ℕ → R) :
    SolvesForwardRecursion (forwardAntiderivative f₀ g) f₀ g :=
  ⟨forwardAntiderivative_zero f₀ g, forwardAntiderivative_succ f₀ g⟩

/-- The forward recursion has at most one solution. -/
theorem antiderivative_solves [AddCommMonoid R]
    {f : ℕ → R} {f₀ : R} {g : ℕ → R}
    (hf : SolvesForwardRecursion f f₀ g) :
    f = forwardAntiderivative f₀ g := by
  funext x
  induction x with
  | zero =>
      simp [hf.1]
  | succ x ih =>
      rw [hf.2 x, ih, forwardAntiderivative_succ]

/-- Two solutions of the same forward recursion are equal. -/
theorem solves_forward_recursion [AddCommMonoid R]
    {f h : ℕ → R} {f₀ : R} {g : ℕ → R}
    (hf : SolvesForwardRecursion f f₀ g)
    (hh : SolvesForwardRecursion h f₀ g) :
    f = h := by
  rw [antiderivative_solves hf,
    antiderivative_solves hh]

/-! ## Polynomial forward differences -/

noncomputable section

/--
The rational Bernoulli-polynomial basis whose forward difference is `X^m`
and whose value at zero is zero.
-/
def bernoulliForwardQ (m : ℕ) : ℚ[X] :=
  Polynomial.C (((m + 1 : ℕ) : ℚ)⁻¹) *
    (Polynomial.bernoulli (m + 1) - Polynomial.C (_root_.bernoulli (m + 1)))

set_option linter.flexible false in
theorem bernoulli_q_x (m : ℕ) :
    (bernoulliForwardQ m).comp (1 + Polynomial.X) - bernoulliForwardQ m =
      Polynomial.X ^ m := by
  unfold bernoulliForwardQ
  rw [Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.C_comp, Polynomial.C_comp,
    Polynomial.bernoulli_comp_one_add_X]
  have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
  simp [Nat.cast_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, mul_add, add_mul]
  have hscalar : (Polynomial.C (((m : ℚ) + 1)⁻¹) : ℚ[X]) * ((m : ℚ[X]) + 1) = 1 := by
    rw [show ((m : ℚ[X]) + 1) = Polynomial.C ((m : ℚ) + 1) by norm_num]
    rw [← Polynomial.C_mul]
    field_simp [hne]
    simp
  calc
    (Polynomial.C (↑m + 1)⁻¹ : ℚ[X]) * Polynomial.X ^ m +
        Polynomial.C (↑m + 1)⁻¹ * ((m : ℚ[X]) * Polynomial.X ^ m)
        = Polynomial.C (((m : ℚ) + 1)⁻¹) * Polynomial.X ^ m * ((m : ℚ[X]) + 1) := by
            ring
    _ = Polynomial.X ^ m := by
      rw [mul_assoc]
      rw [show Polynomial.X ^ m * ((m : ℚ[X]) + 1) =
        ((m : ℚ[X]) + 1) * Polynomial.X ^ m by ring]
      rw [← mul_assoc, hscalar, one_mul]

theorem bernoulli_forward_q (m : ℕ) :
    (bernoulliForwardQ m).eval 0 = 0 := by
  unfold bernoulliForwardQ
  simp [Polynomial.bernoulli_eval_zero]

/-- The Bernoulli-polynomial basis with forward difference `X^m`. -/
def bernoulliForwardBasis (R : Type*) [CommRing R] [Algebra ℚ R] (m : ℕ) : R[X] :=
  Polynomial.map (algebraMap ℚ R) (bernoulliForwardQ m)

theorem bernoulli_x_sub
    (R : Type*) [CommRing R] [Algebra ℚ R] (m : ℕ) :
    (bernoulliForwardBasis R m).comp (1 + Polynomial.X) - bernoulliForwardBasis R m =
      Polynomial.X ^ m := by
  have h := congrArg (Polynomial.map (algebraMap ℚ R))
    (bernoulli_q_x m)
  simpa [bernoulliForwardBasis, Polynomial.map_sub, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_one, Polynomial.map_X, Polynomial.map_pow]
    using h

theorem bernoulli_forward_basis
    (R : Type*) [CommRing R] [Algebra ℚ R] (m : ℕ) :
    (bernoulliForwardBasis R m).eval 0 = 0 := by
  rw [bernoulliForwardBasis, Polynomial.eval_zero_map, bernoulli_forward_q]
  simp

/-- Zero-initial polynomial solution of a forward recursion. -/
def forwardAntiderivativeZero [CommRing R] [Algebra ℚ R] (g : R[X]) : R[X] :=
  g.sum fun m c => Polynomial.C c * bernoulliForwardBasis R m

lemma forward_antiderivative_add [CommRing R] [Algebra ℚ R]
    (p q : R[X]) :
    forwardAntiderivativeZero (p + q) =
      forwardAntiderivativeZero p + forwardAntiderivativeZero q := by
  unfold forwardAntiderivativeZero
  rw [Polynomial.sum_add_index]
  · intro i
    simp
  · intro i a b
    simp [Polynomial.C_add, add_mul]

lemma forward_antiderivative_monomial [CommRing R] [Algebra ℚ R]
    (m : ℕ) (c : R) :
    forwardAntiderivativeZero (Polynomial.monomial m c) =
      Polynomial.C c * bernoulliForwardBasis R m := by
  unfold forwardAntiderivativeZero
  rw [Polynomial.sum_monomial_index]
  simp

theorem antiderivative_x_sub
    [CommRing R] [Algebra ℚ R] (g : R[X]) :
    (forwardAntiderivativeZero g).comp (1 + Polynomial.X) -
      forwardAntiderivativeZero g = g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [forward_antiderivative_add, Polynomial.add_comp]
      calc
        (forwardAntiderivativeZero p).comp (1 + Polynomial.X) +
            (forwardAntiderivativeZero q).comp (1 + Polynomial.X) -
            (forwardAntiderivativeZero p + forwardAntiderivativeZero q)
            = ((forwardAntiderivativeZero p).comp (1 + Polynomial.X) -
                forwardAntiderivativeZero p) +
              ((forwardAntiderivativeZero q).comp (1 + Polynomial.X) -
                forwardAntiderivativeZero q) := by
                ring
        _ = p + q := by rw [hp, hq]
  | monomial m c =>
      rw [forward_antiderivative_monomial]
      calc
        (Polynomial.C c * bernoulliForwardBasis R m).comp (1 + Polynomial.X) -
            Polynomial.C c * bernoulliForwardBasis R m
            = Polynomial.C c * ((bernoulliForwardBasis R m).comp (1 + Polynomial.X) -
                bernoulliForwardBasis R m) := by
              rw [Polynomial.mul_comp, Polynomial.C_comp]
              ring
        _ = Polynomial.C c * Polynomial.X ^ m := by
              rw [bernoulli_x_sub]
        _ = Polynomial.monomial m c := by
              rw [Polynomial.C_mul_X_pow_eq_monomial]

/-- Polynomial solution of `f(x+1)=f(x)+g(x)` with prescribed value at zero. -/
def polynomialForwardAntiderivative [CommRing R] [Algebra ℚ R]
    (f₀ : R) (g : R[X]) : R[X] :=
  Polynomial.C f₀ + forwardAntiderivativeZero g

theorem forward_antiderivative_zero [CommRing R] [Algebra ℚ R]
    (f₀ : R) (g : R[X]) :
    (polynomialForwardAntiderivative f₀ g).eval 0 = f₀ := by
  unfold polynomialForwardAntiderivative forwardAntiderivativeZero
  rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_sum]
  simp [bernoulli_forward_basis, Polynomial.sum]

theorem forward_antiderivative_x [CommRing R] [Algebra ℚ R]
    (f₀ : R) (g : R[X]) :
    (polynomialForwardAntiderivative f₀ g).comp (1 + Polynomial.X) -
      polynomialForwardAntiderivative f₀ g = g := by
  simp [polynomialForwardAntiderivative, Polynomial.add_comp,
    antiderivative_x_sub]

theorem polynomial_forward_antiderivative [CommRing R] [Algebra ℚ R]
    (f₀ : R) (g : R[X]) (x : R) :
    (polynomialForwardAntiderivative f₀ g).eval (x + 1) =
      (polynomialForwardAntiderivative f₀ g).eval x + g.eval x := by
  have h := congrArg (Polynomial.eval x)
    (forward_antiderivative_x f₀ g)
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X] at h
  have hx : (1 + x : R) = x + 1 := by ring
  rw [hx] at h
  simpa [add_comm] using (sub_eq_iff_eq_add.mp h)

/--
Evaluation of the Bernoulli-polynomial antiderivative on natural inputs
solves the forward recursion from the first part of this file.
-/
theorem forward_solves [CommRing R] [Algebra ℚ R]
    (f₀ : R) (g : R[X]) :
    SolvesForwardRecursion
      (fun x : ℕ => (polynomialForwardAntiderivative f₀ g).eval (x : R))
      f₀
      (fun x : ℕ => g.eval (x : R)) := by
  constructor
  · simpa using forward_antiderivative_zero f₀ g
  · intro x
    simpa [Nat.cast_add, Nat.cast_one] using
      polynomial_forward_antiderivative f₀ g (x : R)

/--
Paper-style existence form of Lemma `bernoulli`: every polynomial increment
has a polynomial solution with the prescribed initial value.
-/
theorem polynomial_forward_solves
    [CommRing R] [Algebra ℚ R] (f₀ : R) (g : R[X]) :
    ∃ f : R[X],
      f.eval 0 = f₀ ∧
        f.comp (1 + Polynomial.X) - f = g ∧
          ∀ x : R, f.eval (x + 1) = f.eval x + g.eval x := by
  exact ⟨polynomialForwardAntiderivative f₀ g,
    forward_antiderivative_zero f₀ g,
    forward_antiderivative_x f₀ g,
    polynomial_forward_antiderivative f₀ g⟩

/--
If a polynomial function satisfies the same forward recursion and initial
value on natural inputs, then it agrees there with the Bernoulli-polynomial
antiderivative.  This is the uniqueness step used after constructing the
increment polynomial.
-/
theorem forward_antiderivative_solves
    [CommRing R] [Algebra ℚ R]
    {f g : R[X]} {f₀ : R}
    (h0 : f.eval 0 = f₀)
    (hrec : ∀ x : ℕ, f.eval ((x : R) + 1) = f.eval (x : R) + g.eval (x : R)) :
    ∀ x : ℕ,
      f.eval (x : R) = (polynomialForwardAntiderivative f₀ g).eval (x : R) := by
  have hf : SolvesForwardRecursion (fun x : ℕ => f.eval (x : R)) f₀
      (fun x : ℕ => g.eval (x : R)) := by
    constructor
    · simpa using h0
    · intro x
      simpa [Nat.cast_add, Nat.cast_one] using hrec x
  have hpoly := forward_solves (R := R) f₀ g
  have heq := solves_forward_recursion hf hpoly
  intro x
  exact congrFun heq x

/--
Polynomial identity version of `forward_antiderivative_solves`.
Agreement with the Bernoulli-polynomial antiderivative on all natural inputs
forces equality of polynomials over a characteristic-zero domain.
-/
theorem polynomial_antiderivative_solves
    [CommRing R] [IsDomain R] [CharZero R] [Algebra ℚ R]
    {f g : R[X]} {f₀ : R}
    (h0 : f.eval 0 = f₀)
    (hrec : ∀ x : ℕ, f.eval ((x : R) + 1) = f.eval (x : R) + g.eval (x : R)) :
    f = polynomialForwardAntiderivative f₀ g := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun x : ℕ => (x : R))
  · exact Nat.cast_injective
  · intro x
    exact forward_antiderivative_solves h0 hrec x

end

end CantEick
end Submission
