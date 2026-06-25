import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Tactic.NoncommRing


/-!
# Noncommutative formal power series

This file defines the completed free associative algebra
`R⟪X⟫ = R⟨⟨X⟩⟩` coefficientwise. Multiplication is the Cauchy product over
all decompositions of a word.
-/

namespace EChapma

variable (R X : Type*) [Ring R]

/-- Formal power series in the noncommuting variables `X`, with coefficients in `R`. -/
structure MSeries where
  /-- The coefficient of a word. -/
  coeff : FreeMonoid X → R

namespace MSeries

variable {R X}

instance : CoeFun (MSeries R X) fun _ => FreeMonoid X → R :=
  ⟨MSeries.coeff⟩

omit [Ring R] in
@[ext]
theorem ext {f g : MSeries R X} (h : ∀ w, f w = g w) : f = g :=
  by cases f; cases g; congr; exact funext h

instance : Zero (MSeries R X) := ⟨⟨fun _ => 0⟩⟩
instance : Add (MSeries R X) := ⟨fun f g => ⟨fun w => f w + g w⟩⟩
instance : Neg (MSeries R X) := ⟨fun f => ⟨fun w => -f w⟩⟩
instance : Sub (MSeries R X) := ⟨fun f g => ⟨fun w => f w - g w⟩⟩
instance : SMul ℕ (MSeries R X) := ⟨fun n f => ⟨fun w => n • f w⟩⟩
instance : SMul ℤ (MSeries R X) := ⟨fun n f => ⟨fun w => n • f w⟩⟩

@[simp] theorem zero_apply (w : FreeMonoid X) : (0 : MSeries R X) w = 0 := rfl
@[simp] theorem add_apply (f g : MSeries R X) (w : FreeMonoid X) :
    (f + g) w = f w + g w := rfl
@[simp] theorem neg_apply (f : MSeries R X) (w : FreeMonoid X) :
    (-f) w = -f w := rfl
@[simp] theorem sub_apply (f g : MSeries R X) (w : FreeMonoid X) :
    (f - g) w = f w - g w := rfl
@[simp] theorem nsmul_apply (n : ℕ) (f : MSeries R X) (w : FreeMonoid X) :
    (n • f) w = n • f w := rfl
@[simp] theorem zsmul_apply (n : ℤ) (f : MSeries R X) (w : FreeMonoid X) :
    (n • f) w = n • f w := rfl

instance instAddGroup : AddCommGroup (MSeries R X) :=
  Function.Injective.addCommGroup
    (fun f : MSeries R X => (f : FreeMonoid X → R))
    (fun _ _ h => ext fun w => congrFun h w)
    rfl
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)

/-- Remove a fixed initial letter from the word at which a series is evaluated. -/
def shift (x : X) (f : MSeries R X) : MSeries R X :=
  ⟨fun w => f (FreeMonoid.of x * w)⟩

omit [Ring R] in
@[simp]
theorem shift_apply (x : X) (f : MSeries R X) (w : FreeMonoid X) :
    shift x f w = f (FreeMonoid.of x * w) :=
  rfl

@[simp]
theorem shift_zero (x : X) : shift x (0 : MSeries R X) = 0 :=
  rfl

@[simp]
theorem shift_add (x : X) (f g : MSeries R X) :
    shift x (f + g) = shift x f + shift x g :=
  rfl

/-- Left multiplication of every coefficient by `a`. -/
def leftScale (a : R) (f : MSeries R X) : MSeries R X :=
  ⟨fun w => a * f w⟩

@[simp]
theorem leftScale_apply (a : R) (f : MSeries R X) (w : FreeMonoid X) :
    leftScale a f w = a * f w :=
  rfl

@[simp]
theorem shift_leftScale (x : X) (a : R) (f : MSeries R X) :
    shift x (leftScale a f) = leftScale a (shift x f) :=
  rfl

/--
The noncommutative Cauchy product, recursively separating the empty left
factor from decompositions whose left factor starts with `x`.
-/
def convolutionList (f g : MSeries R X) : List X → R
  | [] => f 1 * g 1
  | x :: w =>
      f 1 * g (FreeMonoid.ofList (x :: w)) +
        convolutionList (shift x f) g w

/-- The noncommutative Cauchy product of two formal series. -/
def convolution (f g : MSeries R X) : MSeries R X :=
  ⟨fun w => convolutionList f g w.toList⟩

instance : Mul (MSeries R X) := ⟨convolution⟩

@[simp]
theorem mul_apply_one (f g : MSeries R X) :
    (f * g) 1 = f 1 * g 1 :=
  rfl

@[simp]
theorem apply_of_mul (f g : MSeries R X) (x : X) (w : FreeMonoid X) :
    (f * g) (FreeMonoid.of x * w) =
      f 1 * g (FreeMonoid.of x * w) + (shift x f * g) w :=
  rfl

theorem shift_mul (x : X) (f g : MSeries R X) :
    shift x (f * g) =
      leftScale (f 1) (shift x g) + shift x f * g := by
  ext w
  simp [shift]

instance : One (MSeries R X) :=
  ⟨⟨fun w => if w.length = 0 then 1 else 0⟩⟩

instance : NatCast (MSeries R X) :=
  ⟨fun n => n • (1 : MSeries R X)⟩

instance : IntCast (MSeries R X) :=
  ⟨fun n => n • (1 : MSeries R X)⟩

@[simp]
theorem one_apply (w : FreeMonoid X) :
    (1 : MSeries R X) w = if w.length = 0 then 1 else 0 :=
  rfl

@[simp]
theorem one_apply_one : (1 : MSeries R X) 1 = 1 := by
  simp

@[simp]
theorem one_apply_of (x : X) (w : FreeMonoid X) :
    (1 : MSeries R X) (FreeMonoid.of x * w) = 0 := by
  simp

@[simp]
theorem shift_one (x : X) : shift x (1 : MSeries R X) = 0 := by
  ext w
  simp

theorem zero_mul (f : MSeries R X) : 0 * f = 0 := by
  ext w
  induction w using FreeMonoid.inductionOn' generalizing f with
  | one => simp
  | mul_of x w ih =>
      rw [apply_of_mul, zero_apply, MulZeroClass.zero_mul, zero_add, shift_zero, ih]
      rfl

theorem add_mul (f g h : MSeries R X) : (f + g) * h = f * h + g * h := by
  ext w
  induction w using FreeMonoid.inductionOn' generalizing f g h with
  | one => simp [_root_.add_mul]
  | mul_of x w ih =>
      simp only [apply_of_mul, add_apply, _root_.add_mul, shift_add]
      rw [ih (shift x f) (shift x g) h]
      simp only [add_apply]
      abel

theorem mul_zero (f : MSeries R X) : f * 0 = 0 := by
  ext w
  induction w using FreeMonoid.inductionOn' generalizing f with
  | one => simp
  | mul_of x w ih =>
      rw [apply_of_mul, zero_apply, MulZeroClass.mul_zero, zero_add, ih]
      rfl

theorem mul_add (f g h : MSeries R X) : f * (g + h) = f * g + f * h := by
  ext w
  induction w using FreeMonoid.inductionOn' generalizing f g h with
  | one => simp [_root_.mul_add]
  | mul_of x w ih =>
      simp only [apply_of_mul, add_apply, _root_.mul_add]
      rw [ih (shift x f) g h]
      simp only [add_apply]
      abel

theorem leftScale_mul (a : R) (f g : MSeries R X) :
    leftScale a f * g = leftScale a (f * g) := by
  ext w
  induction w using FreeMonoid.inductionOn' generalizing f g with
  | one => simp [leftScale, _root_.mul_assoc]
  | mul_of x w ih =>
      simp only [apply_of_mul, leftScale_apply, shift_leftScale]
      rw [ih]
      simp only [leftScale_apply]
      noncomm_ring

theorem one_mul (f : MSeries R X) : 1 * f = f := by
  ext w
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
      rw [apply_of_mul, one_apply_one, MulOneClass.one_mul, shift_one, zero_mul, zero_apply,
        add_zero]

theorem mul_one (f : MSeries R X) : f * 1 = f := by
  ext w
  induction w using FreeMonoid.inductionOn' generalizing f with
  | one => simp
  | mul_of x w ih =>
      rw [apply_of_mul, one_apply_of, MulZeroClass.mul_zero, zero_add,
        ih (shift x f)]
      rfl

theorem mul_assoc (f g h : MSeries R X) : (f * g) * h = f * (g * h) := by
  ext w
  induction w using FreeMonoid.inductionOn' generalizing f g h with
  | one => simp [_root_.mul_assoc]
  | mul_of x w ih =>
      simp only [apply_of_mul, mul_apply_one]
      rw [shift_mul, add_mul]
      simp only [add_apply]
      rw [leftScale_mul, ih]
      simp only [leftScale_apply]
      noncomm_ring

instance instNonUnital : NonUnitalNonAssocRing (MSeries R X) :=
  NonUnitalNonAssocRing.mk mul_add add_mul zero_mul mul_zero

instance instNonassocRing : NonAssocRing (MSeries R X) :=
  NonAssocRing.mk one_mul mul_one
    (natCast_zero := by
      change (0 : ℕ) • (1 : MSeries R X) = 0
      exact zero_nsmul _)
    (natCast_succ := by
      intro n
      change (n + 1) • (1 : MSeries R X) = n • (1 : MSeries R X) + 1
      exact succ_nsmul 1 n)
    (intCast_ofNat := by
      intro n
      change (n : ℤ) • (1 : MSeries R X) = n • (1 : MSeries R X)
      exact natCast_zsmul 1 n)
    (intCast_negSucc := by
      intro n
      change (Int.negSucc n) • (1 : MSeries R X) = -((n + 1) • (1 : MSeries R X))
      exact negSucc_zsmul 1 n)

instance instSemiring : Semiring (MSeries R X) where
  __ := instNonassocRing.toNonAssocSemiring
  mul_assoc := mul_assoc

instance : Ring (MSeries R X) where
  __ := instSemiring
  __ := instAddGroup
  intCast_ofNat := by
    intro n
    change (n : ℤ) • (1 : MSeries R X) = n • (1 : MSeries R X)
    exact natCast_zsmul 1 n
  intCast_negSucc := by
    intro n
    change (Int.negSucc n) • (1 : MSeries R X) = -((n + 1) • (1 : MSeries R X))
    exact negSucc_zsmul 1 n

end MSeries

end EChapma
