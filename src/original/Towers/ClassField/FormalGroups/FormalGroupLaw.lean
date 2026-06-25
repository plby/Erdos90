import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Class Field Theory, Chapter I, Section 2: formal group laws

This file formalizes Milne's Definition 2.3 and the formal-group-law parts of
Example 2.5.  A one-parameter law is represented by a two-variable formal
power series, and its axioms are equalities after substitution into power
series in one or three variables.

Instead of taking Milne's condition
`F(X,Y) = X + Y + (terms of degree at least two)` as an axiom, we use the
equivalent normalizations `F(X,0) = X` and `F(0,Y) = Y`.  Milne proves this
equivalence from the displayed condition and associativity in Remark 2.4.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

/-- Two-variable formal power series, used for a formal group law. -/
abbrev BinarySeries (R : Type*) [CommRing R] := MvPowerSeries (Fin 2) R

/-- One-variable formal power series, used for inverses and homomorphisms. -/
abbrev UnarySeries (R : Type*) [CommRing R] := MvPowerSeries (Fin 1) R

/-- Three-variable formal power series, used to state associativity. -/
abbrev TernarySeries (R : Type*) [CommRing R] := MvPowerSeries (Fin 3) R

namespace FGLaw

variable {R : Type*} [CommRing R]

/-- The first coordinate in a two-variable power-series ring. -/
def binaryX : BinarySeries R := X (0 : Fin 2)

/-- The second coordinate in a two-variable power-series ring. -/
def binaryY : BinarySeries R := X (1 : Fin 2)

/-- The coordinate in a one-variable power-series ring. -/
def unaryX : UnarySeries R := X (0 : Fin 1)

/-- The first coordinate in a three-variable power-series ring. -/
def ternaryX : TernarySeries R := X (0 : Fin 3)

/-- The second coordinate in a three-variable power-series ring. -/
def ternaryY : TernarySeries R := X (1 : Fin 3)

/-- The third coordinate in a three-variable power-series ring. -/
def ternaryZ : TernarySeries R := X (2 : Fin 3)

/-- Substitute two power series for the two variables of a binary series. -/
def substitute {σ : Type*} (F : BinarySeries R)
    (x y : MvPowerSeries σ R) : MvPowerSeries σ R :=
  subst (Fin.cases x (fun _ ↦ y)) F

/-- Substitute one power series into a unary series. -/
def compose {σ : Type*} (f : UnarySeries R)
    (x : MvPowerSeries σ R) : MvPowerSeries σ R :=
  subst (fun _ ↦ x) f

/-- Substitution into a polynomial binary series computes by ordinary ring
operations, with no convergence side condition. -/
@[simp]
theorem substitute_coe (P : MvPolynomial (Fin 2) R)
    {σ : Type*} (x y : MvPowerSeries σ R) :
    substitute (P : BinarySeries R) x y =
      MvPolynomial.aeval (Fin.cases x (fun _ ↦ y)) P := by
  simp [substitute, MvPowerSeries.subst_coe]

/-- A one-parameter commutative formal group law over `R`.

The inverse is stored as data, together with its zero constant term and its
characterizing uniqueness statement.  Thus `inverse` is Milne's `i_F` rather
than an arbitrary choice made later. -/
structure _root_.Towers.CField.FGroups.FGLaw
    (R : Type*) [CommRing R] where
  law : BinarySeries R
  inverse : UnarySeries R
  left_identity : substitute law 0 unaryX = unaryX
  right_identity : substitute law unaryX 0 = unaryX
  associativity :
    substitute law ternaryX (substitute law ternaryY ternaryZ) =
      substitute law (substitute law ternaryX ternaryY) ternaryZ
  commutativity : substitute law binaryX binaryY = substitute law binaryY binaryX
  inverse_constantCoeff : constantCoeff inverse = 0
  inverse_law : substitute law unaryX inverse = 0
  inverse_unique : ∀ i : UnarySeries R,
    constantCoeff i = 0 → substitute law unaryX i = 0 → i = inverse

end FGLaw

namespace FGLaw

variable {R : Type*} [CommRing R]

/-- The left identity law, exposed under a descriptive theorem name. -/
theorem law_zero_left (F : FGLaw R) :
    substitute F.law 0 unaryX = unaryX :=
  F.left_identity

/-- The right identity law, exposed under a descriptive theorem name. -/
theorem law_zero_right (F : FGLaw R) :
    substitute F.law unaryX 0 = unaryX :=
  F.right_identity

/-- Associativity of a formal group law as an equality in `R⟦X,Y,Z⟧`. -/
theorem law_assoc (F : FGLaw R) :
    substitute F.law ternaryX (substitute F.law ternaryY ternaryZ) =
      substitute F.law (substitute F.law ternaryX ternaryY) ternaryZ :=
  F.associativity

/-- Commutativity of a formal group law as an equality in `R⟦X,Y⟧`. -/
theorem law_comm (F : FGLaw R) :
    substitute F.law binaryX binaryY = substitute F.law binaryY binaryX :=
  F.commutativity

/-- The chosen inverse satisfies `F(X, i_F(X)) = 0`. -/
theorem law_inverse (F : FGLaw R) :
    substitute F.law unaryX F.inverse = 0 :=
  F.inverse_law

/-- Milne's inverse series is uniquely characterized among series in
`X R⟦X⟧` by the inverse equation. -/
theorem inverse_eq (F : FGLaw R) (i : UnarySeries R)
    (hi0 : constantCoeff i = 0) (hi : substitute F.law unaryX i = 0) :
    i = F.inverse :=
  F.inverse_unique i hi0 hi

/-- The additive formal group law `F(X,Y) = X + Y`. -/
def additiveLaw : BinarySeries R :=
  ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
    MvPolynomial (Fin 2) R) : BinarySeries R)

/-- The inverse series for the additive formal group law. -/
def additiveInverse : UnarySeries R := -unaryX

@[simp]
theorem substitute_additiveLaw {σ : Type*} (x y : MvPowerSeries σ R) :
    substitute (additiveLaw (R := R)) x y = x + y := by
  rw [show additiveLaw (R := R) =
      ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
        MvPolynomial (Fin 2) R) : BinarySeries R) from rfl]
  rw [substitute_coe]
  simp only [map_add, MvPolynomial.aeval_X]
  rw [show (1 : Fin 2) = Fin.succ 0 by rfl]
  rfl

/-- Example 2.5(a): ordinary addition is a commutative formal group law. -/
def additive : FGLaw R where
  law := additiveLaw
  inverse := additiveInverse
  left_identity := by simp [unaryX]
  right_identity := by simp [unaryX]
  associativity := by simp [add_assoc]
  commutativity := by simp [add_comm]
  inverse_constantCoeff := by simp [additiveInverse, unaryX]
  inverse_law := by simp [additiveInverse, unaryX]
  inverse_unique i _ hi := by
    simp only [substitute_additiveLaw] at hi
    exact eq_neg_of_add_eq_zero_right hi

/-- The multiplicative formal group law `F(X,Y) = X + Y + XY`. -/
def multiplicativeLaw : BinarySeries R :=
  ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) +
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) :
    MvPolynomial (Fin 2) R) : BinarySeries R)

/-- The formal inverse of `1 + X`.  It is defined using the invertible
constant coefficient `1`, rather than a totalized ring inverse. -/
def unaryXInverse : UnarySeries R :=
  MvPowerSeries.invOfUnit (1 + unaryX) (1 : Rˣ)

@[simp]
theorem unary_x_inverse :
    (1 + unaryX : UnarySeries R) * unaryXInverse = 1 := by
  exact MvPowerSeries.mul_invOfUnit _ _ (by simp [unaryX])

@[simp]
theorem inverse_unary_x :
    unaryXInverse * (1 + unaryX : UnarySeries R) = 1 := by
  exact MvPowerSeries.invOfUnit_mul _ _ (by simp [unaryX])

/-- The inverse series `-X/(1+X)` for the multiplicative formal group law. -/
def multiplicativeInverse : UnarySeries R :=
  -unaryX * unaryXInverse

@[simp]
theorem substitute_multiplicativeLaw {σ : Type*} (x y : MvPowerSeries σ R) :
    substitute (multiplicativeLaw (R := R)) x y = x + y + x * y := by
  rw [show multiplicativeLaw (R := R) =
      ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) +
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) :
        MvPolynomial (Fin 2) R) : BinarySeries R) from rfl]
  rw [substitute_coe]
  simp only [map_add, map_mul, MvPolynomial.aeval_X]
  rw [show (1 : Fin 2) = Fin.succ 0 by rfl]
  rfl

/-- Example 2.5(b): `X + Y + XY` is a commutative formal group law. -/
def multiplicative : FGLaw R where
  law := multiplicativeLaw
  inverse := multiplicativeInverse
  left_identity := by simp [unaryX]
  right_identity := by simp [unaryX]
  associativity := by
    simp only [substitute_multiplicativeLaw]
    ring
  commutativity := by
    simp only [substitute_multiplicativeLaw]
    ring
  inverse_constantCoeff := by
    simp [multiplicativeInverse, unaryXInverse, unaryX]
  inverse_law := by
    simp only [substitute_multiplicativeLaw, multiplicativeInverse]
    let x : UnarySeries R := unaryX
    let v : UnarySeries R := unaryXInverse
    have hv : (1 + x) * v = 1 := by
      simp [x, v]
    change x + -x * v + x * (-x * v) = 0
    calc
      x + -x * v + x * (-x * v) = x * (1 - (1 + x) * v) := by ring
      _ = 0 := by rw [hv]; simp
  inverse_unique i _ hi := by
    simp only [substitute_multiplicativeLaw] at hi
    let x : UnarySeries R := unaryX
    let v : UnarySeries R := unaryXInverse
    change x + i + x * i = 0 at hi
    change i = -x * v
    have hv : (1 + x) * v = 1 := by
      simp [x, v]
    have hi' : (1 + x) * i = -x := by
      calc
        (1 + x) * i = x + i + x * i - x := by ring
        _ = -x := by rw [hi]; simp
    calc
      i = i * 1 := by simp
      _ = i * ((1 + x) * v) := by rw [hv]
      _ = ((1 + x) * i) * v := by ring
      _ = -x * v := by rw [hi']

end FGLaw

end

end Towers.CField.FGroups
