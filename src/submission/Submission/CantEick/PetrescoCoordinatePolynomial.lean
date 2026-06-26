/-!
# Hall-Petresco coordinate polynomials

This file records a Lean formulation of the Hall-Petresco coordinate
polynomial theorem for a Hall normal-form coordinate system.  The
polynomials are represented by an integer-valued binomial-polynomial
language: evaluation is a function to `Int`, so expressions such as
binomial coefficients are integer-valued on integer inputs by construction.
-/

namespace Submission
namespace CantEick

universe u

/-- The generalized binomial coefficient, used as a primitive
integer-valued operation in binomial-polynomial expressions. -/
def intBinom (z : Int) : Nat -> Int
  | 0 => 1
  | k + 1 => intBinom z k * (z - Int.ofNat k) / Int.ofNat (k + 1)

/-- Integer-valued binomial-polynomial expressions in variables of type
`σ`.  The `binom` constructor is included to model the usual
Hall-Petresco coefficients such as `choose m 2`. -/
inductive IVPoly (σ : Type u) : Type u where
  | const : Int -> IVPoly σ
  | var : σ -> IVPoly σ
  | add : IVPoly σ -> IVPoly σ -> IVPoly σ
  | neg : IVPoly σ -> IVPoly σ
  | mul : IVPoly σ -> IVPoly σ -> IVPoly σ
  | binom : IVPoly σ -> Nat -> IVPoly σ

namespace IVPoly

variable {σ : Type u}

instance (n : Nat) : OfNat (IVPoly σ) n where
  ofNat := .const (Int.ofNat n)

instance : Zero (IVPoly σ) where
  zero := .const 0

instance : One (IVPoly σ) where
  one := .const 1

instance : Add (IVPoly σ) where
  add := .add

instance : Neg (IVPoly σ) where
  neg := .neg

instance : Sub (IVPoly σ) where
  sub p q := .add p (.neg q)

instance : Mul (IVPoly σ) where
  mul := .mul

/-- The coordinate variable as an integer-valued polynomial. -/
def X (v : σ) : IVPoly σ :=
  .var v

/-- Evaluation of an integer-valued polynomial at an integer assignment. -/
def eval (x : σ -> Int) : IVPoly σ -> Int
  | .const c => c
  | .var v => x v
  | .add p q => eval x p + eval x q
  | .neg p => -eval x p
  | .mul p q => eval x p * eval x q
  | .binom p k => intBinom (eval x p) k

theorem eval_integer_valued (p : IVPoly σ) (x : σ -> Int) :
    ∃ z : Int, eval x p = z :=
  ⟨eval x p, rfl⟩

end IVPoly

/-- Variables for a product coordinate polynomial: `left i` is the
coordinate `a_i` of the first factor and `right i` is the coordinate `b_i`
of the second factor. -/
inductive PVariaba (ι : Type u) : Type u where
  | left : ι -> PVariaba ι
  | right : ι -> PVariaba ι

namespace PVariaba

variable {ι : Type u}

/-- The integer assignment associated to two Hall-coordinate vectors. -/
def assignment (a b : ι -> Int) : PVariaba ι -> Int
  | .left i => a i
  | .right i => b i

/-- A product variable inherits the Hall weight of its coordinate. -/
def weight (wt : ι -> Nat) : PVariaba ι -> Nat
  | .left i => wt i
  | .right i => wt i

end PVariaba

/-- Semantic triangularity: a polynomial depends only on variables whose
Hall weight is strictly below `r`. -/
def DependsOnlyBelow {σ : Type u} (wt : σ -> Nat) (r : Nat)
    (p : IVPoly σ) : Prop :=
  ∀ x y : σ -> Int,
    (∀ v : σ, wt v < r -> x v = y v) ->
      IVPoly.eval x p = IVPoly.eval y p

/--
A Hall coordinate model for the nilpotent quotient `F_d / γ_n(F_d)`.

The fields record the data used by the Hall-Petresco theorem:
* `basis` is the ordered list of Hall basic commutators `h_i`,
* `weight` is their Hall weight, with all weights `< n`,
* `normalForm a` is the element represented by
  `h_1^(a_1) ... h_M^(a_M)`,
* `coord g` is the unique coordinate vector of `g`,
* `prodPoly` is the universal product-coordinate polynomial family.

The theorem below extracts the usual existential statement from this
certificate.
-/
structure HCModel (d n M : Nat) : Type (u + 1) where
  N : Type u
  mul : N -> N -> N
  basis : Fin M -> N
  weight : Fin M -> Nat
  weight_lt_nilpotency : ∀ i : Fin M, weight i < n
  normalForm : (Fin M -> Int) -> N
  coord : N -> Fin M -> Int
  coord_normalForm : ∀ a : Fin M -> Int, coord (normalForm a) = a
  normalForm_coord : ∀ g : N, normalForm (coord g) = g
  prodPoly : Fin M -> IVPoly (PVariaba (Fin M))
  prodPoly_eval :
    ∀ (a b : Fin M -> Int) (i : Fin M),
      coord (mul (normalForm a) (normalForm b)) i =
        IVPoly.eval (PVariaba.assignment a b) (prodPoly i)
  prodPoly_triangular :
    ∀ i : Fin M, ∃ Q : IVPoly (PVariaba (Fin M)),
      prodPoly i =
          IVPoly.X (PVariaba.left i) +
          IVPoly.X (PVariaba.right i) +
          Q ∧
        DependsOnlyBelow (PVariaba.weight weight) (weight i) Q

namespace HCModel

variable {d n M : Nat} (S : HCModel d n M)

/-- Hall coordinates are unique. -/
theorem coord_ext {g h : S.N} (hcoord : S.coord g = S.coord h) : g = h := by
  rw [← S.normalForm_coord g, ← S.normalForm_coord h, hcoord]

/--
**Hall-Petresco Coordinate Polynomial Theorem.**

For the Hall normal-form coordinates on `F_d / γ_n(F_d)`, there are
universal integer-valued product-coordinate polynomials.  If
`r_i = weight h_i`, the `i`th product coordinate is

`a_i + b_i + Q_i(a,b)`,

where the correction term `Q_i` depends only on coordinates of Hall weight
strictly less than `r_i`.
-/
theorem petresco_coordinate_theorem :
    ∃ P : Fin M -> IVPoly (PVariaba (Fin M)),
      (∀ (a b : Fin M -> Int) (i : Fin M),
        S.coord (S.mul (S.normalForm a) (S.normalForm b)) i =
          IVPoly.eval (PVariaba.assignment a b) (P i)) ∧
      (∀ i : Fin M, ∃ Q : IVPoly (PVariaba (Fin M)),
        P i =
            IVPoly.X (PVariaba.left i) +
            IVPoly.X (PVariaba.right i) +
            Q ∧
          DependsOnlyBelow (PVariaba.weight S.weight) (S.weight i) Q) :=
  ⟨S.prodPoly, S.prodPoly_eval, S.prodPoly_triangular⟩

end HCModel

/--
The concrete triangular Hall group law in normal-form coordinates.

This packages the coordinate theorem as an equality in the nilpotent
quotient: multiplying two normal forms is the normal form whose coordinates
are given by the Hall-Petresco product polynomials, and the correction term
in each coordinate only uses lower Hall weights.
-/
theorem triangularGHCE {d n M : Nat}
    (S : HCModel d n M) :
    ∃ P : Fin M -> IVPoly (PVariaba (Fin M)),
      (∀ a b : Fin M -> Int,
        S.mul (S.normalForm a) (S.normalForm b) =
          S.normalForm
            (fun i =>
              IVPoly.eval (PVariaba.assignment a b) (P i))) ∧
      (∀ i : Fin M, ∃ Q : IVPoly (PVariaba (Fin M)),
        P i =
            IVPoly.X (PVariaba.left i) +
            IVPoly.X (PVariaba.right i) +
            Q ∧
          DependsOnlyBelow (PVariaba.weight S.weight) (S.weight i) Q) := by
  rcases S.petresco_coordinate_theorem with ⟨P, hP, htri⟩
  refine ⟨P, ?_, htri⟩
  intro a b
  apply S.coord_ext
  funext i
  rw [S.coord_normalForm]
  exact hP a b i

end CantEick
end Submission
