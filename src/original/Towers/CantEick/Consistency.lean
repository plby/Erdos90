import Towers.CantEick.PresentationData
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Cant--Eick consistency obstruction

This file formalizes the theorem in Section 4 before the implementation
section: if a consistent nilpotent presentation has multiplication
polynomials, then the associativity defect polynomial vanishes after the
parameters are specialized to that presentation.
-/

namespace Towers
namespace CantEick

open scoped BigOperators

noncomputable section

/-- Variables for a multiplication polynomial `F_i(T; x, y)`. -/
inductive MulVar (n : ℕ) where
  | param : ParameterIndex n → MulVar n
  | left : Fin n → MulVar n
  | right : Fin n → MulVar n
deriving DecidableEq

/-- Variables for an associativity polynomial `P_i(T; x, y, w)`. -/
inductive AssocVar (n : ℕ) where
  | param : ParameterIndex n → AssocVar n
  | x : Fin n → AssocVar n
  | y : Fin n → AssocVar n
  | w : Fin n → AssocVar n
deriving DecidableEq

/-- The non-parameter variables in an associativity polynomial. -/
inductive TripleVar (n : ℕ) where
  | x : Fin n → TripleVar n
  | y : Fin n → TripleVar n
  | w : Fin n → TripleVar n
deriving DecidableEq

/-- The non-parameter variables in a multiplication polynomial. -/
inductive MulInputVar (n : ℕ) where
  | left : Fin n → MulInputVar n
  | right : Fin n → MulInputVar n
deriving DecidableEq

namespace MulVar

variable {n : ℕ}

def toAssocXY : MulVar n → AssocVar n
  | param I => AssocVar.param I
  | left i => AssocVar.x i
  | right i => AssocVar.y i

def toAssocYW : MulVar n → AssocVar n
  | param I => AssocVar.param I
  | left i => AssocVar.y i
  | right i => AssocVar.w i

end MulVar

variable {n : ℕ} {σ : Type*}

/-- Rational evaluation assignment for multiplication variables. -/
def mulVarQ (T : ParameterIndex n → ℚ) (x y : Fin n → ℚ) :
    MulVar n → ℚ
  | MulVar.param I => T I
  | MulVar.left i => x i
  | MulVar.right i => y i

/-- Integer-specialized evaluation assignment for multiplication variables. -/
def evalMulVar (T : ParameterIndex n → ℤ) (x y : Fin n → ℤ) :
    MulVar n → ℚ :=
  mulVarQ (fun I => (T I : ℚ)) (fun i => (x i : ℚ)) (fun i => (y i : ℚ))

/-- Evaluation assignment for the pure multiplication variables `x,y`. -/
def mulInputVar (x y : Fin n → ℤ) : MulInputVar n → ℚ
  | MulInputVar.left i => x i
  | MulInputVar.right i => y i

/-- Evaluate a multiplication polynomial at rational data. -/
def evalMulQ (T : ParameterIndex n → ℚ) (x y : Fin n → ℚ)
    (p : MvPolynomial (MulVar n) ℚ) : ℚ :=
  MvPolynomial.eval (mulVarQ T x y) p

/-- Evaluate a multiplication polynomial at integer data. -/
def evalMulPolynomial (T : ParameterIndex n → ℤ) (x y : Fin n → ℤ)
    (p : MvPolynomial (MulVar n) ℚ) : ℚ :=
  MvPolynomial.eval (evalMulVar T x y) p

/-- Replace parameters by a fixed integer tuple, keeping `x,y` as variables. -/
def mulSpecialization (T : ParameterIndex n → ℤ) :
    MulVar n → MvPolynomial (MulInputVar n) ℚ
  | MulVar.param I => MvPolynomial.C (T I : ℚ)
  | MulVar.left i => MvPolynomial.X (MulInputVar.left i)
  | MulVar.right i => MvPolynomial.X (MulInputVar.right i)

/-- Specialize the parameter variables in a multiplication polynomial. -/
def specializeMul (T : ParameterIndex n → ℤ)
    (p : MvPolynomial (MulVar n) ℚ) :
    MvPolynomial (MulInputVar n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (mulSpecialization T) p

lemma eval_specializeMul (T : ParameterIndex n → ℤ) (x y : Fin n → ℤ)
    (p : MvPolynomial (MulVar n) ℚ) :
    MvPolynomial.eval (mulInputVar x y) (specializeMul T p) =
      evalMulPolynomial T x y p := by
  change
    MvPolynomial.eval (mulInputVar x y)
        (MvPolynomial.eval₂ MvPolynomial.C (mulSpecialization T) p) =
      MvPolynomial.eval (evalMulVar T x y) p
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun f : MulVar n → ℚ => MvPolynomial.eval f p)
  funext v
  cases v <;> simp [mulSpecialization, mulInputVar, evalMulVar, mulVarQ]

/-- Rational evaluation assignment for associativity variables. -/
def assocVarQ (T : ParameterIndex n → ℚ) (x y w : Fin n → ℚ) :
    AssocVar n → ℚ
  | AssocVar.param I => T I
  | AssocVar.x i => x i
  | AssocVar.y i => y i
  | AssocVar.w i => w i

/-- Integer-specialized evaluation assignment for associativity variables. -/
def evalAssocVar (T : ParameterIndex n → ℤ) (x y w : Fin n → ℤ) :
    AssocVar n → ℚ :=
  assocVarQ (fun I => (T I : ℚ)) (fun i => (x i : ℚ))
    (fun i => (y i : ℚ)) (fun i => (w i : ℚ))

/-- Evaluate an associativity polynomial at integer data. -/
def evalAssocPolynomial (T : ParameterIndex n → ℤ) (x y w : Fin n → ℤ)
    (p : MvPolynomial (AssocVar n) ℚ) : ℚ :=
  MvPolynomial.eval (evalAssocVar T x y w) p

/-- Evaluation assignment for the pure variables `x,y,w`. -/
def evalTripleVar (x y w : Fin n → ℤ) : TripleVar n → ℚ
  | TripleVar.x i => x i
  | TripleVar.y i => y i
  | TripleVar.w i => w i

/-- Replace parameters by a fixed integer tuple, keeping `x,y,w` as variables. -/
def assocSpecialization (T : ParameterIndex n → ℤ) :
    AssocVar n → MvPolynomial (TripleVar n) ℚ
  | AssocVar.param I => MvPolynomial.C (T I : ℚ)
  | AssocVar.x i => MvPolynomial.X (TripleVar.x i)
  | AssocVar.y i => MvPolynomial.X (TripleVar.y i)
  | AssocVar.w i => MvPolynomial.X (TripleVar.w i)

/-- Specialize the parameter variables in an associativity polynomial. -/
def specializeAssoc (T : ParameterIndex n → ℤ)
    (p : MvPolynomial (AssocVar n) ℚ) :
    MvPolynomial (TripleVar n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (assocSpecialization T) p

lemma eval_specializeAssoc (T : ParameterIndex n → ℤ) (x y w : Fin n → ℤ)
    (p : MvPolynomial (AssocVar n) ℚ) :
    MvPolynomial.eval (evalTripleVar x y w) (specializeAssoc T p) =
      evalAssocPolynomial T x y w p := by
  change
    MvPolynomial.eval (evalTripleVar x y w)
        (MvPolynomial.eval₂ MvPolynomial.C (assocSpecialization T) p) =
      MvPolynomial.eval (evalAssocVar T x y w) p
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun f : AssocVar n → ℚ => MvPolynomial.eval f p)
  funext v
  cases v <;> simp [assocSpecialization, evalAssocVar, assocVarQ, evalTripleVar]

/-- Substitute `F(T; x, y)` for the left input of another multiplication polynomial. -/
def assocLeftSubst (F : Fin n → MvPolynomial (MulVar n) ℚ) :
    MulVar n → MvPolynomial (AssocVar n) ℚ
  | MulVar.param I => MvPolynomial.X (AssocVar.param I)
  | MulVar.left i => MvPolynomial.rename MulVar.toAssocXY (F i)
  | MulVar.right i => MvPolynomial.X (AssocVar.w i)

/-- Substitute `F(T; y, w)` for the right input of another multiplication polynomial. -/
def assocRightSubst (F : Fin n → MvPolynomial (MulVar n) ℚ) :
    MulVar n → MvPolynomial (AssocVar n) ℚ
  | MulVar.param I => MvPolynomial.X (AssocVar.param I)
  | MulVar.left i => MvPolynomial.X (AssocVar.x i)
  | MulVar.right i => MvPolynomial.rename MulVar.toAssocYW (F i)

/-- The polynomial coordinate of `F(T; F(T;x,y), w)`. -/
def assocLeftPolynomial (F : Fin n → MvPolynomial (MulVar n) ℚ) (i : Fin n) :
    MvPolynomial (AssocVar n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (assocLeftSubst F) (F i)

/-- The polynomial coordinate of `F(T; x, F(T;y,w))`. -/
def assocRightPolynomial (F : Fin n → MvPolynomial (MulVar n) ℚ) (i : Fin n) :
    MvPolynomial (AssocVar n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (assocRightSubst F) (F i)

/-- Cant--Eick's associativity defect `P_i(T;x,y,w)`. -/
def associatorPolynomial (F : Fin n → MvPolynomial (MulVar n) ℚ) (i : Fin n) :
    MvPolynomial (AssocVar n) ℚ :=
  assocLeftPolynomial F i - assocRightPolynomial F i

lemma assoc_left_polynomial (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (T : ParameterIndex n → ℤ) (x y w : Fin n → ℤ) (i : Fin n) :
    evalAssocPolynomial T x y w (assocLeftPolynomial F i) =
      evalMulQ (fun I => (T I : ℚ))
        (fun j => evalMulPolynomial T x y (F j))
        (fun j => (w j : ℚ)) (F i) := by
  change
    MvPolynomial.eval (evalAssocVar T x y w)
        (MvPolynomial.eval₂ MvPolynomial.C (assocLeftSubst F) (F i)) =
      MvPolynomial.eval
        (mulVarQ (fun I => (T I : ℚ))
          (fun j => evalMulPolynomial T x y (F j))
          (fun j => (w j : ℚ))) (F i)
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun f : MulVar n → ℚ => MvPolynomial.eval f (F i))
  funext v
  cases v with
  | param I =>
      simp [assocLeftSubst, evalAssocVar, assocVarQ, mulVarQ]
  | left j =>
      change
        MvPolynomial.eval (evalAssocVar T x y w)
            (MvPolynomial.rename MulVar.toAssocXY (F j)) =
          evalMulPolynomial T x y (F j)
      rw [MvPolynomial.eval_rename]
      apply congrArg (fun f : MulVar n → ℚ => MvPolynomial.eval f (F j))
      funext v
      cases v <;> simp [evalMulVar, mulVarQ, evalAssocVar,
        assocVarQ, MulVar.toAssocXY]
  | right j =>
      simp [assocLeftSubst, evalAssocVar, assocVarQ, mulVarQ]

lemma eval_assoc_polynomial (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (T : ParameterIndex n → ℤ) (x y w : Fin n → ℤ) (i : Fin n) :
    evalAssocPolynomial T x y w (assocRightPolynomial F i) =
      evalMulQ (fun I => (T I : ℚ))
        (fun j => (x j : ℚ))
        (fun j => evalMulPolynomial T y w (F j)) (F i) := by
  change
    MvPolynomial.eval (evalAssocVar T x y w)
        (MvPolynomial.eval₂ MvPolynomial.C (assocRightSubst F) (F i)) =
      MvPolynomial.eval
        (mulVarQ (fun I => (T I : ℚ))
          (fun j => (x j : ℚ))
          (fun j => evalMulPolynomial T y w (F j))) (F i)
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun f : MulVar n → ℚ => MvPolynomial.eval f (F i))
  funext v
  cases v with
  | param I =>
      simp [assocRightSubst, evalAssocVar, assocVarQ, mulVarQ]
  | left j =>
      simp [assocRightSubst, evalAssocVar, assocVarQ, mulVarQ]
  | right j =>
      change
        MvPolynomial.eval (evalAssocVar T x y w)
            (MvPolynomial.rename MulVar.toAssocYW (F j)) =
          evalMulPolynomial T y w (F j)
      rw [MvPolynomial.eval_rename]
      apply congrArg (fun f : MulVar n → ℚ => MvPolynomial.eval f (F j))
      funext v
      cases v <;> simp [evalMulVar, mulVarQ, evalAssocVar,
        assocVarQ, MulVar.toAssocYW]

/-- `F` represents multiplication in the coordinate system of `M`. -/
def RepresentsMultiplication {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ) : Prop :=
  ∀ x y i,
    evalMulPolynomial T x y (F i) =
      (M.coord (M.normalWord x * M.normalWord y) i : ℚ)

lemma eval_associator_zero {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (x y w : Fin n → ℤ) (i : Fin n)
    (hXY : ∀ j,
      evalMulPolynomial T x y (F j) =
        (M.coord (M.normalWord x * M.normalWord y) j : ℚ))
    (hYW : ∀ j,
      evalMulPolynomial T y w (F j) =
        (M.coord (M.normalWord y * M.normalWord w) j : ℚ))
    (hLeft :
      evalMulPolynomial T (M.coord (M.normalWord x * M.normalWord y)) w (F i) =
        (M.coord ((M.normalWord x * M.normalWord y) * M.normalWord w) i : ℚ))
    (hRight :
      evalMulPolynomial T x (M.coord (M.normalWord y * M.normalWord w)) (F i) =
        (M.coord (M.normalWord x * (M.normalWord y * M.normalWord w)) i : ℚ)) :
    evalAssocPolynomial T x y w (associatorPolynomial F i) = 0 := by
  let xy : Fin n → ℤ := M.coord (M.normalWord x * M.normalWord y)
  let yw : Fin n → ℤ := M.coord (M.normalWord y * M.normalWord w)
  have hleft :
      evalAssocPolynomial T x y w (assocLeftPolynomial F i) =
        (M.coord ((M.normalWord x * M.normalWord y) * M.normalWord w) i : ℚ) := by
    rw [assoc_left_polynomial]
    have hassign :
        mulVarQ (fun I => (T I : ℚ))
            (fun j => evalMulPolynomial T x y (F j))
          (fun j => (w j : ℚ)) =
        evalMulVar T xy w := by
      funext v
      cases v with
      | param I => rfl
      | left j => exact hXY j
      | right j => rfl
    rw [show
      evalMulQ (fun I => (T I : ℚ))
          (fun j => evalMulPolynomial T x y (F j))
          (fun j => (w j : ℚ)) (F i) =
        evalMulPolynomial T xy w (F i) by
          change MvPolynomial.eval
              (mulVarQ (fun I => (T I : ℚ))
                (fun j => evalMulPolynomial T x y (F j))
                (fun j => (w j : ℚ))) (F i) =
            MvPolynomial.eval (evalMulVar T xy w) (F i)
          rw [hassign]]
    exact hLeft
  have hright :
      evalAssocPolynomial T x y w (assocRightPolynomial F i) =
        (M.coord (M.normalWord x * (M.normalWord y * M.normalWord w)) i : ℚ) := by
    rw [eval_assoc_polynomial]
    have hassign :
        mulVarQ (fun I => (T I : ℚ))
            (fun j => (x j : ℚ))
            (fun j => evalMulPolynomial T y w (F j)) =
          evalMulVar T x yw := by
      funext v
      cases v with
      | param I => rfl
      | left j => rfl
      | right j => exact hYW j
    rw [show
      evalMulQ (fun I => (T I : ℚ))
          (fun j => (x j : ℚ))
          (fun j => evalMulPolynomial T y w (F j)) (F i) =
        evalMulPolynomial T x yw (F i) by
          change MvPolynomial.eval
              (mulVarQ (fun I => (T I : ℚ))
                (fun j => (x j : ℚ))
                (fun j => evalMulPolynomial T y w (F j))) (F i) =
            MvPolynomial.eval (evalMulVar T x yw) (F i)
          rw [hassign]]
    exact hRight
  calc
    evalAssocPolynomial T x y w (associatorPolynomial F i)
        = evalAssocPolynomial T x y w (assocLeftPolynomial F i) -
          evalAssocPolynomial T x y w (assocRightPolynomial F i) := by
            simp [associatorPolynomial, evalAssocPolynomial]
    _ = (M.coord ((M.normalWord x * M.normalWord y) * M.normalWord w) i : ℚ) -
          (M.coord (M.normalWord x * (M.normalWord y * M.normalWord w)) i : ℚ) := by
            rw [hleft, hright]
    _ = 0 := by
      rw [mul_assoc]
      simp

lemma associator_polynomial_zero {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F)
    (x y w : Fin n → ℤ) (i : Fin n) :
    evalAssocPolynomial T x y w (associatorPolynomial F i) = 0 := by
  exact eval_associator_zero M F x y w i
    (fun j => hF x y j)
    (fun j => hF y w j)
    (by
      have hxyword :
          M.normalWord (M.coord (M.normalWord x * M.normalWord y)) =
            M.normalWord x * M.normalWord y :=
        M.normalWord_coord (M.normalWord x * M.normalWord y)
      simpa [hxyword] using
        hF (M.coord (M.normalWord x * M.normalWord y)) w i)
    (by
      have hywword :
          M.normalWord (M.coord (M.normalWord y * M.normalWord w)) =
            M.normalWord y * M.normalWord w :=
        M.normalWord_coord (M.normalWord y * M.normalWord w)
      simpa [hywword] using
        hF x (M.coord (M.normalWord y * M.normalWord w)) i)

/--
All-integer equality of associator polynomial evaluations implies equality
after specializing the parameters.
-/
theorem specialize_assoc_eval
    (T : ParameterIndex n → ℤ) (p q : MvPolynomial (AssocVar n) ℚ)
    (hEval : ∀ x y w : Fin n → ℤ,
      evalAssocPolynomial T x y w p = evalAssocPolynomial T x y w q) :
    specializeAssoc T p = specializeAssoc T q := by
  apply MvPolynomial.funext_set
    (s := fun _ : TripleVar n => Set.range fun z : ℤ => (z : ℚ))
  · intro v
    exact Set.infinite_range_of_injective Int.cast_injective
  · intro qval hq
    choose z hz using fun v => hq v (Set.mem_univ v)
    let x : Fin n → ℤ := fun i => z (TripleVar.x i)
    let y : Fin n → ℤ := fun i => z (TripleVar.y i)
    let w : Fin n → ℤ := fun i => z (TripleVar.w i)
    have hq_eq : qval = evalTripleVar x y w := by
      funext v
      cases v <;> exact (hz _).symm
    rw [hq_eq, eval_specializeAssoc, eval_specializeAssoc]
    exact hEval x y w

lemma specialize_assoc_int
    (T : ParameterIndex n → ℤ) (p : MvPolynomial (AssocVar n) ℚ)
    (hp : ∀ x y w : Fin n → ℤ, evalAssocPolynomial T x y w p = 0) :
    specializeAssoc T p = 0 := by
  have h := specialize_assoc_eval T p 0
    (fun x y w => by simpa using hp x y w)
  simpa using h

/--
Section 4, theorem: in a consistent presentation, the specialized
associativity defect polynomial is zero.
-/
theorem specialized_associator {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ) (i : Fin n)
    (hEval : ∀ x y w,
      evalAssocPolynomial T x y w (associatorPolynomial F i) = 0) :
    specializeAssoc T (associatorPolynomial F i) = 0 :=
  specialize_assoc_int T (associatorPolynomial F i) hEval

theorem specialized_zero {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F) (i : Fin n) :
    specializeAssoc T (associatorPolynomial F i) = 0 :=
  specialized_associator F i
    (fun x y w => associator_polynomial_zero M F hF x y w i)

/-- Coefficient form of the Section 4 theorem. -/
theorem specialized_associator_eval {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ) (i : Fin n)
    (m : TripleVar n →₀ ℕ)
    (hEval : ∀ x y w,
      evalAssocPolynomial T x y w (associatorPolynomial F i) = 0) :
    (specializeAssoc T (associatorPolynomial F i)).coeff m = 0 := by
  rw [specialized_associator F i hEval]
  simp

theorem specialized_coeff_zero {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F) (i : Fin n)
    (m : TripleVar n →₀ ℕ) :
    (specializeAssoc T (associatorPolynomial F i)).coeff m = 0 := by
  exact specialized_associator_eval F i m
    (fun x y w => associator_polynomial_zero M F hF x y w i)

/-- Evaluation of parameter polynomials at a fixed integer parameter tuple. -/
def parameterEvaluation (T : ParameterIndex n → ℤ) :
    MvPolynomial (ParameterIndex n) ℚ →+* ℚ :=
  MvPolynomial.eval fun I => (T I : ℚ)

/-- Split multiplication variables into the pure input variables and the parameters. -/
def mulVarSum (n : ℕ) : MulVar n ≃ (MulInputVar n ⊕ ParameterIndex n) where
  toFun
    | MulVar.param I => Sum.inr I
    | MulVar.left i => Sum.inl (MulInputVar.left i)
    | MulVar.right i => Sum.inl (MulInputVar.right i)
  invFun
    | Sum.inr I => MulVar.param I
    | Sum.inl (MulInputVar.left i) => MulVar.left i
    | Sum.inl (MulInputVar.right i) => MulVar.right i
  left_inv := by
    intro v
    cases v <;> rfl
  right_inv := by
    intro v
    cases v with
    | inl t => cases t <;> rfl
    | inr I => rfl

/--
View a multiplication polynomial as a polynomial in `x,y` with
parameter-polynomial coefficients.
-/
def mulInputHom (n : ℕ) :
    MvPolynomial (MulVar n) ℚ →+*
      MvPolynomial (MulInputVar n) (MvPolynomial (ParameterIndex n) ℚ) :=
  ((MvPolynomial.sumAlgEquiv ℚ (MulInputVar n) (ParameterIndex n)).toRingEquiv.toRingHom).comp
    ((MvPolynomial.renameEquiv ℚ (mulVarSum n)).toRingEquiv.toRingHom)

/--
View a multiplication polynomial as a polynomial in `x,y` with
parameter-polynomial coefficients.
-/
def mulInputPolynomial (p : MvPolynomial (MulVar n) ℚ) :
    MvPolynomial (MulInputVar n) (MvPolynomial (ParameterIndex n) ℚ) :=
  mulInputHom n p

theorem mul_parameter_evaluation
    (T : ParameterIndex n → ℤ) (p : MvPolynomial (MulVar n) ℚ) :
    MvPolynomial.map (parameterEvaluation T) (mulInputPolynomial p) =
      specializeMul T p := by
  have hhom :
      ((MvPolynomial.map (parameterEvaluation T)).comp (mulInputHom n)) =
        (MvPolynomial.eval₂Hom MvPolynomial.C (mulSpecialization T) :
          MvPolynomial (MulVar n) ℚ →+* MvPolynomial (MulInputVar n) ℚ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [mulInputHom, parameterEvaluation]
    · intro v
      cases v <;>
        simp [mulInputHom, mulVarSum, mulSpecialization, parameterEvaluation]
  change (((MvPolynomial.map (parameterEvaluation T)).comp (mulInputHom n)) p) =
    (MvPolynomial.eval₂Hom MvPolynomial.C (mulSpecialization T)) p
  rw [hhom]

theorem eval_parameter_evaluation
    (T : ParameterIndex n → ℤ) (x y : Fin n → ℤ)
    (p : MvPolynomial (MulVar n) ℚ) :
    MvPolynomial.eval (mulInputVar x y)
        (MvPolynomial.map (parameterEvaluation T) (mulInputPolynomial p)) =
      evalMulPolynomial T x y p := by
  rw [mul_parameter_evaluation, eval_specializeMul]

/-- Split associativity variables into the pure variables and the parameters. -/
def assocVarSum (n : ℕ) : AssocVar n ≃ (TripleVar n ⊕ ParameterIndex n) where
  toFun
    | AssocVar.param I => Sum.inr I
    | AssocVar.x i => Sum.inl (TripleVar.x i)
    | AssocVar.y i => Sum.inl (TripleVar.y i)
    | AssocVar.w i => Sum.inl (TripleVar.w i)
  invFun
    | Sum.inr I => AssocVar.param I
    | Sum.inl (TripleVar.x i) => AssocVar.x i
    | Sum.inl (TripleVar.y i) => AssocVar.y i
    | Sum.inl (TripleVar.w i) => AssocVar.w i
  left_inv := by
    intro v
    cases v <;> rfl
  right_inv := by
    intro v
    cases v with
    | inl t => cases t <;> rfl
    | inr I => rfl

/--
View an associativity polynomial as a polynomial in `x,y,w` with
parameter-polynomial coefficients.
-/
def assocTripleHom (n : ℕ) :
    MvPolynomial (AssocVar n) ℚ →+*
      MvPolynomial (TripleVar n) (MvPolynomial (ParameterIndex n) ℚ) :=
  ((MvPolynomial.sumAlgEquiv ℚ (TripleVar n) (ParameterIndex n)).toRingEquiv.toRingHom).comp
    ((MvPolynomial.renameEquiv ℚ (assocVarSum n)).toRingEquiv.toRingHom)

/--
View an associativity polynomial as a polynomial in `x,y,w` with
parameter-polynomial coefficients.
-/
def assocTriplePolynomial (p : MvPolynomial (AssocVar n) ℚ) :
    MvPolynomial (TripleVar n) (MvPolynomial (ParameterIndex n) ℚ) :=
  assocTripleHom n p

/-- The parameter polynomial multiplying a fixed `x,y,w` monomial in `P_i`. -/
def associatorCoefficientPolynomial
    (F : Fin n → MvPolynomial (MulVar n) ℚ) (i : Fin n)
    (m : TripleVar n →₀ ℕ) :
    MvPolynomial (ParameterIndex n) ℚ :=
  (assocTriplePolynomial (associatorPolynomial F i)).coeff m

theorem assoc_parameter_evaluation
    (T : ParameterIndex n → ℤ) (p : MvPolynomial (AssocVar n) ℚ) :
    (MvPolynomial.map (parameterEvaluation T)) (assocTriplePolynomial p) =
      specializeAssoc T p := by
  have hhom :
      ((MvPolynomial.map (parameterEvaluation T)).comp (assocTripleHom n)) =
        (MvPolynomial.eval₂Hom MvPolynomial.C (assocSpecialization T) :
          MvPolynomial (AssocVar n) ℚ →+* MvPolynomial (TripleVar n) ℚ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [assocTripleHom, parameterEvaluation]
    · intro v
      cases v <;>
        simp [assocTripleHom, assocVarSum, assocSpecialization, parameterEvaluation]
  change (((MvPolynomial.map (parameterEvaluation T)).comp (assocTripleHom n)) p) =
    (MvPolynomial.eval₂Hom MvPolynomial.C (assocSpecialization T)) p
  rw [hhom]

theorem parameter_evaluation_associator
    {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ) (i : Fin n)
    (m : TripleVar n →₀ ℕ) :
    parameterEvaluation T (associatorCoefficientPolynomial F i m) =
      (specializeAssoc T (associatorPolynomial F i)).coeff m := by
  have h := congrArg (fun q : MvPolynomial (TripleVar n) ℚ => q.coeff m)
    (assoc_parameter_evaluation T (associatorPolynomial F i))
  simpa [associatorCoefficientPolynomial, MvPolynomial.coeff_map] using h

/--
Section 4 coefficient form: each parameter coefficient of the associator
vanishes at every consistent parameter tuple represented by `M`.
-/
theorem associator_coefficient_vanishes
    {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ) (i : Fin n)
    (m : TripleVar n →₀ ℕ)
    (hEval : ∀ x y w,
      evalAssocPolynomial T x y w (associatorPolynomial F i) = 0) :
    parameterEvaluation T (associatorCoefficientPolynomial F i m) = 0 := by
  rw [parameter_evaluation_associator F i m]
  exact specialized_associator_eval F i m hEval

theorem associator_polynomial_vanishes
    {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F) (i : Fin n)
    (m : TripleVar n →₀ ℕ) :
    parameterEvaluation T (associatorCoefficientPolynomial F i m) = 0 := by
  exact associator_coefficient_vanishes F i m
    (fun x y w => associator_polynomial_zero M F hF x y w i)

/-- The ideal of parameter polynomials vanishing at a fixed tuple `T`. -/
def vanishingIdealAt (T : ParameterIndex n → ℤ) :
    Ideal (MvPolynomial (ParameterIndex n) ℚ) :=
  RingHom.ker (parameterEvaluation T)

/-- The set of all parameter coefficients of the associator coordinates. -/
def associatorCoefficientSet
    (F : Fin n → MvPolynomial (MulVar n) ℚ) :
    Set (MvPolynomial (ParameterIndex n) ℚ) :=
  Set.range fun im : Fin n × (TripleVar n →₀ ℕ) =>
    associatorCoefficientPolynomial F im.1 im.2

/--
The zero locus of the Section 4 coefficient equations
`C_1(T)=...=C_r(T)=0`.
-/
def consistencyObstructionLocus
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (T : ParameterIndex n → ℤ) : Prop :=
  ∀ p ∈ associatorCoefficientSet F, parameterEvaluation T p = 0

/--
Direct zero-locus form of Section 4's theorem: every consistent parameter
tuple represented by `M` satisfies all associator coefficient equations.
-/
theorem consistency_locus_eval
    {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hEval : ∀ i x y w,
      evalAssocPolynomial T x y w (associatorPolynomial F i) = 0) :
    consistencyObstructionLocus F T := by
  intro p hp
  rcases hp with ⟨⟨i, m⟩, rfl⟩
  exact associator_coefficient_vanishes F i m (hEval i)

theorem consistency_locus_represents
    {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F) :
    consistencyObstructionLocus F T := by
  exact consistency_locus_eval F
    (fun i x y w => associator_polynomial_zero M F hF x y w i)

/--
Set-level form of the Section 4 theorem: if one polynomial family represents
multiplication for every consistent parameter tuple, then the consistency
locus `C_n` is contained in the zero locus of the associator coefficients.
-/
theorem consistency_locus_subset
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : ∀ {T : ParameterIndex n → ℤ} (M : CPres n T),
      RepresentsMultiplication M F) :
    CPres.consistencyLocus n ⊆
      {T | consistencyObstructionLocus F T} := by
  intro T hT
  rcases hT with ⟨M⟩
  exact consistency_locus_represents M F (hF M)

/-- Cant--Eick's Section 4 obstruction ideal `I_n(T)`. -/
def consistencyObstructionIdeal
    (F : Fin n → MvPolynomial (MulVar n) ℚ) :
    Ideal (MvPolynomial (ParameterIndex n) ℚ) :=
  Ideal.span (associatorCoefficientSet F)

theorem associator_consistency_obstruction
    (F : Fin n → MvPolynomial (MulVar n) ℚ) (i : Fin n)
    (m : TripleVar n →₀ ℕ) :
    associatorCoefficientPolynomial F i m ∈ consistencyObstructionIdeal F := by
  exact Ideal.subset_span (Set.mem_range_self (i, m))

theorem consistency_obstruction_ideal
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (J : Ideal (MvPolynomial (ParameterIndex n) ℚ)) :
    consistencyObstructionIdeal F ≤ J ↔
      ∀ (i : Fin n) (m : TripleVar n →₀ ℕ),
        associatorCoefficientPolynomial F i m ∈ J := by
  rw [consistencyObstructionIdeal, Ideal.span_le, associatorCoefficientSet,
    Set.range_subset_iff]
  constructor
  · intro h i m
    exact h (i, m)
  · intro h im
    exact h im.1 im.2

theorem consistency_locus_vanishing
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (T : ParameterIndex n → ℤ) :
    consistencyObstructionLocus F T ↔
      consistencyObstructionIdeal F ≤ vanishingIdealAt T := by
  constructor
  · intro h
    rw [consistencyObstructionIdeal, Ideal.span_le]
    intro p hp
    exact h p hp
  · intro h p hp
    exact h (Ideal.subset_span hp)

/--
Formal statement of the Section 4 conjecture.  This is recorded as a
proposition, not assumed as a theorem: if all obstruction coefficients vanish
at a parameter tuple, then the tuple is consistent.
-/
def consistencyObstructionConjecture
    (F : Fin n → MvPolynomial (MulVar n) ℚ) : Prop :=
  ∀ T : ParameterIndex n → ℤ,
    consistencyObstructionLocus F T → CPres.IsConsistent T

/-- The Section 4 conjecture restated exactly as a zero-locus inclusion. -/
theorem consistency_conjecture_locus
    (F : Fin n → MvPolynomial (MulVar n) ℚ) :
    consistencyObstructionConjecture F ↔
      {T | consistencyObstructionLocus F T} ⊆
        CPres.consistencyLocus n := by
  constructor
  · intro h T hT
    exact h T hT
  · intro h T hT
    exact h hT

/--
Formal version of the sentence following the Section 4 conjecture: if the
conjecture holds, and `F` represents multiplication on every consistent
presentation, then the obstruction equations exactly describe consistency.
-/
theorem consistency_locus_conjecture
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : ∀ {T : ParameterIndex n → ℤ} (M : CPres n T),
      RepresentsMultiplication M F)
    (hConj : consistencyObstructionConjecture F) :
    CPres.consistencyLocus n =
      {T | consistencyObstructionLocus F T} := by
  apply Set.Subset.antisymm
  · exact consistency_locus_subset F hF
  · intro T hT
    exact hConj T hT

theorem consistency_vanishing_eval
    {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hEval : ∀ i x y w,
      evalAssocPolynomial T x y w (associatorPolynomial F i) = 0) :
    consistencyObstructionIdeal F ≤ vanishingIdealAt T := by
  rw [consistencyObstructionIdeal, Ideal.span_le, associatorCoefficientSet,
    Set.range_subset_iff]
  intro im
  exact associator_coefficient_vanishes F im.1 im.2 (hEval im.1)

theorem consistency_ideal_vanishing
    {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F) :
    consistencyObstructionIdeal F ≤ vanishingIdealAt T := by
  exact consistency_vanishing_eval F
    (fun i x y w => associator_polynomial_zero M F hF x y w i)

theorem sub_vanishing_ideal (T : ParameterIndex n → ℤ)
    {p q : MvPolynomial (ParameterIndex n) ℚ}
    (h : p - q ∈ vanishingIdealAt T) :
    parameterEvaluation T p = parameterEvaluation T q := by
  have hzero : parameterEvaluation T (p - q) = 0 := h
  simpa [parameterEvaluation, sub_eq_zero] using hzero

/--
Section 4 corollary, abstract form: replacing a parameter polynomial by a
remainder that differs by an element vanishing at every consistent parameter
does not change its value at that parameter.
-/
theorem remainder_vanishing_ideal
    (T : ParameterIndex n → ℤ)
    {p r : MvPolynomial (ParameterIndex n) ℚ}
    (h : p - r ∈ vanishingIdealAt T) :
    parameterEvaluation T r = parameterEvaluation T p :=
  (sub_vanishing_ideal T h).symm

/--
Section 4 corollary: reducing a parameter polynomial modulo the obstruction
ideal does not change its value at a consistent parameter tuple.
-/
theorem remainder_consistency_obstruction
    {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hEval : ∀ i x y w,
      evalAssocPolynomial T x y w (associatorPolynomial F i) = 0)
    {p r : MvPolynomial (ParameterIndex n) ℚ}
    (h : p - r ∈ consistencyObstructionIdeal F) :
    parameterEvaluation T r = parameterEvaluation T p :=
  remainder_vanishing_ideal T
    ((consistency_vanishing_eval F hEval) h)

theorem remainder_obstruction_ideal
    {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F)
    {p r : MvPolynomial (ParameterIndex n) ℚ}
    (h : p - r ∈ consistencyObstructionIdeal F) :
    parameterEvaluation T r = parameterEvaluation T p :=
  remainder_consistency_obstruction F
    (fun i x y w => associator_polynomial_zero M F hF x y w i) h

/--
Coefficientwise membership in an ideal for polynomials whose coefficients are
parameter polynomials.
-/
def coefficientwiseSubMem
    (I : Ideal (MvPolynomial (ParameterIndex n) ℚ))
    (p r : MvPolynomial σ (MvPolynomial (ParameterIndex n) ℚ)) : Prop :=
  ∀ m, p.coeff m - r.coeff m ∈ I

theorem coefficientwise_vanishing_ideal
    (T : ParameterIndex n → ℤ)
    {p r : MvPolynomial σ (MvPolynomial (ParameterIndex n) ℚ)}
    (h : coefficientwiseSubMem (vanishingIdealAt T) p r) :
    MvPolynomial.map (parameterEvaluation T) p =
      MvPolynomial.map (parameterEvaluation T) r := by
  ext m
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map]
  exact sub_vanishing_ideal T (h m)

/--
Section 4 corollary, coefficientwise polynomial form: reducing every
parameter coefficient modulo the obstruction ideal does not change the
specialization of the whole polynomial at a consistent tuple.
-/
theorem coefficientwise_sub_consistency
    {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F)
    {p r : MvPolynomial σ (MvPolynomial (ParameterIndex n) ℚ)}
    (h : coefficientwiseSubMem (consistencyObstructionIdeal F) p r) :
    MvPolynomial.map (parameterEvaluation T) r =
      MvPolynomial.map (parameterEvaluation T) p := by
  symm
  apply coefficientwise_vanishing_ideal T
  intro m
  exact (consistency_ideal_vanishing M F hF) (h m)

theorem remainder_coefficientwise_eval
    {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hEval : ∀ i x y w,
      evalAssocPolynomial T x y w (associatorPolynomial F i) = 0)
    {p r : MvPolynomial σ (MvPolynomial (ParameterIndex n) ℚ)}
    (h : coefficientwiseSubMem (consistencyObstructionIdeal F) p r) :
    MvPolynomial.map (parameterEvaluation T) r =
      MvPolynomial.map (parameterEvaluation T) p := by
  symm
  apply coefficientwise_vanishing_ideal T
  intro m
  exact (consistency_vanishing_eval F hEval) (h m)

/--
Section 4 corollary for multiplication polynomials: reducing each
parameter-coefficient of a multiplication polynomial modulo the obstruction
ideal does not change its value at a consistent parameter tuple.
-/
theorem remainder_coefficientwise_ideal
    {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hEval : ∀ i x y w,
      evalAssocPolynomial T x y w (associatorPolynomial F i) = 0)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem (consistencyObstructionIdeal F)
      (mulInputPolynomial p) (mulInputPolynomial r))
    (x y : Fin n → ℤ) :
    evalMulPolynomial T x y r = evalMulPolynomial T x y p := by
  have hmap :=
    remainder_coefficientwise_eval
      F hEval h
  have heval := congrArg (MvPolynomial.eval (mulInputVar x y)) hmap
  rw [eval_parameter_evaluation,
    eval_parameter_evaluation] at heval
  exact heval

/--
Section 4 corollary for multiplication polynomials, as equality of the
parameter-specialized polynomials.
-/
theorem specialize_remainder_coefficientwise
    {T : ParameterIndex n → ℤ}
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hEval : ∀ i x y w,
      evalAssocPolynomial T x y w (associatorPolynomial F i) = 0)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem (consistencyObstructionIdeal F)
      (mulInputPolynomial p) (mulInputPolynomial r)) :
    specializeMul T r = specializeMul T p := by
  have hmap :=
    remainder_coefficientwise_eval
      F hEval h
  simpa [mul_parameter_evaluation] using hmap

theorem remainder_coefficientwise_sub
    {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem (consistencyObstructionIdeal F)
      (mulInputPolynomial p) (mulInputPolynomial r))
    (x y : Fin n → ℤ) :
    evalMulPolynomial T x y r = evalMulPolynomial T x y p := by
  exact remainder_coefficientwise_ideal
    F (fun i x y w => associator_polynomial_zero M F hF x y w i) h x y

/--
Represented form of the Section 4 multiplication-remainder corollary, as
equality of parameter-specialized polynomials.
-/
theorem specialize_coefficientwise_ideal
    {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (F : Fin n → MvPolynomial (MulVar n) ℚ)
    (hF : RepresentsMultiplication M F)
    {p r : MvPolynomial (MulVar n) ℚ}
    (h : coefficientwiseSubMem (consistencyObstructionIdeal F)
      (mulInputPolynomial p) (mulInputPolynomial r)) :
    specializeMul T r = specializeMul T p :=
  specialize_remainder_coefficientwise
    F (fun i x y w => associator_polynomial_zero M F hF x y w i) h

end

end CantEick
end Towers
