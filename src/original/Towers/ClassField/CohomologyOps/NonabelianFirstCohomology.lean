import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# Appendix, Exercise A-5: nonabelian first cohomology

Mathlib's nonabelian `H^1` currently concerns sheaves on sites, not an ordinary
group acting by automorphisms on a possibly noncommutative group.  This file
therefore records Milne's definitions directly: crossed homomorphisms, twisting
by an element of the coefficient group, the resulting equivalence relation,
and the pointed quotient set.

The full classification of descended quadratic spaces requires a semilinear
Galois action and descent of isometries.  Those interfaces are not presently
connected to `QuadraticForm.IsometryEquiv`, so the classification theorem is
not asserted here.  Its final concrete `R/C` example is proved directly.
-/

namespace Towers.CField.COps.NFCohomo

variable (G A : Type*) [Group G] [Group A] [MulDistribMulAction G A]

/-- A nonabelian crossed homomorphism `phi : G -> A`, satisfying
`phi (sigma*tau) = phi sigma * sigma(phi tau)`. -/
structure CHom where
  toFun : G → A
  map_mul' : ∀ sigma tau, toFun (sigma * tau) = toFun sigma * sigma • toFun tau

namespace CHom

instance : CoeFun (CHom G A) fun _ ↦ G → A := ⟨CHom.toFun⟩

@[ext]
theorem ext {phi psi : CHom G A} (h : ∀ sigma, phi sigma = psi sigma) :
    phi = psi := by
  cases phi
  cases psi
  simp only [mk.injEq]
  exact funext h

@[simp]
theorem map_mul (phi : CHom G A) (sigma tau : G) :
    phi (sigma * tau) = phi sigma * sigma • phi tau :=
  phi.map_mul' sigma tau

/-- The distinguished trivial crossed homomorphism. -/
protected def one : CHom G A where
  toFun _ := 1
  map_mul' sigma _ := by
    rw [smul_one]
    simp

instance : One (CHom G A) := ⟨CHom.one G A⟩

@[simp]
theorem one_apply (sigma : G) : (1 : CHom G A) sigma = 1 := rfl

/-- Every crossed homomorphism sends the identity to the identity. -/
@[simp]
theorem map_one (phi : CHom G A) : phi 1 = 1 := by
  have h := map_mul G A phi (1 : G) (1 : G)
  have h' : phi 1 * 1 = phi 1 * phi 1 := by
    simpa only [one_mul, one_smul, mul_one] using h
  exact (mul_left_cancel h').symm

/-- Twisting a crossed homomorphism by `a` gives the equivalent cocycle
`sigma |-> a^-1 * phi(sigma) * sigma(a)`. -/
def twist (phi : CHom G A) (a : A) : CHom G A where
  toFun sigma := a⁻¹ * phi sigma * sigma • a
  map_mul' sigma tau := by
    rw [phi.map_mul, mul_smul]
    simp only [smul_mul', smul_inv', mul_assoc]
    group

@[simp]
theorem twist_apply (phi : CHom G A) (a : A) (sigma : G) :
    twist G A phi a sigma = a⁻¹ * phi sigma * sigma • a := rfl

/-- A principal crossed homomorphism. -/
def principal (a : A) : CHom G A :=
  twist G A (1 : CHom G A) a

@[simp]
theorem principal_apply (a : A) (sigma : G) :
    principal G A a sigma = a⁻¹ * sigma • a := by
  simp only [principal, twist_apply, one_apply, mul_one]

/-- Milne's equivalence relation on nonabelian crossed homomorphisms. -/
def IsCohomologous (phi psi : CHom G A) : Prop :=
  ∃ a : A, ∀ sigma : G, psi sigma = a⁻¹ * phi sigma * sigma • a

theorem isCohomologous_refl (phi : CHom G A) :
    IsCohomologous G A phi phi := by
  refine ⟨1, ?_⟩
  intro sigma
  rw [inv_one, one_mul, smul_one, mul_one]

theorem isCohomologous_symm {phi psi : CHom G A}
    (h : IsCohomologous G A phi psi) :
    IsCohomologous G A psi phi := by
  rcases h with ⟨a, ha⟩
  refine ⟨a⁻¹, ?_⟩
  intro sigma
  rw [ha sigma]
  simp only [inv_inv, smul_inv']
  group

theorem isCohomologous_trans {phi psi chi : CHom G A}
    (hphi : IsCohomologous G A phi psi)
    (hpsi : IsCohomologous G A psi chi) :
    IsCohomologous G A phi chi := by
  rcases hphi with ⟨a, ha⟩
  rcases hpsi with ⟨b, hb⟩
  refine ⟨a * b, ?_⟩
  intro sigma
  rw [hb sigma, ha sigma]
  simp only [mul_inv_rev, smul_mul', mul_assoc]

/-- The setoid whose quotient is nonabelian first cohomology. -/
def isCohomologousSetoid : Setoid (CHom G A) where
  r := IsCohomologous G A
  iseqv := ⟨isCohomologous_refl G A, isCohomologous_symm G A,
    isCohomologous_trans G A⟩

/-- The pointed set `H^1(G,A)` for a nonabelian coefficient group. -/
def H1 := Quotient (isCohomologousSetoid G A)

instance : One (H1 G A) :=
  ⟨Quotient.mk (isCohomologousSetoid G A) (1 : CHom G A)⟩

/-- Every principal cocycle represents the distinguished class. -/
theorem principal_cohomologous_one (a : A) :
    IsCohomologous G A (1 : CHom G A) (principal G A a) := by
  exact ⟨a, fun sigma ↦ by simp only [principal_apply, one_apply, mul_one]⟩

end CHom

namespace QExampl

open QuadraticMap

/-- The positive binary diagonal weights `(1,1)`. -/
def positiveWeights (K : Type*) [One K] : Fin 2 → K := fun _ ↦ 1

/-- The split binary diagonal weights `(1,-1)`. -/
def splitWeights (K : Type*) [Ring K] : Fin 2 → K :=
  fun i ↦ if i = 0 then 1 else -1

/-- The forms `X^2+Y^2` and `X^2-Y^2` become isometric over `C`: multiply
the second coordinate by `i`. -/
noncomputable def planeComplexSplit :
    IsometryEquiv
      (weightedSumSquares ℂ (positiveWeights ℂ))
      (weightedSumSquares ℂ (splitWeights ℂ)) :=
  QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
    (fun i ↦ if i = 0 then 1 else Units.mk0 Complex.I (by simp)) (by
      intro i
      fin_cases i <;> simp [positiveWeights, splitWeights, Complex.I_sq])

/-- Over `R`, the positive form `X^2+Y^2` is not isometric to the split form
`X^2-Y^2`; their negative signatures are respectively zero and one. -/
theorem plane_equivalent_split :
    ¬Equivalent
      (weightedSumSquares ℝ (positiveWeights ℝ))
      (weightedSumSquares ℝ (splitWeights ℝ)) := by
  intro h
  have hsig := h.sigNeg_eq
  rw [QuadraticForm.sigNeg_weightedSumSquares,
    QuadraticForm.sigNeg_weightedSumSquares] at hsig
  have hpositive : {i : Fin 2 | positiveWeights ℝ i < 0}.ncard = 0 := by
    rw [show {i : Fin 2 | positiveWeights ℝ i < 0} = (∅ : Set (Fin 2)) by
      ext i
      simp [positiveWeights]]
    simp
  have hsplit : {i : Fin 2 | splitWeights ℝ i < 0}.ncard = 1 := by
    rw [show {i : Fin 2 | splitWeights ℝ i < 0} = ({1} : Set (Fin 2)) by
      ext i
      fin_cases i <;> simp [splitWeights]]
    simp
  rw [hpositive, hsplit] at hsig
  norm_num at hsig

end QExampl

end Towers.CField.COps.NFCohomo
