import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Submission.ClassField.CrossedProducts.MulApply
import Submission.ClassField.CrossedProducts.BrauerBimoduleCriterion


/-!
# Chapter IV, Section 3, Lemma 3.15: bimodule proof infrastructure

Milne proves tensor compatibility by putting commuting actions on

`V = A(c) tensor_L A(d)`.

This file carries out that construction.  It defines the diagonal left action
of `A(c*d)` and the right action of `A(c) tensor_k A(d)`, proves that they
commute, and identifies their combined action with the full endomorphism
algebra of `V` by simplicity and a dimension count.  The resulting Brauer
equivalence is Milne's Lemma 3.15.
-/

namespace Submission.CField.CProduca

noncomputable section

open scoped TensorProduct

universe u

attribute [local instance] Units.mulDistribMulActionRight

namespace CProduc

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (c d : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))

/-- Milne's underlying bimodule candidate `A(c) tensor_L A(d)`. -/
abbrev tensorBimodule := CProduc c ⊗[L] CProduc d

/-- The tensor products of the two standard crossed-product bases form an
`L`-basis of Milne's bimodule. -/
noncomputable def tensorBimoduleBasis :
    Module.Basis (Gal(L/k) × Gal(L/k)) L (tensorBimodule k L c d) :=
  (basis c).tensorProduct (basis d)

instance tensorBimoduleNontrivial :
    Nontrivial (tensorBimodule k L c d) :=
  ⟨tensorBimoduleBasis k L c d (1, 1), 0,
    (tensorBimoduleBasis k L c d).ne_zero (1, 1)⟩

instance tensorBimoduleModule :
    Module.Finite k (tensorBimodule k L c d) :=
  Module.Finite.trans L (tensorBimodule k L c d)

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem tensor_bimodule_basis (rho tau : Gal(L/k)) :
    tensorBimoduleBasis k L c d (rho, tau) =
      basis c rho ⊗ₜ[L] basis d tau := by
  simp [tensorBimoduleBasis]

/-- The contribution of the `(rho,tau)` coordinate to the action of
`l e_sigma`.  It is `k`-linear in that coordinate, with the Galois
automorphism accounting for its `sigma`-semilinearity over `L`. -/
noncomputable def diagonalCoordinateAction
    (sigma : Gal(L/k)) (l : L) (p : Gal(L/k) × Gal(L/k)) :
    L →ₗ[k] tensorBimodule k L c d :=
  (((LinearMap.mulLeft k
      (l * (c (sigma, p.1) : L) * (d (sigma, p.2) : L))).comp
      sigma.toLinearEquiv.toLinearMap).smulRight
        (tensorBimoduleBasis k L c d (sigma * p.1, sigma * p.2)))

/-- The `k`-linear action on `V` of the crossed-product basis element
`l e_sigma` in `A(c*d)`, defined through tensor-basis coordinates. -/
noncomputable def diagonalSingleAction
    (sigma : Gal(L/k)) (l : L) :
    Module.End k (tensorBimodule k L c d) :=
  (Finsupp.lsum k (fun p ↦ diagonalCoordinateAction k L c d sigma l p)).comp
    ((tensorBimoduleBasis k L c d).repr.toLinearMap.restrictScalars k)

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Coordinate formula for the diagonal action. -/
theorem diagonal_single_basis
    (sigma rho tau : Gal(L/k)) (l q : L) :
    diagonalSingleAction k L c d sigma l
        (q • tensorBimoduleBasis k L c d (rho, tau)) =
      (l * sigma q * (c (sigma, rho) : L) * (d (sigma, tau) : L)) •
        tensorBimoduleBasis k L c d (sigma * rho, sigma * tau) := by
  have hrepr :
      (tensorBimoduleBasis k L c d).repr
          (q • tensorBimoduleBasis k L c d (rho, tau)) =
        q • (tensorBimoduleBasis k L c d).repr
          (tensorBimoduleBasis k L c d (rho, tau)) :=
    (tensorBimoduleBasis k L c d).repr.map_smul q _
  rw [diagonalSingleAction, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars]
  change (Finsupp.lsum k
      (fun p ↦ diagonalCoordinateAction k L c d sigma l p))
      ((tensorBimoduleBasis k L c d).repr
        (q • tensorBimoduleBasis k L c d (rho, tau))) = _
  rw [hrepr, Module.Basis.repr_self, Finsupp.smul_single]
  simp only [Finsupp.lsum_single, diagonalCoordinateAction,
    LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    ]
  simp only [smul_eq_mul, mul_one]
  change
    (l * (c (sigma, rho) : L) * (d (sigma, tau) : L) * sigma q) •
        tensorBimoduleBasis k L c d (sigma * rho, sigma * tau) = _
  congr 1
  ring

omit [FiniteDimensional k L] [IsGalois k L] in
/-- In particular, the action on a tensor-basis vector has the expected two
factor-set coefficients. -/
theorem diagonal_action_basis
    (sigma rho tau : Gal(L/k)) (l : L) :
    diagonalSingleAction k L c d sigma l
        (tensorBimoduleBasis k L c d (rho, tau)) =
      (l * (c (sigma, rho) : L) * (d (sigma, tau) : L)) •
        tensorBimoduleBasis k L c d (sigma * rho, sigma * tau) := by
  simpa using diagonal_single_basis k L c d sigma rho tau l 1

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Two `k`-linear endomorphisms of the tensor bimodule agree if they agree
on every `L`-multiple of every tensor-basis vector. -/
theorem ext_bimodule_basis
    (f g : Module.End k (tensorBimodule k L c d))
    (h : ∀ (p : Gal(L/k) × Gal(L/k)) (q : L),
      f (q • tensorBimoduleBasis k L c d p) =
        g (q • tensorBimoduleBasis k L c d p)) :
    f = g := by
  apply LinearMap.ext
  intro x
  rw [← (tensorBimoduleBasis k L c d).repr.symm_apply_apply x]
  generalize (tensorBimoduleBasis k L c d).repr x = z
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single p q =>
      simpa only [Module.Basis.repr_symm_single] using h p q

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The coordinate actions satisfy the crossed-product multiplication law
for the product cocycle `c*d`. -/
theorem diagonal_single_mul
    (sigma tau : Gal(L/k)) (l m : L) :
    diagonalSingleAction k L c d sigma l *
        diagonalSingleAction k L c d tau m =
      diagonalSingleAction k L c d (sigma * tau)
        (l * sigma m * (c (sigma, tau) : L) * (d (sigma, tau) : L)) := by
  apply ext_bimodule_basis k L c d
  rintro ⟨rho, upsilon⟩ q
  change diagonalSingleAction k L c d sigma l
      (diagonalSingleAction k L c d tau m
        (q • tensorBimoduleBasis k L c d (rho, upsilon))) = _
  rw [diagonal_single_basis, diagonal_single_basis,
    diagonal_single_basis]
  simp only [mul_assoc]
  apply congrArg (fun a : L ↦ a •
    tensorBimoduleBasis k L c d (sigma * tau * rho, sigma * tau * upsilon))
  have hc := congrArg Units.val (c.isMulCocycle₂ sigma tau rho)
  have hd := congrArg Units.val (d.isMulCocycle₂ sigma tau upsilon)
  change (c (sigma * tau, rho) : L) * (c (sigma, tau) : L) =
    sigma (c (tau, rho) : L) * (c (sigma, tau * rho) : L) at hc
  change (d (sigma * tau, upsilon) : L) * (d (sigma, tau) : L) =
    sigma (d (tau, upsilon) : L) * (d (sigma, tau * upsilon) : L) at hd
  have hcd :
      (sigma (c (tau, rho) : L) * (c (sigma, tau * rho) : L)) *
          (sigma (d (tau, upsilon) : L) * (d (sigma, tau * upsilon) : L)) =
        ((c (sigma * tau, rho) : L) * (c (sigma, tau) : L)) *
          ((d (sigma * tau, upsilon) : L) * (d (sigma, tau) : L)) := by
    rw [← hc, ← hd]
  rw [show (sigma * tau) q = sigma (tau q) by rfl]
  simp only [map_mul]
  calc
    l * (sigma m * (sigma (tau q) *
        (sigma (c (tau, rho) : L) * sigma (d (tau, upsilon) : L))) *
        ((c (sigma, tau * rho) : L) * (d (sigma, tau * upsilon) : L))) =
      l * sigma m * sigma (tau q) *
        ((sigma (c (tau, rho) : L) * (c (sigma, tau * rho) : L)) *
          (sigma (d (tau, upsilon) : L) *
            (d (sigma, tau * upsilon) : L))) := by ring
    _ = l * sigma m * sigma (tau q) *
        (((c (sigma * tau, rho) : L) * (c (sigma, tau) : L)) *
          ((d (sigma * tau, upsilon) : L) * (d (sigma, tau) : L))) := by
      rw [hcd]
    _ = l *
        (sigma m *
          ((c (sigma, tau) : L) *
            ((d (sigma, tau) : L) *
              (sigma (tau q) *
                ((c (sigma * tau, rho) : L) *
                  (d (sigma * tau, upsilon) : L)))))) := by ring

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem diagonal_single_zero (sigma : Gal(L/k)) :
    diagonalSingleAction k L c d sigma 0 = 0 := by
  apply ext_bimodule_basis k L c d
  rintro ⟨rho, tau⟩ q
  rw [diagonal_single_basis]
  simp

omit [FiniteDimensional k L] [IsGalois k L] in
theorem diagonal_single_add (sigma : Gal(L/k)) (l m : L) :
    diagonalSingleAction k L c d sigma (l + m) =
      diagonalSingleAction k L c d sigma l +
        diagonalSingleAction k L c d sigma m := by
  apply ext_bimodule_basis k L c d
  rintro ⟨rho, tau⟩ q
  rw [LinearMap.add_apply, diagonal_single_basis,
    diagonal_single_basis, diagonal_single_basis]
  rw [add_mul, add_mul, add_mul, add_smul]

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem diagonal_single_one :
    diagonalSingleAction k L c d 1 1 = 1 := by
  apply ext_bimodule_basis k L c d
  rintro ⟨rho, tau⟩ q
  rw [diagonal_single_basis]
  simp

/-- Sum the single-coordinate actions over an element of the crossed product
for the product cocycle. -/
noncomputable def diagonalAction
    (x : CProduc (NMCocycl₂.mul c d)) :
    Module.End k (tensorBimodule k L c d) :=
  sum (NMCocycl₂.mul c d) x
    (fun sigma l ↦ diagonalSingleAction k L c d sigma l)

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem diagonalAction_single (sigma : Gal(L/k)) (l : L) :
    diagonalAction k L c d
        (single (NMCocycl₂.mul c d) sigma l) =
      diagonalSingleAction k L c d sigma l := by
  rw [diagonalAction, sum_single_index]
  exact diagonal_single_zero k L c d sigma

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem diagonalAction_zero :
    diagonalAction k L c d 0 = 0 := by
  exact sum_zero_index (NMCocycl₂.mul c d)

omit [FiniteDimensional k L] [IsGalois k L] in
theorem diagonalAction_add
    (x y : CProduc (NMCocycl₂.mul c d)) :
    diagonalAction k L c d (x + y) =
      diagonalAction k L c d x + diagonalAction k L c d y := by
  exact sum_add_index' (NMCocycl₂.mul c d)
    (fun sigma ↦ diagonal_single_zero k L c d sigma)
    (fun sigma ↦ diagonal_single_add k L c d sigma)

/-- The diagonal action is a ring representation of the crossed product for
the pointwise product cocycle on Milne's tensor bimodule. -/
noncomputable def diagonalLeftHom :
    CProduc (NMCocycl₂.mul c d) →+*
      Module.End k (tensorBimodule k L c d) where
  toFun := diagonalAction k L c d
  map_zero' := diagonalAction_zero k L c d
  map_one' := by
    rw [one_def, diagonalAction_single, diagonal_single_one]
  map_add' := diagonalAction_add k L c d
  map_mul' x y := by
    induction x using induction_on (NMCocycl₂.mul c d) with
    | zero => simp
    | hadd x₁ x₂ hx₁ hx₂ =>
        rw [add_mul, diagonalAction_add, diagonalAction_add, hx₁, hx₂,
          add_mul]
    | hsingle sigma l =>
        induction y using induction_on (NMCocycl₂.mul c d) with
        | zero => simp
        | hadd y₁ y₂ hy₁ hy₂ =>
            rw [mul_add, diagonalAction_add, diagonalAction_add, hy₁, hy₂,
              mul_add]
        | hsingle tau m =>
            rw [single_mul_single, diagonalAction_single,
              diagonalAction_single, diagonalAction_single,
              diagonal_single_mul]
            congr 1
            change
              l * sigma m * ((c (sigma, tau) : L) * (d (sigma, tau) : L)) =
                l * sigma m * (c (sigma, tau) : L) * (d (sigma, tau) : L)
            ring

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The identity Galois coordinate with a base-field coefficient acts by
ordinary base-field scalar multiplication. -/
theorem diagonal_single_action (r : k) :
    diagonalSingleAction k L c d 1 (algebraMap k L r) =
      algebraMap k (Module.End k (tensorBimodule k L c d)) r := by
  apply ext_bimodule_basis k L c d
  rintro ⟨rho, tau⟩ q
  rw [diagonal_single_basis]
  simp only [AlgEquiv.one_apply, NMCocycl₂.apply_one_fst, Units.val_one,
    mul_one, one_mul, tensor_bimodule_basis, basis_apply,
    Module.algebraMap_end_apply]
  rw [← smul_smul]
  rfl

/-- Milne's left action of `A(c*d)` on `A(c) tensor_L A(d)`. -/
noncomputable def diagonalLeftAction :
    CProduc (NMCocycl₂.mul c d) →ₐ[k]
      Module.End k (tensorBimodule k L c d) where
  __ := diagonalLeftHom k L c d
  commutes' r := by
    change diagonalAction k L c d
        (single (NMCocycl₂.mul c d) 1 (algebraMap k L r)) = _
    rw [diagonalAction_single, diagonal_single_action]

omit [FiniteDimensional k L] [IsGalois k L] in
theorem diagonal_action_injective :
    Function.Injective (diagonalLeftAction k L c d) :=
  (diagonalLeftAction k L c d).toRingHom.injective

/-- Right multiplication in a crossed product is linear over its embedded
coefficient field. -/
def rightMulLinear (a : CProduc c) :
    CProduc c →ₗ[L] CProduc c where
  toFun x := x * a
  map_add' x y := add_mul x y a
  map_smul' l x := by
    change (l • x) * a = l • (x * a)
    rw [← coefficient_mul c l x, ← coefficient_mul c l (x * a), mul_assoc]

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem right_mul_linear (a x : CProduc c) :
    rightMulLinear k L c a x = x * a :=
  rfl

/-- The endomorphism of `A(c) tensor_L A(d)` given on pure tensors by
`(x tensor y) |-> (x a) tensor (y b)`. -/
def rightPure (a : CProduc c) (b : CProduc d) :
    Module.End L (tensorBimodule k L c d) :=
  TensorProduct.map (rightMulLinear k L c a) (rightMulLinear k L d b)

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem rightPure_tmul (a x : CProduc c) (b y : CProduc d) :
    rightPure k L c d a b (x ⊗ₜ[L] y) = (x * a) ⊗ₜ[L] (y * b) :=
  rfl

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem right_pure_left (b : CProduc d) :
    rightPure k L c d 0 b = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp [hx, hy]

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem right_pure_zero (a : CProduc c) :
    rightPure k L c d a 0 = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp [hx, hy]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Coordinate formula for right multiplication by two single crossed-product
terms. -/
theorem pure_single_basis
    (rho tau alpha beta : Gal(L/k)) (q a b : L) :
    rightPure k L c d (single c alpha a) (single d beta b)
        (q • tensorBimoduleBasis k L c d (rho, tau)) =
      (q * rho a * (c (rho, alpha) : L) *
          (tau b * (d (tau, beta) : L))) •
        tensorBimoduleBasis k L c d (rho * alpha, tau * beta) := by
  rw [tensor_bimodule_basis, TensorProduct.smul_tmul']
  rw [rightPure_tmul]
  simp only [basis_apply, smul_single, single_mul_single]
  rw [show single c (rho * alpha)
        (q * 1 * rho • a * (c (rho, alpha) : L)) =
      (q * 1 * rho • a * (c (rho, alpha) : L)) •
        single c (rho * alpha) 1 by simp,
    show single d (tau * beta)
        (1 * tau • b * (d (tau, beta) : L)) =
      (1 * tau • b * (d (tau, beta) : L)) •
        single d (tau * beta) 1 by simp,
    TensorProduct.smul_tmul_smul]
  rw [tensor_bimodule_basis, basis_apply, basis_apply]
  congr 1
  simp only [one_mul, mul_one]
  rw [show rho • a = rho a by rfl, show tau • b = tau b by rfl]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- A single diagonal left action commutes with right multiplication by a
single term in each crossed-product factor. -/
theorem diagonal_commute_pure
    (sigma rho tau alpha beta : Gal(L/k)) (l q a b : L) :
    (diagonalSingleAction k L c d sigma l *
        (rightPure k L c d (single c alpha a)
          (single d beta b)).restrictScalars k)
        (q • tensorBimoduleBasis k L c d (rho, tau)) =
      ((rightPure k L c d (single c alpha a)
          (single d beta b)).restrictScalars k *
        diagonalSingleAction k L c d sigma l)
        (q • tensorBimoduleBasis k L c d (rho, tau)) := by
  change diagonalSingleAction k L c d sigma l
      (rightPure k L c d (single c alpha a) (single d beta b)
        (q • tensorBimoduleBasis k L c d (rho, tau))) =
    rightPure k L c d (single c alpha a) (single d beta b)
      (diagonalSingleAction k L c d sigma l
        (q • tensorBimoduleBasis k L c d (rho, tau)))
  rw [pure_single_basis, diagonal_single_basis,
    diagonal_single_basis, pure_single_basis]
  simp only [mul_assoc]
  apply congrArg (fun z : L ↦ z •
    tensorBimoduleBasis k L c d
      (sigma * rho * alpha, sigma * tau * beta))
  have hc := congrArg Units.val (c.isMulCocycle₂ sigma rho alpha)
  have hd := congrArg Units.val (d.isMulCocycle₂ sigma tau beta)
  change (c (sigma * rho, alpha) : L) * (c (sigma, rho) : L) =
    sigma (c (rho, alpha) : L) * (c (sigma, rho * alpha) : L) at hc
  change (d (sigma * tau, beta) : L) * (d (sigma, tau) : L) =
    sigma (d (tau, beta) : L) * (d (sigma, tau * beta) : L) at hd
  rw [show (sigma * rho) a = sigma (rho a) by rfl,
    show (sigma * tau) b = sigma (tau b) by rfl]
  simp only [map_mul]
  have hcd :
      (sigma (c (rho, alpha) : L) * (c (sigma, rho * alpha) : L)) *
          (sigma (d (tau, beta) : L) * (d (sigma, tau * beta) : L)) =
        ((c (sigma * rho, alpha) : L) * (c (sigma, rho) : L)) *
          ((d (sigma * tau, beta) : L) * (d (sigma, tau) : L)) := by
    rw [← hc, ← hd]
  calc
    _ =
      l * sigma q * sigma (rho a) * sigma (tau b) *
        ((sigma (c (rho, alpha) : L) *
            (c (sigma, rho * alpha) : L)) *
          (sigma (d (tau, beta) : L) *
            (d (sigma, tau * beta) : L))) := by ring
    _ = l * sigma q * sigma (rho a) * sigma (tau b) *
        (((c (sigma * rho, alpha) : L) * (c (sigma, rho) : L)) *
          ((d (sigma * tau, beta) : L) * (d (sigma, tau) : L))) := by
      rw [hcd]
    _ = _ := by ring

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Composition of pure right actions reverses multiplication in both
crossed-product factors. -/
theorem rightPure_mul (a a' : CProduc c) (b b' : CProduc d) :
    rightPure k L c d a b * rightPure k L c d a' b' =
      rightPure k L c d (a' * a) (b' * b) := by
  ext x y
  simp [Module.End.mul_apply, mul_assoc]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The pure tensor of the two identity elements acts identically. -/
theorem rightPure_one :
    rightPure k L c d 1 1 = 1 := by
  ext x y
  change (x * single c 1 1) ⊗ₜ[L] (y * single d 1 1) = x ⊗ₜ[L] y
  rw [show single c 1 1 = (1 : CProduc c) from (one_def c).symm,
    show single d 1 1 = (1 : CProduc d) from (one_def d).symm,
    mul_one, mul_one]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The pure right action is additive in its first algebra argument. -/
theorem pure_add_left (a a' : CProduc c) (b : CProduc d) :
    rightPure k L c d (a + a') b =
      rightPure k L c d a b + rightPure k L c d a' b := by
  ext x y
  simp [rightPure, mul_add, TensorProduct.add_tmul]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The pure right action is additive in its second algebra argument. -/
theorem right_pure_add (a : CProduc c) (b b' : CProduc d) :
    rightPure k L c d a (b + b') =
      rightPure k L c d a b + rightPure k L c d a b' := by
  ext x y
  simp [rightPure, mul_add, TensorProduct.tmul_add]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Endomorphism form of the single-coordinate commutation calculation. -/
theorem diagonal_pure_end
    (sigma alpha beta : Gal(L/k)) (l a b : L) :
    diagonalSingleAction k L c d sigma l *
        (rightPure k L c d (single c alpha a)
          (single d beta b)).restrictScalars k =
      (rightPure k L c d (single c alpha a)
          (single d beta b)).restrictScalars k *
        diagonalSingleAction k L c d sigma l := by
  apply ext_bimodule_basis k L c d
  rintro ⟨rho, tau⟩ q
  exact diagonal_commute_pure k L c d
    sigma rho tau alpha beta l q a b

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Every single diagonal action commutes with every pure right action. -/
theorem diagonal_single_pure
    (sigma : Gal(L/k)) (l : L) (a : CProduc c) (b : CProduc d) :
    diagonalSingleAction k L c d sigma l *
        (rightPure k L c d a b).restrictScalars k =
      (rightPure k L c d a b).restrictScalars k *
        diagonalSingleAction k L c d sigma l := by
  induction a using induction_on c with
  | zero => simp
  | hadd a₁ a₂ ha₁ ha₂ =>
      rw [pure_add_left, LinearMap.restrictScalars_add, mul_add, add_mul,
        ha₁, ha₂]
  | hsingle alpha a =>
      induction b using induction_on d with
      | zero => simp
      | hadd b₁ b₂ hb₁ hb₂ =>
          rw [right_pure_add, LinearMap.restrictScalars_add, mul_add,
            add_mul, hb₁, hb₂]
      | hsingle beta b =>
          exact diagonal_pure_end k L c d
            sigma alpha beta l a b

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The full diagonal action of `A(c*d)` commutes with pure right
multiplication on the tensor bimodule. -/
theorem diagonal_action_pure
    (x : CProduc (NMCocycl₂.mul c d))
    (a : CProduc c) (b : CProduc d) :
    diagonalAction k L c d x * (rightPure k L c d a b).restrictScalars k =
      (rightPure k L c d a b).restrictScalars k *
        diagonalAction k L c d x := by
  induction x using induction_on (NMCocycl₂.mul c d) with
  | zero => simp
  | hadd x₁ x₂ hx₁ hx₂ =>
      rw [diagonalAction_add, add_mul, mul_add, hx₁, hx₂]
  | hsingle sigma l =>
      rw [diagonalAction_single]
      exact diagonal_single_pure k L c d sigma l a b

omit [FiniteDimensional k L] [IsGalois k L] in
theorem action_commute_pure
    (x : CProduc (NMCocycl₂.mul c d))
    (a : CProduc c) (b : CProduc d) :
    diagonalLeftAction k L c d x *
        (rightPure k L c d a b).restrictScalars k =
      (rightPure k L c d a b).restrictScalars k *
        diagonalLeftAction k L c d x :=
  diagonal_action_pure k L c d x a b

omit [FiniteDimensional k L] [IsGalois k L] in
theorem pure_algebra_left (r : k) :
    (rightPure k L c d (algebraMap k (CProduc c) r) 1).restrictScalars k =
      algebraMap k (Module.End k (tensorBimodule k L c d)) r := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      change (x * algebraMap k (CProduc c) r) ⊗ₜ[L] (y * 1) =
        r • (x ⊗ₜ[L] y)
      have hxr : x * algebraMap k (CProduc c) r = r • x := by
        rw [← (Algebra.commutes r x), ← Algebra.smul_def]
      rw [mul_one, hxr]
      rfl
  | add x y hx hy =>
      change rightPure k L c d (algebraMap k (CProduc c) r) 1 x =
        r • x at hx
      change rightPure k L c d (algebraMap k (CProduc c) r) 1 y =
        r • y at hy
      change rightPure k L c d (algebraMap k (CProduc c) r) 1 (x + y) =
        r • (x + y)
      rw [map_add, smul_add, hx, hy]

omit [FiniteDimensional k L] [IsGalois k L] in
theorem right_pure_algebra (r : k) :
    (rightPure k L c d 1 (algebraMap k (CProduc d) r)).restrictScalars k =
      algebraMap k (Module.End k (tensorBimodule k L c d)) r := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      change (x * 1) ⊗ₜ[L] (y * algebraMap k (CProduc d) r) =
        r • (x ⊗ₜ[L] y)
      have hyr : y * algebraMap k (CProduc d) r = r • y := by
        rw [← (Algebra.commutes r y), ← Algebra.smul_def]
      rw [mul_one, hyr, TensorProduct.tmul_smul]
  | add x y hx hy =>
      change rightPure k L c d 1 (algebraMap k (CProduc d) r) x =
        r • x at hx
      change rightPure k L c d 1 (algebraMap k (CProduc d) r) y =
        r • y at hy
      change rightPure k L c d 1 (algebraMap k (CProduc d) r) (x + y) =
        r • (x + y)
      rw [map_add, smul_add, hx, hy]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Restricting scalars preserves the reversed composition law for pure
right actions. -/
theorem pure_restrict_scalars
    (a a' : CProduc c) (b b' : CProduc d) :
    (rightPure k L c d a b).restrictScalars k *
        (rightPure k L c d a' b').restrictScalars k =
      (rightPure k L c d (a' * a) (b' * b)).restrictScalars k := by
  apply LinearMap.ext
  intro z
  simpa only [Module.End.mul_apply, LinearMap.restrictScalars_apply] using
    congrArg (fun f : Module.End L (tensorBimodule k L c d) => f z)
      (rightPure_mul k L c d a a' b b')

/-- Right multiplication by the first crossed-product factor. -/
noncomputable def rightFirstAction :
    (CProduc c)ᵐᵒᵖ →ₐ[k]
      Module.End k (tensorBimodule k L c d) where
  toFun a := (rightPure k L c d a.unop 1).restrictScalars k
  map_one' := by
    apply LinearMap.ext
    intro z
    exact congrArg (fun f : Module.End L (tensorBimodule k L c d) => f z)
      (rightPure_one k L c d)
  map_mul' a a' := by
    simp only [MulOpposite.unop_mul]
    apply LinearMap.ext
    intro z
    simpa only [Module.End.mul_apply, LinearMap.restrictScalars_apply,
      mul_one] using
      congrArg (fun f : Module.End L (tensorBimodule k L c d) => f z)
        (rightPure_mul k L c d a.unop a'.unop 1 1).symm
  map_zero' := by simp
  map_add' a a' := by
    simpa only [MulOpposite.unop_add, LinearMap.restrictScalars_add] using
      congrArg (LinearMap.restrictScalars k)
        (pure_add_left k L c d a.unop a'.unop 1)
  commutes' := pure_algebra_left k L c d

/-- Right multiplication by the second crossed-product factor. -/
noncomputable def rightSecondAction :
    (CProduc d)ᵐᵒᵖ →ₐ[k]
      Module.End k (tensorBimodule k L c d) where
  toFun b := (rightPure k L c d 1 b.unop).restrictScalars k
  map_one' := by
    apply LinearMap.ext
    intro z
    exact congrArg (fun f : Module.End L (tensorBimodule k L c d) => f z)
      (rightPure_one k L c d)
  map_mul' b b' := by
    simp only [MulOpposite.unop_mul]
    apply LinearMap.ext
    intro z
    simpa only [Module.End.mul_apply, LinearMap.restrictScalars_apply,
      one_mul] using
      congrArg (fun f : Module.End L (tensorBimodule k L c d) => f z)
        (rightPure_mul k L c d 1 1 b.unop b'.unop).symm
  map_zero' := by simp
  map_add' b b' := by
    simpa only [MulOpposite.unop_add, LinearMap.restrictScalars_add] using
      congrArg (LinearMap.restrictScalars k)
        (right_pure_add k L c d 1 b.unop b'.unop)
  commutes' := right_pure_algebra k L c d

omit [FiniteDimensional k L] [IsGalois k L] in
theorem right_actions_commute
    (a : (CProduc c)ᵐᵒᵖ) (b : (CProduc d)ᵐᵒᵖ) :
    rightFirstAction k L c d a * rightSecondAction k L c d b =
      rightSecondAction k L c d b * rightFirstAction k L c d a := by
  change (rightPure k L c d a.unop 1).restrictScalars k *
      (rightPure k L c d 1 b.unop).restrictScalars k =
    (rightPure k L c d 1 b.unop).restrictScalars k *
      (rightPure k L c d a.unop 1).restrictScalars k
  rw [pure_restrict_scalars, pure_restrict_scalars]
  simp only [one_mul, mul_one]

noncomputable def tensorActionFactors :
    (CProduc c)ᵐᵒᵖ ⊗[k] (CProduc d)ᵐᵒᵖ →ₐ[k]
      Module.End k (tensorBimodule k L c d) :=
  Algebra.TensorProduct.lift (rightFirstAction k L c d)
    (rightSecondAction k L c d) (right_actions_commute k L c d)

/-- The full right action, with the opposite encoding reversal of products. -/
noncomputable def rightTensorAction :
    (CProduc c ⊗[k] CProduc d)ᵐᵒᵖ →ₐ[k]
      Module.End k (tensorBimodule k L c d) :=
  (tensorActionFactors k L c d).comp
    (Algebra.TensorProduct.opAlgEquiv k k (CProduc c)
      (CProduc d)).symm.toAlgHom

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem action_op_tmul
    (a : CProduc c) (b : CProduc d) :
    rightTensorAction k L c d (MulOpposite.op (a ⊗ₜ[k] b)) =
      (rightPure k L c d a b).restrictScalars k := by
  simp only [rightTensorAction, tensorActionFactors, rightFirstAction, one_def, rightSecondAction,
    AlgHom.coe_comp, AlgEquiv.coe_algHom, Function.comp_apply,
    Algebra.TensorProduct.opAlgEquiv_symm_tmul,
    Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    MulOpposite.unop_op]
  rw [pure_restrict_scalars]
  rw [show single c 1 1 = (1 : CProduc c) from (one_def c).symm,
    show single d 1 1 = (1 : CProduc d) from (one_def d).symm,
    one_mul, mul_one]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The two full algebra actions commute. -/
theorem diagonal_commute_tensor
    (x : CProduc (NMCocycl₂.mul c d))
    (y : (CProduc c ⊗[k] CProduc d)ᵐᵒᵖ) :
    diagonalLeftAction k L c d x * rightTensorAction k L c d y =
      rightTensorAction k L c d y * diagonalLeftAction k L c d x := by
  obtain ⟨y, rfl⟩ := MulOpposite.op_surjective y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [action_op_tmul]
      exact action_commute_pure k L c d x a b
  | add y z hy hz =>
      simp only [MulOpposite.op_add, map_add, mul_add, add_mul, hy, hz]

/-- The `L`-dimension of Milne's bimodule is `[L:k]^2`. -/
theorem tensor_bimodule_extension :
    Module.finrank L (tensorBimodule k L c d) = (Module.finrank k L) ^ 2 := by
  rw [Module.finrank_tensorProduct, finrank_over_extension, finrank_over_extension,
    pow_two]

/-- Over the base field, Milne's bimodule has dimension `[L:k]^3`. -/
theorem tensor_bimodule_base :
    Module.finrank k (tensorBimodule k L c d) = (Module.finrank k L) ^ 3 := by
  rw [← Module.finrank_mul_finrank k L (tensorBimodule k L c d),
    tensor_bimodule_extension]
  ring

/-- The tensor product `A(c) tensor_k A(d)` has dimension `[L:k]^4`, the
dimension used in Milne's comparison with `End_C(V)`. -/
theorem finrank_tensor_simple :
    Module.finrank k (CProduc c ⊗[k] CProduc d) =
      (Module.finrank k L) ^ 4 := by
  rw [Module.finrank_tensorProduct, finrank_over_base, finrank_over_base]
  ring

/-- The combined left-right action used in Milne's bimodule proof. -/
noncomputable def combinedTensorAction :
    CProduc (NMCocycl₂.mul c d) ⊗[k]
        (CProduc c ⊗[k] CProduc d)ᵐᵒᵖ →ₐ[k]
      Module.End k (tensorBimodule k L c d) :=
  Algebra.TensorProduct.lift (diagonalLeftAction k L c d)
    (rightTensorAction k L c d)
    (diagonal_commute_tensor k L c d)

theorem combined_action_bijective :
    Function.Bijective (combinedTensorAction k L c d) := by
  letI : IsSimpleRing
      (CProduc (NMCocycl₂.mul c d) ⊗[k]
        (CProduc c ⊗[k] CProduc d)ᵐᵒᵖ) :=
    BGroups.tensor_simple_ring k
      (CProduc (NMCocycl₂.mul c d))
      ((CProduc c ⊗[k] CProduc d)ᵐᵒᵖ)
  have hinjRing : Function.Injective
      (combinedTensorAction k L c d).toRingHom :=
    @RingHom.injective
      (CProduc (NMCocycl₂.mul c d) ⊗[k]
        (CProduc c ⊗[k] CProduc d)ᵐᵒᵖ)
      (Module.End k (tensorBimodule k L c d)) _ _ _ _
      (combinedTensorAction k L c d).toRingHom
  have hinj : Function.Injective (combinedTensorAction k L c d) := by
    intro x y hxy
    exact hinjRing hxy
  have hdim :
      Module.finrank k
          (CProduc (NMCocycl₂.mul c d) ⊗[k]
            (CProduc c ⊗[k] CProduc d)ᵐᵒᵖ) =
        Module.finrank k (Module.End k (tensorBimodule k L c d)) := by
    rw [Module.finrank_tensorProduct, MulOpposite.finrank,
      finrank_over_base, finrank_tensor_simple,
      Module.finrank_linearMap, tensor_bimodule_base]
    ring
  have hsurj : Function.Surjective
      (combinedTensorAction k L c d).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨hinj, hsurj⟩

/-- The combined action identifies the tensor product with the full
endomorphism algebra of Milne's bimodule. -/
noncomputable def combinedTensorEnd :
    CProduc (NMCocycl₂.mul c d) ⊗[k]
        (CProduc c ⊗[k] CProduc d)ᵐᵒᵖ ≃ₐ[k]
      Module.End k (tensorBimodule k L c d) :=
  AlgEquiv.ofBijective (combinedTensorAction k L c d)
    (combined_action_bijective k L c d)

/-- Milne's Lemma IV.3.15: multiplication of cocycles corresponds to tensor
product in the Brauer group. -/
theorem tensorCompatibility : TensorCompatibility k L c d := by
  letI : IsSimpleRing (CProduc (NMCocycl₂.mul c d)) := inferInstance
  letI : IsSimpleRing (CProduc c ⊗[k] CProduc d) := inferInstance
  exact equivalent_op_end
    (k := k) (C := CProduc (NMCocycl₂.mul c d))
    (D := CProduc c ⊗[k] CProduc d)
    (V := tensorBimodule k L c d) (combinedTensorEnd k L c d)

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The balancing relation over `L` is preserved by every pure right action. -/
theorem rightPure_balanced (a x : CProduc c) (b y : CProduc d)
    (l : L) :
    rightPure k L c d a b ((l • x) ⊗ₜ[L] y) =
      rightPure k L c d a b (x ⊗ₜ[L] (l • y)) := by
  rw [TensorProduct.smul_tmul]

end CProduc

end

end Submission.CField.CProduca
