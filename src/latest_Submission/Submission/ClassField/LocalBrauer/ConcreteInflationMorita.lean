import Submission.ClassField.CrossedProducts.BimoduleInfrastructure
import Submission.ClassField.LocalBrauer.ConcreteInflationBasic


/-!
# Chapter IV, Section 4: the Morita comparison for concrete inflation

For finite Galois intermediate fields `F <= E`, let `c` be a factor set for
`Gal(F/K)`.  The standard inflation bimodule is

`E tensor_F CProduc(c)`.

The crossed product of the inflated factor set acts on the left, and the
opposite of `CProduc(c)` acts on the right.  The combined action is the
full endomorphism algebra, which proves that concrete cochain inflation agrees
with the Brauer-theoretic inflation of Corollary 3.16.
-/

namespace Submission.CField.LBrauer

noncomputable section

open scoped TensorProduct

universe u

open BGroups CProduca

variable (K : Type u) [Field K]
variable {Omega : Type u} [Field Omega] [Algebra K Omega]
variable {F E : FiniteGaloisIntermediateField K Omega}
variable [hFEFact : Fact (F <= E)]

local instance concreteInflationFiniteGaloisUnitsActionF :
    MulDistribMulAction Gal(F/K) Fˣ :=
  Units.mulDistribMulActionRight

local instance concreteInflationFiniteGaloisUnitsActionE :
    MulDistribMulAction Gal(E/K) Eˣ :=
  Units.mulDistribMulActionRight

variable (c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ))

set_option maxHeartbeats 20000 in
-- Elaborating the finite Galois index type unfolds intermediate-field subtypes.
/-- The coordinate model of the standard inflation bimodule.  It is the free
`E`-space on `Gal(F/K)`, canonically isomorphic to
`E tensor_F CProduc(c)`. -/
abbrev concreteInflationBimodule
    (_c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ)) :=
  Gal(F/K) →₀ E

set_option maxHeartbeats 20000 in
-- Elaborating the coordinate type unfolds the finite Galois index.
/-- The standard coordinate vector of the inflation bimodule. -/
def inflationBimoduleBasis
    (_c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ))
    (rho : Gal(F/K)) :
    (Gal(F/K) →₀ E) :=
  Finsupp.single rho 1

set_option maxHeartbeats 20000 in
-- Unfolding the coordinate vector traverses the finite Galois index type.
omit hFEFact in
@[simp]
theorem inflation_bimodule_basis (sigma : Gal(F/K)) :
    inflationBimoduleBasis (E := E) K c sigma =
      Finsupp.single sigma 1 := by
  rfl

set_option maxHeartbeats 20000 in
-- The explicit coordinate witness unfolds the finite Galois index type.
instance inflationBimoduleNontrivial :
    Nontrivial ((Gal(F/K) →₀ E)) :=
  ⟨inflationBimoduleBasis (E := E) K c 1, 0,
    by simp [inflationBimoduleBasis]⟩

set_option maxHeartbeats 200000 in
-- Checking scalar linearity through the finite field action is deep.
/-- The contribution of one basis coordinate to the action of an inflated
crossed-product monomial. -/
noncomputable def concreteInflationCoordinate
    (sigma : Gal(E/K)) (l : E) (rho : Gal(F/K)) :
    E →ₗ[K] (Gal(F/K) →₀ E) where
  toFun q := Finsupp.single
    (galoisRestrictionHom K hFEFact.out sigma * rho)
    (l * sigma q *
      (coefficientUnitsHom K hFEFact.out
        (c (galoisRestrictionHom K hFEFact.out sigma, rho)) : E))
  map_add' q r := by
    rw [map_add, mul_add, add_mul, Finsupp.single_add]
  map_smul' r q := by
    rw [Finsupp.smul_single]
    apply congrArg (Finsupp.single
      (galoisRestrictionHom K hFEFact.out sigma * rho))
    rw [show sigma (r • q) = r • sigma q by
      exact (sigma.toLinearEquiv : E ≃ₗ[K] E).map_smul r q]
    simp only [Algebra.smul_def, RingHom.id_apply]
    ring

set_option maxHeartbeats 20000 in
-- Summing the coordinate maps unfolds the finite Galois index type.
/-- The `K`-linear action of a single monomial in the inflated crossed
product. -/
noncomputable def concreteInflationSingle
    (sigma : Gal(E/K)) (l : E) :
    Module.End K ((Gal(F/K) →₀ E)) :=
  Finsupp.lsum K
    (fun rho ↦ concreteInflationCoordinate (E := E) K c sigma l rho)

set_option maxHeartbeats 20000 in
-- The displayed scalar action unfolds the Finsupp coordinate module.
theorem inflation_single_basis
    (sigma : Gal(E/K)) (rho : Gal(F/K)) (l q : E) :
    concreteInflationSingle (E := E) K c sigma l
        (Finsupp.single rho q) =
      Finsupp.single
        (galoisRestrictionHom K hFEFact.out sigma * rho)
        (l * sigma q *
          (coefficientUnitsHom K hFEFact.out
            (c (galoisRestrictionHom K hFEFact.out sigma, rho)) : E)) := by
  simp [concreteInflationSingle, concreteInflationCoordinate,
    ]

set_option maxHeartbeats 20000 in
-- Linear-map extensionality unfolds the Finsupp coordinate module.
omit hFEFact in
/-- `K`-linear endomorphisms of the inflation bimodule are determined on
`E`-multiples of its standard basis. -/
theorem end_ext_bimodule
    (f g : Module.End K ((Gal(F/K) →₀ E)))
    (h : ∀ (rho : Gal(F/K)) (q : E),
      f (Finsupp.single rho q) = g (Finsupp.single rho q)) :
    f = g :=
  Finsupp.lhom_ext h

set_option maxHeartbeats 100000 in
-- The cocycle multiplication calculation unfolds three coordinate actions.
/-- The coordinate actions obey multiplication in the crossed product of the
inflated cocycle. -/
theorem inflation_single_mul
    (sigma tau : Gal(E/K)) (l m : E) :
    concreteInflationSingle (E := E) K c sigma l *
        concreteInflationSingle (E := E) K c tau m =
      concreteInflationSingle (E := E) K c (sigma * tau)
        (l * sigma m *
          (concreteInflationCocycle K hFEFact.out c (sigma, tau) : E)) := by
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  simp only [Module.End.mul_apply]
  rw [inflation_single_basis,
    inflation_single_basis,
    inflation_single_basis]
  simp only [map_mul, mul_assoc]
  apply congrArg (fun a : E ↦ Finsupp.single
      (galoisRestrictionHom K hFEFact.out sigma *
        galoisRestrictionHom K hFEFact.out tau * rho) a)
  let rs := galoisRestrictionHom K hFEFact.out sigma
  let rt := galoisRestrictionHom K hFEFact.out tau
  have hc := congrArg Units.val (c.isMulCocycle₂ rs rt rho)
  change (c (rs * rt, rho) : F) * (c (rs, rt) : F) =
    rs (c (rt, rho) : F) * (c (rs, rt * rho) : F) at hc
  let iFE : F →+* E := IntermediateField.inclusion hFEFact.out
  have hsigmaCoeff :
      sigma (coefficientUnitsHom K hFEFact.out (c (rt, rho)) : E) =
        (coefficientUnitsHom K hFEFact.out
          (Units.map rs (c (rt, rho))) : E) := by
    exact congrArg Units.val
      (coefficient_units_hom K hFEFact.out sigma (c (rt, rho))).symm
  change
    l * (sigma m * (sigma (tau q) *
      (sigma (coefficientUnitsHom K hFEFact.out (c (rt, rho)) : E) *
        (coefficientUnitsHom K hFEFact.out
          (c (rs, rt * rho)) : E)))) =
    l * (sigma m *
      ((coefficientUnitsHom K hFEFact.out (c (rs, rt)) : E) *
        ((sigma * tau) q *
          (coefficientUnitsHom K hFEFact.out
            (c (rs * rt, rho)) : E))))
  rw [hsigmaCoeff]
  change
    l * (sigma m * (sigma (tau q) *
      (iFE (rs (c (rt, rho) : F)) *
        iFE (c (rs, rt * rho) : F)))) =
    l * (sigma m * (iFE (c (rs, rt) : F) *
      ((sigma * tau) q * iFE (c (rs * rt, rho) : F))))
  rw [show (sigma * tau) q = sigma (tau q) by rfl]
  have hcE' :
      iFE (c (rs * rt, rho) : F) * iFE (c (rs, rt) : F) =
        iFE (rs (c (rt, rho) : F)) * iFE (c (rs, rt * rho) : F) := by
    apply Subtype.ext
    simpa [iFE] using congrArg Subtype.val hc
  rw [← hcE']
  ac_rfl

set_option maxHeartbeats 20000 in
-- Extensionality unfolds one coordinate action.
@[simp]
theorem inflation_single_zero (sigma : Gal(E/K)) :
    concreteInflationSingle (E := E) K c sigma 0 = 0 := by
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  rw [inflation_single_basis]
  simp

set_option maxHeartbeats 50000 in
-- Extensionality unfolds three coordinate actions.
theorem inflation_single_add
    (sigma : Gal(E/K)) (l m : E) :
    concreteInflationSingle (E := E) K c sigma (l + m) =
      concreteInflationSingle (E := E) K c sigma l +
        concreteInflationSingle (E := E) K c sigma m := by
  apply Finsupp.lhom_ext
  intro rho q
  simp [concreteInflationSingle, concreteInflationCoordinate,
    add_mul]

set_option maxHeartbeats 20000 in
-- Extensionality unfolds the identity coordinate action.
@[simp]
theorem inflation_single_one :
    concreteInflationSingle (E := E) K c 1 1 = 1 := by
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  rw [inflation_single_basis]
  simp

set_option maxHeartbeats 20000 in
-- Summing over crossed-product coordinates unfolds both Finsupp layers.
/-- Sum the coordinate actions over an element of the inflated crossed
product. -/
noncomputable def concreteInflationAction
    (x : CProduc (concreteInflationCocycle K hFEFact.out c)) :
    Module.End K ((Gal(F/K) →₀ E)) :=
  CProduc.sum (concreteInflationCocycle K hFEFact.out c) x
    (fun sigma l ↦ concreteInflationSingle (E := E) K c sigma l)

set_option maxHeartbeats 20000 in
-- Evaluating the sum at one crossed-product coordinate unfolds both layers.
@[simp]
theorem inflation_single (sigma : Gal(E/K)) (l : E) :
    concreteInflationAction (E := E) K c
        (CProduc.single (concreteInflationCocycle K hFEFact.out c) sigma l) =
      concreteInflationSingle (E := E) K c sigma l := by
  rw [concreteInflationAction, CProduc.sum_single_index]
  exact inflation_single_zero (E := E) K c sigma

set_option maxHeartbeats 20000 in
-- The zero law unfolds the crossed-product sum.
@[simp]
theorem inflation_action_zero :
    concreteInflationAction (E := E) K c 0 = 0 := by
  exact CProduc.sum_zero_index (concreteInflationCocycle K hFEFact.out c)

set_option maxHeartbeats 20000 in
-- The additivity law unfolds the crossed-product sum.
theorem concrete_action_add
    (x y : CProduc (concreteInflationCocycle K hFEFact.out c)) :
    concreteInflationAction (E := E) K c (x + y) =
      concreteInflationAction (E := E) K c x +
        concreteInflationAction (E := E) K c y := by
  exact CProduc.sum_add_index' (concreteInflationCocycle K hFEFact.out c)
    (fun sigma ↦ inflation_single_zero (E := E) K c sigma)
    (fun sigma ↦ inflation_single_add (E := E) K c sigma)

set_option maxHeartbeats 20000 in
-- Isolating the unit calculation keeps bundled-hom elaboration shallow.
theorem inflation_action_one :
    concreteInflationAction (E := E) K c 1 = 1 := by
  rw [CProduc.one_def, inflation_single,
    inflation_single_one]

set_option maxHeartbeats 100000 in
-- Separating the monomial law prevents the outer induction from re-elaborating
-- all three coordinate sums in its deepest branch.
theorem concrete_action_single
    (sigma tau : Gal(E/K)) (l m : E) :
    concreteInflationAction (E := E) K c
        (CProduc.single
            (concreteInflationCocycle K hFEFact.out c) sigma l *
          CProduc.single
            (concreteInflationCocycle K hFEFact.out c) tau m) =
      concreteInflationAction (E := E) K c
          (CProduc.single
            (concreteInflationCocycle K hFEFact.out c) sigma l) *
        concreteInflationAction (E := E) K c
          (CProduc.single
            (concreteInflationCocycle K hFEFact.out c) tau m) := by
  rw [CProduc.single_mul_single,
    inflation_single,
    inflation_single,
    inflation_single,
    inflation_single_mul]
  rfl

set_option maxHeartbeats 100000 in
-- Ring multiplication uses the coordinate multiplication law under two inductions.
theorem inflation_action_mul
    (x y : CProduc (concreteInflationCocycle K hFEFact.out c)) :
    concreteInflationAction (E := E) K c (x * y) =
      concreteInflationAction (E := E) K c x *
        concreteInflationAction (E := E) K c y := by
  induction x using CProduc.induction_on
      (concreteInflationCocycle K hFEFact.out c) with
  | zero =>
      rw [zero_mul, inflation_action_zero,
        zero_mul]
  | hadd x₁ x₂ hx₁ hx₂ =>
      calc
        concreteInflationAction (E := E) K c ((x₁ + x₂) * y) =
            concreteInflationAction (E := E) K c (x₁ * y + x₂ * y) := by
              rw [add_mul]
        _ = concreteInflationAction (E := E) K c (x₁ * y) +
              concreteInflationAction (E := E) K c (x₂ * y) :=
            concrete_action_add (E := E) K c _ _
        _ = concreteInflationAction (E := E) K c x₁ *
              concreteInflationAction (E := E) K c y +
            concreteInflationAction (E := E) K c x₂ *
              concreteInflationAction (E := E) K c y := congrArg₂ (· + ·) hx₁ hx₂
        _ = (concreteInflationAction (E := E) K c x₁ +
              concreteInflationAction (E := E) K c x₂) *
            concreteInflationAction (E := E) K c y := (add_mul _ _ _).symm
        _ = concreteInflationAction (E := E) K c (x₁ + x₂) *
            concreteInflationAction (E := E) K c y := by
              rw [concrete_action_add]
  | hsingle sigma l =>
      induction y using CProduc.induction_on
          (concreteInflationCocycle K hFEFact.out c) with
      | zero =>
          rw [mul_zero, inflation_action_zero,
            mul_zero]
      | hadd y₁ y₂ hy₁ hy₂ =>
          calc
            concreteInflationAction (E := E) K c
                (CProduc.single
                    (concreteInflationCocycle K hFEFact.out c) sigma l *
                  (y₁ + y₂)) =
                concreteInflationAction (E := E) K c
                  (CProduc.single
                      (concreteInflationCocycle K hFEFact.out c) sigma l * y₁ +
                    CProduc.single
                      (concreteInflationCocycle K hFEFact.out c) sigma l * y₂) := by
                rw [mul_add]
            _ = concreteInflationAction (E := E) K c
                  (CProduc.single
                      (concreteInflationCocycle K hFEFact.out c) sigma l * y₁) +
                concreteInflationAction (E := E) K c
                  (CProduc.single
                      (concreteInflationCocycle K hFEFact.out c) sigma l * y₂) :=
                concrete_action_add (E := E) K c _ _
            _ = concreteInflationAction (E := E) K c
                    (CProduc.single
                      (concreteInflationCocycle K hFEFact.out c) sigma l) *
                  concreteInflationAction (E := E) K c y₁ +
                concreteInflationAction (E := E) K c
                    (CProduc.single
                      (concreteInflationCocycle K hFEFact.out c) sigma l) *
                  concreteInflationAction (E := E) K c y₂ :=
                congrArg₂ (· + ·) hy₁ hy₂
            _ = concreteInflationAction (E := E) K c
                    (CProduc.single
                      (concreteInflationCocycle K hFEFact.out c) sigma l) *
                  (concreteInflationAction (E := E) K c y₁ +
                    concreteInflationAction (E := E) K c y₂) :=
                (mul_add _ _ _).symm
            _ = concreteInflationAction (E := E) K c
                    (CProduc.single
                      (concreteInflationCocycle K hFEFact.out c) sigma l) *
                  concreteInflationAction (E := E) K c (y₁ + y₂) := by
                rw [concrete_action_add]
      | hsingle tau m =>
          exact concrete_action_single (E := E) K c sigma tau l m

set_option maxHeartbeats 20000 in
-- The laws are established separately so this bundle only assembles them.
/-- The ring action of the crossed product of the concretely inflated cocycle. -/
noncomputable def concreteInflationRing :
    CProduc (concreteInflationCocycle K hFEFact.out c) →+*
      Module.End K (Gal(F/K) →₀ E) where
  toFun := concreteInflationAction (E := E) K c
  map_zero' := inflation_action_zero (E := E) K c
  map_one' := inflation_action_one (E := E) K c
  map_add' := concrete_action_add (E := E) K c
  map_mul' := inflation_action_mul (E := E) K c

set_option maxHeartbeats 50000 in
-- Scalar commutation unfolds the identity coordinate action.
theorem concrete_inflation_ring (r : K) :
    concreteInflationRing (E := E) K c
        (algebraMap K
          (CProduc (concreteInflationCocycle K hFEFact.out c)) r) =
      algebraMap K (Module.End K (Gal(F/K) →₀ E)) r := by
  change concreteInflationAction (E := E) K c
    (CProduc.single (concreteInflationCocycle K hFEFact.out c) 1
      (algebraMap K E r)) = _
  rw [inflation_single]
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  rw [inflation_single_basis]
  simp only [map_one, one_mul, AlgEquiv.one_apply,
    NMCocycl₂.apply_one_fst, Units.val_one, mul_one,
    Module.algebraMap_end_apply, Finsupp.smul_single]
  rw [Algebra.smul_def]

set_option maxHeartbeats 20000 in
-- The ring and scalar laws are already proved, so this only assembles them.
/-- The left algebra action of the concretely inflated crossed product. -/
noncomputable def inflationLeftAction :
    CProduc (concreteInflationCocycle K hFEFact.out c) →ₐ[K]
      Module.End K (Gal(F/K) →₀ E) where
  __ := concreteInflationRing (E := E) K c
  commutes' := concrete_inflation_ring (E := E) K c

set_option maxHeartbeats 10000 in
-- Naming the embedded coefficient keeps the coordinate LinearMap constructor
-- from repeatedly unfolding the intermediate-field inclusion.
noncomputable def concreteInflationCoefficient
    (alpha rho : Gal(F/K)) (a : F) : E :=
  IntermediateField.inclusion hFEFact.out
    (rho a * (c (rho, alpha) : F))

set_option maxHeartbeats 10000 in
-- Right multiplication by one crossed-product monomial is diagonal on each
-- source coordinate and shifts that coordinate on the right.
/-- The contribution of one coordinate to right multiplication by a monomial
of the original crossed product. -/
noncomputable def inflationCoordinateAction
    (alpha : Gal(F/K)) (a : F) (rho : Gal(F/K)) :
    E →ₗ[K] (Gal(F/K) →₀ E) :=
  (Finsupp.lsingle (R := K) (M := E) (rho * alpha)).comp
    (LinearMap.mulRight K
      (concreteInflationCoefficient (E := E) K c alpha rho a))

set_option maxHeartbeats 20000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- Right multiplication by one monomial of the original crossed product. -/
noncomputable def inflationSingleAction
    (alpha : Gal(F/K)) (a : F) :
    Module.End K (Gal(F/K) →₀ E) :=
  Finsupp.lsum K
    (fun rho ↦ inflationCoordinateAction (E := E) K c alpha a rho)

set_option maxHeartbeats 20000 in
-- Evaluating the Finsupp sum at one coordinate unfolds both layers.
@[simp]
theorem inflation_single_action
    (alpha rho : Gal(F/K)) (a : F) (q : E) :
    inflationSingleAction (E := E) K c alpha a
        (Finsupp.single rho q) =
      Finsupp.single (rho * alpha)
        (q * IntermediateField.inclusion hFEFact.out
          (rho a * (c (rho, alpha) : F))) := by
  simp [inflationSingleAction,
    inflationCoordinateAction, concreteInflationCoefficient,
    mul_assoc]

set_option maxHeartbeats 20000 in
-- The value-level form of the cocycle law is kept separate from the
-- endomorphism calculation below.
theorem inflation_cocycle_identity
    (rho beta alpha : Gal(F/K)) :
    (c (rho * beta, alpha) : F) * (c (rho, beta) : F) =
      rho (c (beta, alpha) : F) * (c (rho, beta * alpha) : F) := by
  have hc := congrArg Units.val (c.isMulCocycle₂ rho beta alpha)
  change (c (rho * beta, alpha) : F) * (c (rho, beta) : F) =
    rho (c (beta, alpha) : F) * (c (rho, beta * alpha) : F) at hc
  exact hc

set_option maxHeartbeats 20000 in
-- Multiplying the two original crossed-product coefficients uses precisely
-- the preceding cocycle value identity.
theorem concrete_inflation_coefficient
    (rho beta alpha : Gal(F/K)) (b a : F) :
    (rho b * (c (rho, beta) : F)) *
        ((rho * beta) a * (c (rho * beta, alpha) : F)) =
      rho (b * beta a * (c (beta, alpha) : F)) *
        (c (rho, beta * alpha) : F) := by
  have hc := inflation_cocycle_identity K c rho beta alpha
  rw [show (rho * beta) a = rho (beta a) by rfl]
  simp only [map_mul]
  calc
    _ = rho b * rho (beta a) *
        ((c (rho * beta, alpha) : F) * (c (rho, beta) : F)) := by ac_rfl
    _ = rho b * rho (beta a) *
        (rho (c (beta, alpha) : F) * (c (rho, beta * alpha) : F)) := by
          rw [hc]
    _ = _ := by ac_rfl

set_option maxHeartbeats 10000 in
-- A monomorphic associativity lemma avoids repeated normalization of the
-- intermediate-field subtype in later coefficient calculations.
theorem inflation_assoc_e (x y z : E) :
    x * y * z = x * (y * z) :=
  mul_assoc x y z

set_option maxHeartbeats 50000 in
-- Specializing associativity to the two named right coefficients is kept out
-- of the inclusion-transport proof.
theorem concrete_inflation_assoc
    (rho beta alpha : Gal(F/K)) (q : E) (b a : F) :
    (q * concreteInflationCoefficient (E := E) K c beta rho b) *
        concreteInflationCoefficient (E := E) K c alpha (rho * beta) a =
      q * (concreteInflationCoefficient (E := E) K c beta rho b *
        concreteInflationCoefficient (E := E) K c alpha (rho * beta) a) :=
  inflation_assoc_e (E := E) K _ _ _

set_option maxHeartbeats 20000 in
-- The scalar part of composing two right monomial actions.
theorem concrete_inflation_mul
    (rho beta alpha : Gal(F/K)) (q : E) (b a : F) :
    (q * concreteInflationCoefficient (E := E) K c beta rho b) *
        concreteInflationCoefficient (E := E) K c alpha (rho * beta) a =
      q * concreteInflationCoefficient (E := E) K c (beta * alpha) rho
        (b * beta a * (c (beta, alpha) : F)) := by
  have hF := concrete_inflation_coefficient K c rho beta alpha b a
  unfold concreteInflationCoefficient
  calc
    _ = q * (IntermediateField.inclusion hFEFact.out
          (rho b * (c (rho, beta) : F)) *
        IntermediateField.inclusion hFEFact.out
          ((rho * beta) a * (c (rho * beta, alpha) : F))) :=
          concrete_inflation_assoc
            (E := E) K c rho beta alpha q b a
    _ = q * IntermediateField.inclusion hFEFact.out
        ((rho b * (c (rho, beta) : F)) *
          ((rho * beta) a * (c (rho * beta, alpha) : F))) :=
          congrArg (fun z : E ↦ q * z)
            (map_mul (IntermediateField.inclusion hFEFact.out) _ _).symm
    _ = _ := by rw [hF]

set_option maxHeartbeats 20000 in
-- This is the cocycle identity transported through the inclusion `F → E`.
theorem concrete_single_action
    (alpha beta : Gal(F/K)) (a b : F) :
    inflationSingleAction (E := E) K c alpha a *
        inflationSingleAction (E := E) K c beta b =
      inflationSingleAction (E := E) K c (beta * alpha)
        (b * beta a * (c (beta, alpha) : F)) := by
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  calc
    (inflationSingleAction (E := E) K c alpha a *
        inflationSingleAction (E := E) K c beta b)
        (Finsupp.single rho q) =
      inflationSingleAction (E := E) K c alpha a
        (Finsupp.single (rho * beta)
          (q * concreteInflationCoefficient (E := E) K c beta rho b)) :=
        congrArg (inflationSingleAction (E := E) K c alpha a)
          (inflation_single_action
            (E := E) K c beta rho b q)
    _ = Finsupp.single ((rho * beta) * alpha)
        ((q * concreteInflationCoefficient (E := E) K c beta rho b) *
          concreteInflationCoefficient (E := E) K c alpha (rho * beta) a) :=
        inflation_single_action
          (E := E) K c alpha (rho * beta) a _
    _ = Finsupp.single (rho * (beta * alpha))
        (q * concreteInflationCoefficient (E := E) K c (beta * alpha) rho
          (b * beta a * (c (beta, alpha) : F))) :=
        congrArg₂ (fun i x ↦ Finsupp.single i x)
          (mul_assoc rho beta alpha)
          (concrete_inflation_mul
            (E := E) K c rho beta alpha q b a)
    _ = inflationSingleAction (E := E) K c (beta * alpha)
        (b * beta a * (c (beta, alpha) : F))
          (Finsupp.single rho q) :=
        (inflation_single_action (E := E) K c
          (beta * alpha) rho (b * beta a * (c (beta, alpha) : F)) q).symm

set_option maxHeartbeats 20000 in
-- Extensionality reduces the zero law to the displayed coordinate formula.
@[simp]
theorem concrete_inflation_action (alpha : Gal(F/K)) :
    inflationSingleAction (E := E) K c alpha 0 = 0 := by
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  rw [inflation_single_action]
  simp

set_option maxHeartbeats 50000 in
-- Extensionality reduces coefficient additivity to distributivity in `E`.
theorem concrete_inflation_add
    (alpha : Gal(F/K)) (a b : F) :
    inflationSingleAction (E := E) K c alpha (a + b) =
      inflationSingleAction (E := E) K c alpha a +
        inflationSingleAction (E := E) K c alpha b := by
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  rw [LinearMap.add_apply,
    inflation_single_action,
    inflation_single_action,
    inflation_single_action]
  rw [← Finsupp.single_add]
  apply congrArg (Finsupp.single (rho * alpha))
  simp only [map_add, map_mul, add_mul, mul_add]

set_option maxHeartbeats 20000 in
-- The normalized cocycle makes the identity monomial act identically.
@[simp]
theorem inflation_right_single :
    inflationSingleAction (E := E) K c 1 1 = 1 := by
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  rw [inflation_single_action]
  simp

set_option maxHeartbeats 20000 in
-- Sum the monomial right actions over the original crossed product.
noncomputable def inflationRightAction (x : CProduc c) :
    Module.End K (Gal(F/K) →₀ E) :=
  CProduc.sum c x
    (fun alpha a ↦ inflationSingleAction (E := E) K c alpha a)

set_option maxHeartbeats 20000 in
-- Evaluating the crossed-product sum at one coordinate.
@[simp]
theorem inflation_action_single (alpha : Gal(F/K)) (a : F) :
    inflationRightAction (E := E) K c
        (CProduc.single c alpha a) =
      inflationSingleAction (E := E) K c alpha a := by
  rw [inflationRightAction, CProduc.sum_single_index]
  exact concrete_inflation_action (E := E) K c alpha

set_option maxHeartbeats 20000 in
-- The zero law unfolds the crossed-product sum.
@[simp]
theorem concrete_inflation_zero :
    inflationRightAction (E := E) K c 0 = 0 := by
  exact CProduc.sum_zero_index c

set_option maxHeartbeats 20000 in
-- Additivity follows from additivity of every monomial action.
theorem inflation_action_add (x y : CProduc c) :
    inflationRightAction (E := E) K c (x + y) =
      inflationRightAction (E := E) K c x +
        inflationRightAction (E := E) K c y := by
  exact CProduc.sum_add_index' c
    (fun alpha ↦ concrete_inflation_action (E := E) K c alpha)
    (fun alpha ↦ concrete_inflation_add (E := E) K c alpha)

set_option maxHeartbeats 50000 in
-- The monomial anti-multiplication law packages the coordinate cocycle theorem.
theorem concrete_inflation_single
    (alpha beta : Gal(F/K)) (a b : F) :
    inflationRightAction (E := E) K c (CProduc.single c alpha a) *
        inflationRightAction (E := E) K c (CProduc.single c beta b) =
      inflationRightAction (E := E) K c
        (CProduc.single c beta b * CProduc.single c alpha a) := by
  rw [CProduc.single_mul_single,
    inflation_action_single,
    inflation_action_single,
    inflation_action_single,
    concrete_single_action]
  rfl

set_option maxHeartbeats 100000 in
-- Right multiplication reverses products.
theorem concrete_inflation_rev (x y : CProduc c) :
    inflationRightAction (E := E) K c x *
        inflationRightAction (E := E) K c y =
      inflationRightAction (E := E) K c (y * x) := by
  induction x using CProduc.induction_on c with
  | zero =>
      rw [concrete_inflation_zero, zero_mul, mul_zero,
        concrete_inflation_zero]
  | hadd x₁ x₂ hx₁ hx₂ =>
      calc
        inflationRightAction (E := E) K c (x₁ + x₂) *
            inflationRightAction (E := E) K c y =
          (inflationRightAction (E := E) K c x₁ +
            inflationRightAction (E := E) K c x₂) *
              inflationRightAction (E := E) K c y := by
                rw [inflation_action_add]
        _ = inflationRightAction (E := E) K c x₁ *
              inflationRightAction (E := E) K c y +
            inflationRightAction (E := E) K c x₂ *
              inflationRightAction (E := E) K c y := add_mul _ _ _
        _ = inflationRightAction (E := E) K c (y * x₁) +
            inflationRightAction (E := E) K c (y * x₂) :=
              congrArg₂ (· + ·) hx₁ hx₂
        _ = inflationRightAction (E := E) K c (y * x₁ + y * x₂) :=
              (inflation_action_add (E := E) K c _ _).symm
        _ = inflationRightAction (E := E) K c (y * (x₁ + x₂)) :=
              congrArg (inflationRightAction (E := E) K c)
                (mul_add y x₁ x₂).symm
  | hsingle alpha a =>
      induction y using CProduc.induction_on c with
      | zero =>
          rw [concrete_inflation_zero, mul_zero, zero_mul,
            concrete_inflation_zero]
      | hadd y₁ y₂ hy₁ hy₂ =>
          calc
            inflationRightAction (E := E) K c
                (CProduc.single c alpha a) *
              inflationRightAction (E := E) K c (y₁ + y₂) =
              inflationRightAction (E := E) K c
                  (CProduc.single c alpha a) *
                (inflationRightAction (E := E) K c y₁ +
                  inflationRightAction (E := E) K c y₂) := by
                    rw [inflation_action_add]
            _ = inflationRightAction (E := E) K c
                    (CProduc.single c alpha a) *
                  inflationRightAction (E := E) K c y₁ +
                inflationRightAction (E := E) K c
                    (CProduc.single c alpha a) *
                  inflationRightAction (E := E) K c y₂ := mul_add _ _ _
            _ = inflationRightAction (E := E) K c
                    (y₁ * CProduc.single c alpha a) +
                inflationRightAction (E := E) K c
                    (y₂ * CProduc.single c alpha a) :=
                  congrArg₂ (· + ·) hy₁ hy₂
            _ = inflationRightAction (E := E) K c
                (y₁ * CProduc.single c alpha a +
                  y₂ * CProduc.single c alpha a) :=
                  (inflation_action_add (E := E) K c _ _).symm
            _ = inflationRightAction (E := E) K c
                ((y₁ + y₂) * CProduc.single c alpha a) :=
                  congrArg (inflationRightAction (E := E) K c)
                    (add_mul y₁ y₂ _).symm
      | hsingle beta b =>
          exact concrete_inflation_single
            (E := E) K c alpha beta a b

set_option maxHeartbeats 20000 in
-- The identity monomial acts identically.
theorem concrete_inflation_right :
    inflationRightAction (E := E) K c 1 = 1 := by
  rw [CProduc.one_def, inflation_action_single,
    inflation_right_single]

set_option maxHeartbeats 30000 in
-- The reversed product law is ordinary multiplication on the opposite ring.
noncomputable def concreteInflationHom :
    (CProduc c)ᵐᵒᵖ →+* Module.End K (Gal(F/K) →₀ E) where
  toFun x := inflationRightAction (E := E) K c x.unop
  map_zero' := concrete_inflation_zero (E := E) K c
  map_one' := concrete_inflation_right (E := E) K c
  map_add' x y := inflation_action_add (E := E) K c x.unop y.unop
  map_mul' x y := by
    change inflationRightAction (E := E) K c (y.unop * x.unop) = _
    exact (concrete_inflation_rev
      (E := E) K c x.unop y.unop).symm

set_option maxHeartbeats 50000 in
-- A base-field scalar acts on the coordinate module by ordinary scalar
-- multiplication, also from the right.
theorem concrete_inflation_algebra (r : K) :
    concreteInflationHom (E := E) K c
        (algebraMap K ((CProduc c)ᵐᵒᵖ) r) =
      algebraMap K (Module.End K (Gal(F/K) →₀ E)) r := by
  change inflationRightAction (E := E) K c
    (CProduc.single c 1 (algebraMap K F r)) = _
  rw [inflation_action_single]
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  rw [inflation_single_action]
  simp only [mul_one,     NMCocycl₂.apply_one_snd, Units.val_one,
    Module.algebraMap_end_apply, Finsupp.smul_single]
  apply congrArg (Finsupp.single rho)
  simp only [Algebra.smul_def]
  rw [mul_comm]
  rw [rho.commutes r, (IntermediateField.inclusion hFEFact.out).commutes r]

set_option maxHeartbeats 20000 in
-- The ring and scalar laws are already proved, so this only assembles them.
noncomputable def concreteInflationAlg :
    (CProduc c)ᵐᵒᵖ →ₐ[K] Module.End K (Gal(F/K) →₀ E) where
  __ := concreteInflationHom (E := E) K c
  commutes' := concrete_inflation_algebra (E := E) K c

set_option maxHeartbeats 20000 in
-- The field-valued coefficient identity behind commutation of the two actions.
theorem inflation_commutation_identity
    (rs rho alpha : Gal(F/K)) (a : F) :
    rs (rho a * (c (rho, alpha) : F)) * (c (rs, rho * alpha) : F) =
      (c (rs, rho) : F) *
        ((rs * rho) a * (c (rs * rho, alpha) : F)) := by
  have hc := inflation_cocycle_identity K c rs rho alpha
  simp only [map_mul]
  rw [show rs (rho a) = (rs * rho) a by rfl]
  calc
    _ = (rs * rho) a *
        (rs (c (rho, alpha) : F) * (c (rs, rho * alpha) : F)) := by ac_rfl
    _ = (rs * rho) a *
        ((c (rs * rho, alpha) : F) * (c (rs, rho) : F)) := by rw [← hc]
    _ = _ := by ac_rfl

set_option maxHeartbeats 100000 in
-- Restriction of a Galois automorphism commutes with the field inclusion.
theorem inflation_sigma_inclusion
    (sigma : Gal(E/K)) (x : F) :
    sigma (IntermediateField.inclusion hFEFact.out x) =
      IntermediateField.inclusion hFEFact.out
        (galoisRestrictionHom K hFEFact.out sigma x) := by
  letI : Algebra F E := (IntermediateField.inclusion hFEFact.out).toAlgebra
  change sigma (algebraMap F E x) =
    algebraMap F E ((sigma.restrictNormal F) x)
  exact (AlgEquiv.restrictNormal_commutes sigma F x).symm

set_option maxHeartbeats 100000 in
-- The E-valued scalar identity behind commutation of two monomial actions.
theorem inflation_commutation_coefficient
    (sigma : Gal(E/K)) (rho alpha : Gal(F/K)) (l q : E) (a : F) :
    let rs := galoisRestrictionHom K hFEFact.out sigma
    l * sigma (q * concreteInflationCoefficient (E := E) K c alpha rho a) *
        (coefficientUnitsHom K hFEFact.out
          (c (rs, rho * alpha)) : E) =
      (l * sigma q * (coefficientUnitsHom K hFEFact.out
        (c (rs, rho)) : E)) *
        concreteInflationCoefficient (E := E) K c alpha (rs * rho) a := by
  dsimp only
  let rs := galoisRestrictionHom K hFEFact.out sigma
  have hfield := inflation_commutation_identity K c rs rho alpha a
  have hsigmaCoeff :
      sigma (concreteInflationCoefficient (E := E) K c alpha rho a) =
        IntermediateField.inclusion hFEFact.out
          (rs (rho a * (c (rho, alpha) : F))) := by
    unfold concreteInflationCoefficient
    exact inflation_sigma_inclusion K sigma _
  rw [map_mul, hsigmaCoeff]
  unfold concreteInflationCoefficient
  let iFE : F →+* E := IntermediateField.inclusion hFEFact.out
  change
    l * (sigma q * iFE
      (rs (rho a * (c (rho, alpha) : F)))) *
        iFE (c (rs, rho * alpha) : F) =
      (l * sigma q * iFE (c (rs, rho) : F)) *
        iFE
          ((rs * rho) a * (c (rs * rho, alpha) : F))
  have hfieldE := congrArg iFE hfield
  calc
    _ = l * sigma q *
        (iFE (rs (rho a * (c (rho, alpha) : F))) *
          iFE (c (rs, rho * alpha) : F)) := by ac_rfl
    _ = l * sigma q * iFE
        (rs (rho a * (c (rho, alpha) : F)) *
          (c (rs, rho * alpha) : F)) :=
      congrArg (fun z : E ↦ l * sigma q * z) (map_mul iFE _ _).symm
    _ = l * sigma q * iFE
        ((c (rs, rho) : F) *
          ((rs * rho) a * (c (rs * rho, alpha) : F))) :=
      congrArg (fun z : E ↦ l * sigma q * z) hfieldE
    _ = l * sigma q *
        (iFE (c (rs, rho) : F) *
          iFE ((rs * rho) a * (c (rs * rho, alpha) : F))) :=
      congrArg (fun z : E ↦ l * sigma q * z) (map_mul iFE _ _)
    _ = _ := by ac_rfl

set_option maxHeartbeats 10000 in
-- A left monomial commutes with a right monomial on every coordinate.
theorem inflation_actions_commute
    (sigma : Gal(E/K)) (alpha : Gal(F/K)) (l : E) (a : F) :
    concreteInflationSingle (E := E) K c sigma l *
        inflationSingleAction (E := E) K c alpha a =
      inflationSingleAction (E := E) K c alpha a *
        concreteInflationSingle (E := E) K c sigma l := by
  apply end_ext_bimodule (F := F) (E := E) K
  intro rho q
  let rs := galoisRestrictionHom K hFEFact.out sigma
  change concreteInflationSingle (E := E) K c sigma l
      (inflationSingleAction (E := E) K c alpha a
        (Finsupp.single rho q)) =
    inflationSingleAction (E := E) K c alpha a
      (concreteInflationSingle (E := E) K c sigma l
        (Finsupp.single rho q))
  calc
    _ = concreteInflationSingle (E := E) K c sigma l
        (Finsupp.single (rho * alpha)
          (q * concreteInflationCoefficient (E := E) K c alpha rho a)) :=
      congrArg (concreteInflationSingle (E := E) K c sigma l)
        (inflation_single_action (E := E) K c alpha rho a q)
    _ = Finsupp.single (rs * (rho * alpha))
        (l * sigma (q * concreteInflationCoefficient (E := E) K c alpha rho a) *
          (coefficientUnitsHom K hFEFact.out
            (c (rs, rho * alpha)) : E)) :=
      inflation_single_basis (E := E) K c sigma (rho * alpha) l _
    _ = Finsupp.single ((rs * rho) * alpha)
        ((l * sigma q * (coefficientUnitsHom K hFEFact.out
          (c (rs, rho)) : E)) *
          concreteInflationCoefficient (E := E) K c alpha (rs * rho) a) :=
      congrArg₂ (fun i x ↦ Finsupp.single i x)
        (mul_assoc rs rho alpha).symm
        (inflation_commutation_coefficient
          (E := E) K c sigma rho alpha l q a)
    _ = inflationSingleAction (E := E) K c alpha a
        (Finsupp.single (rs * rho)
          (l * sigma q * (coefficientUnitsHom K hFEFact.out
            (c (rs, rho)) : E))) :=
      (inflation_single_action (E := E) K c alpha (rs * rho) a _).symm
    _ = _ := congrArg (inflationSingleAction (E := E) K c alpha a)
      (inflation_single_basis (E := E) K c sigma rho l q).symm

set_option maxHeartbeats 50000 in
-- A left monomial commutes with the summed right action.
theorem inflation_single_commute
    (sigma : Gal(E/K)) (l : E) (a : CProduc c) :
    concreteInflationSingle (E := E) K c sigma l *
        inflationRightAction (E := E) K c a =
      inflationRightAction (E := E) K c a *
        concreteInflationSingle (E := E) K c sigma l := by
  induction a using CProduc.induction_on c with
  | zero => rw [concrete_inflation_zero, mul_zero, zero_mul]
  | hadd a b ha hb =>
      calc
        concreteInflationSingle (E := E) K c sigma l *
            inflationRightAction (E := E) K c (a + b) =
          concreteInflationSingle (E := E) K c sigma l *
            (inflationRightAction (E := E) K c a +
              inflationRightAction (E := E) K c b) := by
                rw [inflation_action_add]
        _ = concreteInflationSingle (E := E) K c sigma l *
              inflationRightAction (E := E) K c a +
            concreteInflationSingle (E := E) K c sigma l *
              inflationRightAction (E := E) K c b := mul_add _ _ _
        _ = inflationRightAction (E := E) K c a *
              concreteInflationSingle (E := E) K c sigma l +
            inflationRightAction (E := E) K c b *
              concreteInflationSingle (E := E) K c sigma l :=
                congrArg₂ (· + ·) ha hb
        _ = (inflationRightAction (E := E) K c a +
              inflationRightAction (E := E) K c b) *
            concreteInflationSingle (E := E) K c sigma l :=
                (add_mul _ _ _).symm
        _ = inflationRightAction (E := E) K c (a + b) *
            concreteInflationSingle (E := E) K c sigma l := by
                rw [inflation_action_add]
  | hsingle alpha a =>
      rw [inflation_action_single]
      exact inflation_actions_commute
        (E := E) K c sigma alpha l a

set_option maxHeartbeats 50000 in
-- The full inflated left action commutes with the full right action.
theorem actions_commute_unop
    (x : CProduc (concreteInflationCocycle K hFEFact.out c))
    (a : CProduc c) :
    inflationLeftAction (E := E) K c x *
        inflationRightAction (E := E) K c a =
      inflationRightAction (E := E) K c a *
        inflationLeftAction (E := E) K c x := by
  induction x using CProduc.induction_on
      (concreteInflationCocycle K hFEFact.out c) with
  | zero => simp
  | hadd x y hx hy =>
      calc
        inflationLeftAction (E := E) K c (x + y) *
            inflationRightAction (E := E) K c a =
          (inflationLeftAction (E := E) K c x +
            inflationLeftAction (E := E) K c y) *
              inflationRightAction (E := E) K c a :=
          congrArg (fun z ↦ z * inflationRightAction (E := E) K c a)
            ((inflationLeftAction (E := E) K c).map_add x y)
        _ = inflationLeftAction (E := E) K c x *
              inflationRightAction (E := E) K c a +
            inflationLeftAction (E := E) K c y *
              inflationRightAction (E := E) K c a := add_mul _ _ _
        _ = inflationRightAction (E := E) K c a *
              inflationLeftAction (E := E) K c x +
            inflationRightAction (E := E) K c a *
              inflationLeftAction (E := E) K c y :=
                congrArg₂ (· + ·) hx hy
        _ = inflationRightAction (E := E) K c a *
            (inflationLeftAction (E := E) K c x +
              inflationLeftAction (E := E) K c y) :=
                (mul_add _ _ _).symm
        _ = inflationRightAction (E := E) K c a *
            inflationLeftAction (E := E) K c (x + y) :=
              congrArg (fun z ↦ inflationRightAction (E := E) K c a * z)
                ((inflationLeftAction (E := E) K c).map_add x y).symm
  | hsingle sigma l =>
      calc
        inflationLeftAction (E := E) K c
              (CProduc.single
                (concreteInflationCocycle K hFEFact.out c) sigma l) *
            inflationRightAction (E := E) K c a =
          concreteInflationSingle (E := E) K c sigma l *
            inflationRightAction (E := E) K c a :=
          congrArg (fun z ↦ z * inflationRightAction (E := E) K c a)
            (inflation_single (E := E) K c sigma l)
        _ = inflationRightAction (E := E) K c a *
            concreteInflationSingle (E := E) K c sigma l :=
          inflation_single_commute
            (E := E) K c sigma l a
        _ = inflationRightAction (E := E) K c a *
            inflationLeftAction (E := E) K c
              (CProduc.single
                (concreteInflationCocycle K hFEFact.out c) sigma l) :=
          congrArg (fun z ↦ inflationRightAction (E := E) K c a * z)
            (inflation_single (E := E) K c sigma l).symm

set_option maxHeartbeats 20000 in
-- Extra heartbeats are needed for the large search space in this proof.
theorem concrete_actions_commute
    (x : CProduc (concreteInflationCocycle K hFEFact.out c))
    (a : (CProduc c)ᵐᵒᵖ) :
    inflationLeftAction (E := E) K c x *
        concreteInflationAlg (E := E) K c a =
      concreteInflationAlg (E := E) K c a *
        inflationLeftAction (E := E) K c x :=
  actions_commute_unop (E := E) K c x a.unop

set_option maxHeartbeats 30000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- The combined left-right action on the coordinate inflation bimodule. -/
noncomputable def inflationCombinedAction :
    CProduc (concreteInflationCocycle K hFEFact.out c) ⊗[K]
        (CProduc c)ᵐᵒᵖ →ₐ[K]
      Module.End K (Gal(F/K) →₀ E) :=
  Algebra.TensorProduct.lift (inflationLeftAction (E := E) K c)
    (concreteInflationAlg (E := E) K c)
    (concrete_actions_commute (E := E) K c)

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 100000 in
-- The coordinate module is free over E on Gal(F/K).
omit hFEFact in
theorem inflation_bimodule_upper :
    Module.finrank E (Gal(F/K) →₀ E) = Module.finrank K F := by
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
  exact IsGalois.card_aut_eq_finrank K F

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 100000 in
-- Restricting scalars multiplies the dimension by [E:K].
omit hFEFact in
theorem inflation_bimodule_base :
    Module.finrank K (Gal(F/K) →₀ E) =
      Module.finrank K E * Module.finrank K F := by
  rw [← Module.finrank_mul_finrank K E (Gal(F/K) →₀ E),
    inflation_bimodule_upper]

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 100000 in
-- The combined source and target have the same finite K-dimension.
theorem inflation_combined_end :
    Module.finrank K
        (CProduc (concreteInflationCocycle K hFEFact.out c) ⊗[K]
          (CProduc c)ᵐᵒᵖ) =
      Module.finrank K (Module.End K (Gal(F/K) →₀ E)) := by
  rw [Module.finrank_tensorProduct, MulOpposite.finrank,
    CProduc.finrank_over_base, CProduc.finrank_over_base,
    Module.finrank_linearMap,
    inflation_bimodule_base]
  ring

set_option synthInstance.maxHeartbeats 500000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
-- Simplicity gives injectivity; equal finite dimensions give surjectivity.
theorem inflation_combined_bijective :
    Function.Bijective (inflationCombinedAction (E := E) K c) := by
  letI : IsSimpleRing
      (CProduc (concreteInflationCocycle K hFEFact.out c) ⊗[K]
        (CProduc c)ᵐᵒᵖ) :=
    BGroups.tensor_simple_ring K
      (CProduc (concreteInflationCocycle K hFEFact.out c))
      ((CProduc c)ᵐᵒᵖ)
  have hinjRing : Function.Injective
      (inflationCombinedAction (E := E) K c).toRingHom :=
    @RingHom.injective
      (CProduc (concreteInflationCocycle K hFEFact.out c) ⊗[K]
        (CProduc c)ᵐᵒᵖ)
      (Module.End K (Gal(F/K) →₀ E)) _ _ _ _
      (inflationCombinedAction (E := E) K c).toRingHom
  have hinj : Function.Injective
      (inflationCombinedAction (E := E) K c) := by
    intro x y hxy
    exact hinjRing hxy
  have hinjLinear : Function.Injective
      (inflationCombinedAction (E := E) K c).toLinearMap := by
    intro x y hxy
    exact hinj hxy
  have hsurj : Function.Surjective
      (inflationCombinedAction (E := E) K c).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := K)
      (V := CProduc (concreteInflationCocycle K hFEFact.out c) ⊗[K]
        (CProduc c)ᵐᵒᵖ)
      (V₂ := Module.End K (Gal(F/K) →₀ E))
      (f := (inflationCombinedAction (E := E) K c).toLinearMap)
      (inflation_combined_end (E := E) K c)).mp hinjLinear
  exact ⟨hinj, hsurj⟩

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 50000 in
/-- The combined action is the full endomorphism algebra. -/
noncomputable def inflationCombinedEnd :
    CProduc (concreteInflationCocycle K hFEFact.out c) ⊗[K]
        (CProduc c)ᵐᵒᵖ ≃ₐ[K]
      Module.End K (Gal(F/K) →₀ E) :=
  AlgEquiv.ofBijective (inflationCombinedAction (E := E) K c)
    (inflation_combined_bijective (E := E) K c)

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 50000 in
/-- Concrete cochain inflation preserves the Brauer class. -/
theorem brauer_equivalent_inflation :
    IsBrauerEquivalent
      (CProduc.centralSimpleCSA K F c)
      (CProduc.centralSimpleCSA K E
        (concreteInflationCocycle K hFEFact.out c)) := by
  exact (equivalent_op_end K
    (CProduc (concreteInflationCocycle K hFEFact.out c))
    (CProduc c) (Gal(F/K) →₀ E)
    (inflationCombinedEnd (E := E) K c)).symm

end


noncomputable section

universe u

open BGroups CProduca

variable (K : Type u) [Field K]

set_option synthInstance.maxHeartbeats 100000 in
-- This retains the original separable-closure API while the Morita theorem
-- above is available over an arbitrary ambient field.
set_option maxHeartbeats 50000 in
/-- Abstract inflation agrees unconditionally with concrete cochain
inflation for finite levels of the chosen separable closure. -/
theorem inflation_concrete_cocycle
    {F E : FiniteGaloisIntermediateField K (SeparableClosure K)}
    [hFEFact : Fact (F ≤ E)]
    (c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ)) :
    inflationHom K hFEFact.out (MHTwo.mk c) =
      MHTwo.mk
        (concreteInflationCocycle K hFEFact.out c) := by
  apply (CProduc.hRelativeBrauer K E).injective
  rw [relative_brauer_inflation]
  apply Subtype.ext
  change BGroups.brauerClass K
      (CProduc.centralSimpleCSA K F c) =
    BGroups.brauerClass K
      (CProduc.centralSimpleCSA K E
        (concreteInflationCocycle K hFEFact.out c))
  exact (BGroups.brauer_class _ _ _).2
    (brauer_equivalent_inflation K c)


end

end Submission.CField.LBrauer
