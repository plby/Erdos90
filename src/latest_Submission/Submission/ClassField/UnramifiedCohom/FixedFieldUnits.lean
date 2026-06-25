import Submission.ClassField.UnramifiedCohom.UnitsAction
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Fixed-field units in Corollary III.1.6

For a closed normal subgroup of an infinite Galois group, this file
identifies the units integral over the base domain in the fixed field with
the invariant integral units upstairs.  The construction is algebraic and
does not require the fixed field to be finite over the base field.
-/

namespace Submission.CField.UCohom

open CategoryTheory

noncomputable section

attribute [local instance] Units.mulDistribMulActionRight

variable (A K L : Type)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsFractionRing A K] [Algebra.IsAlgebraic K L] [IsGalois K L]

local instance ambientIntegralClosureAction :
    MulSemiringAction Gal(L/K) (integralClosure A L) :=
  IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)

section FixedField

variable (N : ClosedSubgroup Gal(L/K)) [N.Normal]

private abbrev F := IntermediateField.fixedField N.1
private abbrev B := integralClosure A L
private abbrev C := integralClosure A (F K L N)

local instance fixedIntegralClosureAction :
    MulSemiringAction Gal(F K L N/K) (C A K L N) :=
  IsIntegralClosure.MulSemiringAction A K (F K L N) (C A K L N)

/-- Inclusion of the integral closure in the fixed field into the ambient
integral closure. -/
private def fixedClosureAmbient : C A K L N →+* B A L where
  toFun x := ⟨((x : F K L N) : L), x.property.map
    ((F K L N).val.restrictScalars A)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The induced unit action is expensive for typeclass synthesis.
/-- An invariant ambient integral unit, regarded as a unit in the integral
closure inside the fixed field. -/
private def invariantFixedUnit
    (x : (Rep.ofMulDistribMulAction Gal(L/K) (B A L)ˣ).quotientToInvariants
      N.1) : (C A K L N)ˣ := by
  let u : (B A L)ˣ := x.1.toMul
  have hfix (n : N) : n.1 ((u : B A L) : L) = ((u : B A L) : L) := by
    have h := congrArg Additive.toMul (x.2 n)
    have hu := congrArg (fun z : (B A L)ˣ ↦ (((z : B A L) : L))) h
    exact (algebraMap.coe_smul' (B := B A L) (C := L) n.1
      (u : B A L)).symm.trans hu
  have hfixInv (n : N) : n.1 (((u⁻¹ : (B A L)ˣ) : B A L) : L) =
      (((u⁻¹ : (B A L)ˣ) : B A L) : L) := by
    have hu0 : n.1 • u = u := congrArg Additive.toMul (x.2 n)
    have hi : n.1 • u⁻¹ = u⁻¹ := by
      rw [smul_inv']
      exact congrArg Inv.inv hu0
    have hu := congrArg
      (fun z : (B A L)ˣ ↦ (((z : B A L) : L))) hi
    exact (algebraMap.coe_smul' (B := B A L) (C := L) n.1
      ((u⁻¹ : (B A L)ˣ) : B A L)).symm.trans hu
  let a : F K L N := ⟨((u : B A L) : L), by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ ↦ hfix ⟨σ, hσ⟩⟩
  let ai : F K L N := ⟨(((u⁻¹ : (B A L)ˣ) : B A L) : L), by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ ↦ hfixInv ⟨σ, hσ⟩⟩
  have ha : IsIntegral A a :=
    IntermediateField.coe_isIntegral_iff.mp u.1.property
  have hai : IsIntegral A ai :=
    IntermediateField.coe_isIntegral_iff.mp (u⁻¹).1.property
  exact
    { val := ⟨a, ha⟩
      inv := ⟨ai, hai⟩
      val_inv := by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : B A L ↦ (z : L)) u.val_inv
      inv_val := by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : B A L ↦ (z : L)) u.inv_val }

set_option synthInstance.maxHeartbeats 200000 in
-- The induced unit action is expensive for typeclass synthesis.
/-- Units of the integral closure in the fixed field are exactly the
`N`-invariant units of the ambient integral closure. -/
noncomputable def fixedUnitsInvariants :
    (C A K L N)ˣ ≃*
      Multiplicative
        ((Rep.ofMulDistribMulAction Gal(L/K) (B A L)ˣ).quotientToInvariants
          N.1) where
  toFun u := by
    let w : (B A L)ˣ :=
      Units.map (fixedClosureAmbient A K L N) u
    refine Multiplicative.ofAdd ⟨Additive.ofMul w, ?_⟩
    intro n
    change Additive.ofMul (n.1 • w) = Additive.ofMul w
    apply Additive.ofMul.injective
    apply Units.ext
    apply Subtype.ext
    exact (algebraMap.coe_smul' (B := B A L) (C := L) n.1
      (w : B A L)).trans <| by
      exact u.1.1.property n
  invFun x := invariantFixedUnit A K L N x.toAdd
  left_inv u := by
    apply Units.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    rfl
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The induced additive structure unfolds the integral-closure unit action.
/-- The additive form of the fixed-field/invariants equivalence, oriented
from invariants to fixed-field units. -/
private noncomputable def invariantsFixedUnits :
    (Rep.ofMulDistribMulAction Gal(L/K) (B A L)ˣ).quotientToInvariants N.1 ≃+
      Additive (C A K L N)ˣ :=
  (AddEquiv.additiveMultiplicative _).trans
    (fixedUnitsInvariants A K L N).symm.toAdditive

set_option synthInstance.maxHeartbeats 200000 in
-- The coercions pass through two type tags and the invariant submodule.
omit [IsGalois K L] in
@[simp]
theorem invariants_units_coe
    (x : (Rep.ofMulDistribMulAction Gal(L/K) (B A L)ˣ).quotientToInvariants
      N.1) :
    (((invariantsFixedUnits A K L N x).toMul :
        C A K L N) : F K L N) =
      ⟨(((Rep.toAdditive (M := Gal(L/K)) (G := (B A L)ˣ) x.1).toMul :
        (B A L)ˣ) : B A L), by
          rw [IntermediateField.mem_fixedField_iff]
          intro σ hσ
          have h := congrArg Additive.toMul (x.2 ⟨σ, hσ⟩)
          have hu := congrArg (fun z : (B A L)ˣ ↦ (((z : B A L) : L))) h
          exact (algebraMap.coe_smul' (B := B A L) (C := L) σ
            ((Rep.toAdditive (M := Gal(L/K)) (G := (B A L)ˣ) x.1).toMul :
              B A L)).symm.trans hu⟩ := by
  rfl

set_option maxHeartbeats 600000 in
-- Reducing both integral-closure unit actions is expensive.
set_option synthInstance.maxHeartbeats 600000 in
-- The integral-closure actions also make typeclass synthesis expensive.
/-- The fixed-field/invariants equivalence intertwines the quotient action
with the action obtained by restricting automorphisms to the fixed field. -/
theorem invariants_units_equivariant
    (g : Gal(L/K) ⧸ N.1)
    (x : (Rep.ofMulDistribMulAction Gal(L/K) (B A L)ˣ).quotientToInvariants
      N.1) :
    invariantsFixedUnits A K L N
        (((Rep.ofMulDistribMulAction Gal(L/K) (B A L)ˣ).quotientToInvariants
          N.1).ρ g x) =
      (Rep.ofMulDistribMulAction Gal(F K L N/K) (C A K L N)ˣ).ρ
        (InfiniteGalois.normalAutEquivQuotient N g)
        (invariantsFixedUnits A K L N x) := by
  induction g using QuotientGroup.induction_on with
  | _ σ =>
      rw [InfiniteGalois.normalAutEquivQuotient_apply]
      apply Additive.toMul.injective
      apply Units.ext
      apply Subtype.ext
      rw [invariants_units_coe]
      apply Subtype.ext
      simp only [Rep.ofMulDistribMulAction_ρ_apply_apply,
        Representation.ofQuotient_coe_apply]
      let u : (B A L)ˣ :=
        (Rep.toAdditive (M := Gal(L/K)) (G := (B A L)ˣ) x.1).toMul
      let v : (C A K L N)ˣ :=
        (invariantsFixedUnits A K L N x).toMul
      change ((((σ • u : (B A L)ˣ) : B A L) : L)) =
        ((((((AlgEquiv.restrictNormalHom (F K L N) σ) • v :
          (C A K L N)ˣ) : C A K L N) : F K L N) : L))
      calc
        ((((σ • u : (B A L)ˣ) : B A L) : L)) =
            (((σ • (u : B A L) : B A L) : L)) :=
          congrArg (fun z : B A L ↦ (z : L)) (Units.coe_smul σ u)
        _ = σ (((u : B A L) : L)) :=
          algebraMap.coe_smul' (B := B A L) (C := L) σ (u : B A L)
        _ = σ (((v : C A K L N) : F K L N) : L) := by
          apply congrArg σ
          exact (congrArg Subtype.val
            (invariants_units_coe
              A K L N x)).symm
        _ = (((AlgEquiv.restrictNormalHom (F K L N) σ)
            ((v : C A K L N) : F K L N) : F K L N) : L) :=
          (AlgEquiv.restrictNormalHom_apply (F K L N) σ
            ((v : C A K L N) : F K L N)).symm
        _ = (((((AlgEquiv.restrictNormalHom (F K L N) σ) •
            (v : C A K L N) : C A K L N) : F K L N) : L)) := by
          apply congrArg (fun z : F K L N ↦ (z : L))
          exact (algebraMap.coe_smul' (B := C A K L N) (C := F K L N)
            (AlgEquiv.restrictNormalHom (F K L N) σ)
            (v : C A K L N)).symm
        _ = ((((((AlgEquiv.restrictNormalHom (F K L N) σ) • v :
            (C A K L N)ˣ) : C A K L N) : F K L N) : L)) := by
          apply congrArg (fun z : C A K L N ↦ (((z : F K L N) : L)))
          exact (Units.coe_smul
            (AlgEquiv.restrictNormalHom (F K L N) σ) v).symm

set_option maxHeartbeats 600000 in
-- Constructing the representation equivalence unfolds both unit actions.
set_option synthInstance.maxHeartbeats 200000 in
-- The integral-closure actions make the representation construction expensive.
/-- Equivariant identification of invariant ambient integral units with the
integral units in the fixed field. -/
noncomputable def invariantsRepIso :
    (Rep.ofMulDistribMulAction Gal(L/K) (B A L)ˣ).quotientToInvariants N.1 ≅
      Rep.res (InfiniteGalois.normalAutEquivQuotient N).toMonoidHom
        (Rep.ofMulDistribMulAction Gal(F K L N/K) (C A K L N)ˣ) := by
  let e := invariantsFixedUnits A K L N
  let eRep :
      ((Rep.ofMulDistribMulAction Gal(L/K) (B A L)ˣ).quotientToInvariants
        N.1).ρ.Equiv
        (Rep.res (InfiniteGalois.normalAutEquivQuotient N).toMonoidHom
          (Rep.ofMulDistribMulAction Gal(F K L N/K) (C A K L N)ˣ)).ρ :=
    Representation.Equiv.mk e.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro x
      change e
          (((Rep.ofMulDistribMulAction Gal(L/K) (B A L)ˣ).quotientToInvariants
            N.1).ρ g x) =
        (Rep.ofMulDistribMulAction Gal(F K L N/K) (C A K L N)ˣ).ρ
          (InfiniteGalois.normalAutEquivQuotient N g) (e x)
      exact invariants_units_equivariant
        A K L N g x)
  exact Rep.mkIso eRep

set_option maxHeartbeats 600000 in
-- Unfolding the continuous action to its underlying representation is expensive.
set_option synthInstance.maxHeartbeats 200000 in
-- The underlying unit action also requires a deeper typeclass search.
/-- The same equivariant identification, stated for the underlying
representation of the continuous integral-closure unit action. -/
noncomputable def integralRepIso :
    ((Submission.CField.PCohom.underlyingRep
      (integralDiscreteAction A K L)).quotientToInvariants N.1) ≅
      Rep.res (InfiniteGalois.normalAutEquivQuotient N).toMonoidHom
        (Rep.ofMulDistribMulAction Gal(F K L N/K) (C A K L N)ˣ) := by
  exact invariantsRepIso A K L N

end FixedField

end

end Submission.CField.UCohom
