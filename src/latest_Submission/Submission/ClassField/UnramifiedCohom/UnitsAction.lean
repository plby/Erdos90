import Submission.ClassField.UnramifiedCohom.FiniteQuotient
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The continuous Galois module of units in an algebraic extension

This supplies the coefficient object needed for Milne's Corollary III.1.6.
The units of the integral closure are given the discrete topology.  Their
natural Galois action is continuous because every algebraic element has an
open stabilizer in the Krull topology.
-/

namespace Submission.CField.UCohom

open CategoryTheory

noncomputable section

attribute [local instance] Units.mulDistribMulActionRight

variable (A K L : Type)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsFractionRing A K] [Algebra.IsAlgebraic K L]

local instance : MulSemiringAction Gal(L/K) (integralClosure A L) :=
  IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)

set_option synthInstance.maxHeartbeats 200000 in
-- Inferring the induced unit action unfolds the integral-closure action.
local instance : MulAction Gal(L/K) (Additive (integralClosure A L)ˣ) where
  smul g x := Additive.ofMul (g • x.toMul)
  one_smul x := by
    change Additive.ofMul (1 • x.toMul) = x
    rw [one_smul]
    rfl
  mul_smul g h x := by
    change Additive.ofMul ((g * h) • x.toMul) =
      Additive.ofMul (g • h • x.toMul)
    rw [mul_smul]

set_option synthInstance.maxHeartbeats 200000 in
-- Inferring the induced unit action unfolds the integral-closure action.
/-- A unit of the integral closure has open stabilizer in the Krull
topology. -/
theorem integral_stabilizer_open
    (x : Additive (integralClosure A L)ˣ) :
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
  have hx := stabilizer_isOpen_of_isIntegral
    (K := K) (L := L) ((x.toMul.1 : integralClosure A L) : L)
  convert hx using 1
  ext g
  change (Additive.ofMul (g • x.toMul) = x) ↔
    g (((x.toMul : (integralClosure A L)ˣ) : integralClosure A L) : L) =
      (((x.toMul : (integralClosure A L)ˣ) : integralClosure A L) : L)
  constructor
  · intro h
    have hu := congrArg Additive.toMul h
    change g • x.toMul = x.toMul at hu
    have hb := congrArg
      (fun u : (integralClosure A L)ˣ ↦
        (((u : integralClosure A L) : L))) hu
    exact (algebraMap.coe_smul'
      (B := integralClosure A L) (C := L) g
      (x.toMul : integralClosure A L)).symm.trans hb
  · intro h
    apply Additive.toMul.injective
    change g • x.toMul = x.toMul
    apply Units.ext
    apply Subtype.ext
    exact (algebraMap.coe_smul'
      (B := integralClosure A L) (C := L) g
      (x.toMul : integralClosure A L)).trans h

set_option maxHeartbeats 600000 in
-- The nested integral-closure and topological action structures are expensive.
set_option maxRecDepth 5000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The induced unit action requires a deeper typeclass search.
/-- The units of the integral closure of `A` in `L`, as a discrete
continuous module for the Krull-topological Galois group `Gal(L/K)`. -/
noncomputable def integralDiscreteAction :
    DiscreteContAction (TopModuleCat ℤ) Gal(L/K) := by
  let X := Additive (integralClosure A L)ˣ
  letI : TopologicalSpace X := ⊥
  letI : DiscreteTopology X := ⟨rfl⟩
  letI : MulAction Gal(L/K) X := inferInstance
  letI : ContinuousSMul Gal(L/K) X :=
    continuousSMul_iff_stabilizer_isOpen.mpr
      (integral_stabilizer_open A K L)
  let R := Rep.ofMulDistribMulAction Gal(L/K) (integralClosure A L)ˣ
  let act (g : Gal(L/K)) : X →L[ℤ] X :=
    { toLinearMap := R.ρ g
      cont := continuous_of_discreteTopology }
  let T : Action (TopModuleCat ℤ) Gal(L/K) :=
    { V := TopModuleCat.of ℤ X
      ρ :=
        { toFun := fun g ↦ TopModuleCat.ofHom (act g)
          map_one' := by
            apply ConcreteCategory.ext
            ext x
            exact congrArg (fun f : Module.End ℤ X ↦ f x) R.ρ.map_one
          map_mul' := fun g h ↦ by
            apply ConcreteCategory.ext
            ext x
            exact congrArg (fun f : Module.End ℤ X ↦ f x)
              (R.ρ.map_mul g h) } }
  have hT : T.IsContinuous := by
    rw [Action.isContinuous_def]
    exact continuous_smul.congr fun _ ↦ rfl
  exact ⟨⟨T, hT⟩, by
    change DiscreteTopology X
    infer_instance⟩

end

end Submission.CField.UCohom
