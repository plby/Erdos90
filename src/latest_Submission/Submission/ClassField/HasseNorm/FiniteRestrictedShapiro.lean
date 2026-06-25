import Submission.ClassField.HasseNorm.FiniteStageCohomology
import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# Restricted Shapiro for finite-place local units

For one finite base prime, the Galois group permutes the upper prime-adic
local-unit factors transitively.  This file identifies their product with
the representation coinduced from one chosen factor and applies Shapiro's
lemma.  The chosen-factor action is obtained from the already constructed
product action by using families supported at the chosen prime; this avoids
introducing any independent completion-transport convention.
-/

namespace Submission.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.COps
open Submission.CField.Ideles
open Submission.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The stabilizer of one literal upper prime in the fiber over `P`. -/
noncomputable def primeAboveStabilizer
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    Subgroup Gal(L/K) := by
  letI := aboveMulAction (K := K) (L := L) P
  exact MulAction.stabilizer Gal(L/K) Q

/-- Local-unit families supported at one chosen upper prime. -/
def aboveUnitsSupported
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    Subgroup (PrimesAboveUnits (K := K) (L := L) P) where
  carrier := {x | ∀ R, R ≠ Q → x R = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro x y hx hy R hR
    change x R * y R = 1
    rw [hx R hR, hy R hR, one_mul]
  inv_mem' := by
    intro x hx R hR
    change (x R)⁻¹ = 1
    rw [hx R hR, inv_one]

set_option maxHeartbeats 1000000 in
-- Checking support preservation expands the dependent restricted-product
-- action at every upper prime.
set_option synthInstance.maxHeartbeats 300000 in
/-- The chosen-prime stabilizer preserves families supported at that
prime. -/
@[reducible]
noncomputable def primesAboveAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    MulDistribMulAction (primeAboveStabilizer (K := K) (L := L) P Q)
      (aboveUnitsSupported (K := K) (L := L) P Q) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  letI := primesUnitsAction (K := K) (L := L) P
  refine
    { smul := fun sigma x => ⟨sigma.1 • x.1, ?_⟩
      one_smul := fun x => Subtype.ext (one_smul Gal(L/K) x.1)
      mul_smul := fun sigma tau x =>
        Subtype.ext (mul_smul sigma.1 tau.1 x.1)
      smul_one := fun sigma => Subtype.ext (smul_one sigma.1)
      smul_mul := fun sigma x y => Subtype.ext (smul_mul' sigma.1 x.1 y.1) }
  intro R hRQ
  have hsigmaQ : sigma.1 • Q = Q := sigma.2
  have hinvR : sigma.1⁻¹ • R ≠ Q := by
    intro h
    apply hRQ
    calc
      R = sigma.1 • (sigma.1⁻¹ • R) := (smul_inv_smul sigma.1 R).symm
      _ = sigma.1 • Q := congrArg (fun T => sigma.1 • T) h
      _ = Q := hsigmaQ
  apply Subtype.ext
  change Units.map
      (finitePlaceTransport (K := K) sigma.1 R.1).toRingHom.toMonoidHom
        ((x.1 (sigma.1⁻¹ • R)).1) = 1
  rw [x.2 (sigma.1⁻¹ • R) hinvR]
  exact map_one _

/-- The representation on a family supported at the chosen upper prime. -/
noncomputable def resizedSupportedRepresentation
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    Rep (ULift.{u} ℤ)
      (primeAboveStabilizer (K := K) (L := L) P Q) := by
  letI := primesAboveAction
    (K := K) (L := L) P Q
  exact uliftMulRepresentation
    (G := primeAboveStabilizer (K := K) (L := L) P Q)
    (M := aboveUnitsSupported (K := K) (L := L) P Q)

/-- Evaluation at the chosen prime identifies a supported family with the
actual local-unit group at that prime. -/
noncomputable def primesAboveSupported
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    aboveUnitsSupported (K := K) (L := L) P Q ≃*
      IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q.1 := by
  classical
  exact
  {
  toFun x := x.1 Q
  invFun x := ⟨Pi.mulSingle
      (M := fun R : FinitePrimesAbove (K := K) (L := L) P =>
        IdeleUnitSubgroup (NumberField.RingOfIntegers L) L R.1) Q x,
    fun R hR => Pi.mulSingle_eq_of_ne
      (M := fun T : FinitePrimesAbove (K := K) (L := L) P =>
        IdeleUnitSubgroup (NumberField.RingOfIntegers L) L T.1)
      hR x⟩
  left_inv x := by
    apply Subtype.ext
    funext R
    by_cases hR : R = Q
    · subst R
      exact Pi.mulSingle_eq_same
        (M := fun R : FinitePrimesAbove (K := K) (L := L) P =>
          IdeleUnitSubgroup (NumberField.RingOfIntegers L) L R.1)
        Q (x.1 Q)
    · change Pi.mulSingle
          (M := fun T : FinitePrimesAbove (K := K) (L := L) P =>
            IdeleUnitSubgroup (NumberField.RingOfIntegers L) L T.1)
          Q (x.1 Q) R = x.1 R
      rw [Pi.mulSingle_eq_of_ne hR]
      exact (x.2 R hR).symm
  right_inv x := Pi.mulSingle_eq_same
    (M := fun R : FinitePrimesAbove (K := K) (L := L) P =>
      IdeleUnitSubgroup (NumberField.RingOfIntegers L) L R.1) Q x
  map_mul' x y := rfl }

set_option maxHeartbeats 1000000 in
-- Transporting the stabilizer action through the supported-family equivalence
-- requires substantial dependent rewriting.
set_option synthInstance.maxHeartbeats 300000 in
/-- The stabilizer action on the actual chosen local-unit group, transported
from the supported-family model. -/
@[reducible]
noncomputable def unitsStabilizerAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    MulDistribMulAction (primeAboveStabilizer (K := K) (L := L) P Q)
      (IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q.1) := by
  letI := primesAboveAction
    (K := K) (L := L) P Q
  let e := primesAboveSupported
    (K := K) (L := L) P Q
  letI : MulAction
      (primeAboveStabilizer (K := K) (L := L) P Q)
      (IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q.1) :=
    e.symm.toEquiv.mulAction
      (primeAboveStabilizer (K := K) (L := L) P Q)
  refine
    { smul_mul := fun sigma x y => by
        change e (sigma • e.symm (x * y)) =
          e (sigma • e.symm x) * e (sigma • e.symm y)
        rw [← e.map_mul]
        apply congrArg e
        rw [e.symm.map_mul, smul_mul']
      smul_one := fun sigma => by
        change e (sigma • e.symm 1) = 1
        rw [e.symm.map_one, smul_one, e.map_one] }

set_option maxHeartbeats 1000000 in
-- Building the resized local-unit representation requires resolving the full
-- stabilizer action and scalar tower.
set_option synthInstance.maxHeartbeats 300000 in
/-- Resized representation on the chosen upper local-unit group. -/
noncomputable def resizedUnitsRepresentation
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    Rep (ULift.{u} ℤ)
      (primeAboveStabilizer (K := K) (L := L) P Q) := by
  letI := unitsStabilizerAction (K := K) (L := L) P Q
  exact uliftMulRepresentation
    (G := primeAboveStabilizer (K := K) (L := L) P Q)
    (M := IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q.1)

set_option maxHeartbeats 1000000 in
-- The representation isomorphism elaborates mutually inverse dependent unit
-- maps together with their equivariance proofs.
set_option synthInstance.maxHeartbeats 300000 in
/-- Supported families and the actual chosen local-unit group are
isomorphic as stabilizer representations. -/
noncomputable def resizedSupportedIso
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    resizedSupportedRepresentation
        (K := K) (L := L) P Q ≅
      resizedUnitsRepresentation
        (K := K) (L := L) P Q := by
  letI := primesAboveAction
    (K := K) (L := L) P Q
  letI := unitsStabilizerAction
    (K := K) (L := L) P Q
  apply Rep.mkIso
  let e := primesAboveSupported
    (K := K) (L := L) P Q
  refine
    { toLinearEquiv :=
        { toEquiv := e.toAdditive.toEquiv
          map_add' := e.toAdditive.map_add
          map_smul' := fun r x => map_zsmul e.toAdditive r.down x }
      isIntertwining' := fun sigma => by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        change e (sigma • x.toMul) =
          e (sigma • e.symm (e x.toMul))
        rw [e.symm_apply_apply] }

set_option maxHeartbeats 1000000 in
-- Constructing the supported projection requires normalizing a dependent
-- family of local-unit subgroups.
set_option synthInstance.maxHeartbeats 300000 in
/-- Projection to the family supported at the chosen prime. -/
noncomputable def primesAboveProjection
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    PrimesAboveUnits (K := K) (L := L) P →*
      aboveUnitsSupported (K := K) (L := L) P Q := by
  classical
  exact
  {
  toFun x := ⟨Pi.mulSingle
      (M := fun R : FinitePrimesAbove (K := K) (L := L) P =>
        IdeleUnitSubgroup (NumberField.RingOfIntegers L) L R.1)
      Q (x Q), fun R hR =>
    Pi.mulSingle_eq_of_ne
      (M := fun T : FinitePrimesAbove (K := K) (L := L) P =>
        IdeleUnitSubgroup (NumberField.RingOfIntegers L) L T.1)
      hR (x Q)⟩
  map_one' := by
    apply Subtype.ext
    funext R
    by_cases hR : R = Q <;> simp [hR]
  map_mul' x y := by
    apply Subtype.ext
    exact Pi.mulSingle_mul
      (f := fun R : FinitePrimesAbove (K := K) (L := L) P =>
        IdeleUnitSubgroup (NumberField.RingOfIntegers L) L R.1)
      Q (x Q) (y Q) }

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem above_projection_self
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (x : PrimesAboveUnits (K := K) (L := L) P) :
    (primesAboveProjection
      (K := K) (L := L) P Q x).1 Q = x Q := by
  classical
  exact Pi.mulSingle_eq_same
    (M := fun R : FinitePrimesAbove (K := K) (L := L) P =>
      IdeleUnitSubgroup (NumberField.RingOfIntegers L) L R.1) Q (x Q)

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
theorem above_projection_ne
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q R : FinitePrimesAbove (K := K) (L := L) P)
    (hR : R ≠ Q)
    (x : PrimesAboveUnits (K := K) (L := L) P) :
    (primesAboveProjection
      (K := K) (L := L) P Q x).1 R = 1 :=
  (primesAboveProjection
    (K := K) (L := L) P Q x).2 R hR

set_option maxHeartbeats 1000000 in
-- Equivariance of the support projection expands both dependent place actions
-- and the transported stabilizer action.
set_option synthInstance.maxHeartbeats 300000 in
omit [FiniteDimensional K L] in
/-- The support projection commutes with the chosen-prime stabilizer
action. -/
theorem above_projection_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (sigma : primeAboveStabilizer (K := K) (L := L) P Q)
    (x : PrimesAboveUnits (K := K) (L := L) P) :
    primesAboveProjection
        (K := K) (L := L) P Q
        ((primesUnitsAction
          (K := K) (L := L) P).smul sigma.1 x) =
      (primesAboveAction
        (K := K) (L := L) P Q).smul sigma
          (primesAboveProjection
            (K := K) (L := L) P Q x) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  apply Subtype.ext
  funext R
  by_cases hR : R = Q
  · subst R
    rw [above_projection_self]
    apply Subtype.ext
    change Units.map
        (finitePlaceTransport (K := K) sigma.1 Q.1).toRingHom.toMonoidHom
          ((x (sigma.1⁻¹ • Q)).1) =
      Units.map
        (finitePlaceTransport (K := K) sigma.1 Q.1).toRingHom.toMonoidHom
          (((primesAboveProjection
            (K := K) (L := L) P Q x).1 (sigma.1⁻¹ • Q)).1)
    have hsigmaInvQ : sigma.1⁻¹ • Q = Q := sigma⁻¹ |>.2
    have hsource : x (sigma.1⁻¹ • Q) =
        (primesAboveProjection
          (K := K) (L := L) P Q x).1 (sigma.1⁻¹ • Q) := by
      exact hsigmaInvQ.symm ▸
        (above_projection_self
          (K := K) (L := L) P Q x).symm
    exact congrArg
      (Units.map
        (finitePlaceTransport (K := K) sigma.1 Q.1).toRingHom.toMonoidHom)
      (congrArg Subtype.val hsource)
  · exact ((primesAboveProjection
      (K := K) (L := L) P Q
        ((primesUnitsAction
          (K := K) (L := L) P).smul sigma.1 x)).2 R hR).trans
        (((primesAboveAction
          (K := K) (L := L) P Q).smul sigma
            (primesAboveProjection
              (K := K) (L := L) P Q x)).2 R hR).symm

set_option maxHeartbeats 1000000 in
-- Packaging support projection as an intertwiner requires a large dependent
-- function extensionality calculation.
set_option synthInstance.maxHeartbeats 300000 in
/-- Projection to the chosen supported factor is equivariant for the
stabilizer action. -/
noncomputable def primesAboveEvaluation
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    Rep.res
        (primeAboveStabilizer (K := K) (L := L) P Q).subtype
        (resizedPrimesRepresentation
          (K := K) (L := L) P) ⟶
      resizedSupportedRepresentation
        (K := K) (L := L) P Q := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  letI := aboveMulAction (K := K) (L := L) P
  letI := primesUnitsAction (K := K) (L := L) P
  letI := primesAboveAction
    (K := K) (L := L) P Q
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul
            (primesAboveProjection
              (K := K) (L := L) P Q x.toMul)
          map_add' := fun x y => congrArg Additive.ofMul
            ((primesAboveProjection
              (K := K) (L := L) P Q).map_mul x.toMul y.toMul)
          map_smul' := fun r x => map_zsmul
            (primesAboveProjection
              (K := K) (L := L) P Q).toAdditive r.down x }
      isIntertwining' := ?_ }
  intro sigma
  apply LinearMap.ext
  intro x
  exact congrArg Additive.ofMul
    (above_projection_smul
      (K := K) (L := L) P Q sigma x.toMul)

omit [FiniteDimensional K L] in
@[simp]
theorem above_evaluation_self
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (x : Rep.res
      (primeAboveStabilizer (K := K) (L := L) P Q).subtype
      (resizedPrimesRepresentation
        (K := K) (L := L) P)) :
    ((primesAboveEvaluation
      (K := K) (L := L) P Q) x).toMul.1 Q = x.toMul Q := by
  change (primesAboveProjection
    (K := K) (L := L) P Q x.toMul).1 Q = x.toMul Q
  exact above_projection_self
    (K := K) (L := L) P Q x.toMul

/-- The adjunction map from the product of upper local-unit factors to the
coinduced supported-factor representation. -/
noncomputable def aboveCoinducedSupported
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    resizedPrimesRepresentation
        (K := K) (L := L) P ⟶
      milneInducedModule
        (primeAboveStabilizer (K := K) (L := L) P Q)
        (resizedSupportedRepresentation
          (K := K) (L := L) P Q) :=
  Rep.resCoindToHom
    (primeAboveStabilizer (K := K) (L := L) P Q).subtype
    (resizedPrimesRepresentation
      (K := K) (L := L) P)
    (resizedSupportedRepresentation
      (K := K) (L := L) P Q)
    (primesAboveEvaluation (K := K) (L := L) P Q)

omit [FiniteDimensional K L] in
@[simp]
theorem above_coinduced_supported
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (x : resizedPrimesRepresentation
      (K := K) (L := L) P)
    (sigma : Gal(L/K)) :
    (((aboveCoinducedSupported
      (K := K) (L := L) P Q) x).1 sigma).toMul.1 Q =
        ((primesUnitsAction
          (K := K) (L := L) P).smul sigma x.toMul) Q := by
  change ((primesAboveEvaluation
    (K := K) (L := L) P Q)
      ((resizedPrimesRepresentation
        (K := K) (L := L) P).ρ sigma x)).toMul.1 Q = _
  rw [above_evaluation_self]
  rfl

/-- The restricted-Shapiro forward map is injective. -/
theorem coinduced_supported_injective
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    Function.Injective
      (aboveCoinducedSupported
        (K := K) (L := L) P Q) := by
  letI := aboveMulAction (K := K) (L := L) P
  letI : MulAction.IsPretransitive Gal(L/K)
      (FinitePrimesAbove (K := K) (L := L) P) :=
    primesAbovePretransitive (K := K) (L := L) P
  intro x y hxy
  apply Additive.toMul.injective
  funext R
  obtain ⟨sigma, hsigma⟩ := MulAction.exists_smul_eq Gal(L/K) Q R
  subst R
  apply Subtype.ext
  apply Units.ext
  apply (finitePlaceTransport (K := K) sigma⁻¹ Q.1).injective
  have heval := congrArg
    (fun f => ((((f.1 sigma⁻¹).toMul.1 Q).1 :
      (Q.1.adicCompletion L)ˣ) : Q.1.adicCompletion L)) hxy
  dsimp only at heval
  rw [above_coinduced_supported,
    above_coinduced_supported] at heval
  simpa only [primesUnitsAction, inv_inv] using heval

/-- A chosen element carrying an upper prime back to the distinguished
prime. -/
noncomputable def primeAboveReturn
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (R : FinitePrimesAbove (K := K) (L := L) P) : Gal(L/K) := by
  letI := aboveMulAction (K := K) (L := L) P
  letI : MulAction.IsPretransitive Gal(L/K)
      (FinitePrimesAbove (K := K) (L := L) P) :=
    primesAbovePretransitive (K := K) (L := L) P
  exact Classical.choose (MulAction.exists_smul_eq Gal(L/K) R Q)

@[simp]
theorem above_return_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (R : FinitePrimesAbove (K := K) (L := L) P) :
    (aboveMulAction (K := K) (L := L) P).smul
      (primeAboveReturn (K := K) (L := L) P Q R) R = Q := by
  letI := aboveMulAction (K := K) (L := L) P
  letI : MulAction.IsPretransitive Gal(L/K)
      (FinitePrimesAbove (K := K) (L := L) P) :=
    primesAbovePretransitive (K := K) (L := L) P
  exact Classical.choose_spec (MulAction.exists_smul_eq Gal(L/K) R Q)

/-- Milne's inverse construction for the product of local-unit factors. -/
noncomputable def coinducedSupportedUnits
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (f : milneInducedModule
      (primeAboveStabilizer (K := K) (L := L) P Q)
      (resizedSupportedRepresentation
        (K := K) (L := L) P Q)) :
    resizedPrimesRepresentation
      (K := K) (L := L) P := by
  letI := primesUnitsAction (K := K) (L := L) P
  exact Additive.ofMul (fun R =>
    let sigma := primeAboveReturn (K := K) (L := L) P Q R
    ((primesUnitsAction (K := K) (L := L) P).smul
      sigma⁻¹ (f.1 sigma).toMul.1) R)

set_option synthInstance.maxHeartbeats 300000 in
-- Verifying the restricted-Shapiro inverse resolves a deeply nested cochain
-- representation and stabilizer instance.
/-- Milne's inverse is a right inverse to the restricted-Shapiro forward
map. -/
theorem primes_above_coinduced
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (f : milneInducedModule
      (primeAboveStabilizer (K := K) (L := L) P Q)
      (resizedSupportedRepresentation
        (K := K) (L := L) P Q)) :
    aboveCoinducedSupported
        (K := K) (L := L) P Q
        (coinducedSupportedUnits
          (K := K) (L := L) P Q f) = f := by
  letI := aboveMulAction (K := K) (L := L) P
  letI := primesUnitsAction (K := K) (L := L) P
  letI := primesAboveAction
    (K := K) (L := L) P Q
  apply Subtype.ext
  funext tau
  apply Additive.toMul.injective
  apply Subtype.ext
  funext R
  by_cases hR : R = Q
  · subst R
    rw [above_coinduced_supported]
    let sigma := primeAboveReturn (K := K) (L := L) P Q (tau⁻¹ • Q)
    have hsigma : sigma • (tau⁻¹ • Q) = Q :=
      above_return_smul (K := K) (L := L) P Q (tau⁻¹ • Q)
    have htheta : tau * sigma⁻¹ ∈
        primeAboveStabilizer (K := K) (L := L) P Q := by
      have hinv := congrArg (fun R => sigma⁻¹ • R) hsigma
      have hsigmaInv : sigma⁻¹ • Q = tau⁻¹ • Q := by
        simpa using hinv.symm
      change (tau * sigma⁻¹) • Q = Q
      rw [mul_smul, hsigmaInv, smul_inv_smul]
    let theta : primeAboveStabilizer (K := K) (L := L) P Q :=
      ⟨tau * sigma⁻¹, htheta⟩
    change ((primesUnitsAction
      (K := K) (L := L) P).smul tau
        ((primesUnitsAction
          (K := K) (L := L) P).smul sigma⁻¹
            (f.1 sigma).toMul.1)) Q = (f.1 tau).toMul.1 Q
    have hmul :
        (primesUnitsAction
          (K := K) (L := L) P).smul (tau * sigma⁻¹)
            (f.1 sigma).toMul.1 =
          (primesUnitsAction
            (K := K) (L := L) P).smul tau
              ((primesUnitsAction
                (K := K) (L := L) P).smul sigma⁻¹
                  (f.1 sigma).toMul.1) :=
      (primesUnitsAction
        (K := K) (L := L) P).mul_smul tau sigma⁻¹ (f.1 sigma).toMul.1
    rw [← congrFun hmul Q]
    change ((primesAboveAction
      (K := K) (L := L) P Q).smul theta (f.1 sigma).toMul).1 Q =
        (f.1 tau).toMul.1 Q
    have hcov : f.1 sigma =
        (resizedSupportedRepresentation
          (K := K) (L := L) P Q).ρ theta⁻¹ (f.1 tau) := by
      simpa [theta] using f.2 theta⁻¹ tau
    rw [hcov]
    change ((primesAboveAction
      (K := K) (L := L) P Q).smul theta
        ((primesAboveAction
          (K := K) (L := L) P Q).smul theta⁻¹ (f.1 tau).toMul)).1 Q =
      (f.1 tau).toMul.1 Q
    calc
      _ = ((primesAboveAction
          (K := K) (L := L) P Q).smul (theta * theta⁻¹)
            (f.1 tau).toMul).1 Q :=
        congrFun (congrArg Subtype.val
          ((primesAboveAction
            (K := K) (L := L) P Q).mul_smul theta theta⁻¹
              (f.1 tau).toMul).symm) Q
      _ = (f.1 tau).toMul.1 Q := by
        rw [mul_inv_cancel]
        exact congrFun (congrArg Subtype.val
          ((primesAboveAction
            (K := K) (L := L) P Q).one_smul (f.1 tau).toMul)) Q
  · exact (((aboveCoinducedSupported
        (K := K) (L := L) P Q)
          (coinducedSupportedUnits
            (K := K) (L := L) P Q f)).1 tau).toMul.2 R hR |>.trans
      ((f.1 tau).toMul.2 R hR).symm

/-- The restricted-Shapiro forward map is surjective. -/
theorem coinduced_supported_surjective
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    Function.Surjective
      (aboveCoinducedSupported
        (K := K) (L := L) P Q) := by
  intro f
  exact ⟨coinducedSupportedUnits
    (K := K) (L := L) P Q f,
    primes_above_coinduced
      (K := K) (L := L) P Q f⟩

/-- The product of upper local-unit groups is coinduced from the supported
chosen-prime representation. -/
noncomputable def resizedInducedIso
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    resizedPrimesRepresentation
        (K := K) (L := L) P ≅
      milneInducedModule
        (primeAboveStabilizer (K := K) (L := L) P Q)
        (resizedSupportedRepresentation
          (K := K) (L := L) P Q) :=
  Rep.mkIso
    ((aboveCoinducedSupported
      (K := K) (L := L) P Q).hom.ofBijective
      ⟨coinduced_supported_injective
          (K := K) (L := L) P Q,
        coinduced_supported_surjective
          (K := K) (L := L) P Q⟩)

/-- Restricted Proposition VII.2.2 for the product of upper local-unit
groups, with the coefficient written as the actual chosen local-unit group. -/
noncomputable def aboveInducedIso
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    resizedPrimesRepresentation
        (K := K) (L := L) P ≅
      milneInducedModule
        (primeAboveStabilizer (K := K) (L := L) P Q)
        (resizedUnitsRepresentation
          (K := K) (L := L) P Q) :=
  resizedInducedIso
      (K := K) (L := L) P Q ≪≫
    (Rep.coindFunctor (ULift.{u} ℤ)
      (primeAboveStabilizer (K := K) (L := L) P Q).subtype).mapIso
        (resizedSupportedIso
          (K := K) (L := L) P Q)

/-- Degree-two restricted Shapiro for the product of local units above one
finite base prime. -/
noncomputable def resizedAboveUnits
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    H2 (resizedPrimesRepresentation
        (K := K) (L := L) P) ≃+
      H2 (resizedUnitsRepresentation
        (K := K) (L := L) P Q) :=
  (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
      (aboveInducedIso
        (K := K) (L := L) P Q)) ≪≫
    shapiro
      (primeAboveStabilizer (K := K) (L := L) P Q)
      (resizedUnitsRepresentation
        (K := K) (L := L) P Q) 2).toLinearEquiv.toAddEquiv

end

end Submission.CField.HNorm
