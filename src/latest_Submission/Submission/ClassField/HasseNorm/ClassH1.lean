import Submission.ClassField.CyclicIdeles.FiniteGalois
import Submission.ClassField.Shifting.ExceptionalTateTransport
import Submission.ClassField.HasseNorm.ULiftShapiro

/-!
# Resizing the idèle-class degree-one cohomology

Theorem VII.5.1 uses the integral idèle-class representation, whereas the
arbitrary-universe Hasse norm argument uses the same additive group and
Galois action over `ULift ℤ`.  This file proves the degree-minus-one and
degree-zero Tate comparisons and discharges the exact scalar-resizing bridge
isolated in Theorem VII.5.1.
-/

namespace Submission.CField.HNorm

open CategoryTheory CategoryTheory.Limits Representation
open IsDedekindDomain NumberField
open Submission.CField.Shifting
open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.CIdeles
open groupCohomology

noncomputable section

universe u

section ScalarComparison

variable {G : Type u} [Group G] [Fintype G]
  (A : Rep.{u, 0, u} ℤ G)

omit [Fintype G] in
private theorem ulift_integral_smul (r : ULift.{u} ℤ) (x : A) :
    (uliftIntegralRepresentation A).hV2.smul r x =
      A.hV2.smul r.down x := by
  change (AddCommGroup.toIntModule A).smul r.down x =
    A.hV2.smul r.down x
  exact congrArg (fun m : Module ℤ A => m.smul r.down x)
    (Subsingleton.elim _ _)

omit [Fintype G] in
private theorem int_u_coinvariants :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    (Coinvariants.ker (uliftIntegralRepresentation A).ρ).toAddSubgroup =
      (Coinvariants.ker A.ρ).toAddSubgroup := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  apply le_antisymm
  · intro x hx
    change x ∈ Coinvariants.ker (uliftIntegralRepresentation A).ρ at hx
    change x ∈ Coinvariants.ker A.ρ
    refine @Submodule.span_induction (ULift.{u} ℤ) A _ _
      (uliftIntegralRepresentation A).hV2 _
      (fun x _ ↦ x ∈ Coinvariants.ker A.ρ) ?_ ?_ ?_ ?_ _ hx
    · rintro x ⟨⟨g, y⟩, rfl⟩
      let y' : A := y
      change A.ρ g y' - y' ∈ Coinvariants.ker A.ρ
      exact Coinvariants.sub_mem_ker g y'
    · exact (Coinvariants.ker A.ρ).zero_mem
    · intro x y _ _ hx hy
      exact (Coinvariants.ker A.ρ).add_mem hx hy
    · intro r x _ hx
      have h := (Coinvariants.ker A.ρ).smul_mem r.down hx
      change (uliftIntegralRepresentation A).hV2.smul r x ∈
        Coinvariants.ker A.ρ
      rw [ulift_integral_smul A]
      exact h
  · intro x hx
    change x ∈ Coinvariants.ker A.ρ at hx
    change x ∈ Coinvariants.ker (uliftIntegralRepresentation A).ρ
    refine @Submodule.span_induction ℤ A _ _ A.hV2 _
      (fun x _ ↦ x ∈ Coinvariants.ker
        (uliftIntegralRepresentation A).ρ) ?_ ?_ ?_ ?_ _ hx
    · rintro x ⟨⟨g, y⟩, rfl⟩
      exact Coinvariants.sub_mem_ker g y
    · exact (Coinvariants.ker (uliftIntegralRepresentation A).ρ).zero_mem
    · intro x y _ _ hx hy
      exact (Coinvariants.ker
        (uliftIntegralRepresentation A).ρ).add_mem hx hy
    · intro r x _ hx
      have h := (Coinvariants.ker
        (uliftIntegralRepresentation A).ρ).smul_mem (ULift.up r) hx
      change A.hV2.smul r x ∈
        Coinvariants.ker (uliftIntegralRepresentation A).ρ
      change (uliftIntegralRepresentation A).hV2.smul (ULift.up r) x ∈
        Coinvariants.ker (uliftIntegralRepresentation A).ρ at h
      rw [ulift_integral_smul A] at h
      exact h

private noncomputable def intUCoinvariants :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    A.ρ.Coinvariants ≃+ (uliftIntegralRepresentation A).ρ.Coinvariants := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  exact QuotientAddGroup.quotientAddEquivOfEq
    (int_u_coinvariants A).symm

omit [Fintype G] in
@[simp]
private theorem int_coinvariants_mk (x : A) :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    intUCoinvariants A (Coinvariants.mk A.ρ x) =
      Coinvariants.mk (uliftIntegralRepresentation A).ρ x := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  rfl

private noncomputable def intUInvariants :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    A.ρ.invariants ≃+ (uliftIntegralRepresentation A).ρ.invariants := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  exact {
  toFun x := ⟨x.1, fun g => x.2 g⟩
  invFun x := ⟨x.1, fun g => x.2 g⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; rfl }

private theorem int_u_commutes :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    ∀ x : A.ρ.Coinvariants,
    intUInvariants A
        ((ICohomo.normCoinvariantsInvariants A).toAddMonoidHom x) =
      (Shifting.normCoinvariantsInvariants
        (uliftIntegralRepresentation A)).toAddMonoidHom
        (intUCoinvariants A x) := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  intro x
  induction x using Coinvariants.induction_on with
  | _ x =>
      rw [int_coinvariants_mk]
      apply Subtype.ext
      dsimp only [intUInvariants]
      change ((ICohomo.normCoinvariantsInvariants A).toAddMonoidHom
          (Coinvariants.mk A.ρ x)).1 =
        ((Shifting.normCoinvariantsInvariants
          (uliftIntegralRepresentation A)).toAddMonoidHom
            (Coinvariants.mk (uliftIntegralRepresentation A).ρ x)).1
      rw [show ((ICohomo.normCoinvariantsInvariants A).toAddMonoidHom
          (Coinvariants.mk A.ρ x)).1 = A.ρ.norm x by rfl]
      rw [show ((Shifting.normCoinvariantsInvariants
          (uliftIntegralRepresentation A)).toAddMonoidHom
            (Coinvariants.mk (uliftIntegralRepresentation A).ρ x)).1 =
          (uliftIntegralRepresentation A).ρ.norm x by rfl]
      simp only [Representation.norm, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro g _
      rfl

/-- Scalar resizing from `ℤ` to `ULift ℤ` preserves Tate degree minus one. -/
noncomputable def tateULift :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    tateNegOne A ≃+
      tateCohomologyOne (uliftIntegralRepresentation A) := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  exact {
  toFun x := ⟨intUCoinvariants A x.1, by
    have hx : (ICohomo.normCoinvariantsInvariants A).toAddMonoidHom
        x.1 = 0 := x.2
    change (Shifting.normCoinvariantsInvariants
      (uliftIntegralRepresentation A)).toAddMonoidHom
      (intUCoinvariants A x.1) = 0
    rw [← int_u_commutes A, hx, map_zero]⟩
  invFun x := ⟨(intUCoinvariants A).symm x.1, by
    change (ICohomo.normCoinvariantsInvariants A).toAddMonoidHom
      ((intUCoinvariants A).symm x.1) = 0
    apply (intUInvariants A).injective
    rw [int_u_commutes, AddEquiv.apply_symm_apply]
    exact x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact (intUCoinvariants A).left_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact (intUCoinvariants A).right_inv x.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add (intUCoinvariants A) x.1 y.1 }

private noncomputable def intULift :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    A.ρ.invariants →+
      tateCohomologyZero (uliftIntegralRepresentation A) := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  exact (QuotientAddGroup.mk'
      (Shifting.normCoinvariantsInvariants
        (uliftIntegralRepresentation A)).toAddMonoidHom.range).comp
    (intUInvariants A).toAddMonoidHom

private theorem int_u_surjective :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    Function.Surjective (intULift A) := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Shifting.normCoinvariantsInvariants
      (uliftIntegralRepresentation A)).toAddMonoidHom.range
      x
  exact ⟨(intUInvariants A).symm y, by
    change QuotientAddGroup.mk' _
      (intUInvariants A
        ((intUInvariants A).symm y)) =
      QuotientAddGroup.mk' _ y
    rw [AddEquiv.apply_symm_apply]⟩

private theorem int_u_ker :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    (ICohomo.normCoinvariantsInvariants A).toAddMonoidHom.range =
      (intULift A).ker := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply AddMonoidHom.mem_ker.mpr
    change QuotientAddGroup.mk' _
      (intUInvariants A
        ((ICohomo.normCoinvariantsInvariants A).toAddMonoidHom y)) = 0
    rw [int_u_commutes]
    exact (QuotientAddGroup.eq_zero_iff _).2
      ⟨intUCoinvariants A y, rfl⟩
  · intro hx
    have hx' := AddMonoidHom.mem_ker.mp hx
    change QuotientAddGroup.mk' _
      (intUInvariants A x) = 0 at hx'
    have hmem : intUInvariants A x ∈
        (Shifting.normCoinvariantsInvariants
          (uliftIntegralRepresentation A)).toAddMonoidHom.range :=
      (QuotientAddGroup.eq_zero_iff _).1 hx'
    obtain ⟨y, hy⟩ := hmem
    refine ⟨(intUCoinvariants A).symm y, ?_⟩
    apply (intUInvariants A).injective
    rw [int_u_commutes, AddEquiv.apply_symm_apply]
    exact hy

/-- Scalar resizing from `ℤ` to `ULift ℤ` preserves Tate degree zero. -/
noncomputable def tateIntLift :
    letI : Module ℤ A := A.hV2
    letI : Module (ULift.{u} ℤ) A :=
      (uliftIntegralRepresentation A).hV2
    tateZero A ≃+
      tateCohomologyZero (uliftIntegralRepresentation A) := by
  letI : Module ℤ A := A.hV2
  letI : Module (ULift.{u} ℤ) A :=
    (uliftIntegralRepresentation A).hV2
  exact (QuotientAddGroup.quotientAddEquivOfEq
      (int_u_ker A)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (intULift A)
      (int_u_surjective A))

end ScalarComparison

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

private abbrev ideleIntRepresentation : Rep ℤ Gal(L/K) :=
  classCokernelRepresentation (K := K) (L := L)

/-- The generic scalar-resized idèle-class representation agrees with the
one used in Theorem VII.5.1. -/
noncomputable def intUIso :
    uliftIntegralRepresentation (ideleIntRepresentation K L) ≅
      ideleCohomologyRepresentation K L := by
  exact Rep.mkIso
    { toLinearEquiv := LinearEquiv.refl (ULift.{u} ℤ)
        (ideleIntRepresentation K L)
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        rfl }

/-- The unconditional degree-minus-one half of the scalar-resizing bridge
isolated in Theorem VII.5.1. -/
noncomputable def tateScalarResizing :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    tateNegOne (ideleIntRepresentation K L) ≃+
      tateCohomologyOne (ideleCohomologyRepresentation K L) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  exact (tateULift
    (ideleIntRepresentation K L)).trans
      (tateNegIso
        (intUIso K L)).toAddEquiv

/-- The unconditional degree-zero half of the scalar-resizing bridge isolated
in Theorem VII.5.1. -/
noncomputable def scalarResizingAdd :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    tateZero (ideleIntRepresentation K L) ≃+
      tateCohomologyZero (ideleCohomologyRepresentation K L) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  exact (tateIntLift
    (ideleIntRepresentation K L)).trans
      (tateZeroIso
        (intUIso K L)).toAddEquiv

/-- The scalar-resizing bridge postulated in Theorem VII.5.1 follows from the
explicit degree-minus-one and degree-zero comparisons above. -/
theorem scalarResizingBridge :
    ScalarResizingBridge.{u} := by
  intro K L _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  exact ⟨⟨tateScalarResizing K L⟩,
    ⟨scalarResizingAdd K L⟩⟩

end

end Submission.CField.HNorm
