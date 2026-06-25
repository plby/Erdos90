import Submission.ClassField.LocalClass.TotallyCarrySplitting
import Submission.ClassField.CrossedProducts.SplitNonemptyHom
import Submission.ClassField.CrossedProducts.EndRestrictScalars

namespace Submission.CField.LClass

noncomputable section

universe u

open ValuativeRel
open Submission.NumberTheory.Milne
open Submission.CField.BGroups
open Submission.CField.CProduca

private abbrev vInteger (F : Type u) [Field F] [ValuativeRel F] :=
  Valuation.integer (ValuativeRel.valuation F)

set_option maxHeartbeats 1000000 in
-- The centralizer carries scalar structures from both the base and subfield.
set_option synthInstance.maxHeartbeats 200000 in
/-- If a degree-`f` field embeds in a degree-`f*m` division algebra, then a
matching totally ramified degree-`m` extension of that field embeds in the
division algebra through the centralizer. -/
theorem totally_ramified_centralizer
    (K C L D : Type u)
    [Field K] [NontriviallyNormedField C] [Algebra K C]
    [FiniteDimensional K C]
    [IsUltrametricDist C] [ValuativeRel C]
    [IsNonarchimedeanLocalField C]
    [Valuation.Compatible (NormedField.valuation (K := C))]
    [NontriviallyNormedField L] [Algebra K L] [Algebra C L]
    [IsScalarTower K C L]
    [FiniteDimensional C L]
    [IsUltrametricDist L] [ValuativeRel L]
    [IsNonarchimedeanLocalField L]
    [Valuation.Compatible (NormedField.valuation (K := L))]
    [Algebra (vInteger C) (vInteger L)]
    [Module.Finite (vInteger C) (vInteger L)]
    [Module.IsTorsionFree (vInteger C) (vInteger L)]
    [IsScalarTower (vInteger C) C L]
    [IsScalarTower (vInteger C) (vInteger L) L]
    [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [Module.Finite K D]
    (f m : ℕ) [NeZero m]
    (hC : Module.finrank K C = f)
    (hD : Module.finrank K D = (f * m) ^ 2)
    (hL : Module.finrank C L = m)
    (i : C →ₐ[K] D)
    (htotal : TotallyRamified (vInteger C) (vInteger L)
      (IsLocalRing.maximalIdeal (vInteger C))) :
    Nonempty (L →ₐ[K] D) := by
  let E : Subalgebra K D := i.range
  let H : Subalgebra K D := Subalgebra.centralizer K (E : Set D)
  have hcomm : ∀ x y : E, x * y = y * x := by
    intro x y
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    apply Subtype.ext
    change (x : D) * (y : D) = (y : D) * (x : D)
    rw [← ha, ← hb, ← map_mul, mul_comm, map_mul]
  letI : Module.Finite K E :=
    Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : CommRing E :=
    { (inferInstance : Ring E) with mul_comm := hcomm }
  letI : Field E := fieldOfFiniteDimensional K E
  letI : IsSimpleRing E := inferInstance
  have hEH : E ≤ H := by
    intro x hx
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hcomm ⟨y, hy⟩ ⟨x, hx⟩)
  letI : Algebra E H :=
    (Subalgebra.inclusion hEH).toRingHom.toAlgebra' fun e h ↦ by
      apply Subtype.ext
      exact Iff.mp (Subalgebra.mem_centralizer_iff K) h.2 e e.2
  letI : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    change algebraMap K D x = algebraMap K D x
    rfl
  letI : Module.Finite K H :=
    Module.Finite.of_injective H.val.toLinearMap Subtype.val_injective
  letI : Module.Finite E H :=
    Module.Finite.of_restrictScalars_finite K E H
  letI : IsDomain H :=
    Function.Injective.isDomain H.val.toRingHom Subtype.val_injective
  letI : DivisionRing H := divisionRingOfFiniteDimensional E H
  let eCE : C ≃ₐ[K] E := AlgEquiv.ofInjectiveField i
  let algCH : Algebra C H :=
    ((algebraMap E H).comp eCE.toRingHom).toAlgebra' fun c h ↦ by
      exact Algebra.commutes (eCE c) h
  letI : Algebra C H := algCH
  letI : IsScalarTower K C H := IsScalarTower.of_algebraMap_eq' <| by
    ext x
    change algebraMap K D x = i (algebraMap K C x)
    exact (i.commutes x).symm
  letI : Module.Finite C H :=
    Module.Finite.of_restrictScalars_finite K C H
  letI : Algebra.IsCentral C H := by
    constructor
    intro z hz
    rw [Subalgebra.mem_center_iff] at hz
    have hzdouble : (z : D) ∈
        Subalgebra.centralizer K (H : Set D) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro c hc
      exact congrArg Subtype.val (hz ⟨c, hc⟩)
    have hzE : (z : D) ∈ E := by
      rw [centralizer_centralizer_eq K D E] at hzdouble
      exact hzdouble
    let c : C := eCE.symm ⟨z, hzE⟩
    rw [Algebra.mem_bot]
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change i c = z
    exact congrArg Subtype.val (eCE.apply_symm_apply ⟨z, hzE⟩)
  have hE : Module.finrank K E = f := by
    rw [← hC]
    exact eCE.toLinearEquiv.finrank_eq.symm
  have hKH : Module.finrank K H = f * Module.finrank C H := by
    rw [← hC]
    exact (Module.finrank_mul_finrank K C H).symm
  have hcentral := finrank_mul_centralizer K D E
  have hCH : Module.finrank C H = m ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by simpa [hC] using
      (Module.finrank_pos (R := K) (M := C))) (by simpa [hC] using
      (Module.finrank_pos (R := K) (M := C))))
    calc
      f * f * Module.finrank C H = f * (f * Module.finrank C H) := by ring
      _ = Module.finrank K E * Module.finrank K H := by rw [hE, hKH]
      _ = Module.finrank K D := hcentral
      _ = (f * m) ^ 2 := hD
      _ = f * f * (m ^ 2) := by ring
  have hsqrt : Nat.sqrt (Module.finrank C H) = m := by
    rw [hCH]
    simp
  have hsplit : ISBy C L H :=
    split_totally_ramified C L H
      (hL.trans hsqrt.symm) htotal
  have hHL : Module.finrank C H = m ^ 2 := hCH
  obtain ⟨iLH⟩ :=
    (split_nonempty_alg C L H m hHL hL).1 hsplit
  exact ⟨(H.val.restrictScalars K).comp (iLH.restrictScalars K)⟩

end

end Submission.CField.LClass
