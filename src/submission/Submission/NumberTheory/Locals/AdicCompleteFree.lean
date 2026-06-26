import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Adic completeness of finite free modules

Finite free modules over an adically complete ring are complete for the
induced filtration.  In particular, a finite free formally unramified local
algebra over an adically complete local ring is Henselian.  This is the
completeness input used in the uniqueness part of Milne's Proposition 7.50.
-/

namespace Submission.NumberTheory.Milne

noncomputable section

open IsLocalRing

/-- A finite product of adically complete modules is adically complete. -/
theorem adic_complete_pi
    {R ι : Type*} [CommRing R] [Finite ι]
    (I : Ideal R) [IsAdicComplete I R] :
    IsAdicComplete I (ι → R) := by
  letI : Fintype ι := Fintype.ofFinite ι
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · constructor
    intro x hx
    funext i
    apply IsHausdorff.haus (I := I) (M := R) inferInstance
    intro n
    have hi := (hx n).map (LinearMap.proj i : (ι → R) →ₗ[R] R)
    simpa only [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)] using hi
  · constructor
    intro f hf
    have hfcoord (i : ι) {m n : ℕ} (hmn : m ≤ n) :
        f m i ≡ f n i [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      have hi := (hf hmn).map (LinearMap.proj i : (ι → R) →ₗ[R] R)
      simpa only [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)] using hi
    choose L hL using fun i ↦
      IsPrecomplete.prec (I := I) (M := R) inferInstance (hfcoord i)
    refine ⟨L, fun n ↦ ?_⟩
    rw [SModEq.sub_mem]
    rw [show f n - L = ∑ i, (f n i - L i) •
        (Pi.basisFun R ι) i by
      rw [← (Pi.basisFun R ι).sum_equivFun (f n - L)]
      apply Finset.sum_congr rfl
      intro i hi
      simp]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem_smul
    · have hLi := hL i n
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hLi
    · exact Submodule.mem_top

/-- Adic completeness is invariant under a linear equivalence. -/
theorem adic_complete_linear
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) [IsAdicComplete I N] :
    IsAdicComplete I M := by
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · constructor
    intro x hx
    apply e.injective
    rw [map_zero]
    apply IsHausdorff.haus (I := I) (M := N) inferInstance
    intro n
    have hn := (hx n).map e.toLinearMap
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective] at hn
    change e x ≡ e 0 [SMOD (I ^ n • ⊤ : Submodule R N)] at hn
    simpa only [map_zero] using hn
  · constructor
    intro f hf
    have hef {m n : ℕ} (hmn : m ≤ n) :
        e (f m) ≡ e (f n) [SMOD (I ^ m • ⊤ : Submodule R N)] := by
      have hn := (hf hmn).map e.toLinearMap
      simpa only [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr e.surjective] using hn
    obtain ⟨L, hL⟩ :=
      IsPrecomplete.prec (I := I) (M := N) inferInstance hef
    refine ⟨e.symm L, fun n ↦ ?_⟩
    have hn := (hL n).map e.symm.toLinearMap
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.symm.surjective] at hn
    change e.symm (e (f n)) ≡ e.symm L
      [SMOD (I ^ n • ⊤ : Submodule R M)] at hn
    rw [e.symm_apply_apply] at hn
    exact hn

/-- A finite free module over an adically complete ring is complete for the
induced adic filtration. -/
theorem adic_complete_free
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M]
    (I : Ideal R) [IsAdicComplete I R] :
    IsAdicComplete I M := by
  let b := Module.Free.chooseBasis R M
  letI : IsAdicComplete I
      (Module.Free.ChooseBasisIndex R M → R) :=
    adic_complete_pi I
  exact adic_complete_linear I b.equivFun

/-- A finite free formally unramified local algebra over an adically complete
local ring is Henselian. -/
theorem henselian_formally_unramified
    (A U : Type*) [CommRing A] [CommRing U] [Algebra A U]
    [IsLocalRing A] [IsLocalRing U] [IsLocalHom (algebraMap A U)]
    [Module.Finite A U] [Module.Free A U]
    [Algebra.FormallyUnramified A U]
    [IsAdicComplete (maximalIdeal A) A] :
    HenselianLocalRing U := by
  let I := maximalIdeal A
  letI : IsAdicComplete I U :=
    adic_complete_free I
  have hmax : maximalIdeal U = I.map (algebraMap A U) :=
    Algebra.FormallyUnramified.map_maximalIdeal.symm
  letI : IsAdicComplete (I.map (algebraMap A U)) U :=
    (IsAdicComplete.map_algebraMap_iff (I := I) (M := U)).mpr inferInstance
  letI : IsAdicComplete (maximalIdeal U) U := by
    rw [hmax]
    infer_instance
  exact
    { toIsLocalRing := inferInstance
      is_henselian := by
        intro p hp a ha hpa
        exact @HenselianRing.is_henselian U _ (maximalIdeal U)
          (IsAdicComplete.henselianRing U (maximalIdeal U))
          p hp a ha
          (hpa.map (Ideal.Quotient.mk (maximalIdeal U))) }

end

end Submission.NumberTheory.Milne
