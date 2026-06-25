import Submission.NumberTheory.Locals.TeichmullerLifts
import Submission.ClassField.LocalBrauer.IntegralModelUniqueness

/-!
# Frobenius splitting in unramified integral models

This file supplies the completeness infrastructure needed to run the
Teichmuller-lift proof of Frobenius-polynomial splitting in an arbitrary
finite unramified DVR model.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open IsLocalRing ValuativeRel

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
    have hi := (hx n).map
      (LinearMap.proj i : (ι → R) →ₗ[R] R)
    simpa only [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)] using hi
  · constructor
    intro f hf
    have hfcoord (i : ι) {m n : ℕ} (hmn : m ≤ n) :
        f m i ≡ f n i [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      have hi := (hf hmn).map
        (LinearMap.proj i : (ι → R) →ₗ[R] R)
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

/-- A finite free module over an adically complete ring is adically
complete for the induced filtration. -/
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
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    HenselianLocalRing U := by
  let I := IsLocalRing.maximalIdeal A
  letI : IsAdicComplete I U :=
    adic_complete_free I
  have hmax : IsLocalRing.maximalIdeal U =
      I.map (algebraMap A U) := by
    exact Algebra.FormallyUnramified.map_maximalIdeal.symm
  letI : IsAdicComplete (I.map (algebraMap A U)) U :=
    (IsAdicComplete.map_algebraMap_iff (I := I) (M := U)).mpr
      inferInstance
  letI : IsAdicComplete (IsLocalRing.maximalIdeal U) U := by
    rw [hmax]
    infer_instance
  exact
    { toIsLocalRing := inferInstance
      is_henselian := by
        intro p hp a ha hpa
        exact @HenselianRing.is_henselian U _
          (IsLocalRing.maximalIdeal U)
          (IsAdicComplete.henselianRing U (IsLocalRing.maximalIdeal U))
          p hp a ha
          (hpa.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal U))) }

/-- Formal unramifiedness of a local algebra implies unramifiedness at its
maximal ideal: the latter is the same condition after localization. -/
theorem unramified_maximal_formally
    (A U : Type*) [CommRing A] [CommRing U] [Algebra A U]
    [IsLocalRing U] [Algebra.FormallyUnramified A U] :
    Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal U) :=
  Algebra.FormallyUnramified.comp A U _

/-- The topology on the valuation-relation integer ring of a local field is
the topology defined by powers of its maximal ideal. -/
theorem local_integer_adic
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K] :
    IsAdic (maximalIdeal 𝒪[K]) := by
  letI : IsDiscreteValuationRing 𝒪[K] :=
    discrete_valuation_ring K
  rw [isAdic_iff]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  constructor
  · intro n
    rw [hπ.maximalIdeal_pow_eq_setOf_le_v_coe_pow]
    have hopen := (valuation K).isOpen_closedBall
      (show (valuation K).restrict ((π : K) ^ n) ≠ 0 by
        simp [hπ.ne_zero])
    rw [← map_pow]
    simpa only [Set.preimage_setOf_eq, Valuation.restrict_le_iff] using
      hopen.preimage continuous_subtype_val
  · intro s hs
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    have ht' : t ∈ nhds (0 : K) := by simpa using ht
    rw [IsValuativeTopology.mem_nhds_zero_iff] at ht'
    obtain ⟨γ, hγ⟩ := ht'
    have hπval : valuation K (π : K) < 1 :=
      Valuation.integer.v_irreducible_lt_one hπ
    obtain ⟨n, hn⟩ : ∃ n : ℕ, valuation K (π : K) ^ n < γ :=
      exists_pow_lt₀ hπval γ
    refine ⟨n, ?_⟩
    intro y hy
    apply hts
    apply hγ
    have hy' : valuation K (y : K) ≤ valuation K (π : K) ^ n := by
      exact (Set.ext_iff.mp
        (hπ.maximalIdeal_pow_eq_setOf_le_v_coe_pow (valuation K) n) y).mp hy
    exact hy'.trans_lt hn

/-- The valuation-relation integer ring of a local field is complete for its
maximal-ideal-adic filtration. -/
theorem integer_adic_complete
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K] :
    IsAdicComplete (maximalIdeal 𝒪[K]) 𝒪[K] := by
  have hclosed : IsClosed (𝒪[K] : Set K) := Valued.isClosed_integer K
  letI : IsUniformAddGroup 𝒪[K] :=
    (𝒪[K]).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace 𝒪[K] := hclosed.completeSpace_coe
  exact (local_integer_adic K).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

/-- Consequently, the valuation-relation integer ring of a local field is
Henselian. -/
theorem integer_henselian_ring
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K] :
    HenselianLocalRing 𝒪[K] := by
  letI : IsAdicComplete (maximalIdeal 𝒪[K]) 𝒪[K] :=
    integer_adic_complete K
  exact
    { toIsLocalRing := inferInstance
      is_henselian := by
        intro p hp a ha hpa
        exact @HenselianRing.is_henselian 𝒪[K] _
          (maximalIdeal 𝒪[K])
          (IsAdicComplete.henselianRing 𝒪[K] (maximalIdeal 𝒪[K]))
          p hp a ha
          (hpa.map (Ideal.Quotient.mk (maximalIdeal 𝒪[K]))) }

end

end Submission.CField.LBrauer
