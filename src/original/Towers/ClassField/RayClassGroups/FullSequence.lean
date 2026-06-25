import Towers.ClassField.RayClassGroups.ForbiddenIdeal
import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Milne, Class Field Theory, Lemma V.1.1 (full source sequence)

The tracked development proves exactness from `K^S` onward.  This file adds
the initial units map and identifies its range with the kernel of the
principal-ideal map, yielding the complete source sequence

`0 → Rˣ → K^S → I^S → Cl(R) → 0`.
-/

namespace Towers.CField.RCGroups

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The inclusion of integral units into `K^S`. -/
def unitsElementsPrime (S : Finset (HeightOneSpectrum R)) :
    Rˣ →* ElementsPrimeTo R K S where
  toFun u :=
    ⟨Units.map (algebraMap R K).toMonoidHom u, by
      change toPrincipalIdeal R K
          (Units.map (algebraMap R K).toMonoidHom u) ∈
        IdealsPrimeTo R K S
      have hprincipal :
          toPrincipalIdeal R K
            (Units.map (algebraMap R K).toMonoidHom u) = 1 := by
        apply Units.ext
        rw [coe_toPrincipalIdeal]
        change FractionalIdeal.spanSingleton R⁰
            (algebraMap R K (u : R)) = 1
        rw [← FractionalIdeal.spanSingleton_one]
        apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
        refine ⟨u⁻¹, ?_⟩
        rw [Units.smul_def, Algebra.smul_def, ← map_mul]
        simp
      rw [hprincipal]
      intro p hp
      exact FractionalIdeal.count_one K p⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Units.map (algebraMap R K).toMonoidHom)
  map_mul' u v := by
    apply Subtype.ext
    exact map_mul (Units.map (algebraMap R K).toMonoidHom) u v

/-- The units inclusion is injective. -/
theorem units_elements_injective
    (S : Finset (HeightOneSpectrum R)) :
    Function.Injective (unitsElementsPrime R K S) := by
  intro u v huv
  apply Units.ext
  apply (FaithfulSMul.algebraMap_injective R K)
  exact congrArg (fun x : ElementsPrimeTo R K S => ((x.1 : Kˣ) : K)) huv

/-- Exactness at `K^S`: an element generates the unit fractional ideal
exactly when it comes from an integral unit. -/
theorem range_units_elements
    (S : Finset (HeightOneSpectrum R)) :
    (unitsElementsPrime R K S).range =
      (principalIdealPrime R K S).ker := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change toPrincipalIdeal R K
      (Units.map (algebraMap R K).toMonoidHom u) = 1
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    change FractionalIdeal.spanSingleton R⁰
        (algebraMap R K (u : R)) = 1
    rw [← FractionalIdeal.spanSingleton_one]
    apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
    refine ⟨u⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def, ← map_mul]
    simp
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    have hprincipal : toPrincipalIdeal R K x.1 = 1 := by
      exact congrArg Subtype.val hx
    have hspan :
        FractionalIdeal.spanSingleton R⁰ (x.1 : K) = 1 := by
      simpa only [coe_toPrincipalIdeal, Units.val_one] using
        congrArg Units.val hprincipal
    have hxmem : (x.1 : K) ∈ (1 : FractionalIdeal R⁰ K) := by
      rw [← hspan]
      apply (FractionalIdeal.mem_spanSingleton R⁰).mpr
      exact ⟨1, by simp⟩
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hxmem
    have hprincipalInv : toPrincipalIdeal R K x.1⁻¹ = 1 := by
      rw [map_inv, hprincipal, inv_one]
    have hspanInv :
        FractionalIdeal.spanSingleton R⁰ ((x.1⁻¹ : Kˣ) : K) = 1 := by
      simpa only [coe_toPrincipalIdeal, Units.val_one] using
        congrArg Units.val hprincipalInv
    have hxinvMem : ((x.1⁻¹ : Kˣ) : K) ∈
        (1 : FractionalIdeal R⁰ K) := by
      rw [← hspanInv]
      apply (FractionalIdeal.mem_spanSingleton R⁰).mpr
      exact ⟨1, by simp⟩
    obtain ⟨s, hs⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hxinvMem
    have hrs : r * s = 1 := by
      apply (FaithfulSMul.algebraMap_injective R K)
      rw [map_mul, hr, hs]
      simp
    have hsr : s * r = 1 := by simpa [mul_comm] using hrs
    let u : Rˣ := ⟨r, s, hrs, hsr⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hr

/-- **Lemma V.1.1, literal full exactness statement.** -/
theorem source_exact (S : Finset (HeightOneSpectrum R)) :
    Function.Injective (unitsElementsPrime R K S) ∧
      (unitsElementsPrime R K S).range =
        (principalIdealPrime R K S).ker ∧
      (principalIdealPrime R K S).range =
        (idealClassPrime R K S).ker ∧
      Function.Surjective (idealClassPrime R K S) := by
  exact ⟨units_elements_injective R K S,
    range_units_elements R K S,
    range_principal_class R K S,
    ideal_class_surjective R K S⟩

end

end Towers.CField.RCGroups
