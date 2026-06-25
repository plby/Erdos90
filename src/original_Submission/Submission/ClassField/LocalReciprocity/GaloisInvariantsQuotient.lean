import Submission.ClassField.LocalReciprocity.TateZeroQuotient

/-!
# Universe-polymorphic Galois invariants modulo norms

The elementary identification of fixed units modulo the action norm with
base-field units modulo the field norm does not use the Type-0 cohomology
category.  This file records it in arbitrary universes for completion fields.
-/

namespace Submission.CField.LRecip

open Submission.CField.LFTheory
open Submission.CField.LBrauer

noncomputable section

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

private def unitsInvariantsUniverse :
    Kˣ →* FMAct.invariants Gal(L/K) Lˣ where
  toFun x := ⟨Units.map (algebraMap K L) x, by
    intro sigma
    apply Units.ext
    simp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

private theorem invariants_universe_bijective :
    Function.Bijective (unitsInvariantsUniverse K L) := by
  constructor
  · intro x y hxy
    apply Units.ext
    apply (algebraMap K L).injective
    have h := congrArg
      (fun z : FMAct.invariants Gal(L/K) Lˣ ↦ ((z.1 : Lˣ) : L)) hxy
    simpa [unitsInvariantsUniverse] using h
  · intro x
    have hfixed : ∀ sigma : Gal(L/K), sigma (x.1 : L) = (x.1 : L) := by
      intro sigma
      exact congrArg Units.val (x.2 sigma)
    obtain ⟨a, ha⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed
        (F := K) (E := L) (x.1 : L)).2 hfixed
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, map_zero] at ha
      exact x.1.ne_zero ha.symm
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact ha

noncomputable def baseInvariantsUniverse :
    Kˣ ≃* FMAct.invariants Gal(L/K) Lˣ :=
  MulEquiv.ofBijective (unitsInvariantsUniverse K L)
    (invariants_universe_bijective K L)

private theorem base_invariants_universe (x : Lˣ) :
    baseInvariantsUniverse K L (normOnUnits K L x) =
      FMAct.norm Gal(L/K) Lˣ x := by
  apply Subtype.ext
  apply Units.ext
  simpa [baseInvariantsUniverse,
    unitsInvariantsUniverse, normOnUnits,
    FMAct.norm] using
      (Algebra.norm_eq_prod_automorphisms K (x : L))

private theorem galois_comap_universe :
    (FMAct.norm Gal(L/K) Lˣ).range ≤
      (normOnUnits K L).range.comap
        (baseInvariantsUniverse K L).symm.toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  exact (baseInvariantsUniverse K L).eq_symm_apply.mpr
    (base_invariants_universe K L x)

private theorem base_comap_universe :
    (normOnUnits K L).range ≤
      (FMAct.norm Gal(L/K) Lˣ).range.comap
        (baseInvariantsUniverse K L).toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x,
    (base_invariants_universe K L x).symm⟩

/-- Galois invariants modulo the action norm are the field-unit norm
quotient, in arbitrary universes. -/
noncomputable def galoisInvariantsUniverse :
    FMAct.invariantsModNorm Gal(L/K) Lˣ ≃*
      Kˣ ⧸ normSubgroup K L where
  toFun := QuotientGroup.map
    (FMAct.norm Gal(L/K) Lˣ).range
    (normOnUnits K L).range
    (baseInvariantsUniverse K L).symm.toMonoidHom
    (galois_comap_universe K L)
  invFun := QuotientGroup.map
    (normOnUnits K L).range
    (FMAct.norm Gal(L/K) Lˣ).range
    (baseInvariantsUniverse K L).toMonoidHom
    (base_comap_universe K L)
  left_inv q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (FMAct.norm Gal(L/K) Lˣ).range q
    apply congrArg (QuotientGroup.mk'
      (FMAct.norm Gal(L/K) Lˣ).range)
    exact (baseInvariantsUniverse K L).apply_symm_apply x
  right_inv q := by
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (normOnUnits K L).range q
    apply congrArg (QuotientGroup.mk' (normOnUnits K L).range)
    exact (baseInvariantsUniverse K L).symm_apply_apply x
  map_mul' x y := map_mul _ x y

@[simp]
theorem galois_invariants_universe
    (x : Kˣ) :
    galoisInvariantsUniverse K L
        (QuotientGroup.mk'
          (FMAct.norm Gal(L/K) Lˣ).range
          ⟨Units.map (algebraMap K L) x, by
            intro sigma
            apply Units.ext
            exact sigma.commutes x⟩) =
      QuotientGroup.mk' (normSubgroup K L) x := by
  change QuotientGroup.mk' (normSubgroup K L)
      ((baseInvariantsUniverse K L).symm
        (baseInvariantsUniverse K L x)) = _
  rw [MulEquiv.symm_apply_apply]

end

end Submission.CField.LRecip
