import Towers.NumberTheory.Ideals.PrincipalIdealCriteria

/-!
# Milne, Algebraic Number Theory, Remark 3.24

A Dedekind domain with finite ideal class group becomes a principal ideal domain after
inverting one nonzero element.
-/

namespace Towers.NumberTheory.Milne

open scoped nonZeroDivisors

/-- Remark 3.24: if a Dedekind domain has finite ideal class group, then some principal
localization of it is a principal ideal domain. -/
theorem away_principal_group
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Finite (ClassGroup R)] :
    ∃ b : R, b ≠ 0 ∧ IsPrincipalIdealRing (Localization.Away b) := by
  classical
  letI := Fintype.ofFinite (ClassGroup R)
  let rep : ClassGroup R → (Ideal R)⁰ := fun C =>
    Classical.choose (ClassGroup.mk0_surjective C)
  have hrep (C : ClassGroup R) : ClassGroup.mk0 (rep C) = C :=
    Classical.choose_spec (ClassGroup.mk0_surjective C)
  let J : Ideal R := ∏ C : ClassGroup R, (rep C : Ideal R)
  have hJ0 : J ≠ ⊥ := by
    dsimp only [J]
    exact Finset.prod_ne_zero_iff.mpr fun C _ =>
      mem_nonZeroDivisors_iff_ne_zero.mp (rep C).property
  rw [Submodule.ne_bot_iff] at hJ0
  obtain ⟨b, hbJ, hb0⟩ := hJ0
  refine ⟨b, hb0, ?_⟩
  have hbM : Submonoid.powers b ≤ nonZeroDivisors R := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hb0)
  letI : IsDomain (Localization.Away b) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away b) hbM
  letI : IsDedekindDomain (Localization.Away b) :=
    IsLocalization.isDedekindDomain R hbM (Localization.Away b)
  apply IsPrincipalIdealRing.of_prime_ne_bot
  intro P hP hP0
  let p : Ideal R := P.comap (algebraMap R (Localization.Away b))
  have hp : p.IsPrime := Ideal.comap_isPrime (algebraMap R (Localization.Away b)) P
  have hp0 : p ≠ ⊥ := ne_of_gt
    (IsLocalization.bot_lt_under_prime (Submonoid.powers b) (Localization.Away b) hbM P hP0)
  let p0 : (Ideal R)⁰ := ⟨p, mem_nonZeroDivisors_iff_ne_zero.mpr hp0⟩
  let C : ClassGroup R := ClassGroup.mk0 p0
  have hclasses : ClassGroup.mk0 p0 = ClassGroup.mk0 (rep C) := by
    rw [hrep]
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hclasses
  have hbRep : b ∈ (rep C : Ideal R) := by
    have hJle : J ≤ (rep C : Ideal R) := by
      dsimp only [J]
      exact Ideal.prod_le_inf.trans (Finset.inf_le (s := Finset.univ) (Finset.mem_univ C))
    exact hJle hbJ
  have hmapRep : Ideal.map (algebraMap R (Localization.Away b)) (rep C : Ideal R) = ⊤ := by
    apply IsLocalization.map_eq_top_of_not_subset (Submonoid.powers b)
      (Localization.Away b)
    rw [Set.not_subset_iff_exists_mem_notMem]
    exact ⟨b, hbRep, by simp⟩
  have hmapP : Ideal.map (algebraMap R (Localization.Away b)) p = P := by
    exact IsLocalization.map_under (Submonoid.powers b) (Localization.Away b) P
  have hmapped := congrArg (Ideal.map (algebraMap R (Localization.Away b))) hxy
  rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, hmapP, hmapRep, Ideal.mul_top] at hmapped
  have hxmap : algebraMap R (Localization.Away b) x ≠ 0 :=
    (map_ne_zero_iff (algebraMap R (Localization.Away b))
      (IsLocalization.injective (Localization.Away b) hbM)).mpr hx
  have hymap : algebraMap R (Localization.Away b) y ≠ 0 :=
    (map_ne_zero_iff (algebraMap R (Localization.Away b))
      (IsLocalization.injective (Localization.Away b) hbM)).mpr hy
  let X : (Ideal (Localization.Away b))⁰ :=
    ⟨Ideal.span {algebraMap R (Localization.Away b) x},
      mem_nonZeroDivisors_iff_ne_zero.mpr <| by
        intro hspan
        have : algebraMap R (Localization.Away b) x = 0 :=
          Ideal.span_singleton_eq_bot.mp (hspan.trans bot_eq_zero.symm)
        exact hxmap this⟩
  let Y : (Ideal (Localization.Away b))⁰ :=
    ⟨Ideal.span {algebraMap R (Localization.Away b) y},
      mem_nonZeroDivisors_iff_ne_zero.mpr <| by
        intro hspan
        have : algebraMap R (Localization.Away b) y = 0 :=
          Ideal.span_singleton_eq_bot.mp (hspan.trans bot_eq_zero.symm)
        exact hymap this⟩
  let P0 : (Ideal (Localization.Away b))⁰ :=
    ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hP0⟩
  have hsubmonoid : X * P0 = Y := by
    apply Subtype.ext
    simpa only [Set.image_singleton] using hmapped
  have hclassP : ClassGroup.mk0 P0 = 1 := by
    have hXprincipal : (X : Ideal (Localization.Away b)).IsPrincipal := by
      dsimp only [X]
      infer_instance
    have hYprincipal : (Y : Ideal (Localization.Away b)).IsPrincipal := by
      dsimp only [Y]
      infer_instance
    have hX : ClassGroup.mk0 X = 1 :=
      (ClassGroup.mk0_eq_one_iff X.property).mpr hXprincipal
    have hY : ClassGroup.mk0 Y = 1 :=
      (ClassGroup.mk0_eq_one_iff Y.property).mpr hYprincipal
    calc
      ClassGroup.mk0 P0 = 1 * ClassGroup.mk0 P0 := (one_mul _).symm
      _ = ClassGroup.mk0 X * ClassGroup.mk0 P0 := by rw [hX]
      _ = ClassGroup.mk0 (X * P0) := (ClassGroup.mk0.map_mul X P0).symm
      _ = ClassGroup.mk0 Y := congrArg ClassGroup.mk0 hsubmonoid
      _ = 1 := hY
  exact (ClassGroup.mk0_eq_one_iff P0.property).mp hclassP

end Towers.NumberTheory.Milne
