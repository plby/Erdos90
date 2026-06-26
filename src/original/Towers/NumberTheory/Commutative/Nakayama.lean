import Mathlib

namespace Towers.NumberTheory.Milne

/-- Lemma 1.9(a), Nakayama's lemma: if a proper ideal of a local ring generates a
finitely generated module, then that module is zero. -/
theorem nakayama_eq_bot
    {A M : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I ≠ ⊤)
    (h : I • (⊤ : Submodule A M) = ⊤) :
    (⊤ : Submodule A M) = ⊥ := by
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I
      (⊤ : Submodule A M) Module.Finite.fg_top
  · rw [h]
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hI

/-- Lemma 1.9(b), Nakayama's lemma: if `N + I M = M` for a proper ideal `I`, then
`N = M`. -/
theorem nakayama_eq_top
    {A M : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I ≠ ⊤) (N : Submodule A M)
    (h : N ⊔ I • (⊤ : Submodule A M) = ⊤) :
    N = ⊤ := by
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := I) (N := N) (N' := ⊤) Module.Finite.fg_top
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hI
  · rw [h]

namespace NCounte

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]

/-- A nonzero ideal of a domain generates the whole field after extension of scalars. -/
theorem ideal_smul_top [FaithfulSMul A K] (I : Ideal A) (hI : I ≠ ⊥) :
    I • (⊤ : Submodule A K) = ⊤ := by
  rw [Ideal.smul_top_eq_map]
  have hmap : I.map (algebraMap A K) = ⊤ := by
    rcases (I.map (algebraMap A K)).eq_bot_or_top with hbot | htop
    · exact (hI ((Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective A K)).mp hbot)).elim
    · exact htop
  simp [hmap]

/-- Milne, after Lemma 1.9: finite generation is essential in Nakayama's lemma.
If a local domain has nonzero maximal ideal, then its containing field `K`, viewed as an
`A`-module, is nonzero but satisfies `𝔪K = K`. -/
theorem maximal_smul_top [IsLocalRing A]
    [FaithfulSMul A K]
    (hmax : IsLocalRing.maximalIdeal A ≠ ⊥) :
    IsLocalRing.maximalIdeal A • (⊤ : Submodule A K) = ⊤ :=
  ideal_smul_top _ hmax

theorem module_ne_zero : (⊤ : Submodule A K) ≠ ⊥ := top_ne_bot

end NCounte

end Towers.NumberTheory.Milne
