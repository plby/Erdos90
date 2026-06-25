import Towers.NumberTheory.Galois.CompositumDegreeCriterion

/-!
# Chapter V, Section 3, Theorem 3.25

Milne removes an arbitrary finite set `S` of primes before comparing the
primes which split completely.  The existing compositum criterion treats the
unfiltered splitting sets.  This file proves the literal finite-exception
version.  Its only analytic inputs are the exact Chebotarev statements from
Theorem 3.23 for the fields used in the proof.
-/

namespace Towers.CField.ARecip

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open scoped NumberField

noncomputable section

variable {K Ω : Type*} [Field K] [NumberField K]
  [Field Ω] [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω]

/-- The set `Spl_S(E/K)` in Milne: primes outside `S` which split completely
in `E`. -/
def splittingPrimesOutside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (E : IntermediateField K Ω) : Set (HeightOneSpectrum (𝓞 K)) :=
  splittingPrimes K E \ (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The difficult direction of Theorem 3.25 with Milne's arbitrary finite
exceptional set. -/
theorem splitting_outside_chebotarev
    (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hsubset : splittingPrimesOutside S M ⊆ splittingPrimesOutside S L)
    (hchebCompositum : ChebotarevDensityTheorem K ↑(L ⊔ M))
    (hchebM : ChebotarevDensityTheorem K M) :
    L ≤ M := by
  have hcompositum := splitting_sup_inter L M
  apply intermediate_density_diff
    L M (splittingPrimes K M) (splittingPrimes K ↑(L ⊔ M))
  · apply S.finite_toSet.subset
    intro p hp
    have hpM : p ∈ splittingPrimes K M := hp.1
    have hpNotL : p ∉ splittingPrimes K L := by
      intro hpL
      apply hp.2
      rw [hcompositum]
      exact ⟨hpL, hpM⟩
    by_contra hpS
    have hpOutsideM : p ∈ splittingPrimesOutside S M := ⟨hpM, hpS⟩
    exact hpNotL (hsubset hpOutsideM).1
  · rw [hcompositum]
    have hempty :
        (splittingPrimes K L ∩ splittingPrimes K M) \ splittingPrimes K M = ∅ := by
      ext p
      simp
    rw [hempty]
    exact Set.finite_empty
  · exact splitting_density_chebotarev K ↑(L ⊔ M)
      hchebCompositum
  · exact splitting_density_chebotarev K M hchebM

/-- **Theorem V.3.25**, in the source's literal `Spl_S` form. -/
theorem intermediate_outside_chebotarev
    (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hchebCompositum : ChebotarevDensityTheorem K ↑(L ⊔ M))
    (hchebM : ChebotarevDensityTheorem K M) :
    L ≤ M ↔ splittingPrimesOutside S M ⊆ splittingPrimesOutside S L := by
  constructor
  · intro hLM p hp
    refine ⟨?_, hp.2⟩
    exact ((intermediate_splitting_chebotarev
      L M hchebCompositum hchebM).1 hLM) hp.1
  · intro hsubset
    exact splitting_outside_chebotarev
      L M S hsubset hchebCompositum hchebM

/-- The equality clause of Theorem V.3.25. -/
theorem primes_outside_chebotarev
    (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hchebCompositum : ChebotarevDensityTheorem K ↑(L ⊔ M))
    (hchebL : ChebotarevDensityTheorem K L)
    (hchebM : ChebotarevDensityTheorem K M) :
    L = M ↔ splittingPrimesOutside S L = splittingPrimesOutside S M := by
  constructor
  · rintro rfl
    rfl
  · intro hsplit
    apply splitting_diff_chebotarev
      L M
    · apply S.finite_toSet.subset
      intro p hp
      by_contra hpS
      have hpOutsideL : p ∈ splittingPrimesOutside S L := ⟨hp.1, hpS⟩
      have hpOutsideM : p ∈ splittingPrimesOutside S M := by
        rw [← hsplit]
        exact hpOutsideL
      exact hp.2 hpOutsideM.1
    · apply S.finite_toSet.subset
      intro p hp
      by_contra hpS
      have hpOutsideM : p ∈ splittingPrimesOutside S M := ⟨hp.1, hpS⟩
      have hpOutsideL : p ∈ splittingPrimesOutside S L := by
        rw [hsplit]
        exact hpOutsideM
      exact hp.2 hpOutsideL.1
    · exact hchebCompositum
    · exact hchebL
    · exact hchebM

end

end Towers.CField.ARecip
