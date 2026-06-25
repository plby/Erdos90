import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Towers.NumberTheory.Density.PrimeIdealNatural
import Towers.NumberTheory.Galois.CompositumSplittingPrimes

/-!
# Splitting-density degree criteria in Milne 8.38--8.40

The Chebotarev argument in Theorem 8.38 reduces the desired field inclusion
to an equality of degrees.  This file records both that independent algebraic
step and the consequences of the relevant splitting-set density formulas,
with the analytic Chebotarev inputs stated explicitly as hypotheses.
-/

namespace Towers.NumberTheory.Milne

open IsDedekindDomain Module NumberField

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
  [FiniteDimensional K Ω]

/-- The final degree argument in Milne, Theorem 8.38: if adjoining `L` to
`M` does not increase the degree over `K`, then `L` was already contained in
`M`. -/
theorem intermediate_sup_right
    (L M : IntermediateField K Ω)
    (hdegree : finrank K ↑(L ⊔ M) = finrank K M) :
    L ≤ M := by
  have hM : M = L ⊔ M :=
    IntermediateField.eq_of_le_of_finrank_le
      le_sup_right hdegree.le
  simpa only [← hM] using
    (le_sup_left : L ≤ L ⊔ M)

/-- If the compositum has the degree of each factor, then the two factors are
equal.  This is the last algebraic step in the symmetric form used for
Corollary 8.39. -/
theorem intermediate_finrank_sup
    (L M : IntermediateField K Ω)
    (hleft : finrank K ↑(L ⊔ M) = finrank K L)
    (hright : finrank K ↑(L ⊔ M) = finrank K M) :
    L = M := by
  apply le_antisymm
  · exact intermediate_sup_right L M hright
  · apply intermediate_sup_right M L
    have hsup : M ⊔ L = L ⊔ M := sup_comm M L
    rw [hsup]
    exact hleft

section SplittingDensity

variable [NumberField K]

/-- The density step in Milne's Theorem 8.38.  If the primes splitting in the
compositum are exactly the intersection of the two splitting sets, inclusion
of the second splitting set in the first makes the compositum and the second
field have the same Chebotarev density, hence the same degree. -/
theorem intermediate_field_density
    (L M : IntermediateField K Ω)
    (splittingL splittingM splittingCompositum :
      Set (HeightOneSpectrum (𝓞 K)))
    (hcompositum : splittingCompositum = splittingL ∩ splittingM)
    (hsubset : splittingM ⊆ splittingL)
    (hcompositumDensity :
      PNDensit K splittingCompositum
        (1 / finrank K ↑(L ⊔ M) : ℝ))
    (hMDensity : PNDensit K splittingM
      (1 / finrank K M : ℝ)) :
    L ≤ M := by
  have hset : splittingCompositum = splittingM :=
    hcompositum.trans (Set.inter_eq_right.mpr hsubset)
  rw [hset] at hcompositumDensity
  have hrecip : (1 / finrank K ↑(L ⊔ M) : ℝ) = 1 / finrank K M :=
    tendsto_nhds_unique hcompositumDensity hMDensity
  have hdegree : finrank K ↑(L ⊔ M) = finrank K M := by
    have hleftNat : 0 < finrank K ↑(L ⊔ M) := Module.finrank_pos
    have hrightNat : 0 < finrank K M := Module.finrank_pos
    have hleft : (finrank K ↑(L ⊔ M) : ℝ) ≠ 0 := by
      exact_mod_cast hleftNat.ne'
    have hright : (finrank K M : ℝ) ≠ 0 := by
      exact_mod_cast hrightNat.ne'
    field_simp [hleft, hright] at hrecip
    exact_mod_cast hrecip.symm
  exact intermediate_sup_right L M hdegree

/-- Milne's Corollary 8.39, with the analytic Chebotarev inputs and the
compositum splitting identity made explicit: equal splitting-prime sets force
the two intermediate fields to be equal. -/
theorem intermediate_splitting_density
    (L M : IntermediateField K Ω)
    (splittingL splittingM splittingCompositum :
      Set (HeightOneSpectrum (𝓞 K)))
    (hcompositum : splittingCompositum = splittingL ∩ splittingM)
    (hsplitting : splittingL = splittingM)
    (hcompositumDensity :
      PNDensit K splittingCompositum
        (1 / finrank K ↑(L ⊔ M) : ℝ))
    (hLDensity : PNDensit K splittingL
      (1 / finrank K L : ℝ))
    (hMDensity : PNDensit K splittingM
      (1 / finrank K M : ℝ)) :
    L = M := by
  apply le_antisymm
  · apply intermediate_field_density
      L M splittingL splittingM splittingCompositum hcompositum
    · simpa only [hsplitting] using
        (Set.Subset.rfl : splittingM ⊆ splittingM)
    · exact hcompositumDensity
    · exact hMDensity
  · apply intermediate_field_density
      M L splittingM splittingL splittingCompositum
    · rw [hcompositum, Set.inter_comm]
    · simpa only [hsplitting] using
        (Set.Subset.rfl : splittingM ⊆ splittingM)
    · have hsup : M ⊔ L = L ⊔ M := sup_comm M L
      rw [hsup]
      exact hcompositumDensity
    · exact hLDensity

/-- A finite exceptional set is harmless in the degree argument: if the
compositum and `M` have splitting sets that differ by finitely many primes,
their Chebotarev densities still force `[LM : K] = [M : K]`. -/
theorem intermediate_density_diff
    (L M : IntermediateField K Ω)
    (splittingM splittingCompositum : Set (HeightOneSpectrum (𝓞 K)))
    (hMCompositum : (splittingM \ splittingCompositum).Finite)
    (hCompositumM : (splittingCompositum \ splittingM).Finite)
    (hcompositumDensity :
      PNDensit K splittingCompositum
        (1 / finrank K ↑(L ⊔ M) : ℝ))
    (hMDensity : PNDensit K splittingM
      (1 / finrank K M : ℝ)) :
    L ≤ M := by
  have hMDensity' : PNDensit K splittingCompositum
      (1 / finrank K M : ℝ) :=
    hMDensity.congr_fin_diff K hMCompositum hCompositumM
  apply intermediate_field_density
    L M splittingCompositum splittingCompositum splittingCompositum
  · exact (Set.inter_self splittingCompositum).symm
  · exact Set.Subset.rfl
  · exact hcompositumDensity
  · exact hMDensity'

/-- Milne, Remark 8.40(a), with Chebotarev's density formulas and the
compositum splitting identity explicit: two Galois intermediate fields whose
splitting-prime sets differ at only finitely many primes are equal. -/
theorem intermediate_splitting_diff
    (L M : IntermediateField K Ω)
    (splittingL splittingM splittingCompositum :
      Set (HeightOneSpectrum (𝓞 K)))
    (hcompositum : splittingCompositum = splittingL ∩ splittingM)
    (hLM : (splittingL \ splittingM).Finite)
    (hML : (splittingM \ splittingL).Finite)
    (hcompositumDensity :
      PNDensit K splittingCompositum
        (1 / finrank K ↑(L ⊔ M) : ℝ))
    (hLDensity : PNDensit K splittingL
      (1 / finrank K L : ℝ))
    (hMDensity : PNDensit K splittingM
      (1 / finrank K M : ℝ)) :
    L = M := by
  apply le_antisymm
  · apply intermediate_density_diff
      L M splittingM splittingCompositum
    · apply hML.subset
      intro p hp
      refine ⟨hp.1, ?_⟩
      intro hpL
      apply hp.2
      rw [hcompositum]
      exact ⟨hpL, hp.1⟩
    · rw [hcompositum]
      have hempty : (splittingL ∩ splittingM) \ splittingM = ∅ := by
        ext p
        constructor
        · intro hp
          exact (hp.2 hp.1.2).elim
        · intro hp
          change False at hp
          exact hp.elim
      rw [hempty]
      exact Set.finite_empty
    · exact hcompositumDensity
    · exact hMDensity
  · apply intermediate_density_diff
      M L splittingL splittingCompositum
    · apply hLM.subset
      intro p hp
      refine ⟨hp.1, ?_⟩
      intro hpM
      apply hp.2
      rw [hcompositum]
      exact ⟨hp.1, hpM⟩
    · rw [hcompositum]
      have hempty : (splittingL ∩ splittingM) \ splittingL = ∅ := by
        ext p
        constructor
        · intro hp
          exact (hp.2 hp.1.1).elim
        · intro hp
          change False at hp
          exact hp.elim
      rw [hempty]
      exact Set.finite_empty
    · have hsup : M ⊔ L = L ⊔ M := sup_comm M L
      rw [hsup]
      exact hcompositumDensity
    · exact hLDensity

/-- The degree argument only needs the exceptional primes in each direction
to have density zero. -/
theorem intermediate_field_diff
    (L M : IntermediateField K Ω)
    (splittingM splittingCompositum : Set (HeightOneSpectrum (𝓞 K)))
    (hMCompositum : PNDensit K
      (splittingM \ splittingCompositum) 0)
    (hCompositumM : PNDensit K
      (splittingCompositum \ splittingM) 0)
    (hcompositumDensity :
      PNDensit K splittingCompositum
        (1 / finrank K ↑(L ⊔ M) : ℝ))
    (hMDensity : PNDensit K splittingM
      (1 / finrank K M : ℝ)) :
    L ≤ M := by
  have hMDensity' : PNDensit K splittingCompositum
      (1 / finrank K M : ℝ) :=
    hMDensity.congr_density_zerodiff K hMCompositum hCompositumM
  apply intermediate_field_density
    L M splittingCompositum splittingCompositum splittingCompositum
  · exact (Set.inter_self splittingCompositum).symm
  · exact Set.Subset.rfl
  · exact hcompositumDensity
  · exact hMDensity'

/-- Milne, Remark 8.40(a): two Galois fields are equal when the two directed
differences of their splitting-prime sets have natural density zero. -/
theorem splitting_density_diff
    (L M : IntermediateField K Ω)
    (splittingL splittingM splittingCompositum :
      Set (HeightOneSpectrum (𝓞 K)))
    (hcompositum : splittingCompositum = splittingL ∩ splittingM)
    (hLM : PNDensit K (splittingL \ splittingM) 0)
    (hML : PNDensit K (splittingM \ splittingL) 0)
    (hcompositumDensity :
      PNDensit K splittingCompositum
        (1 / finrank K ↑(L ⊔ M) : ℝ))
    (hLDensity : PNDensit K splittingL
      (1 / finrank K L : ℝ))
    (hMDensity : PNDensit K splittingM
      (1 / finrank K M : ℝ)) :
    L = M := by
  have hempty : PNDensit K
      (∅ : Set (HeightOneSpectrum (𝓞 K))) 0 :=
    prime_natural_density K Set.finite_empty
  apply le_antisymm
  · apply intermediate_field_diff
      L M splittingM splittingCompositum
    · apply hML.mono_zero K
      intro p hp
      refine ⟨hp.1, ?_⟩
      intro hpL
      apply hp.2
      rw [hcompositum]
      exact ⟨hpL, hp.1⟩
    · convert hempty using 1
      rw [hcompositum]
      ext p
      simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_empty_iff_false]
      tauto
    · exact hcompositumDensity
    · exact hMDensity
  · apply intermediate_field_diff
      M L splittingL splittingCompositum
    · apply hLM.mono_zero K
      intro p hp
      refine ⟨hp.1, ?_⟩
      intro hpM
      apply hp.2
      rw [hcompositum]
      exact ⟨hp.1, hpM⟩
    · convert hempty using 1
      rw [hcompositum]
      ext p
      simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_empty_iff_false]
      tauto
    · have hsup : M ⊔ L = L ⊔ M := sup_comm M L
      rw [hsup]
      exact hcompositumDensity
    · exact hLDensity

end SplittingDensity

section ConcreteSplittingPrimes

variable [NumberField K] [NumberField Ω]

/-- Milne, Theorem 8.38: `L ⊆ M` exactly when every prime splitting
completely in `M` also splits completely in `L`. -/
theorem intermediate_splitting_chebotarev
    (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M]
    (hchebCompositum : ChebotarevDensityTheorem K ↑(L ⊔ M))
    (hchebM : ChebotarevDensityTheorem K M) :
    L ≤ M ↔ splittingPrimes K M ⊆ splittingPrimes K L := by
  have hcompositum := splitting_sup_inter L M
  constructor
  · intro hLM
    have hsup : L ⊔ M = M := sup_eq_right.mpr hLM
    have hcomp := hcompositum
    rw [hsup] at hcomp
    intro p hp
    exact ((Set.ext_iff.mp hcomp p).mp hp).1
  · intro hsubset
    apply intermediate_field_density
      L M (splittingPrimes K L) (splittingPrimes K M)
        (splittingPrimes K ↑(L ⊔ M)) hcompositum hsubset
    · exact splitting_density_chebotarev K ↑(L ⊔ M)
        hchebCompositum
    · exact splitting_density_chebotarev K M hchebM

/-- Milne, Remark 8.40(b), in existential form: there is a norm bound such
that checking the splitting implication below that bound forces `L ≤ M`.
The effective Chebotarev theorem gives a quantitative choice of this bound. -/
theorem splitting_test_chebotarev
    (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M]
    (hchebCompositum : ChebotarevDensityTheorem K ↑(L ⊔ M))
    (hchebM : ChebotarevDensityTheorem K M) :
    ∃ B : ℕ,
      (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal.absNorm ≤ B →
        p ∈ splittingPrimes K M → p ∈ splittingPrimes K L) →
      L ≤ M := by
  by_cases hLM : L ≤ M
  · exact ⟨0, fun _ ↦ hLM⟩
  · have hnotSubset : ¬splittingPrimes K M ⊆ splittingPrimes K L := by
      intro hsubset
      exact hLM ((intermediate_splitting_chebotarev
        L M hchebCompositum hchebM).2 hsubset)
    rw [Set.not_subset] at hnotSubset
    obtain ⟨p, hpM, hpL⟩ := hnotSubset
    refine ⟨p.asIdeal.absNorm, ?_⟩
    intro hcheck
    exact (hpL (hcheck p le_rfl hpM)).elim

/-- Milne, Corollary 8.39: two Galois intermediate fields are equal exactly
when their completely split prime sets are equal. -/
theorem intermediate_primes_chebotarev
    (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M]
    (hchebCompositum : ChebotarevDensityTheorem K ↑(L ⊔ M))
    (hchebL : ChebotarevDensityTheorem K L)
    (hchebM : ChebotarevDensityTheorem K M) :
    L = M ↔ splittingPrimes K L = splittingPrimes K M := by
  have hcompositum := splitting_sup_inter L M
  constructor
  · intro h
    subst M
    rfl
  · intro hsplitting
    apply intermediate_splitting_density
      L M (splittingPrimes K L) (splittingPrimes K M)
        (splittingPrimes K ↑(L ⊔ M)) hcompositum hsplitting
    · exact splitting_density_chebotarev K ↑(L ⊔ M)
        hchebCompositum
    · exact splitting_density_chebotarev K L hchebL
    · exact splitting_density_chebotarev K M hchebM

/-- Milne, Remark 8.40(a): finitely many exceptional splitting primes do
not affect the equality conclusion. -/
theorem splitting_diff_chebotarev
    (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M]
    (hLM : (splittingPrimes K L \ splittingPrimes K M).Finite)
    (hML : (splittingPrimes K M \ splittingPrimes K L).Finite)
    (hchebCompositum : ChebotarevDensityTheorem K ↑(L ⊔ M))
    (hchebL : ChebotarevDensityTheorem K L)
    (hchebM : ChebotarevDensityTheorem K M) :
    L = M := by
  have hcompositum := splitting_sup_inter L M
  apply intermediate_splitting_diff
    L M (splittingPrimes K L) (splittingPrimes K M)
      (splittingPrimes K ↑(L ⊔ M)) hcompositum hLM hML
  · exact splitting_density_chebotarev K ↑(L ⊔ M)
      hchebCompositum
  · exact splitting_density_chebotarev K L hchebL
  · exact splitting_density_chebotarev K M hchebM

/-- Milne, Remark 8.40(a), in its density-zero form for the actual sets of
primes splitting completely. -/
theorem intermediate_diff_chebotarev
    (L M : IntermediateField K Ω)
    [IsGalois K L] [IsGalois K M]
    (hLM : PNDensit K
      (splittingPrimes K L \ splittingPrimes K M) 0)
    (hML : PNDensit K
      (splittingPrimes K M \ splittingPrimes K L) 0)
    (hchebCompositum : ChebotarevDensityTheorem K ↑(L ⊔ M))
    (hchebL : ChebotarevDensityTheorem K L)
    (hchebM : ChebotarevDensityTheorem K M) :
    L = M := by
  have hcompositum := splitting_sup_inter L M
  apply splitting_density_diff
    L M (splittingPrimes K L) (splittingPrimes K M)
      (splittingPrimes K ↑(L ⊔ M)) hcompositum hLM hML
  · exact splitting_density_chebotarev K ↑(L ⊔ M)
      hchebCompositum
  · exact splitting_density_chebotarev K L hchebL
  · exact splitting_density_chebotarev K M hchebM

end ConcreteSplittingPrimes

end

end Towers.NumberTheory.Milne
