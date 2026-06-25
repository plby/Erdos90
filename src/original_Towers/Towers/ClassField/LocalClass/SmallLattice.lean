import Towers.ClassField.LocalClass.StableAcyclicLattice
import Towers.ClassField.LocalClass.LocalExponential

/-!
# Arbitrarily small regular normal-basis lattices

The lattice in Lemma III.2.3 may be multiplied by an arbitrarily small
nonzero base-field integer.  This puts the entire regular lattice inside any
prescribed neighborhood of zero while preserving openness, Galois stability,
and cohomological acyclicity.
-/

namespace Towers.CField.LClass

open CategoryTheory
open Towers.NumberTheory.Milne
open Towers.CField.LBrauer
open scoped NormedField Valued

noncomputable section

attribute [local instance] NormedField.toValued

universe u

/-- The small-lattice refinement of Lemma III.2.3. -/
theorem stable_acyclic_subset
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    let A := Valued.integer K
    ∀ (U : Set L), U ∈ nhds (0 : L) →
    ∃ (d : A) (hd : d ≠ 0),
      IsOpen (integralNormalSpan A K L d hd : Set L) ∧
      (integralNormalSpan A K L d hd : Set L) ⊆ U ∧
      (∀ g : Gal(L/K),
        integralNormalSpan A K L d hd ≤
          (integralNormalSpan A K L d hd).comap
            ((Rep.ofDistribMulAction A Gal(L/K) L).ρ g)) ∧
      Nonempty (Rep.leftRegular A Gal(L/K) ≅
        integralBasisRepresentation A K L d hd) ∧
      ∀ r : ℕ, 0 < r → Limits.IsZero (groupCohomology
        (integralBasisRepresentation A K L d hd) r) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) :=
    valuation_normed_algebra K L
  let A := Valued.integer K
  let B := Valued.integer L
  letI : IsIntegralClosure B A L := valued_integer_closure K L
  letI : Algebra.IsIntegral A B :=
    IsIntegralClosure.isIntegral_algebra A L
  letI : Algebra B L := B.subtype.toAlgebra
  letI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro U hU
  obtain ⟨d, hd, hspan, _hopen, _hstable, _hreg, _hzero⟩ :=
    stable_acyclic_lattice K L
  rw [Metric.mem_nhds_iff] at hU
  obtain ⟨ε, hε, hεU⟩ := hU
  obtain ⟨aK, haKpos, haKlt⟩ :=
    NormedField.exists_norm_lt K (lt_min hε zero_lt_one)
  let a : A := ⟨aK, by
    simpa only [NormedField.valuation_apply] using
      (haKlt.trans_le (min_le_right _ _)).le⟩
  have ha0 : a ≠ 0 := by
    intro ha
    have : aK = 0 := congrArg Subtype.val ha
    simp [this] at haKpos
  let d' : A := a * d
  have hd' : d' ≠ 0 := mul_ne_zero ha0 hd
  have hgen (g : Gal(L/K)) :
      ‖d' • IsGalois.normalBasis K L g‖ < ε := by
    have hdmem : d • IsGalois.normalBasis K L g ∈
        integralNormalSpan A K L d hd := by
      rw [← scaled_normal_basis A K L d hd g]
      exact Submodule.subset_span (Set.mem_range_self g)
    have hdle : ‖d • IsGalois.normalBasis K L g‖ ≤ 1 := by
      have hz := hspan hdmem
      change (NormedField.valuation (K := L))
        (d • IsGalois.normalBasis K L g) ≤ 1 at hz
      simpa [NormedField.valuation_apply] using hz
    have haMap : algebraMap A L a = algebraMap K L aK := rfl
    have hdMap : algebraMap A L d =
        algebraMap (Valued.integer K) L d := rfl
    calc
      ‖d' • IsGalois.normalBasis K L g‖ =
          ‖algebraMap K L aK *
            (d • IsGalois.normalBasis K L g)‖ := by
        simp [d', Algebra.smul_def, map_mul, haMap, hdMap, mul_assoc]
      _ = ‖aK‖ * ‖d • IsGalois.normalBasis K L g‖ := by
        rw [norm_mul, norm_algebraMap]
        simp only [norm_one, mul_one]
      _ ≤ ‖aK‖ * 1 := mul_le_mul_of_nonneg_left hdle (norm_nonneg _)
      _ < ε := (mul_one _).trans_lt (haKlt.trans_le (min_le_left _ _))
  have hsmall : (integralNormalSpan A K L d' hd' : Set L) ⊆
      Metric.ball 0 ε := by
    intro x hx
    have hxnorm : ‖x‖ < ε := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨g, rfl⟩ := hx
          simpa only [scaled_normal_basis] using hgen g
      | zero => simpa only [norm_zero] using hε
      | add x y _ _ hx hy =>
          exact (IsUltrametricDist.norm_add_le_max x y).trans_lt
            (max_lt hx hy)
      | smul r x _ hx =>
          rw [Algebra.smul_def, norm_mul]
          have hr : ‖algebraMap A L r‖ ≤ 1 := by
            change ‖algebraMap K L (r : K)‖ ≤ 1
            rw [norm_algebraMap]
            have hrK : ‖(r : K)‖ ≤ 1 := by
              have h := r.property
              change (NormedField.valuation (K := K)) (r : K) ≤ 1 at h
              simpa [NormedField.valuation_apply] using h
            simpa only [norm_one, mul_one] using hrK
          exact (mul_le_of_le_one_left (norm_nonneg x) hr).trans_lt hx
    simpa [Metric.mem_ball, dist_zero_right] using hxnorm
  have hint' (g : Gal(L/K)) :
      IsIntegral A (d' • IsGalois.normalBasis K L g) := by
    rw [show d' • IsGalois.normalBasis K L g =
        a • (d • IsGalois.normalBasis K L g) by
      simp [d', smul_smul]]
    rw [Algebra.smul_def]
    have hdmem : d • IsGalois.normalBasis K L g ∈
        integralNormalSpan A K L d hd := by
      rw [← scaled_normal_basis A K L d hd g]
      exact Submodule.subset_span (Set.mem_range_self g)
    let z : B := ⟨d • IsGalois.normalBasis K L g, hspan hdmem⟩
    have hz : IsIntegral A (z : L) :=
      (Algebra.IsIntegral.isIntegral z).algebraMap
    exact (isIntegral_algebraMap).mul (by simpa [z] using hz)
  have hopen' : IsOpen (integralNormalSpan A K L d' hd' : Set L) :=
    integral_basis_open A K L d' hd' hint' fun z ↦
      (Algebra.IsIntegral.isIntegral z).algebraMap
  refine ⟨d', hd', hopen', ?_, ?_, ?_, ?_⟩
  · exact fun x hx ↦ hεU (hsmall hx)
  · exact fun g ↦ integral_basis_stable A K L d' hd' g
  · exact ⟨representationIsoRegular A K L d' hd'⟩
  · intro r hr
    exact cohomology_iso_regular A
      (integralBasisRepresentation A K L d' hd')
      (representationIsoRegular A K L d' hd').symm r hr

end

end Towers.CField.LClass
