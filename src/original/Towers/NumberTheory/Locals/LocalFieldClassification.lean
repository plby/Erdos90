import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Algebra.CharP.Subring
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Towers.NumberTheory.Locals.CompleteDVRHenselian
import Towers.NumberTheory.Locals.CompletionUniversal
import Towers.NumberTheory.Locals.Ostrowski
import Towers.NumberTheory.Locals.TeichmullerLifts
import Towers.NumberTheory.Locals.UniformizerExpansion

/-!
# Classification ingredients for local fields

This file records the classification results used in Milne's Remark 7.49 that
are presently exposed by Mathlib.

* An archimedean local field contains a continuous copy of `ℝ`, is finite
  dimensional over it, and is isomorphic as a ring to `ℝ` or `ℂ`.
* A characteristic-zero nonarchimedean local field contains a continuous
  copy of `ℚ_[p]` for a unique prime `p` and is finite-dimensional over it.
  For a normed `ℚ_[p]`-extension, local compactness is equivalent to finite
  dimension.
* Laurent series over a field are complete for the `X`-adic valuation; their
  power-series integer model is a discrete valuation ring with residue field
  the coefficient field.  The Laurent-series field is locally compact exactly
  when that coefficient field is finite.

In positive characteristic, the coefficient-field section and unique
uniformizer expansions are assembled below into an isomorphism with a
Laurent-series field that is compatible with the valuation topology.
-/

namespace Towers.NumberTheory.Milne

noncomputable section

open Filter Valued Valued.integer
open IsLocalRing
open scoped LaurentSeries NNReal NormedField PowerSeries WithZero

/-- Milne, Remark 7.49(a), after constructing the canonical normed
`ℝ`-algebra structure: the field is isomorphic to `ℝ` or `ℂ`. -/
theorem archimedean_real_or
    (K : Type*) [NormedField K] [NormedAlgebra ℝ K] :
    Nonempty (K ≃ₐ[ℝ] ℝ) ∨ Nonempty (K ≃ₐ[ℝ] ℂ) :=
  NormedAlgebra.Real.nonempty_algEquiv_or K

/-- In a characteristic-zero nonarchimedean local field, the norm remains
nontrivial after restriction to `ℚ`.

Indeed, if every nonzero rational had norm one, the natural-number casts
would form an infinite one-separated family in the compact closed unit ball. -/
theorem local_restriction_nontrivial
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [CharZero K] :
    ((NormedField.toAbsoluteValue K).comp
      (algebraMap ℚ K).injective).IsNontrivial := by
  let v : AbsoluteValue ℚ ℝ :=
    (NormedField.toAbsoluteValue K).comp (algebraMap ℚ K).injective
  by_contra hv
  have hv_one : ∀ q : ℚ, q ≠ 0 → v q = 1 :=
    v.not_isNontrivial_iff.mp hv
  letI : ProperSpace K :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  let u : ℕ → K := fun n ↦ (n : K)
  have hu (n : ℕ) : u n ∈ Metric.closedBall (0 : K) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hn : n = 0
    · simp [u, hn]
    · have heq := hv_one (n : ℚ) (by exact_mod_cast hn)
      change ‖algebraMap ℚ K (n : ℚ)‖ = 1 at heq
      simpa [u] using heq.le
  obtain ⟨a, -, φ, hφ, hφa⟩ :=
    (isCompact_closedBall (0 : K) 1).tendsto_subseq hu
  have hcauchy : CauchySeq (u ∘ φ) := hφa.cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.mp hcauchy) 1 zero_lt_one
  have hdist : dist ((u ∘ φ) (N + 1)) ((u ∘ φ) N) < 1 :=
    hN (N + 1) (Nat.le_succ N)
  have hφne : φ (N + 1) ≠ φ N :=
    ne_of_gt (hφ (Nat.lt_succ_self N))
  have hq : (φ (N + 1) : ℚ) - φ N ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hφne)
  have heq := hv_one ((φ (N + 1) : ℚ) - φ N) hq
  change ‖algebraMap ℚ K ((φ (N + 1) : ℚ) - φ N)‖ = 1 at heq
  have hdist_eq : dist ((u ∘ φ) (N + 1)) ((u ∘ φ) N) = 1 := by
    rw [dist_eq_norm]
    simpa [u, map_sub] using heq
  exact (lt_irrefl (1 : ℝ)) (hdist_eq ▸ hdist)

/-- The restriction to `ℚ` of an archimedean local-field norm is equivalent
to the usual real absolute value. -/
theorem local_restriction_real
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [CharZero K]
    (harch : ¬ IsNonarchimedean (NormedField.toAbsoluteValue K)) :
    ((NormedField.toAbsoluteValue K).comp
      (algebraMap ℚ K).injective).IsEquiv Rat.AbsoluteValue.real := by
  let v : AbsoluteValue ℚ ℝ :=
    (NormedField.toAbsoluteValue K).comp (algebraMap ℚ K).injective
  apply ostrowski_archimedean v (local_restriction_nontrivial K)
  intro hv
  apply harch
  rw [nonarchimedean_nat_cast]
  have hv_nat := (nonarchimedean_nat_cast v).mp hv
  intro n
  have hn := hv_nat n
  change ‖algebraMap ℚ K (n : ℚ)‖ ≤ 1 at hn
  simpa using hn

/-- The Ostrowski step in Milne, Remark 7.49(b): the norm induced on `ℚ` by
a characteristic-zero nonarchimedean local field is equivalent to a `p`-adic
absolute value for a uniquely determined prime `p`. -/
theorem local_restriction_padic
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] [CharZero K] :
    ∃! p : ℕ, ∃ (_ : Fact p.Prime),
      ((NormedField.toAbsoluteValue K).comp (algebraMap ℚ K).injective).IsEquiv
        (Rat.AbsoluteValue.padic p) := by
  let v : AbsoluteValue ℚ ℝ :=
    (NormedField.toAbsoluteValue K).comp (algebraMap ℚ K).injective
  apply ostrowski_nonarchimedean v (local_restriction_nontrivial K)
  intro x y
  change ‖algebraMap ℚ K (x + y)‖ ≤
    max ‖algebraMap ℚ K x‖ ‖algebraMap ℚ K y‖
  simpa only [map_add] using
    (IsUltrametricDist.norm_add_le_max (algebraMap ℚ K x) (algebraMap ℚ K y))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def completionRingEquiv
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    (h : v.IsEquiv u) : v.Completion ≃+* u.Completion := by
  exact UniformSpace.Completion.mapRingEquiv
    (WithAbs.congr v u (.refl F))
    ((AbsoluteValue.isEquiv_iff_isHomeomorph v u).1 h).continuous
    ((AbsoluteValue.isEquiv_iff_isHomeomorph u v).1 h.symm).continuous

set_option backward.isDefEq.respectTransparency false in
private theorem continuous_ring_symm
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    (h : v.IsEquiv u) : Continuous (completionRingEquiv h).symm := by
  unfold completionRingEquiv
  change Continuous (UniformSpace.Completion.map
    (WithAbs.congr u v (.refl F)))
  exact UniformSpace.Completion.continuous_map

/-- The completion of `ℚ` for its usual real absolute value is `ℝ`. -/
noncomputable def rationalRealAbsolute :
    Rat.AbsoluteValue.real.Completion ≃+* ℝ :=
  (completion_unique_equiv Rat.AbsoluteValue.real
    (Rat.castHom ℝ)
    (fun q ↦ by
      change ‖(q : ℝ)‖ = Rat.AbsoluteValue.real q
      rw [Real.norm_eq_abs, Rat.AbsoluteValue.real_eq_abs, Rat.cast_abs])
    (by simpa using (Rat.denseRange_cast (𝕜 := ℝ)))).choose

theorem isometry_real_absolute :
    Isometry rationalRealAbsolute :=
  (completion_unique_equiv Rat.AbsoluteValue.real
    (Rat.castHom ℝ)
    (fun q ↦ by
      change ‖(q : ℝ)‖ = Rat.AbsoluteValue.real q
      rw [Real.norm_eq_abs, Rat.AbsoluteValue.real_eq_abs, Rat.cast_abs])
    (by simpa using (Rat.denseRange_cast (𝕜 := ℝ)))).choose_spec.1.1

noncomputable def rationalRealIsometry :
    Rat.AbsoluteValue.real.Completion ≃ᵢ ℝ :=
  { rationalRealAbsolute.toEquiv with
    isometry_toFun := isometry_real_absolute }

/-- An archimedean local field contains a continuous copy of `ℝ` and is
finite-dimensional for the algebra structure induced by that embedding. -/
theorem real_embedding_dimensional
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [CharZero K]
    (harch : ¬ IsNonarchimedean (NormedField.toAbsoluteValue K)) :
    ∃ f : ℝ →+* K, Function.Injective f ∧ Continuous f ∧
      letI : Algebra ℝ K := f.toAlgebra
      FiniteDimensional ℝ K := by
  let v : AbsoluteValue ℚ ℝ :=
    (NormedField.toAbsoluteValue K).comp (algebraMap ℚ K).injective
  have heq : v.IsEquiv Rat.AbsoluteValue.real :=
    local_restriction_real K harch
  letI : ProperSpace K :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  obtain ⟨F, hF, -⟩ := completion_universal v (algebraMap ℚ K) (fun q ↦ by rfl)
  let e : v.Completion ≃+* Rat.AbsoluteValue.real.Completion :=
    completionRingEquiv heq
  let f : ℝ →+* K :=
    F.comp (e.symm.toRingHom.comp
      rationalRealAbsolute.symm.toRingHom)
  have hfcont : Continuous f :=
    hF.1.continuous.comp
      ((continuous_ring_symm heq).comp
        rationalRealIsometry.symm.continuous)
  refine ⟨f, ?_, hfcont, ?_⟩
  · exact hF.1.injective.comp
      (e.symm.injective.comp rationalRealAbsolute.symm.injective)
  · letI : Algebra ℝ K := f.toAlgebra
    letI : ContinuousSMul ℝ K :=
      continuousSMul_of_algebraMap ℝ K (by
        change Continuous f
        exact hfcont)
    exact FiniteDimensional.of_locallyCompactSpace ℝ

/-- Milne, Remark 7.49(a): every characteristic-zero archimedean local field
is isomorphic as a ring to `ℝ` or `ℂ`.

The intermediate `ℝ`-algebra structure is induced by a continuous embedding;
no normalization of the original absolute value is required. -/
theorem archimedean_or_complex
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [CharZero K]
    (harch : ¬ IsNonarchimedean (NormedField.toAbsoluteValue K)) :
    Nonempty (K ≃+* ℝ) ∨ Nonempty (K ≃+* ℂ) := by
  obtain ⟨f, -, -, hfin⟩ := real_embedding_dimensional K harch
  letI : Algebra ℝ K := f.toAlgebra
  letI : FiniteDimensional ℝ K := hfin
  letI : Algebra.IsAlgebraic ℝ K := Algebra.IsAlgebraic.of_finite ℝ K
  rcases Real.nonempty_algEquiv_or K with hreal | hcomplex
  · exact Or.inl ⟨hreal.some.toRingEquiv⟩
  · exact Or.inr ⟨hcomplex.some.toRingEquiv⟩

/-- The completion of `ℚ` for its standard `p`-adic absolute value is the
field of `p`-adic numbers. -/
noncomputable def rationalPadicCompletion
    (p : ℕ) [Fact p.Prime] :
    (Rat.AbsoluteValue.padic p).Completion ≃+* ℚ_[p] :=
  (completion_unique_equiv (Rat.AbsoluteValue.padic p)
    (Rat.castHom ℚ_[p])
    (fun q ↦ by simp)
    (by simpa using Padic.denseRange_ratCast p)).choose

theorem isometry_rational_padic
    (p : ℕ) [Fact p.Prime] :
    Isometry (rationalPadicCompletion p) :=
  (completion_unique_equiv (Rat.AbsoluteValue.padic p)
    (Rat.castHom ℚ_[p])
    (fun q ↦ by simp)
    (by simpa using Padic.denseRange_ratCast p)).choose_spec.1.1

noncomputable def rationalPadicIsometry
    (p : ℕ) [Fact p.Prime] :
    (Rat.AbsoluteValue.padic p).Completion ≃ᵢ ℚ_[p] :=
  { (rationalPadicCompletion p).toEquiv with
    isometry_toFun := isometry_rational_padic p }

/-- Milne, Remark 7.49(b): every characteristic-zero nonarchimedean local
field contains a continuously embedded copy of `ℚ_[p]` for a prime `p`, and
is finite-dimensional for the algebra structure induced by that embedding.

The embedding need not be isometric for the original norm: Ostrowski only
identifies that norm with a positive power of the normalized `p`-adic norm. -/
theorem padic_embedding_dimensional
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] [CharZero K] :
    ∃ p : ℕ, ∃ _hp : Fact p.Prime, ∃ f : ℚ_[p] →+* K,
      Function.Injective f ∧ Continuous f ∧
        letI : Algebra ℚ_[p] K := f.toAlgebra
        FiniteDimensional ℚ_[p] K := by
  obtain ⟨p, ⟨hp, heq⟩, -⟩ := local_restriction_padic K
  letI : Fact p.Prime := hp
  let v : AbsoluteValue ℚ ℝ :=
    (NormedField.toAbsoluteValue K).comp (algebraMap ℚ K).injective
  letI : ProperSpace K :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  obtain ⟨F, hF, -⟩ := completion_universal v (algebraMap ℚ K) (fun q ↦ by rfl)
  let e : v.Completion ≃+* (Rat.AbsoluteValue.padic p).Completion :=
    completionRingEquiv heq
  let f : ℚ_[p] →+* K :=
    F.comp (e.symm.toRingHom.comp (rationalPadicCompletion p).symm.toRingHom)
  refine ⟨p, hp, f, ?_, ?_, ?_⟩
  · exact hF.1.injective.comp
      (e.symm.injective.comp (rationalPadicCompletion p).symm.injective)
  · exact hF.1.continuous.comp
      ((continuous_ring_symm heq).comp
        (rationalPadicIsometry p).symm.continuous)
  · letI : Algebra ℚ_[p] K := f.toAlgebra
    letI : ContinuousSMul ℚ_[p] K :=
      continuousSMul_of_algebraMap ℚ_[p] K (by
        change Continuous f
        exact hF.1.continuous.comp
          ((continuous_ring_symm heq).comp
            (rationalPadicIsometry p).symm.continuous))
    exact FiniteDimensional.of_locallyCompactSpace ℚ_[p]

/-- Milne, Remark 7.49(a,b), assembled in characteristic zero: a local field
is either `ℝ` or `ℂ` as a ring, or it contains a continuous copy of `ℚ_[p]`
and is finite-dimensional over that copy. -/
theorem charac_local_class
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K]
    [CharZero K] :
    (Nonempty (K ≃+* ℝ) ∨ Nonempty (K ≃+* ℂ)) ∨
      ∃ p : ℕ, ∃ _hp : Fact p.Prime, ∃ f : ℚ_[p] →+* K,
        Function.Injective f ∧ Continuous f ∧
          letI : Algebra ℚ_[p] K := f.toAlgebra
          FiniteDimensional ℚ_[p] K := by
  by_cases hnonarch :
      IsNonarchimedean (NormedField.toAbsoluteValue K)
  · right
    letI : IsUltrametricDist K :=
      IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (by
        simpa using hnonarch)
    exact padic_embedding_dimensional K
  · left
    exact archimedean_or_complex K hnonarch

/-- The easy direction of Milne, Remark 7.49(b): every finite normed
extension of `ℚ_[p]` is locally compact. -/
theorem extension_locally_compact
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] :
    LocallyCompactSpace L := by
  letI : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  infer_instance

/-- The finiteness step in Milne, Remark 7.49(b): a locally compact normed
extension of `ℚ_[p]` is finite-dimensional.  In particular, an infinite-degree
normed extension cannot be locally compact. -/
theorem dimensional_locally_compact
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L]
    [LocallyCompactSpace L] :
    FiniteDimensional ℚ_[p] L :=
  FiniteDimensional.of_locallyCompactSpace ℚ_[p]

/-- Milne, Remark 7.49(b), once the `ℚ_[p]`-algebra structure has been
constructed: a normed extension of `ℚ_[p]` is locally compact exactly when
it has finite degree. -/
theorem locally_compact_dimensional
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L] :
    LocallyCompactSpace L ↔ FiniteDimensional ℚ_[p] L := by
  constructor
  · intro h
    letI : LocallyCompactSpace L := h
    exact dimensional_locally_compact p L
  · intro h
    letI : FiniteDimensional ℚ_[p] L := h
    exact extension_locally_compact p L

/-- The coefficient-field construction needed in Milne, Remark 7.49(c).
For a complete equal-characteristic local ring with finite residue field,
Teichmuller lifting gives an injective ring section of the residue map. -/
theorem equal_characteristic_residue
    (A : Type*) [CommRing A] [HenselianLocalRing A]
    [Finite (ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP A p] :
    ∃ s : ResidueField A →+* A,
      (residue A).comp s = RingHom.id _ ∧ Function.Injective s := by
  letI := Fintype.ofFinite (ResidueField A)
  exact ⟨teichmullerLiftHom A p,
    residue_comp_teichmuller A p,
    teichmuller_lift_injective A p⟩

/-- The coefficient-field step of Milne, Remark 7.49(c), directly for a
complete equal-characteristic discretely valued field.  Completeness makes
the integer ring Henselian, so its finite residue field embeds back into it as
a section of the residue map. -/
theorem equal_characteristic_section
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsDiscreteValuationRing (Valued.integer K)]
    [Finite (ResidueField (Valued.integer K))]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ s : ResidueField (Valued.integer K) →+* Valued.integer K,
      (residue (Valued.integer K)).comp s = RingHom.id _ ∧
        Function.Injective s := by
  letI : HenselianLocalRing (Valued.integer K) :=
    valued_henselian_ring K
  exact equal_characteristic_residue (Valued.integer K) p

private theorem valued_integer_topology
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Valued.integer K)] :
    IsLinearTopology (Valued.integer K) (Valued.integer K) := by
  rw [isLinearTopology_iff_hasBasis_ideal]
  let h := valued_integer_adic K
  refine h.hasBasis_nhds_zero.to_hasBasis ?_ ?_
  · intro n _
    exact ⟨maximalIdeal (Valued.integer K) ^ n,
      h.hasBasis_nhds_zero.mem_iff.mpr ⟨n, trivial, subset_rfl⟩, subset_rfl⟩
  · intro I hI
    obtain ⟨n, -, hn⟩ := h.hasBasis_nhds_zero.mem_iff.mp hI
    exact ⟨n, trivial, hn⟩

private theorem section_representative_set
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    (s : ResidueField (Valued.integer K) →+* Valued.integer K)
    (hs : (residue (Valued.integer K)).comp s = RingHom.id _) :
    RRSet
      (Set.range fun a ↦ ((s a : Valued.integer K) : K)) := by
  let A := Valued.integer K
  let k := ResidueField A
  have hs_apply (a : k) : residue A (s a) = a :=
    DFunLike.congr_fun hs a
  constructor
  · rintro _ ⟨a, rfl⟩
    exact (s a).property
  · intro x hx
    let xA : A := ⟨x, hx⟩
    refine ⟨((s (residue A xA) : A) : K), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · have hz : xA - s (residue A xA) ∈ maximalIdeal A := by
        rw [← residue_eq_zero_iff]
        simp [hs_apply]
      have hv := (NormedField.valuation (K := K)).mem_maximalIdeal_iff.mp hz
      exact_mod_cast hv
    · intro y hy
      rcases hy with ⟨⟨a, rfl⟩, hclose⟩
      have hz : xA - s a ∈ maximalIdeal A := by
        have hv :
            NormedField.valuation (K := K) ((xA - s a : A) : K) < 1 := by
          exact_mod_cast hclose
        exact (NormedField.valuation (K := K)).mem_maximalIdeal_iff.mpr hv
      have hz0 := (residue_eq_zero_iff (xA - s a)).mpr hz
      have ha : a = residue A xA :=
        (sub_eq_zero.mp (by simpa [map_sub, hs_apply] using hz0)).symm
      exact congrArg (fun z ↦ ((s z : A) : K)) ha

/-- Evaluation at a norm uniformizer identifies formal power series over a
coefficient field with the valuation ring.  This is the integral core of
Milne's positive-characteristic classification. -/
noncomputable def seriesValuedInteger
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsDiscreteValuationRing (Valued.integer K)]
    (pi : K) (hpi : IsNormUniformizer pi)
    (s : ResidueField (Valued.integer K) →+* Valued.integer K)
    (hs : (residue (Valued.integer K)).comp s = RingHom.id _) :
    (ResidueField (Valued.integer K))⟦X⟧ ≃+* Valued.integer K := by
  let A := Valued.integer K
  let k := ResidueField A
  let piA : A := ⟨pi, hpi.2.1.le⟩
  letI : UniformSpace k := ⊥
  letI : DiscreteTopology k := ⟨rfl⟩
  letI : IsUniformAddGroup A := A.toAddSubgroup.isUniformAddGroup
  have hclosed : IsClosed (A : Set K) := by
    rw [show (A : Set K) = Metric.closedBall 0 1 by
      ext x
      simp [A, Valued.integer.mem_iff]]
    exact Metric.isClosed_closedBall
  letI : CompleteSpace A := hclosed.completeSpace_coe
  letI : IsLinearTopology A A := valued_integer_topology K
  have hspi : PowerSeries.HasEval piA := by
    rw [PowerSeries.hasEval_def, IsTopologicallyNilpotent, tendsto_subtype_rng]
    simpa [piA] using
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpi.2.1
  have hsc : Continuous s := continuous_of_discreteTopology
  let f : k⟦X⟧ →+* A := PowerSeries.eval₂Hom hsc hspi
  have hsum (F : k⟦X⟧) :
      HasSum (fun n ↦ ((s (PowerSeries.coeff n F) : A) : K) * pi ^ n)
        ((f F : A) : K) := by
    have h := PowerSeries.hasSum_eval₂ hsc hspi F
    rw [← PowerSeries.coe_eval₂Hom hsc hspi] at h
    have hm := h.map A.subtype continuous_subtype_val
    simpa [Function.comp_def, f, piA] using hm
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro F G hFG
    apply PowerSeries.ext
    have hS := section_representative_set K s hs
    have huniq :=
      unique_uniformizer_expansion hpi hS ((f F : A) : K) (f F).property
    have hcoeff :
        (fun n ↦ ((s (PowerSeries.coeff n F) : A) : K)) =
          fun n ↦ ((s (PowerSeries.coeff n G) : A) : K) := by
      apply huniq.unique
      · exact ⟨fun n ↦ ⟨PowerSeries.coeff n F, rfl⟩, hsum F⟩
      · refine ⟨fun n ↦ ⟨PowerSeries.coeff n G, rfl⟩, ?_⟩
        simpa [hFG] using hsum G
    intro n
    apply s.injective
    exact Subtype.ext (congrFun hcoeff n)
  · intro x
    have hS := section_representative_set K s hs
    obtain ⟨a, ha, -⟩ :=
      unique_uniformizer_expansion hpi hS (x : K) x.property
    choose c hc using fun n ↦ ha.1 n
    let F : k⟦X⟧ := PowerSeries.mk c
    refine ⟨F, Subtype.ext ?_⟩
    have hterms :
        (fun n ↦ ((s (PowerSeries.coeff n F) : A) : K) * pi ^ n) =
          fun n ↦ a n * pi ^ n := by
      funext n
      rw [show PowerSeries.coeff n F = c n by simp [F]]
      exact congrArg (· * pi ^ n) (hc n)
    exact tendsto_nhds_unique (hsum F).tendsto_sum_nat
      (hterms.symm ▸ ha.2.tendsto_sum_nat)

/-- A coefficient-field section and a norm uniformizer identify the field
with Laurent series over its residue field. -/
noncomputable def laurentResidueSection
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsDiscreteValuationRing (Valued.integer K)]
    (pi : K) (hpi : IsNormUniformizer pi)
    (s : ResidueField (Valued.integer K) →+* Valued.integer K)
    (hs : (residue (Valued.integer K)).comp s = RingHom.id _) :
    LaurentSeries (ResidueField (Valued.integer K)) ≃+* K :=
  IsFractionRing.ringEquivOfRingEquiv
    (seriesValuedInteger K pi hpi s hs)

/-- The Laurent-series equivalence carries the `X`-adic valuation ring
exactly onto the norm valuation ring of `K`. -/
theorem laurent_section_val
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsDiscreteValuationRing (Valued.integer K)]
    (pi : K) (hpi : IsNormUniformizer pi)
    (s : ResidueField (Valued.integer K) →+* Valued.integer K)
    (hs : (residue (Valued.integer K)).comp s = RingHom.id _)
    (f : LaurentSeries (ResidueField (Valued.integer K))) :
    Valued.v f ≤ (1 : ℤᵐ⁰) ↔
      ‖laurentResidueSection K pi hpi s hs f‖ ≤ 1 := by
  let A := (ResidueField (Valued.integer K))⟦X⟧
  let B := Valued.integer K
  let h : A ≃+* B := seriesValuedInteger K pi hpi s hs
  let e : LaurentSeries (ResidueField (Valued.integer K)) ≃+* K :=
    laurentResidueSection K pi hpi s hs
  constructor
  · rw [LaurentSeries.val_le_one_iff_eq_coe]
    rintro ⟨F, rfl⟩
    have he : e (F : LaurentSeries (ResidueField (Valued.integer K))) =
        ((h F : B) : K) := by
      simpa [e, h] using
        (IsFractionRing.ringEquivOfRingEquiv_algebraMap h F)
    rw [he]
    exact (h F).property
  · intro hf
    rw [LaurentSeries.val_le_one_iff_eq_coe]
    let y : B := ⟨e f, hf⟩
    refine ⟨h.symm y, ?_⟩
    apply e.injective
    have he : e ((h.symm y : A) :
        LaurentSeries (ResidueField (Valued.integer K))) =
        ((h (h.symm y) : B) : K) := by
      simpa [e, h] using
        (IsFractionRing.ringEquivOfRingEquiv_algebraMap h (h.symm y))
    rw [he]
    simp [y]

/-- The `X`-adic valuation is equivalent to the pullback of the norm
valuation along the Laurent-series equivalence. -/
theorem laurent_section_valuation
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsDiscreteValuationRing (Valued.integer K)]
    (pi : K) (hpi : IsNormUniformizer pi)
    (s : ResidueField (Valued.integer K) →+* Valued.integer K)
    (hs : (residue (Valued.integer K)).comp s = RingHom.id _) :
    (Valued.v : Valuation
      (LaurentSeries (ResidueField (Valued.integer K))) ℤᵐ⁰).IsEquiv
      ((NormedField.valuation (K := K)).comap
        (laurentResidueSection K pi hpi s hs).toRingHom) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro f
  change Valued.v f ≤ (1 : ℤᵐ⁰) ↔
    ‖laurentResidueSection K pi hpi s hs f‖₊ ≤ 1
  exact_mod_cast
    laurent_section_val K pi hpi s hs f

private theorem uniform_continuous_valuation
    {F L Γ₀ Γ₀' : Type*} [Field F] [Field L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₀']
    [Valued F Γ₀] [Valued L Γ₀']
    (e : F ≃+* L)
    (h : (Valued.v : Valuation F Γ₀).IsEquiv
      ((Valued.v : Valuation L Γ₀').comap e.toRingHom)) :
    UniformContinuous e := by
  refine uniformContinuous_of_continuousAt_zero e.toRingHom ?_
  rw [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero F Γ₀).tendsto_iff
    (Valued.hasBasis_nhds_zero L Γ₀')]
  intro γ _
  obtain ⟨r, hr⟩ :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (Valued.v : Valuation L Γ₀') γ
  have hr₀ : r ≠ 0 := by
    intro hrz
    subst r
    apply Units.ne_zero γ
    rw [← hr]
    simp
  let δ : (MonoidWithZeroHom.ValueGroup₀
      (Valued.v : Valuation F Γ₀))ˣ :=
    Units.mk0 ((Valued.v : Valuation F Γ₀).restrict (e.symm r)) (by
      exact (Valued.v : Valuation F Γ₀).restrict.ne_zero_iff.mpr (by
        simp [hr₀]))
  refine ⟨δ, trivial, ?_⟩
  intro x hx
  simp only [Set.mem_setOf_eq, δ, Units.val_mk0] at hx ⊢
  have hx' :
      (Valued.v : Valuation F Γ₀) x <
        (Valued.v : Valuation F Γ₀) (e.symm r) :=
    (Valued.v : Valuation F Γ₀).restrict_lt_iff.mp hx
  have hw :
      ((Valued.v : Valuation L Γ₀').comap e.toRingHom) x <
        ((Valued.v : Valuation L Γ₀').comap e.toRingHom) (e.symm r) :=
    (h.lt_iff_lt (x := x) (y := e.symm r)).mp hx'
  have hw' :
      (Valued.v : Valuation L Γ₀') (e x) <
        (Valued.v : Valuation L Γ₀') r := by
    simpa using hw
  rw [← hr]
  change (Valued.v : Valuation L Γ₀').restrict (e x) <
    (Valued.v : Valuation L Γ₀').restrict r
  exact (Valued.v : Valuation L Γ₀').restrict_lt_iff.mpr hw'

theorem continuous_laurent_section
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsDiscreteValuationRing (Valued.integer K)]
    (pi : K) (hpi : IsNormUniformizer pi)
    (s : ResidueField (Valued.integer K) →+* Valued.integer K)
    (hs : (residue (Valued.integer K)).comp s = RingHom.id _) :
    UniformContinuous (laurentResidueSection K pi hpi s hs) := by
  apply uniform_continuous_valuation
  simpa only [NormedField.v_eq_valuation] using
    laurent_section_valuation K pi hpi s hs

theorem uniform_laurent_section
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsDiscreteValuationRing (Valued.integer K)]
    (pi : K) (hpi : IsNormUniformizer pi)
    (s : ResidueField (Valued.integer K) →+* Valued.integer K)
    (hs : (residue (Valued.integer K)).comp s = RingHom.id _) :
    UniformContinuous (laurentResidueSection K pi hpi s hs).symm := by
  let e := laurentResidueSection K pi hpi s hs
  have h :=
    laurent_section_valuation K pi hpi s hs
  have hinv :
      (NormedField.valuation (K := K)).IsEquiv
        ((Valued.v : Valuation
          (LaurentSeries (ResidueField (Valued.integer K))) ℤᵐ⁰).comap
            e.symm.toRingHom) := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    have hx := h.le_one_iff_le_one (x := e.symm x)
    simpa [e] using hx.symm
  apply uniform_continuous_valuation
  simpa only [NormedField.v_eq_valuation] using hinv

/-- The Laurent-series ring equivalence is an equivalence of uniform spaces
for the `X`-adic uniformity and the norm uniformity on `K`. -/
noncomputable def laurentUniformSection
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsDiscreteValuationRing (Valued.integer K)]
    (pi : K) (hpi : IsNormUniformizer pi)
    (s : ResidueField (Valued.integer K) →+* Valued.integer K)
    (hs : (residue (Valued.integer K)).comp s = RingHom.id _) :
    LaurentSeries (ResidueField (Valued.integer K)) ≃ᵤ K :=
  { (laurentResidueSection K pi hpi s hs).toEquiv with
    uniformContinuous_toFun :=
      continuous_laurent_section K pi hpi s hs
    uniformContinuous_invFun :=
      uniform_laurent_section K pi hpi s hs }

/-- Every complete discretely valued nonarchimedean field admits a norm
uniformizer. -/
theorem exists_is_uniformizer
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Valued.integer K)] :
    ∃ pi : K, IsNormUniformizer pi := by
  let A := Valued.integer K
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine ⟨(pi : K), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact Subtype.coe_ne_coe.mpr hpi.ne_zero
  · simpa using Valued.integer.norm_irreducible_lt_one hpi
  · intro x hx
    let xA : A := ⟨x, hx.le⟩
    have hxmem : xA ∈ maximalIdeal A := by
      apply (NormedField.valuation (K := K)).mem_maximalIdeal_iff.mpr
      exact_mod_cast hx
    rw [hpi.maximalIdeal_eq, Ideal.mem_span_singleton'] at hxmem
    obtain ⟨y, hy⟩ := hxmem
    have hyK : (y : K) * (pi : K) = x := congrArg Subtype.val hy
    rw [← hyK, mul_div_cancel_right₀ _ (Subtype.coe_ne_coe.mpr hpi.ne_zero)]
    exact y.property

/-- Milne, Remark 7.49(c): a complete equal-characteristic discretely valued
field with finite residue field is isomorphic to the Laurent-series field over
that residue field. -/
theorem equal_characteristic_laurent
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsDiscreteValuationRing (Valued.integer K)]
    [Finite (ResidueField (Valued.integer K))]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nonempty (K ≃+* LaurentSeries (ResidueField (Valued.integer K))) := by
  obtain ⟨pi, hpi⟩ := exists_is_uniformizer K
  obtain ⟨s, hs, -⟩ :=
    equal_characteristic_section K p
  exact ⟨(laurentResidueSection K pi hpi s hs).symm⟩

/-- Topological form of Milne, Remark 7.49(c): the isomorphism with a
Laurent-series field can be chosen to be a homeomorphism.  More precisely,
it and its inverse are uniformly continuous for the norm and `X`-adic
uniformities. -/
theorem equal_characteristic_homeomorphic
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsDiscreteValuationRing (Valued.integer K)]
    [Finite (ResidueField (Valued.integer K))]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ e : K ≃+* LaurentSeries (ResidueField (Valued.integer K)),
      IsHomeomorph e := by
  obtain ⟨pi, hpi⟩ := exists_is_uniformizer K
  obtain ⟨s, hs, -⟩ :=
    equal_characteristic_section K p
  let e := laurentResidueSection K pi hpi s hs
  refine ⟨e.symm, ?_⟩
  exact
    (laurentUniformSection K pi hpi s hs).symm.toHomeomorph.isHomeomorph

@[reducible] private def normedValuationRank
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] :
    (NormedField.valuation (K := K)).RankOne := by
  apply Valuation.RankLeOne.rankOne_of_exists
  obtain ⟨x, hxpos, hxlt⟩ := NormedField.exists_norm_lt_one K
  refine ⟨x, ?_, ?_⟩
  · intro hx
    subst x
    simp at hxpos
  · apply ne_of_lt
    change ‖x‖₊ < 1
    exact_mod_cast hxlt

private theorem compact_space_proper
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] :
    CompactSpace (Valued.integer K) := by
  rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
    Subtype.range_coe_subtype]
  convert isCompact_closedBall (0 : K) 1 using 1
  ext x
  simp [Valued.integer.mem_iff]

/-- Milne, Remark 7.49(c), stated for a local field rather than with its
complete-DVR consequences as separate hypotheses.  Local compactness makes
the field proper; for a nontrivially normed ultrametric field, properness is
equivalent to completeness together with discreteness of the valuation ring
and finiteness of its residue field. -/
theorem equal_characteristic_series
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nonempty (K ≃+* LaurentSeries (ResidueField (Valued.integer K))) := by
  letI : ProperSpace K :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  letI : CompleteSpace K := inferInstance
  letI : (NormedField.valuation (K := K)).RankOne :=
    normedValuationRank K
  letI : CompactSpace (Valued.integer K) :=
    compact_space_proper K
  have hlocal :=
    (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
      (K := K)).1 (inferInstance : CompactSpace (Valued.integer K))
  letI : IsDiscreteValuationRing (Valued.integer K) := hlocal.2.1
  letI : Finite (ResidueField (Valued.integer K)) := hlocal.2.2
  exact equal_characteristic_laurent K p

/-- Topological form of the equal-characteristic local-field classification
in Milne, Remark 7.49(c), with completeness, discrete valuation, and finite
residue field all derived from local compactness. -/
theorem equal_homeomorphic_laurent
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ e : K ≃+* LaurentSeries (ResidueField (Valued.integer K)),
      IsHomeomorph e := by
  letI : ProperSpace K :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  letI : CompleteSpace K := inferInstance
  letI : (NormedField.valuation (K := K)).RankOne :=
    normedValuationRank K
  letI : CompactSpace (Valued.integer K) :=
    compact_space_proper K
  have hlocal :=
    (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
      (K := K)).1 (inferInstance : CompactSpace (Valued.integer K))
  letI : IsDiscreteValuationRing (Valued.integer K) := hlocal.2.1
  letI : Finite (ResidueField (Valued.integer K)) := hlocal.2.2
  exact equal_characteristic_homeomorphic K p

/-- The topological part of Milne, Remark 7.49(c): the Laurent-series field
`k((T))` is complete for its `T`-adic valuation. -/
theorem laurentSeries_complete (k : Type*) [Field k] :
    CompleteSpace k⸨X⸩ := by
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
-- The adic-completion algebra equivalence has a deep `NormedField` instance search.
/-- Milne, Remark 7.49(c): the Laurent-series field is canonically
isomorphic, as a `k`-algebra, to the `X`-adic completion of `k(X)`. -/
theorem laurent_rat_func
    (k : Type*) [Field k] :
    Nonempty (k⸨X⸩ ≃ₐ[k] LaurentSeries.RatFuncAdicCompl k) :=
  ⟨LaurentSeries.LaurentSeriesAlgEquiv k⟩

/-- Milne's finite-tail description in Remark 7.49(c): every Laurent series
is an integral power of `X` times a formal power series. -/
theorem laurent_single_part
    {k : Type*} [Semiring k] (f : k⸨X⸩) :
    ∃ n : ℤ, ∃ g : k⟦X⟧,
      f = (HahnSeries.single n 1 : k⸨X⸩) * g := by
  exact ⟨f.order, f.powerSeriesPart,
    (LaurentSeries.single_order_mul_powerSeriesPart f).symm⟩

/-- The ring-theoretic part of Milne, Remark 7.49(c): `k[[T]]`, the integer
model inside `k((T))`, is a discrete valuation ring. -/
theorem series_discrete_valuation (k : Type*) [Field k] :
    IsDiscreteValuationRing k⟦X⟧ := by
  infer_instance

/-- The residue field of `k[[T]]` is canonically isomorphic to `k`. -/
def powerSeriesResidue (k : Type*) [Field k] :
    IsLocalRing.ResidueField k⟦X⟧ ≃+* k :=
  PowerSeries.residueFieldOfPowerSeries

/-- Consequently, when `k` is finite, the residue field of `k[[T]]` is
finite, as required for the local-field model `k((T))`. -/
theorem series_residue_field
    (k : Type*) [Field k] [Finite k] :
    Finite (IsLocalRing.ResidueField k⟦X⟧) := by
  exact Finite.of_equiv k (powerSeriesResidue k).symm.toEquiv

/-- The valuation integers in the Laurent-series field are precisely the
power series. -/
def laurentSeriesInteger (k : Type*) [Field k] :
    Valued.integer (LaurentSeries k) ≃+* k⟦X⟧ := by
  let f : k⟦X⟧ →+* Valued.integer (LaurentSeries k) :=
    { toFun := fun F ↦
        ⟨(F : k⸨X⸩),
          (LaurentSeries.val_le_one_iff_eq_coe k (F : k⸨X⸩)).2 ⟨F, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun F G ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun F G ↦ by ext; simp }
  exact (RingEquiv.ofBijective f ⟨
    fun F G h ↦ HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h),
    fun x ↦ by
      obtain ⟨F, hF⟩ :=
        (LaurentSeries.val_le_one_iff_eq_coe k (x : k⸨X⸩)).1 x.property
      exact ⟨F, Subtype.ext hF⟩⟩).symm

/-- If the coefficient field is finite, the residue field of the valuation
ring in `k((T))` is finite. -/
theorem laurent_series_residue
    (k : Type*) [Field k] [Finite k] :
    Finite (IsLocalRing.ResidueField (Valued.integer (LaurentSeries k))) := by
  letI : Finite (IsLocalRing.ResidueField k⟦X⟧) :=
    series_residue_field k
  exact Finite.of_equiv (IsLocalRing.ResidueField k⟦X⟧)
    (IsLocalRing.ResidueField.mapEquiv
      (laurentSeriesInteger k).symm).toEquiv

@[reducible] private noncomputable def laurent_series_rank
    (k : Type*) [Field k] :
    (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰).RankOne :=
  { hom' :=
      (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' :=
      (WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
    exists_val_nontrivial := by
      obtain ⟨x, hx⟩ :=
        LaurentSeries.valuation_surjective k (WithZero.exp (-1 : ℤ))
      refine ⟨x, ?_, ?_⟩
      · rw [hx]
        simp
      · rw [hx]
        simp }

/-- The model direction of Milne, Remark 7.49(c): Laurent series over a finite
field form a locally compact field for the `T`-adic topology. -/
theorem laurent_series_compact
    (k : Type*) [Field k] [Finite k] :
    LocallyCompactSpace k⸨X⸩ := by
  letI : (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰).RankOne :=
    laurent_series_rank k
  letI : NormedField k⸨X⸩ := Valued.toNormedField k⸨X⸩ ℤᵐ⁰
  letI : IsDiscreteValuationRing (Valued.integer (LaurentSeries k)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (laurentSeriesInteger k).symm
  letI : Finite (IsLocalRing.ResidueField (Valued.integer (LaurentSeries k))) :=
    laurent_series_residue k
  letI : ProperSpace k⸨X⸩ :=
    (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := LaurentSeries k)).2 ⟨inferInstance, inferInstance, inferInstance⟩
  infer_instance

/-- The converse to the Laurent-series model direction: if `k((T))` is
locally compact in its `T`-adic topology, then its coefficient field is
finite. -/
theorem laurent_series_locally
    (k : Type*) [Field k] [LocallyCompactSpace k⸨X⸩] :
    Finite k := by
  letI : (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰).RankOne :=
    laurent_series_rank k
  letI : NormedField k⸨X⸩ := Valued.toNormedField k⸨X⸩ ℤᵐ⁰
  letI : ProperSpace k⸨X⸩ :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k⸨X⸩
  letI : Finite (ResidueField (Valued.integer (LaurentSeries k))) :=
    (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := LaurentSeries k)).1 (inferInstance : ProperSpace k⸨X⸩) |>.2.2
  exact Finite.of_equiv (ResidueField (Valued.integer (LaurentSeries k)))
    ((ResidueField.mapEquiv (laurentSeriesInteger k)).trans
      (powerSeriesResidue k)).toEquiv

/-- Milne, Remark 7.49(c), for the model fields: `k((T))` is locally compact
if and only if the coefficient field `k` is finite. -/
theorem laurent_locally_compact
    (k : Type*) [Field k] :
    LocallyCompactSpace k⸨X⸩ ↔ Finite k := by
  constructor
  · intro h
    letI : LocallyCompactSpace k⸨X⸩ := h
    exact laurent_series_locally k
  · intro h
    letI : Finite k := h
    exact laurent_series_compact k

end

end Towers.NumberTheory.Milne
