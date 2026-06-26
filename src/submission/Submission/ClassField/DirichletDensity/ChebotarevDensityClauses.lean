import Submission.ClassField.DirichletDensity.PolarLogBridge
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Chapter VI, Section 4, Proposition 4.4

The five clauses below are stated for Milne's Dirichlet density, including
the "any two imply the third" form of additivity.
-/

namespace Submission.CField.DDensit

open IsDedekindDomain NumberField Set
open nonZeroDivisors
open Submission.CField.PDensit

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

local notation "PrimeK" => HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- Proposition VI.4.4(a). -/
def AllDirichletDensity : Prop :=
  PrimeDirichletDensity K (Set.univ : Set PrimeK) 1

/-- Proposition VI.4.4(b). -/
def DirichletDensityNonnegative : Prop :=
  ∀ (T : Set PrimeK) (δ : ℝ),
    PrimeDirichletDensity K T δ → 0 ≤ δ

/-- Proposition VI.4.4(c). -/
def SetDirichletDensity : Prop :=
  ∀ T : Set PrimeK, T.Finite → PrimeDirichletDensity K T 0

/-- Proposition VI.4.4(d), with all three choices of the initially known
pair of densities. -/
def DirichletDisjointLaws : Prop :=
  ∀ (T T₁ T₂ : Set PrimeK) (δ δ₁ δ₂ : ℝ),
    T = T₁ ∪ T₂ → Disjoint T₁ T₂ →
    ((PrimeDirichletDensity K T₁ δ₁ ∧
        PrimeDirichletDensity K T₂ δ₂) →
      PrimeDirichletDensity K T (δ₁ + δ₂)) ∧
    ((PrimeDirichletDensity K T δ ∧
        PrimeDirichletDensity K T₁ δ₁) →
      PrimeDirichletDensity K T₂ (δ - δ₁)) ∧
    ((PrimeDirichletDensity K T δ ∧
        PrimeDirichletDensity K T₂ δ₂) →
      PrimeDirichletDensity K T₁ (δ - δ₂))

/-- Proposition VI.4.4(e). -/
def DirichletDensityMonotone : Prop :=
  ∀ (T T' : Set PrimeK) (δ δ' : ℝ), T ⊆ T' →
    PrimeDirichletDensity K T δ →
    PrimeDirichletDensity K T' δ' → δ ≤ δ'

/-- Clause (a) is the immediate combination explicitly cited by the source:
all primes have polar density one, and polar density implies Dirichlet
density. -/
theorem chebotarevDensityClauses
    (h31a : AllPolarDensity K)
    (h41a : PolarImpliesDirichlet.{u}) :
    AllDirichletDensity K :=
  h41a K Set.univ 1 h31a

/-- The number of integral ideals of a prescribed norm, viewed as a real
coefficient of the Dedekind zeta series. -/
private noncomputable def idealNormCount (n : ℕ) : ℝ :=
  Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I.absNorm = n}

private theorem sum_count_icc (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, idealNormCount K n) + 1 =
      Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I.absNorm ≤ N} := by
  unfold idealNormCount
  norm_cast
  rw [show Finset.Icc 1 N = Finset.Ioc 0 N from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I.absNorm = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le N),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- Integral-ideal reciprocal norms are summable in the half-plane `s>1`.
This is the convergence fact needed to rearrange prime sums over disjoint
sets. -/
private theorem summable_ideal_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun I : Ideal (NumberField.RingOfIntegers K) ↦
      Real.rpow (I.absNorm : ℝ) (-s)) := by
  let count : ℕ → ℝ := fun N ↦
    Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I.absNorm ≤ N}
  have hquot : (fun N : ℕ ↦ count N / (N : ℝ)) =O[Filter.atTop]
      (fun _ ↦ (1 : ℝ)) :=
    (((Ideal.tendsto_norm_le_div_atTop K).comp
      tendsto_natCast_atTop_atTop).isBigO_one ℝ).congr'
      (by filter_upwards with N; simp [count]) Filter.EventuallyEq.rfl
  have hcount : count =O[Filter.atTop] (fun N : ℕ ↦ (N : ℝ)) := by
    have hmul := hquot.mul (Asymptotics.isBigO_refl (fun N : ℕ ↦ (N : ℝ)) Filter.atTop)
    apply hmul.congr'
    · filter_upwards [Filter.eventually_ne_atTop 0] with N hN
      dsimp [count]
      field_simp
    · filter_upwards with N
      simp
  have hpartial :
      (fun N ↦ ∑ n ∈ Finset.Icc 1 N, idealNormCount K n) =O[Filter.atTop]
        (fun N : ℕ ↦ (N : ℝ) ^ (1 : ℝ)) := by
    have hone : (fun _ : ℕ ↦ (1 : ℝ)) =O[Filter.atTop] (fun N : ℕ ↦ (N : ℝ)) := by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨1, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      simpa using hN
    have hsub := hcount.sub hone
    apply hsub.congr'
    · filter_upwards with N
      dsimp [count]
      linarith [sum_count_icc K N]
    · filter_upwards with N
      simp [Real.rpow_one]
  have hL : LSeriesSummable (fun n ↦ idealNormCount K n) (s : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hpartial
      (fun n ↦ Nat.cast_nonneg _) zero_le_one (by simpa using hs)
  let fibers : ℕ → Set (Ideal (NumberField.RingOfIntegers K)) :=
    fun n ↦ {I | I.absNorm = n}
  have houter : Summable (fun n ↦
      ∑' I : fibers n, Real.rpow (I.1.absNorm : ℝ) (-s)) := by
    apply hL.norm.congr
    intro n
    letI : Fintype (fibers n) := (Ideal.finite_setOf_absNorm_eq n).fintype
    simp_rw [show ∀ I : fibers n, I.1.absNorm = n from fun I ↦ I.2]
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term_zero, Real.zero_rpow (by linarith : -s ≠ 0)]
    · rw [LSeries.term_of_ne_zero hn, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), tsum_fintype]
      simp [idealNormCount, fibers, Real.rpow_neg (Nat.cast_nonneg n),
        div_eq_mul_inv, Fintype.card_eq_nat_card]
  rw [summable_partition (f := fun I : Ideal (NumberField.RingOfIntegers K) ↦
    Real.rpow (I.absNorm : ℝ) (-s)) (s := fibers)]
  · refine ⟨fun n ↦ ?_, houter⟩
    letI : Fintype (fibers n) := (Ideal.finite_setOf_absNorm_eq n).fintype
    exact (hasSum_fintype _).summable
  · intro I
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro I
    refine ⟨I.absNorm, ?_, ?_⟩
    · rfl
    · intro n hn
      exact hn.symm

private theorem summable_prime_rpow
    (T : Set PrimeK) {s : ℝ} (hs : 1 < s) :
    Summable (fun p : T ↦ Real.rpow (p.1.asIdeal.absNorm : ℝ) (-s)) := by
  apply (summable_ideal_rpow K hs).comp_injective
  intro p q hpq
  apply Subtype.ext
  exact HeightOneSpectrum.ext hpq

private theorem reciprocal_union_disjoint
    {T₁ T₂ : Set PrimeK} (hdis : Disjoint T₁ T₂) {s : ℝ} (hs : 1 < s) :
    primeReciprocalSum K (T₁ ∪ T₂) s =
      primeReciprocalSum K T₁ s +
        primeReciprocalSum K T₂ s := by
  unfold primeReciprocalSum
  apply Summable.tsum_union_disjoint
    (f := fun p : PrimeK ↦ Real.rpow (p.asIdeal.absNorm : ℝ) (-s)) hdis
  · simpa only [Function.comp_apply] using summable_prime_rpow K T₁ hs
  · simpa only [Function.comp_apply] using summable_prime_rpow K T₂ hs

private theorem boundedDifference_add
    {f₁ f₂ g₁ g₂ : ℝ → ℝ}
    (h₁ : BoundedDifferenceNear f₁ g₁)
    (h₂ : BoundedDifferenceNear f₂ g₂) :
    BoundedDifferenceNear (fun s ↦ f₁ s + f₂ s)
      (fun s ↦ g₁ s + g₂ s) := by
  obtain ⟨ε₁, hε₁, B₁, hB₁⟩ := h₁
  obtain ⟨ε₂, hε₂, B₂, hB₂⟩ := h₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, B₁ + B₂, ?_⟩
  intro s hs
  have hs₁ : s ∈ Set.Ioo (1 : ℝ) (1 + ε₁) :=
    ⟨hs.1, by linarith [hs.2, min_le_left ε₁ ε₂]⟩
  have hs₂ : s ∈ Set.Ioo (1 : ℝ) (1 + ε₂) :=
    ⟨hs.1, by linarith [hs.2, min_le_right ε₁ ε₂]⟩
  calc
    |(f₁ s + f₂ s) - (g₁ s + g₂ s)| =
        |(f₁ s - g₁ s) + (f₂ s - g₂ s)| := by ring_nf
    _ ≤ |f₁ s - g₁ s| + |f₂ s - g₂ s| := abs_add_le _ _
    _ ≤ B₁ + B₂ := add_le_add (hB₁ s hs₁) (hB₂ s hs₂)

private theorem boundedDifference_sub
    {f₁ f₂ g₁ g₂ : ℝ → ℝ}
    (h₁ : BoundedDifferenceNear f₁ g₁)
    (h₂ : BoundedDifferenceNear f₂ g₂) :
    BoundedDifferenceNear (fun s ↦ f₁ s - f₂ s)
      (fun s ↦ g₁ s - g₂ s) := by
  obtain ⟨ε₁, hε₁, B₁, hB₁⟩ := h₁
  obtain ⟨ε₂, hε₂, B₂, hB₂⟩ := h₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, B₁ + B₂, ?_⟩
  intro s hs
  have hs₁ : s ∈ Set.Ioo (1 : ℝ) (1 + ε₁) :=
    ⟨hs.1, by linarith [hs.2, min_le_left ε₁ ε₂]⟩
  have hs₂ : s ∈ Set.Ioo (1 : ℝ) (1 + ε₂) :=
    ⟨hs.1, by linarith [hs.2, min_le_right ε₁ ε₂]⟩
  calc
    |(f₁ s - f₂ s) - (g₁ s - g₂ s)| =
        |(f₁ s - g₁ s) - (f₂ s - g₂ s)| := by ring_nf
    _ ≤ |f₁ s - g₁ s| + |f₂ s - g₂ s| := abs_sub _ _
    _ ≤ B₁ + B₂ := add_le_add (hB₁ s hs₁) (hB₂ s hs₂)

theorem chebotarev_density_clauses : SetDirichletDensity K := by
  intro T hT
  letI : Fintype T := hT.fintype
  refine ⟨1, zero_lt_one, (Fintype.card T : ℝ), ?_⟩
  intro s hs
  change |primeReciprocalSum K T s - 0 * Real.log (1 / (s - 1))| ≤ _
  simp only [zero_mul, sub_zero]
  have hnonneg : 0 ≤ primeReciprocalSum K T s :=
    tsum_nonneg fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [abs_of_nonneg hnonneg, primeReciprocalSum, tsum_fintype]
  calc
    ∑ p : T, (p.1.asIdeal.absNorm : ℝ) ^ (-s)
        ≤ ∑ _p : T, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm p.1).le)
        (by linarith [hs.1])
    _ = Fintype.card T := by simp

theorem chebotarevClausesNonnegative : DirichletDensityNonnegative K := by
  intro T δ hδ
  by_contra hnot
  have hδneg : δ < 0 := lt_of_not_ge hnot
  obtain ⟨ε, hε, B, hB⟩ := hδ
  have hlog : Filter.Tendsto (fun N : ℕ ↦ δ * Real.log (N : ℝ))
      Filter.atTop Filter.atBot :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg hδneg
  have hsmall : Filter.Tendsto (fun N : ℕ ↦ ((N : ℝ)⁻¹))
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hevNeg : ∀ᶠ N : ℕ in Filter.atTop,
      δ * Real.log (N : ℝ) < -B :=
    (hlog.eventually (Filter.eventually_lt_atBot (-B))).mono fun N hN ↦ hN
  have hevSmall : ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ)⁻¹ < ε :=
    hsmall.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hNpos, hNneg, hNsmall⟩ :
      ∃ N : ℕ, 0 < N ∧ δ * Real.log (N : ℝ) < -B ∧ (N : ℝ)⁻¹ < ε := by
    have hev : ∀ᶠ N : ℕ in Filter.atTop,
        0 < N ∧ δ * Real.log (N : ℝ) < -B ∧ (N : ℝ)⁻¹ < ε :=
      (Filter.eventually_gt_atTop 0).and (hevNeg.and hevSmall)
    exact Filter.Eventually.exists hev
  let s₀ : ℝ := 1 + (N : ℝ)⁻¹
  have hs₀ : s₀ ∈ Set.Ioo (1 : ℝ) (1 + ε) := by
    dsimp [s₀]
    constructor
    · exact lt_add_of_pos_right _ (inv_pos.mpr (Nat.cast_pos.mpr hNpos))
    · linarith
  have hbound := hB s₀ hs₀
  have hlogeq : Real.log (1 / (s₀ - 1)) = Real.log (N : ℝ) := by
    dsimp [s₀]
    rw [add_sub_cancel_left, one_div, inv_inv]
  have hsum_nonneg : 0 ≤ primeReciprocalSum K T s₀ :=
    tsum_nonneg fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hupper : primeReciprocalSum K T s₀ ≤
      δ * Real.log (N : ℝ) + B := by
    dsimp only at hbound
    rw [hlogeq] at hbound
    linarith [le_abs_self
      (primeReciprocalSum K T s₀ - δ * Real.log (N : ℝ))]
  linarith

private theorem dirichlet_density_disjoint
    {T₁ T₂ : Set PrimeK} {δ₁ δ₂ : ℝ} (hdis : Disjoint T₁ T₂)
    (h₁ : PrimeDirichletDensity K T₁ δ₁)
    (h₂ : PrimeDirichletDensity K T₂ δ₂) :
    PrimeDirichletDensity K (T₁ ∪ T₂) (δ₁ + δ₂) := by
  obtain ⟨ε, hε, B, hB⟩ := boundedDifference_add h₁ h₂
  refine ⟨ε, hε, B, ?_⟩
  intro s hs
  dsimp only
  rw [reciprocal_union_disjoint K hdis hs.1]
  simpa only [add_mul] using hB s hs

private theorem dirichlet_density_union
    {T₁ T₂ : Set PrimeK} {δ δ₁ : ℝ} (hdis : Disjoint T₁ T₂)
    (h : PrimeDirichletDensity K (T₁ ∪ T₂) δ)
    (h₁ : PrimeDirichletDensity K T₁ δ₁) :
    PrimeDirichletDensity K T₂ (δ - δ₁) := by
  obtain ⟨ε, hε, B, hB⟩ := boundedDifference_sub h h₁
  refine ⟨ε, hε, B, ?_⟩
  intro s hs
  have hunion := reciprocal_union_disjoint K hdis hs.1
  dsimp only at hB ⊢
  have := hB s hs
  rw [hunion] at this
  convert this using 1
  all_goals ring_nf

private theorem dirichlet_left_union
    {T₁ T₂ : Set PrimeK} {δ δ₂ : ℝ} (hdis : Disjoint T₁ T₂)
    (h : PrimeDirichletDensity K (T₁ ∪ T₂) δ)
    (h₂ : PrimeDirichletDensity K T₂ δ₂) :
    PrimeDirichletDensity K T₁ (δ - δ₂) := by
  have hswap : Disjoint T₂ T₁ := hdis.symm
  have hunion : T₂ ∪ T₁ = T₁ ∪ T₂ := Set.union_comm _ _
  exact dirichlet_density_union K hswap (hunion ▸ h) h₂

theorem disjoint_union : DirichletDisjointLaws K := by
  intro T T₁ T₂ δ δ₁ δ₂ hT hdis
  subst T
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    exact dirichlet_density_disjoint K hdis h₁ h₂
  · rintro ⟨h, h₁⟩
    exact dirichlet_density_union K hdis h h₁
  · rintro ⟨h, h₂⟩
    exact dirichlet_left_union K hdis h h₂

theorem chebotarevClausesMonotone : DirichletDensityMonotone K := by
  classical
  intro T T' δ δ' hsub hT hT'
  let D : Set PrimeK := T' \ T
  have hdis : Disjoint T D := Set.disjoint_sdiff_right
  have hunion : T ∪ D = T' := by
    ext p
    simp only [D, Set.mem_union, Set.mem_diff]
    constructor
    · rintro (hp | hp)
      · exact hsub hp
      · exact hp.1
    · intro hp
      exact if hpt : p ∈ T then Or.inl hpt else Or.inr ⟨hp, hpt⟩
  have hD : PrimeDirichletDensity K D (δ' - δ) :=
    dirichlet_density_union K hdis (hunion ▸ hT') hT
  have hnonneg : 0 ≤ δ' - δ := chebotarevClausesNonnegative K D (δ' - δ) hD
  linarith

/-- Full Proposition VI.4.4.  Clause (a) uses exactly the two results cited
in the source; clauses (b)--(e) are unconditional consequences of the
literal bounded-difference definition. -/
theorem chebotarevClausesStatement
    (h31a : AllPolarDensity K)
    (h41a : PolarImpliesDirichlet.{u}) :
    (AllDirichletDensity K ∧
          DirichletDensityNonnegative K ∧
          SetDirichletDensity K ∧
          DirichletDisjointLaws K ∧ DirichletDensityMonotone K) :=
  ⟨chebotarevDensityClauses K h31a h41a,
    chebotarevClausesNonnegative K,
    chebotarev_density_clauses K,
    disjoint_union K,
    chebotarevClausesMonotone K⟩

/-- Hierarchical form: Proposition 4.4 follows from the already stated
Propositions 3.1 and 4.1. -/
theorem chebotarev_clauses_previous
    (h31 : EulerDensityLaws K)
    (h41 : PolarDirichletBridge.{u}) :
    (AllDirichletDensity K ∧
          DirichletDensityNonnegative K ∧
          SetDirichletDensity K ∧
          DirichletDisjointLaws K ∧ DirichletDensityMonotone K) :=
  chebotarevClausesStatement K h31.1 h41.1

end

end Submission.CField.DDensit
