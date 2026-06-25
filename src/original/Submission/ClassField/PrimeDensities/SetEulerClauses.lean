import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.ClassField.EulerProducts.DedekindZetaContinuation

/-!
# Chapter VI, Section 3, Proposition 3.1

This file uses Milne's actual *polar density*, rather than replacing it by
natural density.  For a set `T` of finite primes, `setEulerProduct K T`
is the literal Euler product `prod_{p in T} (1-N(p)^(-s))^-1`.  A density
certificate records the positive power, its meromorphic continuation near
`1`, and the pole order there.
-/

namespace Submission.CField.PDensit

open Complex Filter IsDedekindDomain NumberField Set Topology
open scoped BigOperators NumberField
open Submission.CField.EProduc

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The local Euler factor attached to a finite prime. -/
def setEulerClauses (s : ℂ)
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K)) : ℂ :=
  (1 - (p.asIdeal.absNorm : ℂ) ^ (-s))⁻¹

/-- Milne's `zeta_{K,T}(s)`, as the product over the primes belonging to
`T`.  As usual for `tprod`, this has its intended value where the family is
multipliable; the polar-density certificate below only compares it on the
initial real half-plane near `1`. -/
def setEulerProduct
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (s : ℂ) : ℂ :=
  ∏' p : T, setEulerClauses K s p.1

/-- A positive power of the Euler product extends meromorphically to a
neighborhood of `1` and has a pole of order `m` there. -/
def PolarDensityCertificate
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (n m : ℕ) : Prop :=
  0 < n ∧ ∃ F : ℂ → ℂ,
    MeromorphicAt F 1 ∧
    (∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
      F (x : ℂ) = (setEulerProduct K T (x : ℂ)) ^ n) ∧
    meromorphicOrderAt F 1 = (-(m : ℤ) : WithTop ℤ)

/-- Milne's definition: `T` has polar density `delta=m/n` if a positive
integral power has a pole of order `m` at `1`. -/
def PrimePolarDensity
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (δ : ℝ) : Prop :=
  ∃ n m : ℕ, PolarDensityCertificate K T n m ∧ δ = (m : ℝ) / n

/-- Proposition VI.3.1(a): all finite primes have polar density one. -/
def AllPolarDensity : Prop :=
  PrimePolarDensity K Set.univ 1

/-- Proposition VI.3.1(b): every defined polar density is nonnegative. -/
def PolarDensityNonnegative : Prop :=
  ∀ (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (δ : ℝ),
    PrimePolarDensity K T δ → 0 ≤ δ

/-- Proposition VI.3.1(c), including all three choices of which two
densities are initially known. -/
def PolarDisjointLaws : Prop :=
  ∀ (T T₁ T₂ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (δ δ₁ δ₂ : ℝ),
    T = T₁ ∪ T₂ → Disjoint T₁ T₂ →
    ((PrimePolarDensity K T₁ δ₁ ∧
        PrimePolarDensity K T₂ δ₂) →
      PrimePolarDensity K T (δ₁ + δ₂)) ∧
    ((PrimePolarDensity K T δ ∧
        PrimePolarDensity K T₁ δ₁) →
      PrimePolarDensity K T₂ (δ - δ₁)) ∧
    ((PrimePolarDensity K T δ ∧
        PrimePolarDensity K T₂ δ₂) →
      PrimePolarDensity K T₁ (δ - δ₂))

/-- Proposition VI.3.1(d): polar density is monotone under inclusion. -/
def PolarDensityMonotone : Prop :=
  ∀ (T T' : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (δ δ' : ℝ),
    T ⊆ T' → PrimePolarDensity K T δ →
      PrimePolarDensity K T' δ' → δ ≤ δ'

/-- Proposition VI.3.1(e): a finite set has polar density zero. -/
def SetPolarDensity : Prop :=
  ∀ T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)), T.Finite →
    PrimePolarDensity K T 0

/-- **Proposition VI.3.1 (source statement).** -/
def EulerDensityLaws : Prop :=
  AllPolarDensity K ∧
    PolarDensityNonnegative K ∧
    PolarDisjointLaws K ∧
    PolarDensityMonotone K ∧ SetPolarDensity K

/-- Part (b) is already forced by the source definition: both the pole order
and the positive power are natural numbers. -/
theorem eulerClausesNonnegative : PolarDensityNonnegative K := by
  intro T δ hδ
  obtain ⟨n, m, hn, rfl⟩ := hδ
  exact div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- Each local Euler factor is analytic and nonzero at `1`. -/
theorem analytic_euler_clauses
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AnalyticAt ℂ (fun s ↦ setEulerClauses K s p) 1 := by
  have hNnat : p.asIdeal.absNorm ≠ 0 :=
    Nat.ne_of_gt (zero_lt_one.trans
      (NumberField.HeightOneSpectrum.one_lt_absNorm p))
  have hNcomplex : (p.asIdeal.absNorm : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hNnat
  have hpow : AnalyticAt ℂ
      (fun s : ℂ ↦ (p.asIdeal.absNorm : ℂ) ^ (-s)) 1 :=
    (differentiable_id.neg.const_cpow (.inl hNcomplex)).analyticAt 1
  have hden : AnalyticAt ℂ
      (fun s : ℂ ↦ 1 - (p.asIdeal.absNorm : ℂ) ^ (-s)) 1 :=
    analyticAt_const.sub hpow
  have hNneOne : (p.asIdeal.absNorm : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_gt
      (NumberField.HeightOneSpectrum.one_lt_absNorm p))
  have hdenne :
      (1 : ℂ) - (p.asIdeal.absNorm : ℂ) ^ (-(1 : ℂ)) ≠ 0 := by
    rw [Complex.cpow_neg_one]
    simpa [sub_ne_zero] using hNneOne
  exact hden.inv hdenne

/-- In particular, a local Euler factor has neither a zero nor a pole at
`1`. -/
theorem set_euler_clauses
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    setEulerClauses K 1 p ≠ 0 := by
  rw [setEulerClauses]
  apply inv_ne_zero
  rw [Complex.cpow_neg_one]
  have hNnat : p.asIdeal.absNorm ≠ 0 :=
    Nat.ne_of_gt (zero_lt_one.trans
      (NumberField.HeightOneSpectrum.one_lt_absNorm p))
  have hNcomplex : (p.asIdeal.absNorm : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hNnat
  have hNneOne : (p.asIdeal.absNorm : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_gt
      (NumberField.HeightOneSpectrum.one_lt_absNorm p))
  intro h
  have hinv : (p.asIdeal.absNorm : ℂ)⁻¹ = 1 := (sub_eq_zero.mp h).symm
  have := congrArg Inv.inv hinv
  exact hNneOne (by simpa [hNcomplex] using this)

/-- A finite prime-set Euler product is analytic and nonzero at `1`. -/
theorem analytic_set_euler
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : T.Finite) :
    AnalyticAt ℂ (setEulerProduct K T) 1 ∧
      setEulerProduct K T 1 ≠ 0 := by
  letI : Fintype T := hT.fintype
  have heq : setEulerProduct K T =
      fun s ↦ ∏ p : T, setEulerClauses K s p.1 := by
    funext s
    simp [setEulerProduct, tprod_fintype]
  rw [heq]
  constructor
  · exact Finset.univ.analyticAt_fun_prod fun p _ ↦
      analytic_euler_clauses K p.1
  · exact Finset.prod_ne_zero_iff.mpr fun p _ ↦
      set_euler_clauses K p.1

/-- Proposition VI.3.1(e), directly from the finite Euler product. -/
theorem euler_clauses_density : SetPolarDensity K := by
  intro T hT
  obtain ⟨han, hne⟩ := analytic_set_euler K T hT
  refine ⟨1, 0, ?_, by norm_num⟩
  refine ⟨Nat.one_pos, setEulerProduct K T, han.meromorphicAt, ?_, ?_⟩
  · filter_upwards [] with x
    simp
  · change meromorphicOrderAt (setEulerProduct K T) 1 =
      ((0 : ℤ) : WithTop ℤ)
    rw [meromorphicOrderAt_eq_int_iff han.meromorphicAt]
    refine ⟨setEulerProduct K T, han, hne, ?_⟩
    filter_upwards [] with z
    simp

/-- The three elementary Euler-product facts used in Proposition 3.1 and
not currently packaged for prime ideals of an arbitrary number field.
They assert only the absolutely-convergent identities on the original
half-plane `x > 1`: products multiply over disjoint unions, their norms are
at least one there, and the product over all primes is Dedekind zeta. -/
structure SetEulerBridge : Prop where
  disjointUnion :
    ∀ (T₁ T₂ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))),
      Disjoint T₁ T₂ → ∀ x : ℝ, 1 < x →
        setEulerProduct K (T₁ ∪ T₂) (x : ℂ) =
          setEulerProduct K T₁ (x : ℂ) *
            setEulerProduct K T₂ (x : ℂ)
  one_le_norm :
    ∀ (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
      (n : ℕ), ∀ x : ℝ, 1 < x →
        1 ≤ ‖(setEulerProduct K T (x : ℂ)) ^ n‖
  univ_dedekind_zeta :
    ∀ x : ℝ, 1 < x →
      setEulerProduct K Set.univ (x : ℂ) = dedekindZeta K (x : ℂ)

/-- The real axis approaching `1` from the right maps into the punctured
complex neighbourhood of `1`. -/
private theorem tendsto_real_nhds :
    Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (x : ℂ) ≠ (1 : ℂ)
    exact_mod_cast ne_of_gt hx

/-- A meromorphic continuation of a positive power of a prime-set Euler
product cannot vanish at `1`; equivalently, its order is nonpositive.  This
is the analytic content of Milne's positivity observation in part (b). -/
theorem meromorphic_nonpos_matches
    (hbridge : SetEulerBridge K)
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (n : ℕ) (F : ℂ → ℂ)
    (hmatch : ∀ᶠ (x : ℝ) in 𝓝[>] 1,
      F (x : ℂ) = (setEulerProduct K T (x : ℂ)) ^ n) :
    meromorphicOrderAt F 1 ≤ 0 := by
  by_contra hnot
  have hpos : 0 < meromorphicOrderAt F 1 := lt_of_not_ge hnot
  have hzeroComplex := tendsto_zero_of_meromorphicOrderAt_pos hpos
  have hzero : Tendsto (fun x : ℝ ↦ ‖F (x : ℂ)‖) (𝓝[>] 1) (𝓝 0) := by
    simpa using (hzeroComplex.comp tendsto_real_nhds).norm
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 1, ‖F (x : ℂ)‖ < 1 :=
    hzero.eventually (eventually_lt_nhds zero_lt_one)
  have hfalse : ∀ᶠ x : ℝ in 𝓝[>] 1, False := by
    filter_upwards [hlt, hmatch, self_mem_nhdsWithin] with x hx hEq hxOne
    rw [hEq] at hx
    exact (not_lt_of_ge (hbridge.one_le_norm T n x hxOne)) hx
  exact hfalse.exists.elim fun _ h ↦ h

/-- If the two disjoint pieces have polar density, their union has the sum
of those densities. -/
theorem polar_density_disjoint
    (hbridge : SetEulerBridge K)
    {T₁ T₂ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))}
    {δ₁ δ₂ : ℝ}
    (h₁ : PrimePolarDensity K T₁ δ₁)
    (h₂ : PrimePolarDensity K T₂ δ₂)
    (hdis : Disjoint T₁ T₂) :
    PrimePolarDensity K (T₁ ∪ T₂) (δ₁ + δ₂) := by
  obtain ⟨n₁, m₁, ⟨hn₁, F₁, hF₁, hmatch₁, hord₁⟩, rfl⟩ := h₁
  obtain ⟨n₂, m₂, ⟨hn₂, F₂, hF₂, hmatch₂, hord₂⟩, rfl⟩ := h₂
  refine ⟨n₁ * n₂, m₁ * n₂ + m₂ * n₁, ?_, ?_⟩
  · refine ⟨Nat.mul_pos hn₁ hn₂,
      fun z ↦ F₁ z ^ n₂ * F₂ z ^ n₁,
      (hF₁.pow n₂).mul (hF₂.pow n₁), ?_, ?_⟩
    · filter_upwards [hmatch₁, hmatch₂, self_mem_nhdsWithin] with x hx₁ hx₂ hx
      rw [hx₁, hx₂, hbridge.disjointUnion T₁ T₂ hdis x hx]
      calc
        (setEulerProduct K T₁ (x : ℂ) ^ n₁) ^ n₂ *
            (setEulerProduct K T₂ (x : ℂ) ^ n₂) ^ n₁ =
          setEulerProduct K T₁ (x : ℂ) ^ (n₁ * n₂) *
            setEulerProduct K T₂ (x : ℂ) ^ (n₂ * n₁) := by
              rw [pow_mul, pow_mul]
        _ = setEulerProduct K T₁ (x : ℂ) ^ (n₁ * n₂) *
            setEulerProduct K T₂ (x : ℂ) ^ (n₁ * n₂) := by
              rw [Nat.mul_comm n₂ n₁]
        _ = (setEulerProduct K T₁ (x : ℂ) *
            setEulerProduct K T₂ (x : ℂ)) ^ (n₁ * n₂) := by
              rw [mul_pow]
    · change meromorphicOrderAt (F₁ ^ n₂ * F₂ ^ n₁) 1 = _
      rw [meromorphicOrderAt_mul (hF₁.pow n₂) (hF₂.pow n₁),
        meromorphicOrderAt_pow hF₁, meromorphicOrderAt_pow hF₂,
        hord₁, hord₂]
      norm_cast
      push_cast
      ring
  · push_cast
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn₁),
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn₂)]

/-- If a disjoint union and its first piece have density, the second piece
has the difference of the two densities. -/
theorem polar_sdiff_union
    (hbridge : SetEulerBridge K)
    {T T₁ T₂ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))}
    {δ δ₁ : ℝ} (hTset : T = T₁ ∪ T₂) (hdis : Disjoint T₁ T₂)
    (hT : PrimePolarDensity K T δ)
    (h₁ : PrimePolarDensity K T₁ δ₁) :
    PrimePolarDensity K T₂ (δ - δ₁) := by
  obtain ⟨n, m, ⟨hn, F, hF, hmatch, hord⟩, rfl⟩ := hT
  obtain ⟨n₁, m₁, ⟨hn₁, F₁, hF₁, hmatch₁, hord₁⟩, rfl⟩ := h₁
  let G : ℂ → ℂ := fun z ↦ F z ^ n₁ / F₁ z ^ n
  have hG : MeromorphicAt G 1 := (hF.pow n₁).div (hF₁.pow n)
  have hGmatch : ∀ᶠ (x : ℝ) in 𝓝[>] 1,
      G (x : ℂ) = (setEulerProduct K T₂ (x : ℂ)) ^ (n * n₁) := by
    filter_upwards [hmatch, hmatch₁, self_mem_nhdsWithin] with x hxT hx₁ hx
    have hUnion := hbridge.disjointUnion T₁ T₂ hdis x hx
    have hP₁bound := hbridge.one_le_norm T₁ (n₁ * n) x hx
    have hP₁ne : (setEulerProduct K T₁ (x : ℂ)) ^ (n₁ * n) ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hP₁bound
      norm_num at hP₁bound
    simp only [G, hxT, hx₁]
    rw [hTset, hUnion]
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
    rw [Nat.mul_comm n₁ n] at hP₁ne ⊢
    exact div_eq_iff hP₁ne |>.2 (by ring)
  have hordG : meromorphicOrderAt G 1 =
      (((-(m * n₁ : ℕ) : ℤ) + (m₁ * n : ℕ) : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt (F ^ n₁ / F₁ ^ n) 1 = _
    rw [meromorphicOrderAt_div (hF.pow n₁) (hF₁.pow n),
      meromorphicOrderAt_pow hF, meromorphicOrderAt_pow hF₁, hord, hord₁]
    norm_cast
    push_cast
    ring
  have hnonpos := meromorphic_nonpos_matches
    K hbridge T₂ (n * n₁) G hGmatch
  rw [hordG] at hnonpos
  have hcross : m₁ * n ≤ m * n₁ := by
    norm_cast at hnonpos
    omega
  refine ⟨n * n₁, m * n₁ - m₁ * n, ?_, ?_⟩
  · refine ⟨Nat.mul_pos hn hn₁, G, hG, hGmatch, ?_⟩
    rw [hordG]
    norm_cast
    push_cast [Nat.cast_sub hcross]
    omega
  · push_cast [Nat.cast_sub hcross]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn),
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn₁)]

/-- The symmetric two-out-of-three case. -/
theorem polar_density_sdiff
    (hbridge : SetEulerBridge K)
    {T T₁ T₂ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))}
    {δ δ₂ : ℝ} (hTset : T = T₁ ∪ T₂) (hdis : Disjoint T₁ T₂)
    (hT : PrimePolarDensity K T δ)
    (h₂ : PrimePolarDensity K T₂ δ₂) :
    PrimePolarDensity K T₁ (δ - δ₂) := by
  apply polar_sdiff_union K hbridge
    (T := T) (T₁ := T₂) (T₂ := T₁)
    (hTset.trans (Set.union_comm T₁ T₂)) hdis.symm hT h₂

/-- Proposition VI.3.1(c), with all three choices of the initially known
pair of densities. -/
theorem two_out_three
    (hbridge : SetEulerBridge K) : PolarDisjointLaws K := by
  intro T T₁ T₂ δ δ₁ δ₂ hTset hdis
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    rw [hTset]
    exact polar_density_disjoint K hbridge h₁ h₂ hdis
  · rintro ⟨hT, h₁⟩
    exact polar_sdiff_union K hbridge
      hTset hdis hT h₁
  · rintro ⟨hT, h₂⟩
    exact polar_density_sdiff K hbridge
      hTset hdis hT h₂

/-- Proposition VI.3.1(d), obtained from (b) and the second two-out-of-three
case applied to `T' = T ∪ (T' \ T)`. -/
theorem eulerClausesMonotone
    (hbridge : SetEulerBridge K) : PolarDensityMonotone K := by
  intro T T' δ δ' hsub hT hT'
  have hdecomp : T' = T ∪ (T' \ T) := by
    ext p
    constructor
    · intro hp
      by_cases hpT : p ∈ T
      · exact Or.inl hpT
      · exact Or.inr ⟨hp, hpT⟩
    · rintro (hp | hp)
      · exact hsub hp
      · exact hp.1
  have hdiff : PrimePolarDensity K (T' \ T) (δ' - δ) :=
    polar_sdiff_union K hbridge
      hdecomp Set.disjoint_sdiff_right hT' hT
  have hnonneg : 0 ≤ δ' - δ := eulerClausesNonnegative K _ _ hdiff
  linarith

/-- Corollary 2.12's explicit nonzero-residue expansion says that its
Dedekind-zeta continuation has order exactly `-1` at `1`. -/
theorem meromorphic_zeta_continuation
    (h212 : (DedekindContinuationConclusion K)) :
    meromorphicOrderAt (dedekindZetaContinuation K) 1 =
      ((-(1 : ℤ) : ℤ) : WithTop ℤ) := by
  rcases h212 with ⟨hagree, hmero, hdiff, hhol, hexp, hres, hc, hformula⟩
  let b : ℝ := 1 - 1 / (numberFieldDegree K : ℝ)
  have hb : b < 1 := ray_error_exponent K
  have hmem : (1 : ℂ) ∈ {s : ℂ | b < s.re} := by simpa using hb
  have hopen : IsOpen {s : ℂ | b < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hHan : AnalyticAt ℂ (dedekindHolomorphicPart K) 1 :=
    hhol.analyticAt (hopen.mem_nhds hmem)
  let G : ℂ → ℂ := fun z ↦
    (dedekindZeta_residue K : ℂ) +
      (z - 1) * dedekindHolomorphicPart K z
  have hGan : AnalyticAt ℂ G 1 := by
    exact analyticAt_const.add
      ((analyticAt_id.sub analyticAt_const).mul hHan)
  have hGne : G 1 ≠ 0 := by
    simpa [G] using (Complex.ofReal_ne_zero.mpr hc)
  rw [meromorphicOrderAt_eq_int_iff (hmero 1 hmem)]
  refine ⟨G, hGan, hGne, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [hexp z]
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  simp only [G, zpow_neg_one, smul_eq_mul]
  field_simp [hsub]

/-- Proposition VI.3.1(a): the Euler product over all prime ideals agrees
with the Dedekind zeta function on `Re(s)>1`, whose continuation has a
simple pole by Corollary 2.12. -/
theorem all_primes
    (hbridge : SetEulerBridge K)
    (h212 : (DedekindContinuationConclusion K)) : AllPolarDensity K := by
  rcases h212 with ⟨hagree, hmero, hdiff, hhol, hexp, hres, hc, hformula⟩
  refine ⟨1, 1, ?_, by norm_num⟩
  refine ⟨Nat.one_pos, dedekindZetaContinuation K,
    ?_, ?_, ?_⟩
  · let b : ℝ := 1 - 1 / (numberFieldDegree K : ℝ)
    have hb : b < 1 := ray_error_exponent K
    exact hmero 1 (by simpa [b] using hb)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxComplex : 1 < ((x : ℂ).re) := by simpa using hx
    rw [hagree (x : ℂ) hxComplex, ← hbridge.univ_dedekind_zeta x hx]
    simp
  · exact meromorphic_zeta_continuation
      K ⟨hagree, hmero, hdiff, hhol, hexp, hres, hc, hformula⟩

/-- The exact source proposition follows from Corollary 2.12 and the narrow
initial-half-plane Euler-product bridge above. -/
theorem euler_clauses_bridge
    (hbridge : SetEulerBridge K)
    (h212 : (DedekindContinuationConclusion K)) :
    EulerDensityLaws K := by
  exact ⟨all_primes K hbridge h212,
    eulerClausesNonnegative K,
    two_out_three K hbridge,
    eulerClausesMonotone K hbridge,
    euler_clauses_density K⟩

end

end Submission.CField.PDensit
