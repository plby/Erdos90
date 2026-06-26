import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!
# Milne, Chapter 8, Definition 8.30: natural density of prime ideals

For a set `S` of finite primes of a number field, Milne defines its natural
density by counting primes of absolute norm at most `N` and comparing that
count with the corresponding count for all finite primes.
-/

namespace Submission.NumberTheory.Milne

open Filter IsDedekindDomain NumberField Topology

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def primeAboveRational
    (p : {p : ℕ // p.Prime}) : HeightOneSpectrum (𝓞 K) := by
  let pIdeal : Ideal ℤ := Ideal.span {(p.1 : ℤ)}
  letI : pIdeal.IsPrime :=
    Ideal.isPrime_of_prime
      (Ideal.prime_span_singleton_iff.mpr
        (Nat.prime_iff_prime_int.mp p.2))
  let P : pIdeal.primesOver (𝓞 K) := Classical.choice (Ideal.nonempty_primesOver pIdeal)
  exact
    ⟨P.1, P.2.1,
      Ideal.ne_bot_of_mem_primesOver
        (Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast p.2.ne_zero)) P.2⟩

private theorem above_rational_injective :
    Function.Injective (primeAboveRational K) := by
  intro p q hpq
  let pIdeal : Ideal ℤ := Ideal.span {(p.1 : ℤ)}
  let qIdeal : Ideal ℤ := Ideal.span {(q.1 : ℤ)}
  letI : pIdeal.IsPrime :=
    Ideal.isPrime_of_prime
      (Ideal.prime_span_singleton_iff.mpr
        (Nat.prime_iff_prime_int.mp p.2))
  letI : qIdeal.IsPrime :=
    Ideal.isPrime_of_prime
      (Ideal.prime_span_singleton_iff.mpr
        (Nat.prime_iff_prime_int.mp q.2))
  have hp_over :
      pIdeal = (primeAboveRational K p).asIdeal.under ℤ :=
    (Classical.choice (Ideal.nonempty_primesOver pIdeal)).2.2.over
  have hq_over :
      qIdeal = (primeAboveRational K q).asIdeal.under ℤ :=
    (Classical.choice (Ideal.nonempty_primesOver qIdeal)).2.2.over
  have hpqIdeal : pIdeal = qIdeal := by
    rw [hp_over, hq_over, hpq]
  apply Subtype.ext
  have hassociated : Associated (p.1 : ℤ) (q.1 : ℤ) :=
    Ideal.span_singleton_eq_span_singleton.mp hpqIdeal
  simpa [Int.associated_iff_natAbs] using hassociated

/-- Every number field has infinitely many finite primes. -/
theorem infinite_primeIdeals : Infinite (HeightOneSpectrum (𝓞 K)) := by
  letI : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOf_prime.to_subtype
  exact Infinite.of_injective _ (above_rational_injective K)

/-- The number of finite primes in `S` whose absolute norm is at most `N`. -/
noncomputable def primeIdealCount
    (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) : ℕ :=
  Nat.card {p : HeightOneSpectrum (𝓞 K) // p ∈ S ∧ p.asIdeal.absNorm ≤ N}

/-- The bounded set used in `primeIdealCount` is finite. -/
theorem ideals_abs_norm
    (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    {p : HeightOneSpectrum (𝓞 K) | p ∈ S ∧ p.asIdeal.absNorm ≤ N}.Finite := by
  exact
    (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le N).subset
      fun p hp ↦ hp.2

/-- Milne, Definition 8.30. A set of finite primes has natural density `δ`
if the proportion of primes of norm at most `N` that lie in the set tends to
`δ` as `N → ∞`. -/
def PNDensit
    (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto
    (fun N : ℕ ↦
      (primeIdealCount K S N : ℝ) /
        primeIdealCount K Set.univ N)
    atTop (nhds δ)

/-- The number of finite primes of bounded absolute norm tends to infinity. -/
theorem tendsto_univ_top :
    Tendsto (primeIdealCount K Set.univ) atTop atTop := by
  classical
  letI : Infinite (HeightOneSpectrum (𝓞 K)) := infinite_primeIdeals K
  refine tendsto_atTop.2 fun b ↦ ?_
  obtain ⟨s, hs⟩ := Finset.exists_card_eq
    (α := HeightOneSpectrum (𝓞 K)) b
  let B : ℕ := s.sup fun p ↦ p.asIdeal.absNorm
  filter_upwards [eventually_ge_atTop B] with N hN
  change b ≤ {p | p ∈ (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ∧
    p.asIdeal.absNorm ≤ N}.ncard
  have hsubset : (↑s : Set (HeightOneSpectrum (𝓞 K))) ⊆
      {p | p ∈ (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ∧
        p.asIdeal.absNorm ≤ N} := by
    intro p hp
    exact ⟨Set.mem_univ p, (Finset.le_sup hp).trans hN⟩
  calc
    b = s.card := hs.symm
    _ = (↑s : Set (HeightOneSpectrum (𝓞 K))).ncard := by simp
    _ ≤ {p | p ∈ (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ∧
          p.asIdeal.absNorm ≤ N}.ncard :=
      Set.ncard_le_ncard hsubset (ideals_abs_norm K Set.univ N)

/-- The set of all finite primes has natural density one. -/
theorem natural_density_univ :
    PNDensit K Set.univ 1 := by
  unfold PNDensit
  have hpos : ∀ᶠ N in atTop, 0 < primeIdealCount K Set.univ N :=
    (tendsto_univ_top K).eventually (eventually_gt_atTop 0)
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [hpos] with N hN
  simp [Nat.ne_of_gt hN]

/-- A finite set of finite primes has natural density zero. -/
theorem prime_natural_density
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    PNDensit K S 0 := by
  unfold PNDensit
  have hdenom :
      Tendsto (fun N : ℕ ↦ (primeIdealCount K Set.univ N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_univ_top K)
  have hupper :
      Tendsto
        (fun N : ℕ ↦ (S.ncard : ℝ) / primeIdealCount K Set.univ N)
        atTop (nhds 0) :=
    hdenom.const_div_atTop (S.ncard : ℝ)
  exact squeeze_zero
    (fun N : ℕ ↦ by positivity)
    (fun N : ℕ ↦ by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hcount : primeIdealCount K S N ≤ S.ncard := by
        change {p | p ∈ S ∧ p.asIdeal.absNorm ≤ N}.ncard ≤ S.ncard
        exact Set.ncard_le_ncard (fun _ hp ↦ hp.1) hS
      exact_mod_cast hcount)
    hupper

/-- Any set of finite primes with positive natural density is infinite. -/
theorem Set.Infinite.prime_ideal_densi
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hS : PNDensit K S δ) (hδ : 0 < δ) :
    S.Infinite := by
  intro hfinite
  have hzero := prime_natural_density K hfinite
  have : δ = 0 := tendsto_nhds_unique hS hzero
  exact hδ.ne' this

private theorem count_union_disjoint
    {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : Disjoint S T) (N : ℕ) :
    primeIdealCount K (S ∪ T) N =
      primeIdealCount K S N + primeIdealCount K T N := by
  unfold primeIdealCount
  change
    {p : HeightOneSpectrum (𝓞 K) | p ∈ S ∪ T ∧ p.asIdeal.absNorm ≤ N}.ncard =
      {p : HeightOneSpectrum (𝓞 K) | p ∈ S ∧ p.asIdeal.absNorm ≤ N}.ncard +
        {p : HeightOneSpectrum (𝓞 K) | p ∈ T ∧ p.asIdeal.absNorm ≤ N}.ncard
  let A := {p : HeightOneSpectrum (𝓞 K) | p ∈ S ∧ p.asIdeal.absNorm ≤ N}
  let B := {p : HeightOneSpectrum (𝓞 K) | p ∈ T ∧ p.asIdeal.absNorm ≤ N}
  have hset :
      {p : HeightOneSpectrum (𝓞 K) | p ∈ S ∪ T ∧ p.asIdeal.absNorm ≤ N} = A ∪ B := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, A, B]
    aesop
  have hA : A.Finite := ideals_abs_norm K S N
  have hB : B.Finite := ideals_abs_norm K T N
  have hAB : Disjoint A B :=
    hST.mono (fun _ hp ↦ hp.1) (fun _ hp ↦ hp.1)
  rw [hset, Set.ncard_union_eq hAB hA hB]

/-- Natural density is additive on disjoint sets of finite primes. -/
theorem PNDensit.union_of_disjoint
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}
    (hS : PNDensit K S δ)
    (hT : PNDensit K T ε)
    (hST : Disjoint S T) :
    PNDensit K (S ∪ T) (δ + ε) := by
  unfold PNDensit at hS hT ⊢
  convert hS.add hT using 1
  funext N
  rw [count_union_disjoint K hST]
  push_cast
  ring

/-- The complement of a set of density `δ` has density `1 - δ`. -/
theorem PNDensit.compl
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hS : PNDensit K S δ) :
    PNDensit K Sᶜ (1 - δ) := by
  have hcount (N : ℕ) :
      primeIdealCount K Set.univ N =
        primeIdealCount K S N + primeIdealCount K Sᶜ N := by
    rw [← count_union_disjoint K disjoint_compl_right]
    congr 1
    exact (Set.union_compl_self S).symm
  unfold PNDensit at hS ⊢
  have hall := natural_density_univ K
  unfold PNDensit at hall
  convert hall.sub hS using 1
  · funext N
    rw [hcount]
    push_cast
    ring

/-- Removing a finite set of primes does not change natural density. -/
theorem PNDensit.diff_of_finite
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hS : PNDensit K S δ) (hT : T.Finite) :
    PNDensit K (S \ T) δ := by
  have hST : (S ∩ T).Finite := hT.subset Set.inter_subset_right
  have hSTzero := prime_natural_density K hST
  unfold PNDensit at hS hSTzero ⊢
  have hcount (N : ℕ) :
      primeIdealCount K S N =
        primeIdealCount K (S \ T) N + primeIdealCount K (S ∩ T) N := by
    rw [← count_union_disjoint K
      (Set.disjoint_left.2 fun _ hx hy ↦ hx.2 hy.2)]
    congr 1
    exact (Set.diff_union_inter S T).symm
  convert hS.sub hSTzero using 1
  · funext N
    rw [hcount]
    push_cast
    ring
  · ring_nf

/-- A subset of a density-zero set of finite primes also has density zero. -/
theorem PNDensit.mono_zero
    {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : PNDensit K T 0) (hST : S ⊆ T) :
    PNDensit K S 0 := by
  unfold PNDensit at hT ⊢
  exact squeeze_zero
    (fun N : ℕ ↦ by positivity)
    (fun N : ℕ ↦ by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hcount : primeIdealCount K S N ≤ primeIdealCount K T N := by
        apply Set.ncard_le_ncard
        · intro p hp
          exact ⟨hST hp.1, hp.2⟩
        · exact ideals_abs_norm K T N
      exact_mod_cast hcount)
    hT

/-- Removing a density-zero set of primes does not change natural density. -/
theorem PNDensit.diff_density_zero
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hS : PNDensit K S δ)
    (hT : PNDensit K T 0) :
    PNDensit K (S \ T) δ := by
  have hSTzero : PNDensit K (S ∩ T) 0 :=
    hT.mono_zero K Set.inter_subset_right
  unfold PNDensit at hS hSTzero ⊢
  have hcount (N : ℕ) :
      primeIdealCount K S N =
        primeIdealCount K (S \ T) N + primeIdealCount K (S ∩ T) N := by
    rw [← count_union_disjoint K
      (Set.disjoint_left.2 fun _ hx hy ↦ hx.2 hy.2)]
    congr 1
    exact (Set.diff_union_inter S T).symm
  convert hS.sub hSTzero using 1
  · funext N
    rw [hcount]
    push_cast
    ring
  · ring_nf

/-- Sets of primes that differ by only finitely many elements have the same
natural density.  This is the density-theoretic step in Milne's Remark
8.40(a). -/
theorem PNDensit.congr_fin_diff
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hS : PNDensit K S δ)
    (hST : (S \ T).Finite) (hTS : (T \ S).Finite) :
    PNDensit K T δ := by
  have hcommon : PNDensit K (S ∩ T) δ := by
    have := hS.diff_of_finite K hST
    have hset : S \ (S \ T) = S ∩ T := by
      ext p
      simp only [Set.mem_diff, Set.mem_inter_iff]
      tauto
    rw [hset] at this
    exact this
  have hnew : PNDensit K (T \ S) 0 :=
    prime_natural_density K hTS
  have hdisjoint : Disjoint (T \ S) (S ∩ T) := by
    exact Set.disjoint_left.2 fun _ hx hy ↦ hx.2 hy.1
  have hunion := hnew.union_of_disjoint K hcommon hdisjoint
  convert hunion using 1
  · ext p
    constructor
    · intro hpT
      by_cases hpS : p ∈ S
      · exact Or.inr ⟨hpS, hpT⟩
      · exact Or.inl ⟨hpT, hpS⟩
    · intro hp
      rcases hp with hp | hp
      · exact hp.1
      · exact hp.2
  · ring

/-- Sets of primes whose two directed differences have density zero have the
same natural density.  This is the density-zero form of Milne's Remark
8.40(a). -/
theorem PNDensit.congr_density_zerodiff
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hS : PNDensit K S δ)
    (hST : PNDensit K (S \ T) 0)
    (hTS : PNDensit K (T \ S) 0) :
    PNDensit K T δ := by
  have hcommon : PNDensit K (S ∩ T) δ := by
    have h := hS.diff_density_zero K hST
    have hset : S \ (S \ T) = S ∩ T := by
      ext p
      simp only [Set.mem_diff, Set.mem_inter_iff]
      tauto
    rw [hset] at h
    exact h
  have hdisjoint : Disjoint (T \ S) (S ∩ T) :=
    Set.disjoint_left.2 fun _ hx hy ↦ hx.2 hy.1
  have hunion := hTS.union_of_disjoint K hcommon hdisjoint
  convert hunion using 1
  · ext p
    constructor
    · intro hpT
      by_cases hpS : p ∈ S
      · exact Or.inr ⟨hpS, hpT⟩
      · exact Or.inl ⟨hpT, hpS⟩
    · intro hp
      rcases hp with hp | hp
      · exact hp.1
      · exact hp.2
  · ring

end Submission.NumberTheory.Milne
