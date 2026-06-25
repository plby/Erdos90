import Mathlib.Data.Nat.Prime.Infinite
import Towers.NumberTheory.Density.PrimeIdealNatural

/-!
# Class Field Theory, Introduction: ignoring finitely many primes

Milne observes after Theorem 0.1 that a fixed finite set of finite primes may
be omitted from the discussion.  This file proves the corresponding statement
for natural density: removing finitely many prime ideals does not change it.
-/

namespace Towers.CField.Examples

open Filter IsDedekindDomain NumberField Topology
open scoped NumberField

open Towers.NumberTheory.Milne

noncomputable section

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

private theorem infinite_primeIdeals : Infinite (HeightOneSpectrum (𝓞 K)) := by
  letI : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOf_prime.to_subtype
  exact Infinite.of_injective _ (above_rational_injective K)

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

private theorem eventually_diff_add
    (S F : Set (HeightOneSpectrum (𝓞 K))) (hF : F.Finite) :
    ∀ᶠ N in atTop,
      primeIdealCount K (S \ F) N + (S ∩ F).ncard = primeIdealCount K S N := by
  classical
  let B : ℕ := hF.toFinset.sup fun p ↦ p.asIdeal.absNorm
  filter_upwards [eventually_ge_atTop B] with N hN
  let A : Set (HeightOneSpectrum (𝓞 K)) :=
    {p | p ∈ S ∧ p.asIdeal.absNorm ≤ N}
  have hnorm (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ F) :
      p.asIdeal.absNorm ≤ N :=
    (Finset.le_sup (hF.mem_toFinset.mpr hp)).trans hN
  have hdiff : A \ F = {p | p ∈ S \ F ∧ p.asIdeal.absNorm ≤ N} := by
    ext p
    simp only [A, Set.mem_diff, Set.mem_setOf_eq]
    tauto
  have hinter : A ∩ F = S ∩ F := by
    ext p
    simp only [A, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hpS, -⟩, hpF⟩
      exact ⟨hpS, hpF⟩
    · rintro ⟨hpS, hpF⟩
      exact ⟨⟨hpS, hnorm p hpF⟩, hpF⟩
  have hcard := Set.ncard_inter_add_ncard_diff_eq_ncard A F
    (hs := ideals_abs_norm K S N)
  rw [hinter, hdiff] at hcard
  simpa [primeIdealCount, Nat.card_coe_set_eq, Nat.add_comm] using hcard

/-- Removing a finite set of finite primes does not change natural density.

This is the observation immediately following Milne's introductory problems
0.2 and 0.3.
-/
theorem natural_density_diff
    {S F : Set (HeightOneSpectrum (𝓞 K))} {delta : ℝ}
    (hS : PNDensit K S delta) (hF : F.Finite) :
    PNDensit K (S \ F) delta := by
  unfold PNDensit at hS ⊢
  have hdenom :
      Tendsto (fun N : ℕ ↦ (primeIdealCount K Set.univ N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_univ_top K)
  have hremoved :
      Tendsto
        (fun N : ℕ ↦ ((S ∩ F).ncard : ℝ) /
          primeIdealCount K Set.univ N)
        atTop (nhds 0) :=
    hdenom.const_div_atTop ((S ∩ F).ncard : ℝ)
  have hlimit :
      Tendsto
        (fun N : ℕ ↦ (primeIdealCount K (S \ F) N : ℝ) /
          primeIdealCount K Set.univ N)
        atTop (nhds (delta - 0)) := by
    refine (hS.sub hremoved).congr' ?_
    filter_upwards [eventually_diff_add K S F hF] with N hcount
    rw [← hcount, Nat.cast_add]
    ring
  simpa using hlimit

end

end Towers.CField.Examples
