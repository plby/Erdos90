import Towers.NumberTheory.Locals.UniformizerSeries
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Uniformizer expansions

This file proves the valuation-ring part of Milne's Proposition 7.26. In a
complete nonarchimedean normed field, every integral element has a unique
convergent expansion in powers of a uniformizer with coefficients in a fixed
set of residue representatives.
-/

namespace Towers.NumberTheory.Milne

open Filter
open scoped Topology

noncomputable section

/-- The norm-theoretic uniformizer condition. Besides `0 < ‖pi‖ < 1`, it says
that every element of the maximal ideal is divisible by `pi` with quotient in
the valuation ring. -/
def IsNormUniformizer {K : Type*} [NormedField K] (pi : K) : Prop :=
  pi ≠ 0 ∧ ‖pi‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x / pi‖ ≤ 1

/-- A set of representatives for the residue field of the norm valuation
ring. Congruence modulo the maximal ideal is expressed by `‖x - a‖ < 1`. -/
def RRSet {K : Type*} [NormedField K] (S : Set K) : Prop :=
  (∀ a ∈ S, ‖a‖ ≤ 1) ∧
    ∀ x : K, ‖x‖ ≤ 1 → ∃! a : K, a ∈ S ∧ ‖x - a‖ < 1

private theorem RRSet.eq_normsub_ltone
    {K : Type*} [NormedField K] {S : Set K}
    (hS : RRSet S)
    {a b : K} (ha : a ∈ S) (hb : b ∈ S) (hab : ‖a - b‖ < 1) :
    a = b := by
  exact (hS.2 a (hS.1 a ha)).unique
    ⟨ha, by simp⟩ ⟨hb, hab⟩

private theorem normalized_uniformizer_tail
    {K : Type*} [NormedField K]
    {pi : K} (hpi : pi ≠ 0) {a : ℕ → K} {x : K}
    (ha : HasSum (fun n => a n * pi ^ n) x) (N : ℕ) :
    HasSum (fun n => a (n + N) * pi ^ n)
      ((x - ∑ n ∈ Finset.range N, a n * pi ^ n) / pi ^ N) := by
  have htail := (hasSum_nat_add_iff' N).2 ha
  have hscaled := htail.mul_right (pi ^ N)⁻¹
  simpa [div_eq_mul_inv, pow_add, hpi, mul_assoc] using hscaled

private theorem sub_first_digit
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {pi x : K} (hpi : ‖pi‖ < 1) {a : ℕ → K}
    (ha_norm : ∀ n, ‖a n‖ ≤ 1)
    (ha : HasSum (fun n => a n * pi ^ n) x) :
    ‖x - a 0‖ < 1 := by
  have htail : HasSum (fun n => a (n + 1) * pi ^ (n + 1)) (x - a 0) := by
    simpa using (hasSum_nat_add_iff' 1).2 ha
  have hbound : ‖x - a 0‖ ≤ ‖pi‖ := by
    apply le_of_tendsto htail.tendsto_sum_nat.norm
    filter_upwards [] with N
    change ‖∑ n ∈ Finset.range N, a (n + 1) * pi ^ (n + 1)‖₊ ≤ ‖pi‖₊
    refine (Finset.nnnorm_sum_le_sup_nnnorm _ _).trans (Finset.sup_le fun n hn => ?_)
    exact_mod_cast (show ‖a (n + 1) * pi ^ (n + 1)‖ ≤ ‖pi‖ by
      rw [norm_mul, norm_pow, pow_succ]
      calc
        ‖a (n + 1)‖ * (‖pi‖ ^ n * ‖pi‖) ≤
            1 * (‖pi‖ ^ n * ‖pi‖) := by
              gcongr
              exact ha_norm (n + 1)
        _ ≤ 1 * (1 * ‖pi‖) := by
              gcongr
              exact pow_le_one₀ (norm_nonneg pi) hpi.le
        _ = ‖pi‖ := by ring)
  exact hbound.trans_lt hpi

/-- Milne, Proposition 7.26, valuation-ring form: every element of norm at
most one has a unique expansion in nonnegative powers of a uniformizer, with
digits in a prescribed set of residue representatives. -/
theorem unique_uniformizer_expansion
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K]
    {pi : K} (hpi : IsNormUniformizer pi)
    {S : Set K} (hS : RRSet S)
    (x : K) (hx : ‖x‖ ≤ 1) :
    ∃! a : ℕ → K,
      (∀ n, a n ∈ S) ∧ HasSum (fun n => a n * pi ^ n) x := by
  classical
  let rep : K → K := fun y =>
    if hy : ‖y‖ ≤ 1 then Classical.choose (hS.2 y hy) else 0
  have rep_mem (y : K) (hy : ‖y‖ ≤ 1) : rep y ∈ S := by
    dsimp [rep]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hS.2 y hy)).1.1
  have rep_close (y : K) (hy : ‖y‖ ≤ 1) : ‖y - rep y‖ < 1 := by
    dsimp [rep]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hS.2 y hy)).1.2
  let step : ℕ → K → K := fun _ y => (y - rep y) / pi
  let r : ℕ → K := fun n => Nat.rec x step n
  let a : ℕ → K := fun n => rep (r n)
  have hr_norm : ∀ n, ‖r n‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simpa [r] using hx
    | succ n ih =>
        rw [show r (n + 1) = (r n - rep (r n)) / pi by simp [r, step]]
        exact hpi.2.2 (r n - rep (r n)) (rep_close (r n) ih)
  have ha_mem : ∀ n, a n ∈ S := fun n => rep_mem (r n) (hr_norm n)
  have hr_step (n : ℕ) : r n = a n + pi * r (n + 1) := by
    rw [show r (n + 1) = (r n - rep (r n)) / pi by simp [r, step]]
    dsimp [a]
    rw [mul_div_cancel₀ _ hpi.1]
    ring
  have hremainder (N : ℕ) :
      x = (∑ n ∈ Finset.range N, a n * pi ^ n) + pi ^ N * r N := by
    induction N with
    | zero => simp [r]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, hr_step N, pow_succ]
        ring
  have hpartial :
      Tendsto (fun N => ∑ n ∈ Finset.range N, a n * pi ^ n) atTop (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (g := fun N => ‖pi‖ ^ N)
    · intro N
      rw [hremainder N]
      have heq :
          (∑ n ∈ Finset.range N, a n * pi ^ n) -
              ((∑ n ∈ Finset.range N, a n * pi ^ n) + pi ^ N * r N) =
            -(pi ^ N * r N) := by ring
      rw [heq, norm_neg, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg pi) N) (hr_norm N)
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg pi) hpi.2.1
  have ha_norm : ∀ n, ‖a n‖ ≤ 1 := fun n => hS.1 (a n) (ha_mem n)
  have ha_sum : HasSum (fun n => a n * pi ^ n) x := by
    have hs := (summable_norm_one a pi ha_norm hpi.2.1).hasSum
    have heq := tendsto_nhds_unique hs.tendsto_sum_nat hpartial
    simpa [heq] using hs
  refine ⟨a, ⟨ha_mem, ha_sum⟩, ?_⟩
  intro b hb
  rcases hb with ⟨hb_mem, hb_sum⟩
  funext N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      have hpref :
          (∑ n ∈ Finset.range N, a n * pi ^ n) =
            ∑ n ∈ Finset.range N, b n * pi ^ n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [ih n (Finset.mem_range.mp hn)]
      let y := (x - ∑ n ∈ Finset.range N, a n * pi ^ n) / pi ^ N
      have ha_tail : HasSum (fun n => a (n + N) * pi ^ n) y :=
        normalized_uniformizer_tail hpi.1 ha_sum N
      have hb_tail : HasSum (fun n => b (n + N) * pi ^ n) y := by
        simpa [y, hpref] using
          (normalized_uniformizer_tail hpi.1 hb_sum N)
      have ha_close : ‖y - a N‖ < 1 := by
        simpa using sub_first_digit hpi.2.1
          (fun n => ha_norm (n + N)) ha_tail
      have hb_norm : ∀ n, ‖b n‖ ≤ 1 := fun n => hS.1 (b n) (hb_mem n)
      have hb_close : ‖y - b N‖ < 1 := by
        simpa using sub_first_digit hpi.2.1
          (fun n => hb_norm (n + N)) hb_tail
      symm
      apply hS.eq_normsub_ltone (ha_mem N) (hb_mem N)
      calc
        ‖a N - b N‖ = ‖(a N - y) + (y - b N)‖ := by ring_nf
        _ ≤ max ‖a N - y‖ ‖y - b N‖ := IsUltrametricDist.norm_add_le_max _ _
        _ < 1 := max_lt (by rw [norm_sub_rev]; exact ha_close) hb_close

private theorem norm_pow_uniformizer
    {K : Type*} [NontriviallyNormedField K]
    {pi : K} (hpi : IsNormUniformizer pi) (x : K) :
    ∃ N : ℕ, ‖pi ^ N * x‖ ≤ 1 := by
  have hpow : Tendsto (fun N : ℕ => ‖pi‖ ^ N * ‖x‖) atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (norm_nonneg pi) hpi.2.1).mul_const ‖x‖
  have heventually : ∀ᶠ N in atTop, ‖pi‖ ^ N * ‖x‖ < 1 :=
    (tendsto_order.1 hpow).2 1 zero_lt_one
  rcases eventually_atTop.1 heventually with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  rw [norm_mul, norm_pow]
  exact (hN N le_rfl).le

/-- The canonical pole order used to remove the leading-zero ambiguity from
a Laurent expansion: it is the least `N` for which `pi ^ N * x` is integral. -/
def uniformizerPoleOrder
    {K : Type*} [NontriviallyNormedField K]
    {pi : K} (hpi : IsNormUniformizer pi) (x : K) : ℕ :=
  Nat.find (norm_pow_uniformizer hpi x)

/-- Multiplication by the canonical pole-clearing power makes `x` integral. -/
theorem uniformizer_pole_order
    {K : Type*} [NontriviallyNormedField K]
    {pi : K} (hpi : IsNormUniformizer pi) (x : K) :
    ‖pi ^ uniformizerPoleOrder hpi x * x‖ ≤ 1 :=
  Nat.find_spec (norm_pow_uniformizer hpi x)

/-- The canonical pole order is minimal among powers that make `x` integral. -/
theorem uniformizer_pole
    {K : Type*} [NontriviallyNormedField K]
    {pi : K} (hpi : IsNormUniformizer pi) (x : K) (N : ℕ)
    (hN : ‖pi ^ N * x‖ ≤ 1) :
    uniformizerPoleOrder hpi x ≤ N :=
  Nat.find_min' (norm_pow_uniformizer hpi x) hN

/-- Milne, Proposition 7.26, canonical field form: after fixing the least
pole-clearing exponent, every field element has a unique digit sequence for
its Laurent expansion. -/
theorem unique_uniformizer_laurent
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K]
    {pi : K} (hpi : IsNormUniformizer pi)
    {S : Set K} (hS : RRSet S)
    (x : K) :
    ∃! a : ℕ → K,
      (∀ n, a n ∈ S) ∧
        HasSum (fun n =>
          a n * pi ^ n / pi ^ uniformizerPoleOrder hpi x) x := by
  let N := uniformizerPoleOrder hpi x
  have hxN : ‖pi ^ N * x‖ ≤ 1 :=
    uniformizer_pole_order hpi x
  obtain ⟨a, ha, haUnique⟩ :=
    unique_uniformizer_expansion hpi hS (pi ^ N * x) hxN
  refine ⟨a, ⟨ha.1, ?_⟩, ?_⟩
  · simpa [N, hpi.1] using ha.2.div_const (pi ^ N)
  · intro b hb
    apply haUnique
    refine ⟨hb.1, ?_⟩
    have hscaled := hb.2.mul_right (pi ^ N)
    have hpowne : pi ^ N ≠ 0 := pow_ne_zero _ hpi.1
    convert hscaled using 1
    · funext i
      dsimp
      rw [show uniformizerPoleOrder hpi x = N by rfl]
      field_simp
    · ring

/-- Milne, Proposition 7.26, field form: every field element has a convergent
Laurent expansion with only finitely many negative powers of the uniformizer.
The natural number `N` records the order of the possible pole. -/
theorem uniformizer_laurent_expansion
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K]
    {pi : K} (hpi : IsNormUniformizer pi)
    {S : Set K} (hS : RRSet S)
    (x : K) :
    ∃ N : ℕ, ∃ a : ℕ → K,
      (∀ n, a n ∈ S) ∧ HasSum (fun n => a n * pi ^ n / pi ^ N) x := by
  let N := uniformizerPoleOrder hpi x
  obtain ⟨a, ha, -⟩ :=
    unique_uniformizer_laurent hpi hS x
  exact ⟨N, a, ha⟩

end

end Towers.NumberTheory.Milne
