import Towers.Group.FilteredPresentation

/-!
# Finite-support bookkeeping for GS coefficient sequences

This file contains small, purely arithmetic lemmas about coefficient sequences used
with the filtered-presentation GS convolution API.
-/

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Convert a finite-range universal check into the equivalent `≤`-indexed form. -/
theorem forall_range_succ (P : ℕ → Prop) (N : ℕ) :
    (∀ n ∈ Finset.range (N + 1), P n) ↔ ∀ n, n ≤ N → P n := by
  constructor
  · intro h n hn
    apply h n
    simp
    omega
  · intro h n hn
    apply h n
    simp at hn
    omega

/-- Convert a finite-range existential into the equivalent `≤`-indexed form. -/
theorem exists_mem_le (P : ℕ → Prop) (N : ℕ) :
    (∃ n ∈ Finset.range (N + 1), P n) ↔ ∃ n, n ≤ N ∧ P n := by
  constructor
  · rintro ⟨n, hn, hp⟩
    refine ⟨n, ?_, hp⟩
    simp at hn
    omega
  · rintro ⟨n, hn, hp⟩
    refine ⟨n, ?_, hp⟩
    simp
    omega

/-- A natural sequence is supported in degrees `≤ B`. -/
def SSBound (b : ℕ → ℕ) (B : ℕ) : Prop :=
  ∀ n, B < n → b n = 0

/-- Transport a natural support bound across pointwise equality. -/
theorem SSBound.congr {b c : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (h : ∀ n, c n = b n) : SSBound c B := by
  intro n hn
  rw [h n]
  exact hb n hn

/-- A pointwise smaller natural sequence inherits a support bound. -/
theorem SSBound.of_le {b c : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (hcb : ∀ n, c n ≤ b n) : SSBound c B := by
  intro n hn
  have hz := hb n hn
  have hc0 : c n ≤ 0 := by simpa [hz] using hcb n
  exact Nat.eq_zero_of_le_zero hc0

/-- Monotonicity of support bounds. -/
theorem SSBound.mono {b : ℕ → ℕ} {B C : ℕ}
    (hb : SSBound b B) (hBC : B ≤ C) : SSBound b C := by
  intro n hn
  exact hb n (lt_of_le_of_lt hBC hn)

/-- A supported sequence has zero coefficients strictly above the bound (projection form). -/
theorem coeff_support_bound {b : ℕ → ℕ} {B n : ℕ}
    (hb : SSBound b B) (hn : B < n) : b n = 0 := hb n hn

/-- The zero sequence is supported at every bound. -/
@[simp] theorem seq_support_zero (B : ℕ) :
    SSBound (fun _ => 0) B := by
  intro n hn
  rfl

/-- A sequence supported at a single natural index is supported at that index. -/
theorem support_bound_single (k a : ℕ) :
    SSBound (fun n => if n = k then a else 0) k := by
  intro n hn
  have hne : n ≠ k := by omega
  simp [hne]

/-- A single-index natural sequence is supported at any later bound. -/
theorem seq_support_single {k B a : ℕ} (hk : k ≤ B) :
    SSBound (fun n => if n = k then a else 0) B := by
  exact (support_bound_single k a).mono hk

/-- Shifting a natural sequence left (dropping initial coefficients) preserves any coarse
support bound. -/
theorem SSBound.shiftLeft {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (k : ℕ) :
    SSBound (fun n => b (n + k)) B := by
  intro n hn
  exact hb (n + k) (by omega)

/-- Shifting a natural sequence to the right by `k` shifts its support bound by `k`. -/
theorem SSBound.shiftRight {b : ℕ → ℕ} {B : ℕ} (hb : SSBound b B)
    (k : ℕ) :
    SSBound (fun n => if k ≤ n then b (n - k) else 0) (B + k) := by
  intro n hn
  by_cases hk : k ≤ n
  · have harg : B < n - k := by omega
    simp [hk, hb (n - k) harg]
  · simp [hk]

/-- Filtering a supported natural sequence by a decidable predicate preserves support. -/
theorem SSBound.filter {b : ℕ → ℕ} {B : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (hb : SSBound b B) :
    SSBound (fun n => if P n then b n else 0) B := by
  apply hb.of_le
  intro n
  by_cases h : P n <;> simp [h]

/-- Pointwise maxima preserve a common support bound. -/
theorem SSBound.pointwise_max {b c : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (hc : SSBound c B) :
    SSBound (fun n => max (b n) (c n)) B := by
  intro n hn
  simp [hb n hn, hc n hn]

/-- Pointwise minima preserve a common support bound. -/
theorem SSBound.pointwise_min {b c : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (hc : SSBound c B) :
    SSBound (fun n => min (b n) (c n)) B := by
  intro n hn
  simp [hb n hn, hc n hn]

/-- Pointwise maxima preserve support at the maximum of two bounds. -/
theorem SSBound.pointwise_max_max {b c : ℕ → ℕ} {B C : ℕ}
    (hb : SSBound b B) (hc : SSBound c C) :
    SSBound (fun n => max (b n) (c n)) (max B C) := by
  intro n hn
  have hbn : B < n := lt_of_le_of_lt (le_max_left B C) hn
  have hcn : C < n := lt_of_le_of_lt (le_max_right B C) hn
  simp [hb n hbn, hc n hcn]

/-- A pointwise minimum is supported wherever its left factor is supported. -/
theorem SSBound.pointwise_min_left {b c : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    SSBound (fun n => min (b n) (c n)) B := by
  intro n hn
  simp [hb n hn]

/-- A pointwise minimum is supported wherever its right factor is supported. -/
theorem SSBound.pointwise_min_right {b c : ℕ → ℕ} {C : ℕ}
    (hc : SSBound c C) :
    SSBound (fun n => min (b n) (c n)) C := by
  intro n hn
  simp [hc n hn]

/-- Pointwise minima are supported at the smaller of two natural support bounds.
This is stronger than the corresponding maximum-bound statement because `min 0 x = 0`. -/
theorem SSBound.pointwise_min_min {b c : ℕ → ℕ} {B C : ℕ}
    (hb : SSBound b B) (hc : SSBound c C) :
    SSBound (fun n => min (b n) (c n)) (min B C) := by
  intro n hn
  rcases le_total B C with hBC | hCB
  · have hB : min B C = B := Nat.min_eq_left hBC
    have hbn : B < n := by simpa [hB] using hn
    simp [hb n hbn]
  · have hC : min B C = C := Nat.min_eq_right hCB
    have hcn : C < n := by simpa [hC] using hn
    simp [hc n hcn]

/-- Finite sums of natural sequences with a common support bound have that bound. -/
theorem SSBound.finset_sum {ι : Type*} {s : Finset ι} {b : ι → ℕ → ℕ}
    {B : ℕ} (hb : ∀ i ∈ s, SSBound (b i) B) :
    SSBound (fun n => ∑ i ∈ s, b i n) B := by
  intro n hn
  apply Finset.sum_eq_zero
  intro i hi
  exact hb i hi n hn

/-- Pointwise sums preserve a common support bound. -/
theorem SSBound.add {b c : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (hc : SSBound c B) :
    SSBound (fun n => b n + c n) B := by
  intro n hn
  simp [hb n hn, hc n hn]

/-- For natural sequences, support of a pointwise sum is equivalent to support of both
summands, since coefficients are nonnegative. -/
theorem seq_support_add {b c : ℕ → ℕ} {B : ℕ} :
    SSBound (fun n => b n + c n) B ↔
      SSBound b B ∧ SSBound c B := by
  constructor
  · intro h
    constructor
    · intro n hn
      have hs : b n + c n = 0 := h n hn
      exact Nat.eq_zero_of_add_eq_zero_right hs
    · intro n hn
      have hs : b n + c n = 0 := h n hn
      exact Nat.eq_zero_of_add_eq_zero_left hs
  · rintro ⟨hb, hc⟩
    exact hb.add hc

/-- Pointwise sums preserve support at the maximum of two (possibly different) bounds. -/
theorem SSBound.add_max {b c : ℕ → ℕ} {B C : ℕ}
    (hb : SSBound b B) (hc : SSBound c C) :
    SSBound (fun n => b n + c n) (max B C) := by
  intro n hn
  have hbn : B < n := lt_of_le_of_lt (le_max_left B C) hn
  have hcn : C < n := lt_of_le_of_lt (le_max_right B C) hn
  simp [hb n hbn, hc n hcn]

/-- Pointwise products preserve support at the left bound. -/
theorem SSBound.mul_left {b c : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    SSBound (fun n => b n * c n) B := by
  intro n hn
  simp [hb n hn]

/-- Pointwise products preserve support at the right bound. -/
theorem SSBound.mul_right {b c : ℕ → ℕ} {C : ℕ}
    (hc : SSBound c C) :
    SSBound (fun n => b n * c n) C := by
  intro n hn
  simp [hc n hn]

/-- Pointwise products are supported at the smaller of two support bounds. -/
theorem SSBound.mul_min {b c : ℕ → ℕ} {B C : ℕ}
    (hb : SSBound b B) (hc : SSBound c C) :
    SSBound (fun n => b n * c n) (min B C) := by
  intro n hn
  rcases le_total B C with hBC | hCB
  · have hB : min B C = B := Nat.min_eq_left hBC
    have hbn : B < n := by simpa [hB] using hn
    simp [hb n hbn]
  · have hC : min B C = C := Nat.min_eq_right hCB
    have hcn : C < n := by simpa [hC] using hn
    simp [hc n hcn]

/-- Multiplying a supported natural sequence by a fixed scalar preserves support. -/
theorem SSBound.const_mul {b : ℕ → ℕ} {B : ℕ} (a : ℕ)
    (hb : SSBound b B) :
    SSBound (fun n => a * b n) B := by
  intro n hn
  simp [hb n hn]

/-- Multiplication by a nonzero natural scalar reflects support. -/
theorem seq_support_const {b : ℕ → ℕ} {B a : ℕ} (ha : a ≠ 0) :
    SSBound (fun n => a * b n) B ↔ SSBound b B := by
  constructor
  · intro h n hn
    have hz : a * b n = 0 := h n hn
    exact (Nat.mul_eq_zero.mp hz).elim (fun haz => False.elim (ha haz)) id
  · intro hb
    exact SSBound.const_mul a hb

/-- Right-scalar version of `SSBound.const_mul`. -/
theorem SSBound.mul_const {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (a : ℕ) :
    SSBound (fun n => b n * a) B := by
  intro n hn
  simp [hb n hn]

/-- Right multiplication by a nonzero natural scalar reflects support. -/
theorem seq_bound_const {b : ℕ → ℕ} {B a : ℕ} (ha : a ≠ 0) :
    SSBound (fun n => b n * a) B ↔ SSBound b B := by
  simpa [Nat.mul_comm] using (seq_support_const (b := b) (B := B) (a := a) ha)

/-- Prefix sums of a supported sequence stabilize once the cutoff is at least the
support bound. -/
theorem range_support_bound {b : ℕ → ℕ} {B M N : ℕ}
    (hb : SSBound b B) (hBM : B ≤ M) (hMN : M ≤ N) :
    (∑ k ∈ Finset.range (N + 1), b k) =
      ∑ k ∈ Finset.range (M + 1), b k := by
  classical
  have hsubset : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp at hx ⊢
    omega
  rw [← Finset.sum_sdiff hsubset]
  have htail : ∑ x ∈ Finset.range (N + 1) \ Finset.range (M + 1), b x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxnot : x ∉ Finset.range (M + 1) := (Finset.mem_sdiff.mp hx).2
    have hxgt : B < x := by
      simp at hxnot
      omega
    exact hb x hxgt
  rw [htail, zero_add]


/-- Unordered form of prefix-sum stabilization for a supported sequence. -/
theorem sum_support_bound {b : ℕ → ℕ} {B M N : ℕ}
    (hb : SSBound b B) (hM : B ≤ M) (hN : B ≤ N) :
    (∑ k ∈ Finset.range (M + 1), b k) =
      ∑ k ∈ Finset.range (N + 1), b k := by
  rcases le_total M N with hMN | hNM
  · exact (range_support_bound hb hM hMN).symm
  · exact range_support_bound hb hN hNM

/-- Positivity of the prefix at the support bound propagates to every later prefix. -/
theorem pos_support_bound {b : ℕ → ℕ} {B M : ℕ}
    (hb : SSBound b B) (hBM : B ≤ M)
    (hpos : 0 < ∑ k ∈ Finset.range (B + 1), b k) :
    0 < ∑ k ∈ Finset.range (M + 1), b k := by
  rw [range_support_bound hb (le_rfl) hBM]
  exact hpos

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- If `b` is supported in degrees `≤ B`, then the relator convolution is supported
in degrees `≤ B + maxRelatorDepth`. -/
theorem convolution_support_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B n : ℕ}
    (hb : SSBound b B) (hn : B + FP.maxRelatorDepth < n) :
    FP.relatorDepthConvolution b n = 0 := by
  classical
  unfold relatorDepthConvolution relatorWeightedSum
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hq : FP.depths.depth r ≤ n
  · have hd : FP.depths.depth r ≤ FP.maxRelatorDepth := FP.depth_max_relator r
    have harg : B < n - FP.depths.depth r := by omega
    simp [hq, hb (n - FP.depths.depth r) harg]
  · simp [hq]

/-- The generator-shift contribution of a supported sequence vanishes one degree
after the support bound. -/
theorem shift_contribution_bound
    {b : ℕ → ℕ} {B n : ℕ} (hb : SSBound b B) (hn : B + 1 < n) :
    FP.generatorShiftContribution b n = 0 := by
  by_cases hpos : 0 < n
  · have harg : B < n - 1 := by omega
    simp [generatorShiftContribution, hpos, hb (n - 1) harg]
  · simp [generatorShiftContribution, hpos]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- The integer GS balance has finite support when the coefficient sequence does. -/
theorem gs_balance_support
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B n : ℕ}
    (hb : SSBound b B) (hn : B + FP.maxRelatorDepth + 1 < n) :
    FP.gsCoefficientBalance b n = 0 := by
  have hbzero : b n = 0 := hb n (by omega)
  have hczero : FP.relatorDepthConvolution b n = 0 :=
    FP.convolution_support_bound hb (by omega)
  have hszero : FP.generatorShiftContribution b n = 0 :=
    FP.shift_contribution_bound hb (by omega)
  simp [gsCoefficientBalance, hbzero, hczero, hszero]

/-- Consequently, prefix balance sums stabilize past the explicit support bound. -/
theorem gs_balance_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B M N : ℕ}
    (hb : SSBound b B) (hM : B + FP.maxRelatorDepth + 1 ≤ M)
    (hMN : M ≤ N) :
    FP.gsBalanceSum b N = FP.gsBalanceSum b M := by
  classical
  unfold gsBalanceSum
  -- Split the larger range into the prefix through `M` and the vanishing tail.
  have hsubset : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp at hx ⊢
    omega
  rw [← Finset.sum_sdiff hsubset]
  have htail : ∑ x ∈ Finset.range (N + 1) \ Finset.range (M + 1),
      FP.gsCoefficientBalance b x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxN : x ∈ Finset.range (N + 1) := (Finset.mem_sdiff.mp hx).1
    have hxM : x ∉ Finset.range (M + 1) := (Finset.mem_sdiff.mp hx).2
    simp at hxN hxM
    have hgt : B + FP.maxRelatorDepth + 1 < x := by omega
    exact FP.gs_balance_support hb hgt
  rw [htail, zero_add]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Support-bound wrapper for the relator convolution sequence. -/
theorem SSBound.relatorDepthConvolution
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    SSBound (fun n => FP.relatorDepthConvolution b n)
      (B + FP.maxRelatorDepth) := by
  intro n hn
  exact FP.convolution_support_bound hb hn

/-- Support-bound wrapper for generator shifts. -/
theorem SSBound.generatorShiftContribution {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    SSBound (fun n => FP.generatorShiftContribution b n) (B + 1) := by
  intro n hn
  exact FP.shift_contribution_bound hb hn

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Nat-valued prefix sum of relator convolutions. -/
noncomputable def relatorConvolutionPrefix [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), FP.relatorDepthConvolution b n

/-- Prefix of a coefficient sequence shifted by a depth `q`, with out-of-range
terms omitted. -/
noncomputable def shiftedCoefficientPrefix (b : ℕ → ℕ) (N q : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), if _h : q ≤ n then b (n - q) else 0

/-- Relator-convolution prefixes are monotone in the ambient cutoff. -/
theorem convolution_mono_cutoff {p : ℕ} (FP : FPres p)
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) {M N : ℕ} (hMN : M ≤ N) :
    FP.relatorConvolutionPrefix b M ≤ FP.relatorConvolutionPrefix b N := by
  classical
  unfold relatorConvolutionPrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp at hx ⊢
    omega
  · intro x hxN hxnot
    exact Nat.zero_le _

/-- Relator-convolution prefixes are monotone in the coefficient sequence. -/
theorem convolution_prefix_mono {p : ℕ} (FP : FPres p)
    [Fintype FP.toPresentation.Relator] {b c : ℕ → ℕ}
    (hbc : ∀ k, b k ≤ c k) (N : ℕ) :
    FP.relatorConvolutionPrefix b N ≤ FP.relatorConvolutionPrefix c N := by
  classical
  unfold relatorConvolutionPrefix
  apply Finset.sum_le_sum
  intro n hn
  exact FP.relator_convolution_mono hbc n

/-- Histogram/Fubini form of the convolution prefix sum. -/
theorem convolution_histogram_shifted
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (N : ℕ) :
    FP.relatorConvolutionPrefix b N =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
        FP.relatorDepthMultiplicity q * shiftedCoefficientPrefix b N q := by
  classical
  unfold relatorConvolutionPrefix shiftedCoefficientPrefix
  calc
    (∑ n ∈ Finset.range (N + 1), FP.relatorDepthConvolution b n) =
        ∑ n ∈ Finset.range (N + 1),
          ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
            FP.relatorDepthMultiplicity q *
              (if _h : q ≤ n then b (n - q) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact FP.convolution_histogram_sum b n
    _ = ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
          ∑ n ∈ Finset.range (N + 1),
            FP.relatorDepthMultiplicity q *
              (if _h : q ≤ n then b (n - q) else 0) := by
      exact Finset.sum_comm
    _ = ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
          FP.relatorDepthMultiplicity q *
            (∑ n ∈ Finset.range (N + 1),
              if _h : q ≤ n then b (n - q) else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [Finset.mul_sum]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- With zero shift, a shifted coefficient prefix is the ordinary prefix sum. -/
@[simp] theorem shifted_prefix_shift (b : ℕ → ℕ) (N : ℕ) :
    shiftedCoefficientPrefix b N 0 = ∑ n ∈ Finset.range (N + 1), b n := by
  classical
  unfold shiftedCoefficientPrefix
  apply Finset.sum_congr rfl
  intro n hn
  simp

/-- The degree-zero shifted prefix reads only the zeroth coefficient when the shift is zero. -/
@[simp] theorem shifted_prefix_zero (b : ℕ → ℕ) :
    shiftedCoefficientPrefix b 0 0 = b 0 := by
  simp [shifted_prefix_shift]

/-- If the shift exceeds the prefix length, the shifted prefix is zero. -/
theorem shifted_coefficient_prefix (b : ℕ → ℕ) {N q : ℕ}
    (hNq : N < q) : shiftedCoefficientPrefix b N q = 0 := by
  classical
  unfold shiftedCoefficientPrefix
  apply Finset.sum_eq_zero
  intro n hn
  have hnle : n ≤ N := by
    simpa using (Finset.mem_range.mp hn)
  have hnq : ¬ q ≤ n := by omega
  simp [hnq]

/-- A positive shift has zero prefix at cutoff zero. -/
@[simp] theorem shifted_prefix_succ (b : ℕ → ℕ) (q : ℕ) :
    shiftedCoefficientPrefix b 0 (q + 1) = 0 := by
  exact shifted_coefficient_prefix b (N := 0) (q := q + 1) (by omega)

/-- Shifted coefficient prefixes are monotone in the ambient cutoff. -/
theorem shifted_mono_cutoff (b : ℕ → ℕ) {M N q : ℕ}
    (hMN : M ≤ N) :
    shiftedCoefficientPrefix b M q ≤ shiftedCoefficientPrefix b N q := by
  classical
  unfold shiftedCoefficientPrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp at hx ⊢
    omega
  · intro x hxN hxnot
    by_cases h : q ≤ x <;> simp [h]

/-- Shifted coefficient prefixes are monotone in the coefficient sequence. -/
theorem shifted_prefix_mono {b c : ℕ → ℕ} (hbc : ∀ k, b k ≤ c k)
    (N q : ℕ) :
    shiftedCoefficientPrefix b N q ≤ shiftedCoefficientPrefix c N q := by
  classical
  unfold shiftedCoefficientPrefix
  apply Finset.sum_le_sum
  intro n hn
  by_cases h : q ≤ n
  · simp [h, hbc]
  · simp [h]

/-- Successor recurrence for shifted coefficient prefixes. -/
theorem shifted_coefficient_succ (b : ℕ → ℕ) (N q : ℕ) :
    shiftedCoefficientPrefix b (N + 1) q =
      shiftedCoefficientPrefix b N q +
        (if _h : q ≤ N + 1 then b (N + 1 - q) else 0) := by
  classical
  unfold shiftedCoefficientPrefix
  rw [Finset.sum_range_succ]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

@[simp] theorem shifted_coefficient_zero (b : ℕ → ℕ) (N : ℕ) :
    shiftedCoefficientPrefix b N 0 = ∑ n ∈ Finset.range (N + 1), b n := by
  classical
  unfold shiftedCoefficientPrefix
  simp

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- At the diagonal cutoff, a shifted prefix contains only the zeroth coefficient. -/
theorem shifted_prefix_self (b : ℕ → ℕ) (q : ℕ) :
    shiftedCoefficientPrefix b q q = b 0 := by
  induction q with
  | zero => simp [shiftedCoefficientPrefix]
  | succ q ih =>
      rw [shifted_coefficient_succ]
      have hz : shiftedCoefficientPrefix b q (q + 1) = 0 :=
        shifted_coefficient_prefix b (Nat.lt_succ_self q)
      simp [hz]

/-- Reindex a shifted prefix when the cutoff is written as `q + K`. -/
theorem shifted_prefix_right (b : ℕ → ℕ) (q K : ℕ) :
    shiftedCoefficientPrefix b (q + K) q =
      ∑ k ∈ Finset.range (K + 1), b k := by
  induction K with
  | zero =>
      simpa using shifted_prefix_self b q
  | succ K ih =>
      -- `q + (K+1)` is the successor of `q+K`.
      rw [show q + (K + 1) = q + K + 1 by omega]
      rw [shifted_coefficient_succ]
      rw [ih]
      have hle : q ≤ q + K + 1 := by omega
      have hsub : q + K + 1 - q = K + 1 := by omega
      rw [dif_pos hle, hsub]
      rw [Finset.sum_range_succ (f := b) (n := K + 1)]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Reindex a shifted prefix for an arbitrary cutoff above the shift. -/
theorem shifted_prefix_sub (b : ℕ → ℕ) {N q : ℕ}
    (hq : q ≤ N) :
    shiftedCoefficientPrefix b N q =
      ∑ k ∈ Finset.range (N - q + 1), b k := by
  have hN : q + (N - q) = N := Nat.add_sub_of_le hq
  calc
    shiftedCoefficientPrefix b N q = shiftedCoefficientPrefix b (q + (N - q)) q := by rw [hN]
    _ = ∑ k ∈ Finset.range ((N - q) + 1), b k :=
      shifted_prefix_right b q (N - q)

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Reindexed histogram form of the convolution prefix: for each depth `q`, only
coefficients through `N-q` contribute. -/
theorem convolution_histogram_reindexed
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (N : ℕ) :
    FP.relatorConvolutionPrefix b N =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
        FP.relatorDepthMultiplicity q *
          (if _h : q ≤ N then ∑ k ∈ Finset.range (N - q + 1), b k else 0) := by
  classical
  rw [FP.convolution_histogram_shifted b N]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : q ≤ N
  · simp [h, shifted_prefix_sub b h]
  · have hlt : N < q := Nat.lt_of_not_ge h
    simp [h, shifted_coefficient_prefix b hlt]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- The integer convolution prefix from the core file is the cast of the nat-valued prefix. -/
theorem convolution_coe_relator
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (N : ℕ) :
    FP.convolutionPrefixInt b N = (FP.relatorConvolutionPrefix b N : ℤ) := by
  classical
  unfold convolutionPrefixInt relatorConvolutionPrefix
  exact_mod_cast rfl

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Depth multiplicities vanish above the maximum certified depth. -/
theorem relator_multiplicity_max
    [Fintype FP.toPresentation.Relator] {q : ℕ} (hq : FP.maxRelatorDepth < q) :
    FP.relatorDepthMultiplicity q = 0 := by
  rw [← FP.exact_count_multiplicity q]
  exact FP.exact_relator_max hq

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Finite Cauchy coefficient of an integer sequence against a natural sequence. -/
noncomputable def cauchyCoeffNat (a : ℕ → ℤ) (b : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (n + 1), a q * (b (n - q) : ℤ)

/-- Kronecker-delta integer coefficient sequence. -/
def deltaCoeff (k : ℕ) (c : ℤ) : ℕ → ℤ := fun q => if q = k then c else 0

@[simp] theorem cauchy_nat_delta (c : ℤ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (deltaCoeff 0 c) b n = c * (b n : ℤ) := by
  classical
  unfold cauchyCoeffNat deltaCoeff
  -- only the `q=0` term survives
  calc
    (∑ q ∈ Finset.range (n + 1), (if q = 0 then c else 0) * (b (n - q) : ℤ)) =
        (if (0 : ℕ) ∈ Finset.range (n + 1) then c * (b (n - 0) : ℤ) else 0) := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro q hq hq0
        simp [hq0]
      · intro h0
        simp at h0
    _ = c * (b n : ℤ) := by simp

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Cauchy coefficient against a single delta term. -/
theorem coeff_nat_delta (k : ℕ) (c : ℤ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (deltaCoeff k c) b n =
      if _h : k ≤ n then c * (b (n - k) : ℤ) else 0 := by
  classical
  unfold cauchyCoeffNat deltaCoeff
  by_cases hk : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := by
      simp [Nat.lt_succ_of_le hk]
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro q hq hqk
      simp [hqk]
    · intro hknot
      exact False.elim (hknot hmem)
  · have hnot : k ∉ Finset.range (n + 1) := by
      simp only [Finset.mem_range, not_lt]
      omega
    rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro q hq
      have hqk : q ≠ k := by
        intro h; subst q; exact hnot hq
      simp [hqk]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Cauchy coefficients are additive in the integer coefficient sequence. -/
theorem cauchy_coeff_add (a a' : ℕ → ℤ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (fun q => a q + a' q) b n =
      cauchyCoeffNat a b n + cauchyCoeffNat a' b n := by
  classical
  unfold cauchyCoeffNat
  simp [add_mul, Finset.sum_add_distrib]

/-- Cauchy coefficients are negated by negating the integer coefficient sequence. -/
theorem cauchy_coeff_neg (a : ℕ → ℤ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (fun q => - a q) b n = - cauchyCoeffNat a b n := by
  classical
  unfold cauchyCoeffNat
  simp [Finset.sum_neg_distrib]

/-- Cauchy coefficients are subtractive in the integer coefficient sequence. -/
theorem cauchy_coeff_sub (a a' : ℕ → ℤ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (fun q => a q - a' q) b n =
      cauchyCoeffNat a b n - cauchyCoeffNat a' b n := by
  classical
  simp [sub_eq_add_neg, cauchy_coeff_add, cauchy_coeff_neg]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Integer Cauchy contribution of the finite relator-depth histogram at degree `n`. -/
noncomputable def relatorCauchyInt [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
    (FP.relatorDepthMultiplicity q : ℤ) *
      (if _h : q ≤ n then (b (n - q) : ℤ) else 0)

/-- The integer histogram Cauchy contribution is the cast of the nat convolution. -/
theorem cauchy_int_convolution
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    FP.relatorCauchyInt b n = (FP.relatorDepthConvolution b n : ℤ) := by
  classical
  rw [FP.convolution_histogram_sum b n]
  unfold relatorCauchyInt
  norm_num

/-- The displayed GS product coefficient: current term, relator histogram Cauchy
term, and the negative generator shift. -/
noncomputable def gsProductInt [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (n : ℕ) : ℤ :=
  (b n : ℤ) + FP.relatorCauchyInt b n -
    (FP.generatorShiftContribution b n : ℤ)

@[simp] theorem gs_int_balance
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    FP.gsProductInt b n = FP.gsCoefficientBalance b n := by
  unfold gsProductInt gsCoefficientBalance
  rw [FP.cauchy_int_convolution b n]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Product-coefficient nonnegativity is the same coefficientwise GS inequality. -/
theorem gs_inequality_nonneg
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientInequality b n ↔ 0 ≤ FP.gsProductInt b n := by
  rw [FP.gs_int_balance b n]
  exact FP.inequality_balance_nonneg b n

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- The degree-one delta Cauchy coefficient is a shifted coefficient. -/
theorem cauchy_delta_one (c : ℤ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (deltaCoeff 1 c) b n =
      if _h : 1 ≤ n then c * (b (n - 1) : ℤ) else 0 := by
  simpa using coeff_nat_delta 1 c b n

variable {p : ℕ} (FP : FPres p)

/-- The negative degree-one delta encodes the generator-shift term. -/
theorem cauchy_coeff_delta
    (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (deltaCoeff 1 (-(FP.generatorCount : ℤ))) b n =
      - (FP.generatorShiftContribution b n : ℤ) := by
  classical
  rw [cauchy_delta_one]
  by_cases hn : 1 ≤ n
  · have hpos : 0 < n := by omega
    simp [hn, generatorShiftContribution, hpos]
  · have hpos : ¬ 0 < n := by omega
    simp [hn, generatorShiftContribution, hpos]

/-- The degree-zero delta encodes the current coefficient term. -/
theorem cauchy_delta_zero (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (deltaCoeff 0 (1 : ℤ)) b n = (b n : ℤ) := by
  simp [cauchy_nat_delta]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- The ordinary Cauchy coefficient of the relator-depth multiplicity sequence is
its bounded histogram Cauchy contribution. -/
theorem cauchy_coeff_int
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (fun q => (FP.relatorDepthMultiplicity q : ℤ)) b n =
      FP.relatorCauchyInt b n := by
  classical
  unfold cauchyCoeffNat relatorCauchyInt
  let M := FP.maxRelatorDepth
  by_cases hnM : n ≤ M
  · have hsub : Finset.range (n + 1) ⊆ Finset.range (M + 1) := by
      intro q hq
      simp at hq ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro q hq
      have hqle : q ≤ n := by simpa using (Finset.mem_range.mp hq)
      simp [hqle]
    · intro q hqM hqnot
      have hqgt : n < q := by
        simp at hqM hqnot
        omega
      have hnleq : ¬ q ≤ n := by omega
      simp [hnleq]
  · have hMn : M ≤ n := by omega
    have hsub : Finset.range (M + 1) ⊆ Finset.range (n + 1) := by
      intro q hq
      simp at hq ⊢
      omega
    have hsumL :
        (∑ q ∈ Finset.range (n + 1),
          (FP.relatorDepthMultiplicity q : ℤ) * (b (n - q) : ℤ)) =
        ∑ q ∈ Finset.range (M + 1),
          (FP.relatorDepthMultiplicity q : ℤ) * (b (n - q) : ℤ) := by
      symm
      apply Finset.sum_subset hsub
      intro q hqn hqnot
      have hqgtM : M < q := by
        simp at hqn hqnot
        omega
      have hz : FP.relatorDepthMultiplicity q = 0 := by
        simpa [M] using FP.relator_multiplicity_max hqgtM
      simp [hz]
    rw [hsumL]
    apply Finset.sum_congr rfl
    intro q hq
    have hqleM : q ≤ M := by simpa using (Finset.mem_range.mp hq)
    have hqle : q ≤ n := by omega
    simp [hqle]

/-- The ordinary Cauchy coefficient of depth multiplicities is the integer cast of
relator convolution. -/
theorem cauchy_multiplicity_convolution
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (fun q => (FP.relatorDepthMultiplicity q : ℤ)) b n =
      (FP.relatorDepthConvolution b n : ℤ) := by
  rw [FP.cauchy_coeff_int b n,
    FP.cauchy_int_convolution b n]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- The formal GS polynomial coefficient sequence `1 - d t + \sum r_q t^q`,
where `d` is the generator count and `r_q` is the relator-depth histogram. -/
noncomputable def gsCoeffInt [Fintype FP.toPresentation.Relator] (q : ℕ) : ℤ :=
  deltaCoeff 0 (1 : ℤ) q + deltaCoeff 1 (-(FP.generatorCount : ℤ)) q +
    (FP.relatorDepthMultiplicity q : ℤ)

/-- Cauchy multiplication by the formal GS polynomial gives exactly the integer
coefficient balance. -/
theorem cauchy_gs_balance
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (FP.gsCoeffInt) b n = FP.gsCoefficientBalance b n := by
  classical
  unfold gsCoeffInt
  rw [cauchy_coeff_add]
  rw [cauchy_coeff_add]
  rw [cauchy_delta_zero]
  rw [FP.cauchy_coeff_delta]
  rw [FP.cauchy_multiplicity_convolution]
  unfold gsCoefficientBalance
  ring

/-- Product-coefficient nonnegativity can equivalently be read as nonnegativity of
Cauchy coefficients of the formal GS polynomial. -/
theorem inequality_cauchy_nonneg
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientInequality b n ↔
      0 ≤ cauchyCoeffNat (FP.gsCoeffInt) b n := by
  rw [FP.cauchy_gs_balance b n]
  exact FP.inequality_balance_nonneg b n

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Integer-valued analogue of `SSBound`. -/
def ISBound (a : ℕ → ℤ) (A : ℕ) : Prop :=
  ∀ n, A < n → a n = 0

/-- Transport an integer support bound across pointwise equality. -/
theorem ISBound.congr {a c : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) (h : ∀ n, c n = a n) :
    ISBound c A := by
  intro n hn
  rw [h n]
  exact ha n hn

/-- Casting a finitely supported natural sequence to integers preserves its support bound. -/
theorem SSBound.intCast {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    ISBound (fun n => (b n : ℤ)) B := by
  intro n hn
  simp [hb n hn]

/-- Casting a natural sequence to integers reflects finite support. -/
theorem int_seq_cast {b : ℕ → ℕ} {B : ℕ} :
    ISBound (fun n => (b n : ℤ)) B ↔ SSBound b B := by
  constructor
  · intro h n hn
    exact Int.natCast_eq_zero.mp (h n hn)
  · intro hb
    exact SSBound.intCast hb

/-- Taking `natAbs` of a finitely supported integer sequence gives a finitely supported
natural sequence with the same bound. -/
theorem ISBound.natAbs {a : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) :
    SSBound (fun n => (a n).natAbs) A := by
  intro n hn
  simp [ha n hn]

/-- Conversely, if the `natAbs` sequence is supported, then the integer sequence is supported. -/
theorem ISBound.of_natAbs {a : ℕ → ℤ} {A : ℕ}
    (ha : SSBound (fun n => (a n).natAbs) A) :
    ISBound a A := by
  intro n hn
  exact Int.natAbs_eq_zero.mp (ha n hn)

/-- Support of an integer sequence is equivalent to support of its `natAbs` sequence. -/
theorem int_seq_abs {a : ℕ → ℤ} {A : ℕ} :
    SSBound (fun n => (a n).natAbs) A ↔ ISBound a A := by
  constructor
  · exact ISBound.of_natAbs
  · exact ISBound.natAbs

/-- Taking integer absolute values preserves an integer support bound. -/
theorem ISBound.abs {a : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) :
    ISBound (fun n => |a n|) A := by
  intro n hn
  simp [ha n hn]

/-- Taking absolute values reflects as well as preserves integer support. -/
theorem seq_support_abs {a : ℕ → ℤ} {A : ℕ} :
    ISBound (fun n => |a n|) A ↔ ISBound a A := by
  constructor
  · intro h n hn
    exact abs_eq_zero.mp (h n hn)
  · exact ISBound.abs

/-- Monotonicity of integer support bounds. -/
theorem ISBound.mono {a : ℕ → ℤ} {A C : ℕ}
    (ha : ISBound a A) (hAC : A ≤ C) :
    ISBound a C := by
  intro n hn
  exact ha n (lt_of_le_of_lt hAC hn)

/-- The zero integer sequence is supported at every bound. -/
@[simp] theorem int_seq_bound (A : ℕ) :
    ISBound (fun _ => (0 : ℤ)) A := by
  intro n hn
  rfl

/-- An integer sequence supported at a single index is supported at that index. -/
theorem seq_bound_single (k : ℕ) (z : ℤ) :
    ISBound (fun n => if n = k then z else 0) k := by
  intro n hn
  have hne : n ≠ k := by omega
  simp [hne]

/-- A single-index integer sequence is supported at any later bound. -/
theorem int_seq_single {k A : ℕ} {z : ℤ} (hk : k ≤ A) :
    ISBound (fun n => if n = k then z else 0) A := by
  exact (seq_bound_single k z).mono hk

/-- Shifting an integer sequence left (dropping initial coefficients) preserves any coarse
support bound. -/
theorem ISBound.shiftLeft {a : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) (k : ℕ) :
    ISBound (fun n => a (n + k)) A := by
  intro n hn
  exact ha (n + k) (by omega)

/-- Shifting an integer sequence to the right by `k` shifts its support bound by `k`. -/
theorem ISBound.shiftRight {a : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) (k : ℕ) :
    ISBound (fun n => if k ≤ n then a (n - k) else 0) (A + k) := by
  intro n hn
  by_cases hk : k ≤ n
  · have harg : A < n - k := by omega
    simp [hk, ha (n - k) harg]
  · simp [hk]

/-- Filtering a supported integer sequence by a decidable predicate preserves support. -/
theorem ISBound.filter {a : ℕ → ℤ} {A : ℕ} (P : ℕ → Prop)
    [DecidablePred P] (ha : ISBound a A) :
    ISBound (fun n => if P n then a n else 0) A := by
  intro n hn
  by_cases h : P n <;> simp [h, ha n hn]

/-- Pointwise maxima preserve a common integer support bound. -/
theorem ISBound.pointwise_max {a c : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) (hc : ISBound c A) :
    ISBound (fun n => max (a n) (c n)) A := by
  intro n hn
  simp [ha n hn, hc n hn]

/-- Pointwise minima preserve a common integer support bound. -/
theorem ISBound.pointwise_min {a c : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) (hc : ISBound c A) :
    ISBound (fun n => min (a n) (c n)) A := by
  intro n hn
  simp [ha n hn, hc n hn]

/-- Pointwise maxima preserve support at the maximum of two integer support bounds. -/
theorem ISBound.pointwise_max_max {a c : ℕ → ℤ} {A C : ℕ}
    (ha : ISBound a A) (hc : ISBound c C) :
    ISBound (fun n => max (a n) (c n)) (max A C) := by
  intro n hn
  have han : A < n := lt_of_le_of_lt (le_max_left A C) hn
  have hcn : C < n := lt_of_le_of_lt (le_max_right A C) hn
  simp [ha n han, hc n hcn]

/-- Pointwise minima preserve support at the maximum of two integer support bounds. -/
theorem ISBound.pointwise_min_max {a c : ℕ → ℤ} {A C : ℕ}
    (ha : ISBound a A) (hc : ISBound c C) :
    ISBound (fun n => min (a n) (c n)) (max A C) := by
  intro n hn
  have han : A < n := lt_of_le_of_lt (le_max_left A C) hn
  have hcn : C < n := lt_of_le_of_lt (le_max_right A C) hn
  simp [ha n han, hc n hcn]

/-- Finite sums of integer sequences with a common support bound have that bound. -/
theorem ISBound.finset_sum {ι : Type*} {s : Finset ι} {a : ι → ℕ → ℤ}
    {A : ℕ} (ha : ∀ i ∈ s, ISBound (a i) A) :
    ISBound (fun n => ∑ i ∈ s, a i n) A := by
  intro n hn
  apply Finset.sum_eq_zero
  intro i hi
  exact ha i hi n hn

/-- Pointwise sums preserve a common integer support bound. -/
theorem ISBound.add {a c : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) (hc : ISBound c A) :
    ISBound (fun n => a n + c n) A := by
  intro n hn
  simp [ha n hn, hc n hn]

/-- Pointwise sums preserve support at the maximum of two integer support bounds. -/
theorem ISBound.add_max {a c : ℕ → ℤ} {A C : ℕ}
    (ha : ISBound a A) (hc : ISBound c C) :
    ISBound (fun n => a n + c n) (max A C) := by
  intro n hn
  have han : A < n := lt_of_le_of_lt (le_max_left A C) hn
  have hcn : C < n := lt_of_le_of_lt (le_max_right A C) hn
  simp [ha n han, hc n hcn]

/-- Negating an integer sequence preserves its support bound. -/
theorem ISBound.neg {a : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) :
    ISBound (fun n => - a n) A := by
  intro n hn
  simp [ha n hn]

/-- Pointwise differences preserve a common integer support bound. -/
theorem ISBound.sub {a c : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) (hc : ISBound c A) :
    ISBound (fun n => a n - c n) A := by
  intro n hn
  simp [ha n hn, hc n hn]

/-- Pointwise differences preserve support at the maximum of two integer support bounds. -/
theorem ISBound.sub_max {a c : ℕ → ℤ} {A C : ℕ}
    (ha : ISBound a A) (hc : ISBound c C) :
    ISBound (fun n => a n - c n) (max A C) := by
  intro n hn
  have han : A < n := lt_of_le_of_lt (le_max_left A C) hn
  have hcn : C < n := lt_of_le_of_lt (le_max_right A C) hn
  simp [ha n han, hc n hcn]

/-- Multiplying an integer sequence by a fixed scalar preserves support. -/
theorem ISBound.const_mul {a : ℕ → ℤ} {A : ℕ} (z : ℤ)
    (ha : ISBound a A) :
    ISBound (fun n => z * a n) A := by
  intro n hn
  simp [ha n hn]

/-- Multiplication by a nonzero integer reflects support as well as preserving it. -/
theorem int_seq_const {a : ℕ → ℤ} {A : ℕ} {z : ℤ} (hz : z ≠ 0) :
    ISBound (fun n => z * a n) A ↔ ISBound a A := by
  constructor
  · intro h n hn
    have hzero := h n hn
    exact (mul_eq_zero.mp hzero).elim (fun hz0 => False.elim (hz hz0)) id
  · intro ha
    exact ISBound.const_mul z ha

/-- Right-scalar version of `ISBound.const_mul`. -/
theorem ISBound.mul_const {a : ℕ → ℤ} {A : ℕ}
    (ha : ISBound a A) (z : ℤ) :
    ISBound (fun n => a n * z) A := by
  intro n hn
  simp [ha n hn]

/-- Prefix sums of an integer-supported sequence stabilize once the cutoff is at least the
support bound. -/
theorem int_range_bound {a : ℕ → ℤ} {A M N : ℕ}
    (ha : ISBound a A) (hAM : A ≤ M) (hMN : M ≤ N) :
    (∑ k ∈ Finset.range (N + 1), a k) =
      ∑ k ∈ Finset.range (M + 1), a k := by
  classical
  have hsubset : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp at hx ⊢
    omega
  rw [← Finset.sum_sdiff hsubset]
  have htail : ∑ x ∈ Finset.range (N + 1) \ Finset.range (M + 1), a x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxnot : x ∉ Finset.range (M + 1) := (Finset.mem_sdiff.mp hx).2
    have hxgt : A < x := by
      simp at hxnot
      omega
    exact ha x hxgt
  rw [htail, zero_add]

/-- Unordered form of integer prefix-sum stabilization for a supported sequence. -/
theorem int_support_bound {a : ℕ → ℤ} {A M N : ℕ}
    (ha : ISBound a A) (hM : A ≤ M) (hN : A ≤ N) :
    (∑ k ∈ Finset.range (M + 1), a k) =
      ∑ k ∈ Finset.range (N + 1), a k := by
  rcases le_total M N with hMN | hNM
  · exact (int_range_bound ha hM hMN).symm
  · exact int_range_bound ha hN hNM

/-- Cauchy coefficients vanish beyond the sum of support bounds. -/
theorem cauchy_coeff_support {a : ℕ → ℤ} {b : ℕ → ℕ}
    {A B n : ℕ} (ha : ISBound a A) (hb : SSBound b B)
    (hn : A + B < n) : cauchyCoeffNat a b n = 0 := by
  classical
  unfold cauchyCoeffNat
  apply Finset.sum_eq_zero
  intro q hq
  have hqle : q ≤ n := by simpa using (Finset.mem_range.mp hq)
  by_cases hAq : A < q
  · simp [ha q hAq]
  · have hqA : q ≤ A := by omega
    have hB : B < n - q := by omega
    simp [hb (n - q) hB]

variable {p : ℕ} (FP : FPres p)

/-- Support-bound wrapper for the integer GS balance sequence. -/
theorem ISBound.gsCoefficientBalance
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    ISBound (fun n => FP.gsCoefficientBalance b n)
      (B + FP.maxRelatorDepth + 1) := by
  intro n hn
  exact FP.gs_balance_support hb hn

/-- The formal GS polynomial has support bounded by `maxRelatorDepth + 1`. -/
theorem gs_coeff_bound
    [Fintype FP.toPresentation.Relator] {q : ℕ}
    (hq : FP.maxRelatorDepth + 1 < q) : FP.gsCoeffInt q = 0 := by
  classical
  unfold gsCoeffInt deltaCoeff
  have hq0 : q ≠ 0 := by omega
  have hq1 : q ≠ 1 := by omega
  have hm : FP.maxRelatorDepth < q := by omega
  have hz : FP.relatorDepthMultiplicity q = 0 :=
    FP.relator_multiplicity_max hm
  simp [hq0, hq1, hz]

/-- Support-bound wrapper for the formal GS polynomial coefficients. -/
theorem ISBound.gsCoeffInt
    [Fintype FP.toPresentation.Relator] :
    ISBound (FP.gsCoeffInt) (FP.maxRelatorDepth + 1) := by
  intro q hq
  exact FP.gs_coeff_bound hq

/-- Cauchy coefficients of the formal GS polynomial against a supported sequence
vanish beyond the sum of the two support bounds. -/
theorem cauchy_gs_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B n : ℕ}
    (hb : SSBound b B) (hn : FP.maxRelatorDepth + 1 + B < n) :
    cauchyCoeffNat (FP.gsCoeffInt) b n = 0 := by
  exact cauchy_coeff_support
    (ISBound.gsCoeffInt FP) hb hn

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- For a supported coefficient sequence, it suffices to check the GS inequalities
through the explicit convolution support bound. -/
theorem inequalities_forall_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B)
    (h : ∀ n, n ≤ B + FP.maxRelatorDepth + 1 → FP.gsCoefficientInequality b n) :
    FP.gsCoefficientInequalities b := by
  intro n
  by_cases hn : n ≤ B + FP.maxRelatorDepth + 1
  · exact h n hn
  · have hz : FP.gsCoefficientBalance b n = 0 :=
      FP.gs_balance_support hb (by omega)
    apply (FP.inequality_balance_nonneg b n).2
    rw [hz]

/-- Finite-checking equivalence for supported coefficient sequences. -/
theorem gs_inequalities_forall
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    FP.gsCoefficientInequalities b ↔
      ∀ n, n ≤ B + FP.maxRelatorDepth + 1 → FP.gsCoefficientInequality b n := by
  constructor
  · intro h n hn
    exact h n
  · exact FP.inequalities_forall_bound hb

/-- Equivalent finite-range formulation of the same finite check. -/
theorem gs_inequalities_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    FP.gsCoefficientInequalities b ↔
      ∀ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
        FP.gsCoefficientInequality b n := by
  rw [FP.gs_inequalities_forall hb]
  constructor
  · intro h n hn
    have hnlt : n < B + FP.maxRelatorDepth + 2 := Finset.mem_range.mp hn
    have hnle : n ≤ B + FP.maxRelatorDepth + 1 := by omega
    exact h n hnle
  · intro h n hnle
    apply h
    simp
    omega

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Truncate a natural coefficient sequence after degree `N`. -/
def truncateSeq (b : ℕ → ℕ) (N : ℕ) : ℕ → ℕ :=
  fun n => if n ≤ N then b n else 0

@[simp] theorem truncate_apply_le (b : ℕ → ℕ) {N n : ℕ} (hn : n ≤ N) :
    truncateSeq b N n = b n := by
  simp [truncateSeq, hn]

@[simp] theorem truncate_seq (b : ℕ → ℕ) {N n : ℕ} (hn : N < n) :
    truncateSeq b N n = 0 := by
  have hnot : ¬ n ≤ N := by omega
  simp [truncateSeq, hnot]

/-- Truncating the zero sequence gives the zero sequence. -/
@[simp] theorem truncateSeq_zero (N : ℕ) :
    truncateSeq (fun _ => 0) N = fun _ => 0 := by
  funext n
  by_cases hn : n ≤ N <;> simp [truncateSeq, hn]

/-- A pointwise-zero sequence remains zero after truncation. -/
theorem truncate_seq_forall {b : ℕ → ℕ} (hb : ∀ n, b n = 0) (N : ℕ) :
    truncateSeq b N = fun _ => 0 := by
  funext n
  by_cases hn : n ≤ N
  · simp [truncateSeq, hn, hb n]
  · simp [truncateSeq, hn]

/-- At cutoff zero, only the zeroth coefficient can survive. -/
theorem truncate_seq_cutoff (b : ℕ → ℕ) :
    truncateSeq b 0 = fun n => if n = 0 then b 0 else 0 := by
  funext n
  by_cases hn : n = 0
  · subst n; simp [truncateSeq]
  · have hle : ¬ n ≤ 0 := by omega
    simp [truncateSeq, hn, hle]

/-- The coefficient at the cutoff itself is unchanged by truncation. -/
@[simp] theorem seq_self (b : ℕ → ℕ) (N : ℕ) :
    truncateSeq b N N = b N :=
  truncate_apply_le b (le_rfl)

/-- Truncations are supported at their cutoff. -/
theorem seq_support_truncate (b : ℕ → ℕ) (N : ℕ) :
    SSBound (truncateSeq b N) N := by
  intro n hn
  exact truncate_seq b hn

/-- Truncation is monotone in the underlying coefficient sequence. -/
theorem truncate_mono {b c : ℕ → ℕ} (hbc : ∀ n, b n ≤ c n) (N n : ℕ) :
    truncateSeq b N n ≤ truncateSeq c N n := by
  by_cases hn : n ≤ N
  · simp [truncateSeq, hn, hbc n]
  · simp [truncateSeq, hn]

/-- Truncation is monotone in the cutoff. -/
theorem truncate_seq_mono (b : ℕ → ℕ) {M N n : ℕ} (hMN : M ≤ N) :
    truncateSeq b M n ≤ truncateSeq b N n := by
  by_cases hm : n ≤ M
  · have hn : n ≤ N := le_trans hm hMN
    simp [truncateSeq, hm, hn]
  · by_cases hn : n ≤ N
    · simp [truncateSeq, hm, hn]
    · simp [truncateSeq, hm, hn]

/-- Truncation distributes over pointwise addition of natural sequences. -/
@[simp] theorem truncateSeq_add (b c : ℕ → ℕ) (N : ℕ) :
    truncateSeq (fun n => b n + c n) N =
      fun n => truncateSeq b N n + truncateSeq c N n := by
  funext n
  by_cases hn : n ≤ N <;> simp [truncateSeq, hn]

/-- Truncation commutes with multiplying a natural sequence by a fixed scalar. -/
@[simp] theorem truncate_seq_const (a : ℕ) (b : ℕ → ℕ) (N : ℕ) :
    truncateSeq (fun n => a * b n) N =
      fun n => a * truncateSeq b N n := by
  funext n
  by_cases hn : n ≤ N <;> simp [truncateSeq, hn]

/-- Right-scalar version of `truncate_seq_const`. -/
@[simp] theorem truncate_mul_const (b : ℕ → ℕ) (a N : ℕ) :
    truncateSeq (fun n => b n * a) N =
      fun n => truncateSeq b N n * a := by
  funext n
  by_cases hn : n ≤ N <;> simp [truncateSeq, hn]

/-- Iterated truncation is truncation at the smaller cutoff. -/
@[simp] theorem truncate_seq_seq (b : ℕ → ℕ) (M N : ℕ) :
    truncateSeq (truncateSeq b M) N = truncateSeq b (min M N) := by
  funext n
  unfold truncateSeq
  by_cases hnN : n ≤ N
  · by_cases hnM : n ≤ M
    · have hmin : n ≤ min M N := by omega
      simp [hnN, hnM, hmin]
    · have hmin : ¬ n ≤ min M N := by omega
      simp [hnN, hnM, hmin]
  · have hmin : ¬ n ≤ min M N := by omega
    simp [hnN, hmin]

/-- If the outer cutoff is later, an already-truncated sequence is unchanged. -/
theorem truncate_of_le (b : ℕ → ℕ) {M N : ℕ} (hMN : M ≤ N) :
    truncateSeq (truncateSeq b M) N = truncateSeq b M := by
  rw [truncate_seq_seq, Nat.min_eq_left hMN]

/-- If the outer cutoff is earlier, it determines the iterated truncation. -/
theorem truncate_of_ge (b : ℕ → ℕ) {M N : ℕ} (hNM : N ≤ M) :
    truncateSeq (truncateSeq b M) N = truncateSeq b N := by
  rw [truncate_seq_seq, Nat.min_eq_right hNM]

/-- Truncations commute under iteration. -/
theorem truncateSeq_comm (b : ℕ → ℕ) (M N : ℕ) :
    truncateSeq (truncateSeq b M) N = truncateSeq (truncateSeq b N) M := by
  rw [truncate_seq_seq, truncate_seq_seq, Nat.min_comm]

/-- Prefix mass of a truncation stabilizes at its cutoff. -/
theorem sum_truncate_seq (b : ℕ → ℕ) {N M : ℕ} (hNM : N ≤ M) :
    (∑ k ∈ Finset.range (M + 1), truncateSeq b N k) =
      ∑ k ∈ Finset.range (N + 1), b k := by
  classical
  have hs : (∑ k ∈ Finset.range (M + 1), truncateSeq b N k) =
      ∑ k ∈ Finset.range (N + 1), truncateSeq b N k :=
    range_support_bound (seq_support_truncate b N) (le_rfl) hNM
  rw [hs]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by
    simp at hk
    omega
  exact truncate_apply_le b hkN



/-- If the prefix cutoff is before the truncation cutoff, truncation does not
change that prefix mass. -/
theorem truncate_seq_prefix (b : ℕ → ℕ) {M N : ℕ}
    (hMN : M ≤ N) :
    (∑ k ∈ Finset.range (M + 1), truncateSeq b N k) =
      ∑ k ∈ Finset.range (M + 1), b k := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have hkM : k ≤ M := by
    have := Finset.mem_range.mp hk
    omega
  exact truncate_apply_le b (le_trans hkM hMN)

/-- Prefix mass of a truncation is the original prefix mass up to the smaller of
 the prefix cutoff and the truncation cutoff. -/
theorem truncate_seq_min (b : ℕ → ℕ) (M N : ℕ) :
    (∑ k ∈ Finset.range (M + 1), truncateSeq b N k) =
      ∑ k ∈ Finset.range (min M N + 1), b k := by
  classical
  rcases le_total M N with hMN | hNM
  · have hmin : min M N = M := Nat.min_eq_left hMN
    rw [hmin]
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k ≤ M := by
      have := Finset.mem_range.mp hk
      omega
    exact truncate_apply_le b (le_trans hkM hMN)
  · have hmin : min M N = N := Nat.min_eq_right hNM
    rw [hmin]
    exact sum_truncate_seq b hNM

/-- Prefix mass of a truncation at its own cutoff is the original prefix mass. -/
theorem sum_seq_self (b : ℕ → ℕ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), truncateSeq b N k) =
      ∑ k ∈ Finset.range (N + 1), b k :=
  sum_truncate_seq b (le_rfl : N ≤ N)

/-- Positivity of the original prefix transfers to every later prefix of its truncation. -/
theorem truncate_seq_pos (b : ℕ → ℕ) {N M : ℕ}
    (hNM : N ≤ M) (hpos : 0 < ∑ k ∈ Finset.range (N + 1), b k) :
    0 < ∑ k ∈ Finset.range (M + 1), truncateSeq b N k := by
  rw [sum_truncate_seq b hNM]
  exact hpos

/-- Truncation agrees with the original sequence up to the cutoff. -/
theorem truncate_eq_le (b : ℕ → ℕ) {N n : ℕ} (hn : n ≤ N) :
    truncateSeq b N n = b n := truncate_apply_le b hn

/-- Truncating a sequence at a support bound leaves it unchanged. -/
theorem seq_self_bound {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) : truncateSeq b B = b := by
  funext n
  by_cases hn : n ≤ B
  · exact truncate_apply_le b hn
  · have hgt : B < n := Nat.lt_of_not_ge hn
    rw [truncate_seq b hgt, hb n hgt]

/-- Conversely, if truncation at `B` is the original sequence, then `B` is a support bound. -/
theorem support_seq_self {b : ℕ → ℕ} {B : ℕ}
    (h : truncateSeq b B = b) : SSBound b B := by
  intro n hn
  have happ := congrFun h n
  rw [truncate_seq b hn] at happ
  exact happ.symm

/-- Truncation at `B` is the identity exactly for sequences supported at `B`. -/
theorem truncate_support_bound {b : ℕ → ℕ} {B : ℕ} :
    truncateSeq b B = b ↔ SSBound b B :=
  ⟨support_seq_self, seq_self_bound⟩

/-- Pointwise orientation of truncation identity at a support bound. -/
theorem truncate_seq_support {b : ℕ → ℕ} {B n : ℕ}
    (hb : SSBound b B) : truncateSeq b B n = b n := by
  rw [seq_self_bound hb]

/-- Truncating at any cutoff beyond a support bound also leaves the sequence unchanged. -/
theorem truncate_self_bound {b : ℕ → ℕ} {B M : ℕ}
    (hb : SSBound b B) (hBM : B ≤ M) : truncateSeq b M = b := by
  exact seq_self_bound (hb.mono hBM)

/-- Pointwise orientation of truncation identity at any cutoff beyond a support bound. -/
theorem truncate_seq_self {b : ℕ → ℕ} {B M n : ℕ}
    (hb : SSBound b B) (hBM : B ≤ M) : truncateSeq b M n = b n := by
  rw [truncate_self_bound hb hBM]

variable {p : ℕ} (FP : FPres p)

/-- At a support bound, truncation leaves every GS balance unchanged. -/
theorem gs_balance_seq
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B n : ℕ}
    (hb : SSBound b B) :
    FP.gsCoefficientBalance (truncateSeq b B) n = FP.gsCoefficientBalance b n := by
  rw [seq_self_bound hb]

/-- Truncating beyond a support bound leaves every GS balance unchanged. -/
theorem balance_truncate_seq
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B M n : ℕ}
    (hb : SSBound b B) (hBM : B ≤ M) :
    FP.gsCoefficientBalance (truncateSeq b M) n = FP.gsCoefficientBalance b n := by
  rw [truncate_self_bound hb hBM]

/-- At a support bound, truncation leaves every individual GS inequality unchanged. -/
theorem gs_inequality_seq
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B n : ℕ}
    (hb : SSBound b B) :
    FP.gsCoefficientInequality (truncateSeq b B) n ↔ FP.gsCoefficientInequality b n := by
  rw [FP.inequality_balance_nonneg,
    FP.inequality_balance_nonneg,
    FP.gs_balance_seq hb]

/-- Truncating beyond a support bound preserves each GS inequality. -/
theorem inequality_truncate_seq
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B M n : ℕ}
    (hb : SSBound b B) (hBM : B ≤ M) :
    FP.gsCoefficientInequality (truncateSeq b M) n ↔ FP.gsCoefficientInequality b n := by
  rw [FP.inequality_balance_nonneg,
    FP.inequality_balance_nonneg,
    FP.balance_truncate_seq hb hBM]

/-- At a support bound, truncation preserves the full GS-inequality predicate. -/
theorem inequalities_seq_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    FP.gsCoefficientInequalities (truncateSeq b B) ↔ FP.gsCoefficientInequalities b := by
  constructor
  · intro h n
    exact (FP.gs_inequality_seq
      (B := B) (n := n) hb).1 (h n)
  · intro h n
    exact (FP.gs_inequality_seq
      (B := B) (n := n) hb).2 (h n)

/-- Truncating beyond a support bound preserves the full GS-inequality predicate. -/
theorem gs_inequalities_seq
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B M : ℕ}
    (hb : SSBound b B) (hBM : B ≤ M) :
    FP.gsCoefficientInequalities (truncateSeq b M) ↔ FP.gsCoefficientInequalities b := by
  constructor
  · intro h n
    exact (FP.inequality_truncate_seq
      (B := B) (M := M) (n := n) hb hBM).1 (h n)
  · intro h n
    exact (FP.inequality_truncate_seq
      (B := B) (M := M) (n := n) hb hBM).2 (h n)

/-- Relator convolution is unchanged in degrees at most the truncation cutoff. -/
theorem convolution_truncate_seq
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) {N n : ℕ} (hn : n ≤ N) :
    FP.relatorDepthConvolution (truncateSeq b N) n =
      FP.relatorDepthConvolution b n := by
  apply FP.convolution_congr_upto
  intro k hk
  exact truncate_apply_le b (le_trans hk hn)

/-- Generator shifts are unchanged in degrees at most the truncation cutoff. -/
theorem shift_contribution_seq
    (b : ℕ → ℕ) {N n : ℕ} (hn : n ≤ N) :
    FP.generatorShiftContribution (truncateSeq b N) n =
      FP.generatorShiftContribution b n := by
  by_cases hpos : 0 < n
  · have hpred : n - 1 ≤ N := by omega
    simp [generatorShiftContribution, hpos, truncate_apply_le b hpred]
  · simp [generatorShiftContribution, hpos]

/-- Integer balances are unchanged in degrees at most the truncation cutoff. -/
theorem gs_balance_truncate
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) {N n : ℕ} (hn : n ≤ N) :
    FP.gsCoefficientBalance (truncateSeq b N) n = FP.gsCoefficientBalance b n := by
  unfold gsCoefficientBalance
  rw [truncate_apply_le b hn,
    FP.convolution_truncate_seq b hn,
    FP.shift_contribution_seq b hn]

/-- Coefficient inequalities are unchanged in degrees at most the truncation cutoff. -/
theorem coefficient_inequality_seq
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) {N n : ℕ} (hn : n ≤ N) :
    FP.gsCoefficientInequality (truncateSeq b N) n ↔ FP.gsCoefficientInequality b n := by
  rw [FP.inequality_balance_nonneg,
    FP.inequality_balance_nonneg,
    FP.gs_balance_truncate b hn]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Expand a Cauchy coefficient over any larger finite range, with an indicator
for the admissible triangle. -/
theorem cauchy_coeff_ite (a : ℕ → ℤ) (b : ℕ → ℕ)
    {n N : ℕ} (hn : n ≤ N) :
    cauchyCoeffNat a b n =
      ∑ q ∈ Finset.range (N + 1),
        a q * (if _h : q ≤ n then (b (n - q) : ℤ) else 0) := by
  classical
  unfold cauchyCoeffNat
  have hsub : Finset.range (n + 1) ⊆ Finset.range (N + 1) := by
    intro q hq
    simp at hq ⊢
    omega
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro q hq
    have hqle : q ≤ n := by simpa using (Finset.mem_range.mp hq)
    simp [hqle]
  · intro q hqN hqnot
    have hqgt : n < q := by
      simp at hqN hqnot
      omega
    have hnot : ¬ q ≤ n := by omega
    simp [hnot]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Prefix sum of Cauchy coefficients. -/
noncomputable def cauchyCoeffPrefix (a : ℕ → ℤ) (b : ℕ → ℕ) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), cauchyCoeffNat a b n

/-- Cast form of a shifted coefficient prefix. -/
theorem ite_shifted_int (b : ℕ → ℕ) (N q : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
        (if _h : q ≤ n then (b (n - q) : ℤ) else 0)) =
      (shiftedCoefficientPrefix b N q : ℤ) := by
  classical
  unfold shiftedCoefficientPrefix
  -- This is just coercion through a finite sum of matching ite terms.
  norm_num

/-- Fubini/reindexing formula for prefix sums of Cauchy coefficients. -/
theorem cauchy_coeff_prefixes (a : ℕ → ℤ) (b : ℕ → ℕ) (N : ℕ) :
    cauchyCoeffPrefix a b N =
      ∑ q ∈ Finset.range (N + 1),
        a q * (∑ k ∈ Finset.range (N - q + 1), (b k : ℤ)) := by
  classical
  unfold cauchyCoeffPrefix
  calc
    (∑ n ∈ Finset.range (N + 1), cauchyCoeffNat a b n) =
        ∑ n ∈ Finset.range (N + 1),
          ∑ q ∈ Finset.range (N + 1),
            a q * (if _h : q ≤ n then (b (n - q) : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : n ≤ N := by
        have hlt := Finset.mem_range.mp hn
        omega
      exact cauchy_coeff_ite a b hnle
    _ = ∑ q ∈ Finset.range (N + 1),
          ∑ n ∈ Finset.range (N + 1),
            a q * (if _h : q ≤ n then (b (n - q) : ℤ) else 0) := by
      exact Finset.sum_comm
    _ = ∑ q ∈ Finset.range (N + 1),
          a q * (∑ n ∈ Finset.range (N + 1),
            (if _h : q ≤ n then (b (n - q) : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [Finset.mul_sum]
    _ = ∑ q ∈ Finset.range (N + 1),
          a q * (∑ k ∈ Finset.range (N - q + 1), (b k : ℤ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqle : q ≤ N := by
        have hlt := Finset.mem_range.mp hq
        omega
      rw [ite_shifted_int b N q]
      rw [shifted_prefix_sub b hqle]
      norm_num

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Prefix sums of GS balances are the triangular convolution of the formal GS
polynomial coefficients with coefficient prefixes. -/
theorem gs_balance_prefix
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (N : ℕ) :
    FP.gsBalanceSum b N =
      ∑ q ∈ Finset.range (N + 1),
        FP.gsCoeffInt q *
          (∑ k ∈ Finset.range (N - q + 1), (b k : ℤ)) := by
  classical
  unfold gsBalanceSum
  calc
    (∑ n ∈ Finset.range (N + 1), FP.gsCoefficientBalance b n) =
        ∑ n ∈ Finset.range (N + 1),
          cauchyCoeffNat (FP.gsCoeffInt) b n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [FP.cauchy_gs_balance b n]
    _ = cauchyCoeffPrefix (FP.gsCoeffInt) b N := by
      rfl
    _ = _ := cauchy_coeff_prefixes (FP.gsCoeffInt) b N

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

@[simp] theorem gs_int_zero [Fintype FP.toPresentation.Relator] :
    FP.gsCoeffInt 0 = 1 + (FP.relatorDepthMultiplicity 0 : ℤ) := by
  unfold gsCoeffInt deltaCoeff
  simp

@[simp] theorem gs_int_one [Fintype FP.toPresentation.Relator] :
    FP.gsCoeffInt 1 = -(FP.generatorCount : ℤ) +
      (FP.relatorDepthMultiplicity 1 : ℤ) := by
  unfold gsCoeffInt deltaCoeff
  simp

/-- Away from degrees `0` and `1`, the formal GS polynomial coefficient is just
the relator-depth multiplicity. -/
theorem gs_coeff_int
    [Fintype FP.toPresentation.Relator] {q : ℕ} (h0 : q ≠ 0) (h1 : q ≠ 1) :
    FP.gsCoeffInt q = (FP.relatorDepthMultiplicity q : ℤ) := by
  unfold gsCoeffInt deltaCoeff
  simp [h0, h1]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Cauchy coefficients are additive in the natural coefficient sequence. -/
theorem cauchy_nat_right (a : ℕ → ℤ) (b c : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat a (fun k => b k + c k) n =
      cauchyCoeffNat a b n + cauchyCoeffNat a c n := by
  classical
  unfold cauchyCoeffNat
  simp [mul_add, Finset.sum_add_distrib]

/-- Cauchy coefficients are homogeneous in the natural coefficient sequence. -/
theorem cauchy_coeff_mul (a : ℕ → ℤ) (c : ℕ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat a (fun k => c * b k) n =
      (c : ℤ) * cauchyCoeffNat a b n := by
  classical
  unfold cauchyCoeffNat
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  norm_num
  ring

/-- Right-multiplication version of homogeneity in the natural coefficient sequence. -/
theorem cauchy_nat_mul (a : ℕ → ℤ) (b : ℕ → ℕ) (c n : ℕ) :
    cauchyCoeffNat a (fun k => b k * c) n =
      (c : ℤ) * cauchyCoeffNat a b n := by
  simpa [Nat.mul_comm] using cauchy_coeff_mul a c b n

/-- Prefix Cauchy sums are additive in the natural coefficient sequence. -/
theorem cauchy_coeff_prefix (a : ℕ → ℤ) (b c : ℕ → ℕ) (N : ℕ) :
    cauchyCoeffPrefix a (fun k => b k + c k) N =
      cauchyCoeffPrefix a b N + cauchyCoeffPrefix a c N := by
  classical
  unfold cauchyCoeffPrefix
  simp [cauchy_nat_right, Finset.sum_add_distrib]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Prefix Cauchy sums are homogeneous in the natural coefficient sequence. -/
theorem cauchy_coeff_right (a : ℕ → ℤ) (c : ℕ) (b : ℕ → ℕ) (N : ℕ) :
    cauchyCoeffPrefix a (fun k => c * b k) N =
      (c : ℤ) * cauchyCoeffPrefix a b N := by
  classical
  unfold cauchyCoeffPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [cauchy_coeff_mul]

/-- Right-multiplication version of prefix homogeneity in the natural sequence. -/
theorem cauchy_coeff_nat (a : ℕ → ℤ) (b : ℕ → ℕ) (c N : ℕ) :
    cauchyCoeffPrefix a (fun k => b k * c) N =
      (c : ℤ) * cauchyCoeffPrefix a b N := by
  simpa [Nat.mul_comm] using cauchy_coeff_right a c b N

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- The formal GS polynomial packaged as a finitely supported integer sequence. -/
noncomputable def gsPolynomialFinsupp [Fintype FP.toPresentation.Relator] : ℕ →₀ ℤ :=
  Finsupp.onFinset (Finset.range (FP.maxRelatorDepth + 2))
    (fun n => FP.gsCoeffInt n) (by
      intro n hn
      rw [Finset.mem_range]
      by_contra hlt
      have hbound : FP.maxRelatorDepth + 1 < n := by
        have hnle_not : ¬ n < FP.maxRelatorDepth + 2 := hlt
        omega
      exact hn (FP.gs_coeff_bound hbound))

@[simp] theorem gs_polynomial_finsupp [Fintype FP.toPresentation.Relator] (n : ℕ) :
    FP.gsPolynomialFinsupp n = FP.gsCoeffInt n :=
  Finsupp.onFinset_apply

/-- Zeroth coefficient of the packaged GS polynomial. -/
@[simp] theorem gs_finsupp_zero [Fintype FP.toPresentation.Relator] :
    FP.gsPolynomialFinsupp 0 = 1 + (FP.relatorDepthMultiplicity 0 : ℤ) := by
  simp [gs_polynomial_finsupp]

/-- First coefficient of the packaged GS polynomial. -/
@[simp] theorem gs_finsupp_one [Fintype FP.toPresentation.Relator] :
    FP.gsPolynomialFinsupp 1 =
      -(FP.generatorCount : ℤ) + (FP.relatorDepthMultiplicity 1 : ℤ) := by
  simp [gs_polynomial_finsupp]

/-- The support of the formal GS polynomial lies in the explicit finite range. -/
theorem gs_finsupp_range [Fintype FP.toPresentation.Relator] :
    FP.gsPolynomialFinsupp.support ⊆ Finset.range (FP.maxRelatorDepth + 2) := by
  intro n hn
  rw [Finsupp.mem_support_iff] at hn
  rw [Finset.mem_range]
  by_contra hlt
  have hbound : FP.maxRelatorDepth + 1 < n := by omega
  rw [FP.gs_polynomial_finsupp] at hn
  exact hn (FP.gs_coeff_bound hbound)

/-- The packaged GS polynomial vanishes beyond its explicit support bound. -/
@[simp] theorem gs_finsupp_bound
    [Fintype FP.toPresentation.Relator] {n : ℕ}
    (hn : FP.maxRelatorDepth + 1 < n) :
    FP.gsPolynomialFinsupp n = 0 := by
  rw [FP.gs_polynomial_finsupp]
  exact FP.gs_coeff_bound hn

/-- No index beyond the explicit support bound belongs to the packaged support. -/
theorem finsupp_support_bound
    [Fintype FP.toPresentation.Relator] {n : ℕ}
    (hn : FP.maxRelatorDepth + 1 < n) :
    n ∉ FP.gsPolynomialFinsupp.support := by
  rw [Finsupp.mem_support_iff]
  intro hne
  exact hne (FP.gs_finsupp_bound hn)

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- A Cauchy coefficient may be computed over any support bound for the integer
coefficient sequence. -/
theorem cauchy_coeff_bound {a : ℕ → ℤ} (b : ℕ → ℕ)
    {A n : ℕ} (ha : ISBound a A) :
    cauchyCoeffNat a b n =
      ∑ q ∈ Finset.range (A + 1),
        a q * (if _h : q ≤ n then (b (n - q) : ℤ) else 0) := by
  classical
  by_cases hnA : n ≤ A
  · exact cauchy_coeff_ite a b hnA
  · have hAn : A ≤ n := by omega
    unfold cauchyCoeffNat
    have hsub : Finset.range (A + 1) ⊆ Finset.range (n + 1) := by
      intro q hq
      simp at hq ⊢
      omega
    have hsum :
        (∑ q ∈ Finset.range (n + 1), a q * (b (n - q) : ℤ)) =
        ∑ q ∈ Finset.range (A + 1), a q * (b (n - q) : ℤ) := by
      symm
      apply Finset.sum_subset hsub
      intro q hqn hqnot
      have hAq : A < q := by
        simp at hqn hqnot
        omega
      simp [ha q hAq]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro q hq
    have hqleA : q ≤ A := by simpa using (Finset.mem_range.mp hq)
    have hqle : q ≤ n := by omega
    simp [hqle]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Finite displayed sum for the formal GS-polynomial Cauchy coefficient. -/
theorem cauchy_coeff_gs
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat (FP.gsCoeffInt) b n =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        FP.gsCoeffInt q *
          (if _h : q ≤ n then (b (n - q) : ℤ) else 0) := by
  simpa [Nat.add_assoc] using
    (cauchy_coeff_bound b
      (ISBound.gsCoeffInt FP) (A := FP.maxRelatorDepth + 1) (n := n))

/-- The same finite displayed sum equals the GS balance. -/
theorem gs_balance_sum
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientBalance b n =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        FP.gsCoeffInt q *
          (if _h : q ≤ n then (b (n - q) : ℤ) else 0) := by
  rw [← FP.cauchy_gs_balance b n]
  exact FP.cauchy_coeff_gs b n

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Sum of an integer delta coefficient over a range containing its support. -/
theorem sum_range_coeff (k : ℕ) (c : ℤ) {N : ℕ} (hk : k < N) :
    (∑ q ∈ Finset.range N, deltaCoeff k c q) = c := by
  classical
  unfold deltaCoeff
  rw [Finset.sum_eq_single k]
  · simp
  · intro q hq hqk
    simp [hqk]
  · intro hknot
    exact False.elim (hknot (by simpa using hk))

/-- Sum of an integer delta coefficient over a range missing its support. -/
theorem sum_range_delta (k : ℕ) (c : ℤ) {N : ℕ} (hN : N ≤ k) :
    (∑ q ∈ Finset.range N, deltaCoeff k c q) = 0 := by
  classical
  unfold deltaCoeff
  apply Finset.sum_eq_zero
  intro q hq
  have hqk : q ≠ k := by
    have hqN : q < N := Finset.mem_range.mp hq
    omega
  simp [hqk]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- The sum of the formal GS-polynomial coefficients is `1 - d + r`. -/
theorem range_gs_int
    [Fintype FP.toPresentation.Relator] :
    (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2), FP.gsCoeffInt q) =
      (1 : ℤ) - (FP.generatorCount : ℤ) +
        (Nat.card FP.toPresentation.Relator : ℤ) := by
  classical
  unfold gsCoeffInt
  simp_rw [add_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h0 : (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2), deltaCoeff 0 (1 : ℤ) q) = 1 :=
    sum_range_coeff 0 (1 : ℤ) (by omega)
  have h1 : (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
      deltaCoeff 1 (-(FP.generatorCount : ℤ)) q) = -(FP.generatorCount : ℤ) :=
    sum_range_coeff 1 (-(FP.generatorCount : ℤ)) (by omega)
  have htail : FP.relatorDepthMultiplicity (FP.maxRelatorDepth + 1) = 0 := by
    exact FP.relator_multiplicity_max (by omega)
  have hhistNat :
      (∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
        FP.relatorDepthMultiplicity q) = Nat.card FP.toPresentation.Relator := by
    simpa using FP.sum_finsupp_relators
  have hhistInt :
      (∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
        (FP.relatorDepthMultiplicity q : ℤ)) =
        (Nat.card FP.toPresentation.Relator : ℤ) := by
    exact_mod_cast hhistNat
  have hhistExt :
      (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (FP.relatorDepthMultiplicity q : ℤ)) =
        (Nat.card FP.toPresentation.Relator : ℤ) := by
    rw [show FP.maxRelatorDepth + 2 = (FP.maxRelatorDepth + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    simp [htail, hhistInt]
  rw [h0, h1, hhistExt]
  ring_nf

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Evaluate the finite formal GS polynomial at an integer. -/
noncomputable def gsEvalInt [Fintype FP.toPresentation.Relator] (x : ℤ) : ℤ :=
  ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2), FP.gsCoeffInt q * x ^ q

@[simp] theorem gs_polynomial_int [Fintype FP.toPresentation.Relator] :
    FP.gsEvalInt 1 =
      (1 : ℤ) - (FP.generatorCount : ℤ) +
        (Nat.card FP.toPresentation.Relator : ℤ) := by
  unfold gsEvalInt
  simp [FP.range_gs_int]

@[simp] theorem gs_eval_int [Fintype FP.toPresentation.Relator] :
    FP.gsEvalInt 0 = 1 + (FP.relatorDepthMultiplicity 0 : ℤ) := by
  classical
  unfold gsEvalInt
  rw [Finset.sum_eq_single 0]
  · simp
  · intro q hq hq0
    have hpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hp : (0 : ℤ) ^ q = 0 := by simp [Nat.ne_of_gt hpos]
    simp [hp]
  · intro h0
    exfalso
    apply h0
    simp

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Integer-cast prefix sums of a supported natural sequence stabilize past the bound. -/
theorem coe_seq_bound {b : ℕ → ℕ} {B M : ℕ}
    (hb : SSBound b B) (hBM : B ≤ M) :
    (∑ k ∈ Finset.range (M + 1), (b k : ℤ)) =
      ∑ k ∈ Finset.range (B + 1), (b k : ℤ) := by
  classical
  have hsub : Finset.range (B + 1) ⊆ Finset.range (M + 1) := by
    intro k hk
    simp at hk ⊢
    omega
  symm
  apply Finset.sum_subset hsub
  intro k hkM hknot
  have hBk : B < k := by
    simp at hkM hknot
    omega
  simp [hb k hBk]

/-- Total convolution sum for two finitely supported sequences factors as the
product of their total sums. -/
theorem cauchy_prefix_bound {a : ℕ → ℤ} {b : ℕ → ℕ}
    {A B : ℕ} (ha : ISBound a A) (hb : SSBound b B) :
    cauchyCoeffPrefix a b (A + B) =
      (∑ q ∈ Finset.range (A + 1), a q) *
        (∑ k ∈ Finset.range (B + 1), (b k : ℤ)) := by
  classical
  rw [cauchy_coeff_prefixes]
  have hNsub : Finset.range (A + 1) ⊆ Finset.range (A + B + 1) := by
    intro q hq
    simp at hq ⊢
    omega
  have htrim :
      (∑ q ∈ Finset.range (A + B + 1),
        a q * (∑ k ∈ Finset.range (A + B - q + 1), (b k : ℤ))) =
      ∑ q ∈ Finset.range (A + 1),
        a q * (∑ k ∈ Finset.range (A + B - q + 1), (b k : ℤ)) := by
    symm
    apply Finset.sum_subset hNsub
    intro q hqN hqnot
    have hAq : A < q := by
      simp at hqN hqnot
      omega
    simp [ha q hAq]
  rw [htrim]
  have hconst :
      (∑ q ∈ Finset.range (A + 1),
        a q * (∑ k ∈ Finset.range (A + B - q + 1), (b k : ℤ))) =
      ∑ q ∈ Finset.range (A + 1),
        a q * (∑ k ∈ Finset.range (B + 1), (b k : ℤ)) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqle : q ≤ A := by simpa using (Finset.mem_range.mp hq)
    have hBM : B ≤ A + B - q := by omega
    rw [coe_seq_bound hb hBM]
  rw [hconst]
  rw [← Finset.sum_mul]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Once both factors are supported, the total GS balance prefix factors into the
sum of GS-polynomial coefficients times the total coefficient mass. -/
theorem balance_prefix_factor
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    FP.gsBalanceSum b (FP.maxRelatorDepth + 1 + B) =
      (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2), FP.gsCoeffInt q) *
        (∑ k ∈ Finset.range (B + 1), (b k : ℤ)) := by
  classical
  let A := FP.maxRelatorDepth + 1
  have hbal : FP.gsBalanceSum b (A + B) =
      cauchyCoeffPrefix (FP.gsCoeffInt) b (A + B) := by
    unfold gsBalanceSum cauchyCoeffPrefix
    apply Finset.sum_congr rfl
    intro n hn
    rw [FP.cauchy_gs_balance b n]
  have hfac := cauchy_prefix_bound
      (a := FP.gsCoeffInt) (b := b)
      (A := A) (B := B) (ISBound.gsCoeffInt FP) hb
  simpa [A, Nat.add_assoc] using hbal.trans hfac

/-- Expanded form of the supported total-balance factorization. -/
theorem gs_balance_expanded
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    FP.gsBalanceSum b (FP.maxRelatorDepth + 1 + B) =
      ((1 : ℤ) - (FP.generatorCount : ℤ) +
        (Nat.card FP.toPresentation.Relator : ℤ)) *
        (∑ k ∈ Finset.range (B + 1), (b k : ℤ)) := by
  rw [FP.balance_prefix_factor hb]
  rw [FP.range_gs_int]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- A toy finite-support contradiction criterion: if the total GS polynomial mass
is negative while the supported coefficient sequence has positive total mass,
then the coefficientwise inequalities cannot all hold.  This is the `t = 1`
shadow of the usual GS argument. -/
theorem inequalities_total_poly
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B)
    (hmass : 0 < (∑ k ∈ Finset.range (B + 1), (b k : ℤ)))
    (hneg : (1 : ℤ) - (FP.generatorCount : ℤ) +
        (Nat.card FP.toPresentation.Relator : ℤ) < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  intro hineq
  have hnonneg := FP.prefix_nonneg_inequalities hineq
    (FP.maxRelatorDepth + 1 + B)
  rw [FP.gs_balance_expanded hb] at hnonneg
  nlinarith

/-- Nat-valued mass version of the preceding contradiction criterion. -/
theorem inequalities_total_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B)
    (hmass : 0 < (∑ k ∈ Finset.range (B + 1), b k))
    (hneg : (1 : ℤ) - (FP.generatorCount : ℤ) +
        (Nat.card FP.toPresentation.Relator : ℤ) < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  apply FP.inequalities_total_poly hb _ hneg
  exact_mod_cast hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Contrapositive form: a nonzero supported sequence satisfying all coefficient
inequalities forces the total GS polynomial mass at `1` to be nonnegative. -/
theorem total_nonneg_inequalities
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B)
    (hmass : 0 < (∑ k ∈ Finset.range (B + 1), (b k : ℤ)))
    (hineq : FP.gsCoefficientInequalities b) :
    0 ≤ (1 : ℤ) - (FP.generatorCount : ℤ) +
        (Nat.card FP.toPresentation.Relator : ℤ) := by
  by_contra h
  have hneg : (1 : ℤ) - (FP.generatorCount : ℤ) +
        (Nat.card FP.toPresentation.Relator : ℤ) < 0 := by omega
  exact (FP.inequalities_total_poly hb hmass hneg) hineq

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- The total mass of a truncation through its cutoff is the original prefix mass. -/
theorem range_seq_self (b : ℕ → ℕ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), truncateSeq b N k) =
      ∑ k ∈ Finset.range (N + 1), b k := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by
    have hlt := Finset.mem_range.mp hk
    omega
  simp [truncate_apply_le b hkN]

variable {p : ℕ} (FP : FPres p)

/-- Negative total polynomial mass rules out all-inequality truncated nonzero prefixes. -/
theorem inequalities_seq_total
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N : ℕ}
    (hmass : 0 < (∑ k ∈ Finset.range (N + 1), b k))
    (hneg : (1 : ℤ) - (FP.generatorCount : ℤ) +
        (Nat.card FP.toPresentation.Relator : ℤ) < 0) :
    ¬ FP.gsCoefficientInequalities (truncateSeq b N) := by
  apply FP.inequalities_total_mass
    (seq_support_truncate b N) _ hneg
  simpa [range_seq_self b N] using hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Finite-range criterion specialized to a truncated sequence. -/
theorem gs_truncate_seq
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (N : ℕ) :
    FP.gsCoefficientInequalities (truncateSeq b N) ↔
      ∀ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
        FP.gsCoefficientInequality (truncateSeq b N) n := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (FP.gs_inequalities_bound
      (seq_support_truncate b N))

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Under negative total polynomial mass, a nonzero truncation has an explicit
bounded degree where the coefficient inequality fails. -/
theorem failure_seq_total
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N : ℕ}
    (hmass : 0 < (∑ k ∈ Finset.range (N + 1), b k))
    (hneg : (1 : ℤ) - (FP.generatorCount : ℤ) +
        (Nat.card FP.toPresentation.Relator : ℤ) < 0) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  classical
  have hnot := FP.inequalities_seq_total
    hmass hneg
  by_contra hnone
  have hallRange : ∀ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (truncateSeq b N) n := by
    intro n hn
    by_contra hf
    exact hnone ⟨n, hn, hf⟩
  have hall := (FP.gs_truncate_seq b N).2 hallRange
  exact hnot hall

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Antidiagonal form of the Cauchy coefficient. -/
theorem cauchy_coeff_antidiagonal (a : ℕ → ℤ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffNat a b n =
      ∑ ij ∈ Finset.antidiagonal n, a ij.1 * (b ij.2 : ℤ) := by
  classical
  unfold cauchyCoeffNat
  simpa [Nat.succ_eq_add_one] using
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun q k => a q * (b k : ℤ)) n).symm

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Antidiagonal/product-coefficient form of the GS balance. -/
theorem coefficient_balance_antidiagonal
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientBalance b n =
      ∑ ij ∈ Finset.antidiagonal n,
        FP.gsCoeffInt ij.1 * (b ij.2 : ℤ) := by
  rw [← FP.cauchy_gs_balance b n]
  exact cauchy_coeff_antidiagonal (FP.gsCoeffInt) b n

/-- The coefficientwise inequality is nonnegativity of the antidiagonal product coefficient. -/
theorem inequality_antidiagonal_nonneg
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientInequality b n ↔
      0 ≤ ∑ ij ∈ Finset.antidiagonal n,
        FP.gsCoeffInt ij.1 * (b ij.2 : ℤ) := by
  rw [← FP.coefficient_balance_antidiagonal b n]
  exact FP.inequality_balance_nonneg b n

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Antidiagonal sums may be restricted to the support rectangle of the two factors. -/
theorem cauchy_antidiagonal_bounds {a : ℕ → ℤ} {b : ℕ → ℕ}
    {A B : ℕ} (ha : ISBound a A) (hb : SSBound b B) (n : ℕ) :
    cauchyCoeffNat a b n =
      ∑ ij ∈ (Finset.antidiagonal n).filter (fun ij => ij.1 ≤ A ∧ ij.2 ≤ B),
        a ij.1 * (b ij.2 : ℤ) := by
  classical
  rw [cauchy_coeff_antidiagonal]
  symm
  apply Finset.sum_subset (by intro ij hij; exact (Finset.mem_filter.mp hij).1)
  intro ij hij hnot
  have hbad : ¬ (ij.1 ≤ A ∧ ij.2 ≤ B) := by
    intro hgood
    apply hnot
    exact Finset.mem_filter.mpr ⟨hij, hgood⟩
  by_cases hA : ij.1 ≤ A
  · have hBlt : B < ij.2 := by omega
    simp [hb ij.2 hBlt]
  · have hAlt : A < ij.1 := by omega
    simp [ha ij.1 hAlt]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Antidiagonal GS balance with the polynomial side restricted to its finite support. -/
theorem balance_antidiagonal_support
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    FP.gsCoefficientBalance b n =
      ∑ ij ∈ (Finset.antidiagonal n).filter (fun ij => ij.1 ≤ FP.maxRelatorDepth + 1),
        FP.gsCoeffInt ij.1 * (b ij.2 : ℤ) := by
  classical
  rw [← FP.cauchy_gs_balance b n]
  rw [cauchy_coeff_antidiagonal]
  symm
  apply Finset.sum_subset (by intro ij hij; exact (Finset.mem_filter.mp hij).1)
  intro ij hij hnot
  have hgt : FP.maxRelatorDepth + 1 < ij.1 := by
    have : ¬ ij.1 ≤ FP.maxRelatorDepth + 1 := by
      intro hle; exact hnot (Finset.mem_filter.mpr ⟨hij, hle⟩)
    omega
  simp [FP.gs_coeff_bound hgt]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Antidiagonal GS balance restricted to both the polynomial support and a bound
for the coefficient sequence. -/
theorem balance_antidiagonal_supports
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (n : ℕ) :
    FP.gsCoefficientBalance b n =
      ∑ ij ∈ (Finset.antidiagonal n).filter
          (fun ij => ij.1 ≤ FP.maxRelatorDepth + 1 ∧ ij.2 ≤ B),
        FP.gsCoeffInt ij.1 * (b ij.2 : ℤ) := by
  rw [← FP.cauchy_gs_balance b n]
  exact cauchy_antidiagonal_bounds
    (ISBound.gsCoeffInt FP) hb n

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- A finite weighted sum of integer GS balances. -/
noncomputable def gsBalanceWeighted [Fintype FP.toPresentation.Relator]
    (w : ℕ → ℤ) (b : ℕ → ℕ) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), w n * FP.gsCoefficientBalance b n

/-- Nonnegative weights preserve nonnegativity of a weighted balance sum under
coefficientwise GS inequalities. -/
theorem gs_balance_nonneg
    [Fintype FP.toPresentation.Relator] {w : ℕ → ℤ} {b : ℕ → ℕ} (N : ℕ)
    (hw : ∀ n, n ≤ N → 0 ≤ w n)
    (hineq : FP.gsCoefficientInequalities b) :
    0 ≤ FP.gsBalanceWeighted w b N := by
  classical
  unfold gsBalanceWeighted
  apply Finset.sum_nonneg
  intro n hn
  have hnle : n ≤ N := by
    have hlt := Finset.mem_range.mp hn
    omega
  have hb := (FP.inequality_balance_nonneg b n).1 (hineq n)
  exact mul_nonneg (hw n hnle) hb

/-- Nat-weighted specialization. -/
theorem gs_nonneg_inequalities
    [Fintype FP.toPresentation.Relator] (w : ℕ → ℕ) {b : ℕ → ℕ} (N : ℕ)
    (hineq : FP.gsCoefficientInequalities b) :
    0 ≤ FP.gsBalanceWeighted (fun n => (w n : ℤ)) b N := by
  apply FP.gs_balance_nonneg N
  · intro n hn
    exact_mod_cast (Nat.zero_le (w n))
  · exact hineq

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Geometric integer weights are nonnegative when the base is nonnegative. -/
theorem gs_balance_inequalities
    [Fintype FP.toPresentation.Relator] {x : ℤ} (hx : 0 ≤ x)
    {b : ℕ → ℕ} (N : ℕ) (hineq : FP.gsCoefficientInequalities b) :
    0 ≤ FP.gsBalanceWeighted (fun n => x ^ n) b N := by
  apply FP.gs_balance_nonneg N
  · intro n hn
    exact pow_nonneg hx n
  · exact hineq

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Weighted balance sums expanded over antidiagonals. -/
theorem balance_sum_antidiagonal
    [Fintype FP.toPresentation.Relator] (w : ℕ → ℤ) (b : ℕ → ℕ) (N : ℕ) :
    FP.gsBalanceWeighted w b N =
      ∑ n ∈ Finset.range (N + 1),
        ∑ ij ∈ Finset.antidiagonal n,
          w n * (FP.gsCoeffInt ij.1 * (b ij.2 : ℤ)) := by
  classical
  unfold gsBalanceWeighted
  apply Finset.sum_congr rfl
  intro n hn
  rw [FP.coefficient_balance_antidiagonal b n]
  rw [Finset.mul_sum]

/-- For geometric weights, the antidiagonal exponent may be written as the sum of
coordinates. -/
theorem balance_weighted_antidiagonal
    [Fintype FP.toPresentation.Relator] (x : ℤ) (b : ℕ → ℕ) (N : ℕ) :
    FP.gsBalanceWeighted (fun n => x ^ n) b N =
      ∑ n ∈ Finset.range (N + 1),
        ∑ ij ∈ Finset.antidiagonal n,
          x ^ (ij.1 + ij.2) *
            (FP.gsCoeffInt ij.1 * (b ij.2 : ℤ)) := by
  classical
  rw [FP.balance_sum_antidiagonal]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = n := (Finset.mem_antidiagonal.mp hij)
  simp [hsum]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Geometric weighted sums with the antidiagonal monomial split into two factors. -/
theorem gs_balance_antidiagonal
    [Fintype FP.toPresentation.Relator] (x : ℤ) (b : ℕ → ℕ) (N : ℕ) :
    FP.gsBalanceWeighted (fun n => x ^ n) b N =
      ∑ n ∈ Finset.range (N + 1),
        ∑ ij ∈ Finset.antidiagonal n,
          (FP.gsCoeffInt ij.1 * x ^ ij.1) *
            ((b ij.2 : ℤ) * x ^ ij.2) := by
  classical
  rw [FP.balance_weighted_antidiagonal]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro ij hij
  rw [pow_add]
  ring

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- A finite rectangle can be partitioned by antidiagonals.  This is the basic
finite Fubini identity behind polynomial product evaluations. -/
theorem antidiagonal_filter_rectangle {R : Type} [AddCommMonoid R]
    (A B : ℕ) (f : ℕ → ℕ → R) :
    (∑ n ∈ Finset.range (A + B + 1),
      ∑ ij ∈ (Finset.antidiagonal n).filter (fun ij : ℕ × ℕ => ij.1 ≤ A ∧ ij.2 ≤ B),
        f ij.1 ij.2) =
    ∑ i ∈ Finset.range (A + 1), ∑ j ∈ Finset.range (B + 1), f i j := by
  classical
  rw [← Finset.sum_sigma (s := Finset.range (A + B + 1))
      (t := fun n => (Finset.antidiagonal n).filter
        (fun ij : ℕ × ℕ => ij.1 ≤ A ∧ ij.2 ≤ B))
      (f := fun x : Sigma (fun _ : ℕ => ℕ × ℕ) => f x.2.1 x.2.2)]
  rw [← Finset.sum_product (s := Finset.range (A + 1)) (t := Finset.range (B + 1))
      (f := fun x : ℕ × ℕ => f x.1 x.2)]
  apply Finset.sum_bij (fun x _hx => (x.2.1, x.2.2))
  · intro x hx
    rw [Finset.mem_product]
    rw [Finset.mem_sigma] at hx
    rcases hx with ⟨_hn, hij⟩
    rw [Finset.mem_filter] at hij
    rcases hij with ⟨_hanti, hbds⟩
    constructor <;> simp [hbds.1, hbds.2]
  · intro x hx y hy hxy
    rcases x with ⟨nx, ix⟩
    rcases y with ⟨ny, iy⟩
    simp only at hxy
    have hix : ix = iy := Prod.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
    rw [Finset.mem_sigma] at hx hy
    have hxanti : ix ∈ (Finset.antidiagonal nx) := (Finset.mem_filter.mp hx.2).1
    have hyanti : iy ∈ (Finset.antidiagonal ny) := (Finset.mem_filter.mp hy.2).1
    have hnx : ix.1 + ix.2 = nx := Finset.mem_antidiagonal.mp hxanti
    have hny : iy.1 + iy.2 = ny := Finset.mem_antidiagonal.mp hyanti
    subst iy
    have hn : nx = ny := by omega
    subst ny
    subst nx
    rfl
  · intro y hy
    rcases y with ⟨i, j⟩
    rw [Finset.mem_product] at hy
    rcases hy with ⟨hi, hj⟩
    refine ⟨⟨i + j, (i, j)⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · simp at hi hj ⊢
        omega
      · rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_antidiagonal.mpr rfl
        · constructor <;> (simp at hi hj ⊢; omega)
    · rfl
  · intro x hx
    rfl

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Geometrically weighted total Cauchy sum factors for supported sequences. -/
theorem cauchy_support_bound
    {a : ℕ → ℤ} {b : ℕ → ℕ} {A B : ℕ}
    (ha : ISBound a A) (hb : SSBound b B) (x : ℤ) :
    (∑ n ∈ Finset.range (A + B + 1), cauchyCoeffNat a b n * x ^ n) =
      (∑ i ∈ Finset.range (A + 1), a i * x ^ i) *
        (∑ j ∈ Finset.range (B + 1), (b j : ℤ) * x ^ j) := by
  classical
  calc
    (∑ n ∈ Finset.range (A + B + 1), cauchyCoeffNat a b n * x ^ n) =
        ∑ n ∈ Finset.range (A + B + 1),
          ∑ ij ∈ (Finset.antidiagonal n).filter (fun ij : ℕ × ℕ => ij.1 ≤ A ∧ ij.2 ≤ B),
            (a ij.1 * x ^ ij.1) * ((b ij.2 : ℤ) * x ^ ij.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [cauchy_antidiagonal_bounds ha hb n]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hanti : ij ∈ Finset.antidiagonal n := (Finset.mem_filter.mp hij).1
      have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hanti
      rw [← hsum, pow_add]
      ring
    _ = ∑ i ∈ Finset.range (A + 1), ∑ j ∈ Finset.range (B + 1),
          (a i * x ^ i) * ((b j : ℤ) * x ^ j) := by
      exact antidiagonal_filter_rectangle A B
        (fun i j => (a i * x ^ i) * ((b j : ℤ) * x ^ j))
    _ = (∑ i ∈ Finset.range (A + 1), a i * x ^ i) *
        (∑ j ∈ Finset.range (B + 1), (b j : ℤ) * x ^ j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Geometrically weighted supported GS balance sums factor as polynomial evaluation
 times the weighted coefficient sum. -/
theorem gs_balance_factor
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (x : ℤ) :
    (∑ n ∈ Finset.range (FP.maxRelatorDepth + 1 + B + 1),
        FP.gsCoefficientBalance b n * x ^ n) =
      FP.gsEvalInt x *
        (∑ j ∈ Finset.range (B + 1), (b j : ℤ) * x ^ j) := by
  classical
  let A := FP.maxRelatorDepth + 1
  have hfac := cauchy_support_bound
    (a := FP.gsCoeffInt) (b := b) (A := A) (B := B)
    (ISBound.gsCoeffInt FP) hb x
  have hleft :
      (∑ n ∈ Finset.range (A + B + 1),
        cauchyCoeffNat (FP.gsCoeffInt) b n * x ^ n) =
      ∑ n ∈ Finset.range (A + B + 1),
        FP.gsCoefficientBalance b n * x ^ n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [FP.cauchy_gs_balance b n]
  have heval :
      (∑ i ∈ Finset.range (A + 1), FP.gsCoeffInt i * x ^ i) =
        FP.gsEvalInt x := by
    rfl
  have hbal :
      (∑ n ∈ Finset.range (A + B + 1),
        FP.gsCoefficientBalance b n * x ^ n) =
        (∑ i ∈ Finset.range (A + 1), FP.gsCoeffInt i * x ^ i) *
          (∑ j ∈ Finset.range (B + 1), (b j : ℤ) * x ^ j) := by
    rw [← hleft]
    exact hfac
  simpa [A, gsEvalInt, Nat.add_assoc] using hbal

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Integer-point weighted GS contradiction: at a nonnegative integer `x`, a
negative GS polynomial evaluation is incompatible with a positive weighted mass
of a supported coefficient sequence satisfying all coefficient inequalities. -/
theorem gs_inequalities_int
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ} {x : ℤ}
    (hx : 0 ≤ x) (hb : SSBound b B)
    (hmass : 0 < (∑ j ∈ Finset.range (B + 1), (b j : ℤ) * x ^ j))
    (hneg : FP.gsEvalInt x < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  intro hineq
  let N := FP.maxRelatorDepth + 1 + B
  have hnonneg := FP.gs_balance_inequalities hx N hineq
  have hsum : FP.gsBalanceWeighted (fun n => x ^ n) b N =
      ∑ n ∈ Finset.range (FP.maxRelatorDepth + 1 + B + 1),
        FP.gsCoefficientBalance b n * x ^ n := by
    unfold N gsBalanceWeighted
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hsum] at hnonneg
  rw [FP.gs_balance_factor hb x] at hnonneg
  nlinarith

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- A positive coefficient in a bounded prefix gives positive geometric weighted mass
at a positive integer base. -/
theorem weighted_pos_entry {b : ℕ → ℕ} {B j : ℕ} {x : ℤ}
    (hx : 0 < x) (hj : j ≤ B) (hbj : 0 < b j) :
    0 < (∑ k ∈ Finset.range (B + 1), (b k : ℤ) * x ^ k) := by
  classical
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le (b k))) (pow_nonneg (le_of_lt hx) k)
  · refine ⟨j, ?_, ?_⟩
    · simp [Nat.lt_succ_of_le hj]
    · have hxpow : 0 < x ^ j := pow_pos hx j
      have hbz : 0 < (b j : ℤ) := by exact_mod_cast hbj
      exact mul_pos hbz hxpow

variable {p : ℕ} (FP : FPres p)

/-- Usable integer-evaluation contradiction criterion from one positive prefix entry. -/
theorem inequalities_pos_entry
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B j : ℕ} {x : ℤ}
    (hx : 0 < x) (hb : SSBound b B) (hj : j ≤ B) (hbj : 0 < b j)
    (hneg : FP.gsEvalInt x < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  apply FP.gs_inequalities_int (le_of_lt hx) hb
  · exact weighted_pos_entry hx hj hbj
  · exact hneg

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Truncated-prefix version of the positive-entry integer-evaluation contradiction. -/
theorem inequalities_seq_entry
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N j : ℕ} {x : ℤ}
    (hx : 0 < x) (hj : j ≤ N) (hbj : 0 < b j)
    (hneg : FP.gsEvalInt x < 0) :
    ¬ FP.gsCoefficientInequalities (truncateSeq b N) := by
  apply FP.inequalities_pos_entry
    (b := truncateSeq b N) (B := N) (j := j) hx
    (seq_support_truncate b N) hj
  · simpa [truncate_apply_le b hj] using hbj
  · exact hneg

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Bounded failing degree for a truncated prefix from a negative integer evaluation. -/
theorem failure_seq_entry
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N j : ℕ} {x : ℤ}
    (hx : 0 < x) (hj : j ≤ N) (hbj : 0 < b j)
    (hneg : FP.gsEvalInt x < 0) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  classical
  have hnot := FP.inequalities_seq_entry
    hx hj hbj hneg
  by_contra hnone
  have hallRange : ∀ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (truncateSeq b N) n := by
    intro n hn
    by_contra hf
    exact hnone ⟨n, hn, hf⟩
  have hall := (FP.gs_truncate_seq b N).2 hallRange
  exact hnot hall

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Rational Cauchy coefficient obtained by casting the integer/natural factors. -/
noncomputable def cauchyCoeffRat (a : ℕ → ℤ) (b : ℕ → ℕ) (n : ℕ) : ℚ :=
  ∑ q ∈ Finset.range (n + 1), (a q : ℚ) * (b (n - q) : ℚ)

/-- Rational Cauchy coefficients are casts of the integer Cauchy coefficients. -/
theorem cauchy_rat_int (a : ℕ → ℤ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffRat a b n = (cauchyCoeffNat a b n : ℚ) := by
  classical
  unfold cauchyCoeffRat cauchyCoeffNat
  norm_num

/-- Antidiagonal form of rational Cauchy coefficients. -/
theorem cauchy_rat_antidiagonal (a : ℕ → ℤ) (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffRat a b n =
      ∑ ij ∈ Finset.antidiagonal n, (a ij.1 : ℚ) * (b ij.2 : ℚ) := by
  classical
  rw [cauchy_rat_int, cauchy_coeff_antidiagonal]
  norm_num

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Rational antidiagonal sums may be restricted to support bounds. -/
theorem rat_antidiagonal_bounds {a : ℕ → ℤ} {b : ℕ → ℕ}
    {A B : ℕ} (ha : ISBound a A) (hb : SSBound b B) (n : ℕ) :
    cauchyCoeffRat a b n =
      ∑ ij ∈ (Finset.antidiagonal n).filter (fun ij => ij.1 ≤ A ∧ ij.2 ≤ B),
        (a ij.1 : ℚ) * (b ij.2 : ℚ) := by
  classical
  rw [cauchy_rat_int, cauchy_antidiagonal_bounds ha hb]
  norm_num

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Geometrically weighted total rational Cauchy sum factors for supported sequences. -/
theorem cauchy_rat_bound
    {a : ℕ → ℤ} {b : ℕ → ℕ} {A B : ℕ}
    (ha : ISBound a A) (hb : SSBound b B) (x : ℚ) :
    (∑ n ∈ Finset.range (A + B + 1), cauchyCoeffRat a b n * x ^ n) =
      (∑ i ∈ Finset.range (A + 1), (a i : ℚ) * x ^ i) *
        (∑ j ∈ Finset.range (B + 1), (b j : ℚ) * x ^ j) := by
  classical
  calc
    (∑ n ∈ Finset.range (A + B + 1), cauchyCoeffRat a b n * x ^ n) =
        ∑ n ∈ Finset.range (A + B + 1),
          ∑ ij ∈ (Finset.antidiagonal n).filter (fun ij : ℕ × ℕ => ij.1 ≤ A ∧ ij.2 ≤ B),
            ((a ij.1 : ℚ) * x ^ ij.1) * ((b ij.2 : ℚ) * x ^ ij.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [rat_antidiagonal_bounds ha hb n]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hanti : ij ∈ Finset.antidiagonal n := (Finset.mem_filter.mp hij).1
      have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hanti
      rw [← hsum, pow_add]
      ring
    _ = ∑ i ∈ Finset.range (A + 1), ∑ j ∈ Finset.range (B + 1),
          ((a i : ℚ) * x ^ i) * ((b j : ℚ) * x ^ j) := by
      exact antidiagonal_filter_rectangle A B
        (fun i j => ((a i : ℚ) * x ^ i) * ((b j : ℚ) * x ^ j))
    _ = (∑ i ∈ Finset.range (A + 1), (a i : ℚ) * x ^ i) *
        (∑ j ∈ Finset.range (B + 1), (b j : ℚ) * x ^ j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Evaluate the finite formal GS polynomial at a rational point. -/
noncomputable def gsEvalRat [Fintype FP.toPresentation.Relator] (x : ℚ) : ℚ :=
  ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2), (FP.gsCoeffInt q : ℚ) * x ^ q

/-- Rational Cauchy coefficient of the GS polynomial is the cast of the integer balance. -/
theorem cauchy_rat_balance
    [Fintype FP.toPresentation.Relator] (b : ℕ → ℕ) (n : ℕ) :
    cauchyCoeffRat (FP.gsCoeffInt) b n = (FP.gsCoefficientBalance b n : ℚ) := by
  rw [cauchy_rat_int]
  rw [FP.cauchy_gs_balance b n]

/-- Geometrically weighted supported GS balance sums factor at rational points. -/
theorem gs_balance_rat
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) (x : ℚ) :
    (∑ n ∈ Finset.range (FP.maxRelatorDepth + 1 + B + 1),
        (FP.gsCoefficientBalance b n : ℚ) * x ^ n) =
      FP.gsEvalRat x *
        (∑ j ∈ Finset.range (B + 1), (b j : ℚ) * x ^ j) := by
  classical
  let A := FP.maxRelatorDepth + 1
  have hfac := cauchy_rat_bound
    (a := FP.gsCoeffInt) (b := b) (A := A) (B := B)
    (ISBound.gsCoeffInt FP) hb x
  have hleft :
      (∑ n ∈ Finset.range (A + B + 1),
        cauchyCoeffRat (FP.gsCoeffInt) b n * x ^ n) =
      ∑ n ∈ Finset.range (A + B + 1),
        (FP.gsCoefficientBalance b n : ℚ) * x ^ n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [FP.cauchy_rat_balance b n]
  have hbal :
      (∑ n ∈ Finset.range (A + B + 1),
        (FP.gsCoefficientBalance b n : ℚ) * x ^ n) =
        (∑ i ∈ Finset.range (A + 1), (FP.gsCoeffInt i : ℚ) * x ^ i) *
          (∑ j ∈ Finset.range (B + 1), (b j : ℚ) * x ^ j) := by
    rw [← hleft]
    exact hfac
  simpa [A, gsEvalRat, Nat.add_assoc] using hbal

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Nonnegative rational geometric weights preserve nonnegativity of balance sums. -/
theorem balance_nonneg_inequalities
    [Fintype FP.toPresentation.Relator] {x : ℚ} (hx : 0 ≤ x)
    {b : ℕ → ℕ} (N : ℕ) (hineq : FP.gsCoefficientInequalities b) :
    0 ≤ ∑ n ∈ Finset.range (N + 1), (FP.gsCoefficientBalance b n : ℚ) * x ^ n := by
  classical
  apply Finset.sum_nonneg
  intro n hn
  have hbint : 0 ≤ FP.gsCoefficientBalance b n :=
    (FP.inequality_balance_nonneg b n).1 (hineq n)
  have hbq : 0 ≤ (FP.gsCoefficientBalance b n : ℚ) := by exact_mod_cast hbint
  exact mul_nonneg hbq (pow_nonneg hx n)

/-- Rational-point weighted GS contradiction.  This is the useful `0 < t < 1`
form of the finite-support bookkeeping statement. -/
theorem gs_inequalities_rat
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ} {x : ℚ}
    (hx : 0 ≤ x) (hb : SSBound b B)
    (hmass : 0 < (∑ j ∈ Finset.range (B + 1), (b j : ℚ) * x ^ j))
    (hneg : FP.gsEvalRat x < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  intro hineq
  let N := FP.maxRelatorDepth + 1 + B
  have hnonneg := FP.balance_nonneg_inequalities hx N hineq
  have hfac := FP.gs_balance_rat hb x
  -- rewrite the nonnegative sum using the factorization
  change 0 ≤ ∑ n ∈ Finset.range (N + 1), (FP.gsCoefficientBalance b n : ℚ) * x ^ n at hnonneg
  have hN : N + 1 = FP.maxRelatorDepth + 1 + B + 1 := by rfl
  rw [hN, hfac] at hnonneg
  nlinarith

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- A positive entry gives positive rational geometric mass at a positive base. -/
theorem rat_pos_entry {b : ℕ → ℕ} {B j : ℕ} {x : ℚ}
    (hx : 0 < x) (hj : j ≤ B) (hbj : 0 < b j) :
    0 < (∑ k ∈ Finset.range (B + 1), (b k : ℚ) * x ^ k) := by
  classical
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le (b k))) (pow_nonneg (le_of_lt hx) k)
  · refine ⟨j, ?_, ?_⟩
    · simp [Nat.lt_succ_of_le hj]
    · have hxpow : 0 < x ^ j := pow_pos hx j
      have hbq : 0 < (b j : ℚ) := by exact_mod_cast hbj
      exact mul_pos hbq hxpow

variable {p : ℕ} (FP : FPres p)

/-- Usable rational-evaluation contradiction criterion from one positive prefix entry. -/
theorem inequalities_rat_entry
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B j : ℕ} {x : ℚ}
    (hx : 0 < x) (hb : SSBound b B) (hj : j ≤ B) (hbj : 0 < b j)
    (hneg : FP.gsEvalRat x < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  apply FP.gs_inequalities_rat (le_of_lt hx) hb
  · exact rat_pos_entry hx hj hbj
  · exact hneg

/-- Truncated-prefix rational-evaluation contradiction. -/
theorem inequalities_truncate_entry
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N j : ℕ} {x : ℚ}
    (hx : 0 < x) (hj : j ≤ N) (hbj : 0 < b j)
    (hneg : FP.gsEvalRat x < 0) :
    ¬ FP.gsCoefficientInequalities (truncateSeq b N) := by
  apply FP.inequalities_rat_entry
    (b := truncateSeq b N) (B := N) (j := j) hx
    (seq_support_truncate b N) hj
  · simpa [truncate_apply_le b hj] using hbj
  · exact hneg

/-- Bounded failing degree for a truncated prefix from a negative rational evaluation. -/
theorem failure_truncate_entry
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N j : ℕ} {x : ℚ}
    (hx : 0 < x) (hj : j ≤ N) (hbj : 0 < b j)
    (hneg : FP.gsEvalRat x < 0) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  classical
  have hnot := FP.inequalities_truncate_entry
    hx hj hbj hneg
  by_contra hnone
  have hallRange : ∀ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (truncateSeq b N) n := by
    intro n hn
    by_contra hf
    exact hnone ⟨n, hn, hf⟩
  have hall := (FP.gs_truncate_seq b N).2 hallRange
  exact hnot hall

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Rational evaluation extends integer evaluation on integer points. -/
theorem gs_rat_cast [Fintype FP.toPresentation.Relator] (x : ℤ) :
    FP.gsEvalRat (x : ℚ) = (FP.gsEvalInt x : ℚ) := by
  classical
  unfold gsEvalRat gsEvalInt
  norm_num

@[simp] theorem gs_rat_one [Fintype FP.toPresentation.Relator] :
    FP.gsEvalRat 1 =
      (1 : ℚ) - (FP.generatorCount : ℚ) +
        (Nat.card FP.toPresentation.Relator : ℚ) := by
  have h := FP.gs_rat_cast (1 : ℤ)
  norm_num at h
  simpa only [Nat.card_coe_set_eq] using h

@[simp] theorem gs_rat_zero [Fintype FP.toPresentation.Relator] :
    FP.gsEvalRat 0 = 1 + (FP.relatorDepthMultiplicity 0 : ℚ) := by
  have h := FP.gs_rat_cast (0 : ℤ)
  norm_num at h
  exact h

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Positive nat prefix mass contains a positive entry. -/
theorem pos_entry_range {b : ℕ → ℕ} {B : ℕ}
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k) :
    ∃ j, j ≤ B ∧ 0 < b j := by
  classical
  have hne : (∑ k ∈ Finset.range (B + 1), b k) ≠ 0 := Nat.ne_of_gt hmass
  obtain ⟨j, hj, hjnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨j, ?_, Nat.pos_of_ne_zero hjnz⟩
  have hjlt := Finset.mem_range.mp hj
  omega

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Positive nat prefix mass gives positive rational weighted mass at a positive base. -/
theorem weighted_rat_mass {b : ℕ → ℕ} {B : ℕ} {x : ℚ}
    (hx : 0 < x) (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k) :
    0 < (∑ k ∈ Finset.range (B + 1), (b k : ℚ) * x ^ k) := by
  obtain ⟨j, hj, hbj⟩ := pos_entry_range (b := b) (B := B) hmass
  exact rat_pos_entry hx hj hbj

variable {p : ℕ} (FP : FPres p)

/-- Rational-evaluation contradiction from positive nat prefix mass. -/
theorem inequalities_rat_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ} {x : ℚ}
    (hx : 0 < x) (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k)
    (hneg : FP.gsEvalRat x < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  apply FP.gs_inequalities_rat (le_of_lt hx) hb
  · exact weighted_rat_mass hx hmass
  · exact hneg

/-- Truncated-prefix rational-evaluation contradiction from positive prefix mass. -/
theorem inequalities_seq_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N : ℕ} {x : ℚ}
    (hx : 0 < x) (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k)
    (hneg : FP.gsEvalRat x < 0) :
    ¬ FP.gsCoefficientInequalities (truncateSeq b N) := by
  apply FP.inequalities_rat_mass hx
    (seq_support_truncate b N)
  · simpa [range_seq_self b N] using hmass
  · exact hneg

/-- Bounded failing degree from positive prefix mass and a negative rational evaluation. -/
theorem failure_truncate_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N : ℕ} {x : ℚ}
    (hx : 0 < x) (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k)
    (hneg : FP.gsEvalRat x < 0) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  classical
  have hnot := FP.inequalities_seq_mass
    hx hmass hneg
  by_contra hnone
  have hallRange : ∀ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (truncateSeq b N) n := by
    intro n hn
    by_contra hf
    exact hnone ⟨n, hn, hf⟩
  have hall := (FP.gs_truncate_seq b N).2 hallRange
  exact hnot hall

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Clearing a positive denominator in a single rational monomial. -/
theorem rat_div_mul (m d : ℚ) (hd : d ≠ 0) {q A : ℕ} (hq : q ≤ A) :
    (m / d) ^ q * d ^ A = m ^ q * d ^ (A - q) := by
  rw [div_pow, div_eq_mul_inv]
  calc
    m ^ q * (d ^ q)⁻¹ * d ^ A = m ^ q * ((d ^ q)⁻¹ * d ^ A) := by ring
    _ = m ^ q * d ^ (A - q) := by
      congr 1
      have hdq : d ^ q ≠ 0 := pow_ne_zero q hd
      apply (inv_mul_eq_iff_eq_mul₀ hdq).2
      rw [mul_comm]
      exact (pow_sub_mul_pow d hq).symm

variable {p : ℕ} (FP : FPres p)

/-- Denominator-cleared form of rational GS-polynomial evaluation. -/
theorem rat_div_cleared
    [Fintype FP.toPresentation.Relator] (m d : ℚ) (hd : d ≠ 0) :
    FP.gsEvalRat (m / d) * d ^ (FP.maxRelatorDepth + 1) =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (FP.gsCoeffInt q : ℚ) * m ^ q *
          d ^ (FP.maxRelatorDepth + 1 - q) := by
  classical
  let A := FP.maxRelatorDepth + 1
  unfold gsEvalRat
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  have hqle : q ≤ A := by
    have hlt := Finset.mem_range.mp hq
    simp [A] at hlt ⊢
    omega
  calc
    (FP.gsCoeffInt q : ℚ) * (m / d) ^ q * d ^ A =
        (FP.gsCoeffInt q : ℚ) * ((m / d) ^ q * d ^ A) := by ring
    _ = (FP.gsCoeffInt q : ℚ) * (m ^ q * d ^ (A - q)) := by
      rw [rat_div_mul m d hd hqle]
    _ = (FP.gsCoeffInt q : ℚ) * m ^ q * d ^ (A - q) := by ring

/-- A negative denominator-cleared value certifies a negative rational evaluation. -/
theorem gs_rat_cleared
    [Fintype FP.toPresentation.Relator] {m d : ℚ} (hdpos : 0 < d)
    (hclear : (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (FP.gsCoeffInt q : ℚ) * m ^ q *
          d ^ (FP.maxRelatorDepth + 1 - q)) < 0) :
    FP.gsEvalRat (m / d) < 0 := by
  classical
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hpowpos : 0 < d ^ (FP.maxRelatorDepth + 1) := pow_pos hdpos _
  have hprod : FP.gsEvalRat (m / d) * d ^ (FP.maxRelatorDepth + 1) < 0 := by
    rw [FP.rat_div_cleared m d hdne]
    exact hclear
  by_contra hnot
  have hnonneg : 0 ≤ FP.gsEvalRat (m / d) := le_of_not_gt hnot
  have hprod_nonneg : 0 ≤ FP.gsEvalRat (m / d) * d ^ (FP.maxRelatorDepth + 1) :=
    mul_nonneg hnonneg (le_of_lt hpowpos)
  linarith

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Cleared-denominator certificate form of the rational-evaluation contradiction,
for a positive rational point `m/d`. -/
theorem cleared_rat_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ} {m d : ℚ}
    (hmpos : 0 < m) (hdpos : 0 < d) (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k)
    (hclear : (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (FP.gsCoeffInt q : ℚ) * m ^ q *
          d ^ (FP.maxRelatorDepth + 1 - q)) < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  have hx : 0 < m / d := div_pos hmpos hdpos
  have hneg : FP.gsEvalRat (m / d) < 0 :=
    FP.gs_rat_cleared hdpos hclear
  exact FP.inequalities_rat_mass hx hb hmass hneg

/-- Truncated-prefix cleared-denominator certificate with bounded support implicit. -/
theorem inequalities_cleared_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N : ℕ} {m d : ℚ}
    (hmpos : 0 < m) (hdpos : 0 < d)
    (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k)
    (hclear : (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (FP.gsCoeffInt q : ℚ) * m ^ q *
          d ^ (FP.maxRelatorDepth + 1 - q)) < 0) :
    ¬ FP.gsCoefficientInequalities (truncateSeq b N) := by
  apply FP.cleared_rat_mass
    hmpos hdpos (seq_support_truncate b N)
  · simpa [range_seq_self b N] using hmass
  · exact hclear

/-- Bounded failing degree from a cleared-denominator negative rational certificate. -/
theorem failure_cleared_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N : ℕ} {m d : ℚ}
    (hmpos : 0 < m) (hdpos : 0 < d)
    (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k)
    (hclear : (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (FP.gsCoeffInt q : ℚ) * m ^ q *
          d ^ (FP.maxRelatorDepth + 1 - q)) < 0) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  classical
  have hnot := FP.inequalities_cleared_mass
    hmpos hdpos hmass hclear
  by_contra hnone
  have hallRange : ∀ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (truncateSeq b N) n := by
    intro n hn
    by_contra hf
    exact hnone ⟨n, hn, hf⟩
  have hall := (FP.gs_truncate_seq b N).2 hallRange
  exact hnot hall

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Integer denominator-cleared evaluation at a positive rational `m/d` with
natural numerator and denominator. -/
noncomputable def gsClearedNat [Fintype FP.toPresentation.Relator]
    (m d : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
    FP.gsCoeffInt q * (m : ℤ) ^ q *
      (d : ℤ) ^ (FP.maxRelatorDepth + 1 - q)

/-- Casting the natural cleared evaluation to `ℚ` gives the rational cleared sum. -/
theorem coe_gs_cleared
    [Fintype FP.toPresentation.Relator] (m d : ℕ) :
    (FP.gsClearedNat m d : ℚ) =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (FP.gsCoeffInt q : ℚ) * (m : ℚ) ^ q *
          (d : ℚ) ^ (FP.maxRelatorDepth + 1 - q) := by
  classical
  unfold gsClearedNat
  norm_num

/-- Integer cleared certificate implies a negative rational evaluation at `m/d`. -/
theorem gs_div_cleared
    [Fintype FP.toPresentation.Relator] {m d : ℕ} (hdpos : 0 < d)
    (hclear : FP.gsClearedNat m d < 0) :
    FP.gsEvalRat ((m : ℚ) / (d : ℚ)) < 0 := by
  apply FP.gs_rat_cleared (m := (m : ℚ)) (d := (d : ℚ))
  · exact_mod_cast hdpos
  · rw [← FP.coe_gs_cleared m d]
    exact_mod_cast hclear

/-- Fully integral certificate form of the rational-evaluation contradiction. -/
theorem gs_cleared_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B m d : ℕ}
    (hmpos : 0 < m) (hdpos : 0 < d) (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k)
    (hclear : FP.gsClearedNat m d < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  have hx : 0 < (m : ℚ) / (d : ℚ) := by
    apply div_pos <;> exact_mod_cast (by assumption)
  have hneg := FP.gs_div_cleared hdpos hclear
  exact FP.inequalities_rat_mass hx hb hmass hneg

/-- Truncated integral certificate form. -/
theorem seq_cleared_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N m d : ℕ}
    (hmpos : 0 < m) (hdpos : 0 < d)
    (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k)
    (hclear : FP.gsClearedNat m d < 0) :
    ¬ FP.gsCoefficientInequalities (truncateSeq b N) := by
  apply FP.gs_cleared_mass
    hmpos hdpos (seq_support_truncate b N)
  · simpa [range_seq_self b N] using hmass
  · exact hclear

/-- Bounded failing degree from a fully integral rational certificate. -/
theorem failure_seq_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N m d : ℕ}
    (hmpos : 0 < m) (hdpos : 0 < d)
    (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k)
    (hclear : FP.gsClearedNat m d < 0) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  classical
  have hnot := FP.seq_cleared_mass
    hmpos hdpos hmass hclear
  by_contra hnone
  have hallRange : ∀ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (truncateSeq b N) n := by
    intro n hn
    by_contra hf
    exact hnone ⟨n, hn, hf⟩
  have hall := (FP.gs_truncate_seq b N).2 hallRange
  exact hnot hall

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- A finite, fully integral certificate that the formal GS polynomial is negative
at the positive rational point `num/den`.  The optional classical restriction
`num < den` is kept as a field because most GS applications use a point in `(0,1)`. -/
structure RGCert [Fintype FP.toPresentation.Relator] where
  num : ℕ
  den : ℕ
  num_pos : 0 < num
  den_pos : 0 < den
  proper : num < den
  cleared_neg : FP.gsClearedNat num den < 0

namespace RGCert

variable [Fintype FP.toPresentation.Relator] (C : FP.RGCert)

/-- The rational point represented by a certificate. -/
def point : ℚ := (C.num : ℚ) / (C.den : ℚ)

/-- The certified point is positive. -/
theorem point_pos : 0 < C.point := by
  unfold point
  apply div_pos <;> exact_mod_cast (by first | exact C.num_pos | exact C.den_pos)

/-- The certified point is strictly less than one. -/
theorem point_lt_one : C.point < 1 := by
  unfold point
  have hdq : (0 : ℚ) < C.den := by exact_mod_cast C.den_pos
  rw [div_lt_one hdq]
  exact_mod_cast C.proper

/-- The formal GS polynomial is negative at the certified point. -/
theorem eval_neg : FP.gsEvalRat C.point < 0 := by
  unfold point
  exact FP.gs_div_cleared C.den_pos C.cleared_neg

end RGCert

/-- Certificate-packaged contradiction for supported nonzero coefficient sequences. -/
theorem inequalities_certificate_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (C : FP.RGCert) (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k) :
    ¬ FP.gsCoefficientInequalities b := by
  exact FP.inequalities_rat_mass
    (C.point_pos) hb hmass (C.eval_neg)

/-- Certificate-packaged bounded failing degree for a nonzero truncation. -/
theorem failure_certificate_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N : ℕ}
    (C : FP.RGCert)
    (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  exact FP.failure_truncate_mass
    (C.point_pos) hmass (C.eval_neg)

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Weighted sum of a delta coefficient over a range containing its support. -/
theorem sum_delta_coeff (k : ℕ) (c : ℤ) (w : ℕ → ℤ) {N : ℕ}
    (hk : k < N) :
    (∑ q ∈ Finset.range N, deltaCoeff k c q * w q) = c * w k := by
  classical
  unfold deltaCoeff
  rw [Finset.sum_eq_single k]
  · simp
  · intro q hq hqk
    simp [hqk]
  · intro hknot
    exact False.elim (hknot (by simpa using hk))

/-- Weighted sum of a delta coefficient over a range missing its support. -/
theorem range_delta_coeff (k : ℕ) (c : ℤ) (w : ℕ → ℤ) {N : ℕ}
    (hN : N ≤ k) :
    (∑ q ∈ Finset.range N, deltaCoeff k c q * w q) = 0 := by
  classical
  unfold deltaCoeff
  apply Finset.sum_eq_zero
  intro q hq
  have hqk : q ≠ k := by
    have hqN : q < N := Finset.mem_range.mp hq
    omega
  simp [hqk]

variable {p : ℕ} (FP : FPres p)

/-- Expanded numerator/denominator-cleared GS polynomial value: the two delta
terms are displayed separately from the relator-depth histogram. -/
theorem gs_cleared_expanded
    [Fintype FP.toPresentation.Relator] (m d : ℕ) :
    FP.gsClearedNat m d =
      (d : ℤ) ^ (FP.maxRelatorDepth + 1)
      - (FP.generatorCount : ℤ) * (m : ℤ) * (d : ℤ) ^ FP.maxRelatorDepth
      + ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
          (FP.relatorDepthMultiplicity q : ℤ) * (m : ℤ) ^ q *
            (d : ℤ) ^ (FP.maxRelatorDepth + 1 - q) := by
  classical
  let A := FP.maxRelatorDepth + 1
  let w : ℕ → ℤ := fun q => (m : ℤ) ^ q * (d : ℤ) ^ (A - q)
  unfold gsClearedNat gsCoeffInt
  -- reassociate each term so the delta/histogram sums split cleanly.
  have hsplit :
      (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (deltaCoeff 0 (1 : ℤ) q + deltaCoeff 1 (-(FP.generatorCount : ℤ)) q +
          (FP.relatorDepthMultiplicity q : ℤ)) * (m : ℤ) ^ q *
          (d : ℤ) ^ (FP.maxRelatorDepth + 1 - q)) =
      (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2), deltaCoeff 0 (1 : ℤ) q * w q) +
      (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        deltaCoeff 1 (-(FP.generatorCount : ℤ)) q * w q) +
      (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (FP.relatorDepthMultiplicity q : ℤ) * w q) := by
    simp [w, A, add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [hsplit]
  have h0 := sum_delta_coeff 0 (1 : ℤ) w
      (N := FP.maxRelatorDepth + 2) (by omega)
  have h1 := sum_delta_coeff 1 (-(FP.generatorCount : ℤ)) w
      (N := FP.maxRelatorDepth + 2) (by omega)
  rw [h0, h1]
  have htail : FP.relatorDepthMultiplicity (FP.maxRelatorDepth + 1) = 0 :=
    FP.relator_multiplicity_max (by omega)
  have hhist :
      (∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        (FP.relatorDepthMultiplicity q : ℤ) * w q) =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
        (FP.relatorDepthMultiplicity q : ℤ) * w q := by
    rw [show FP.maxRelatorDepth + 2 = (FP.maxRelatorDepth + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    simp [htail]
  rw [hhist]
  simp [w, A]
  ring_nf

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Constructor for a rational GS certificate from the expanded histogram inequality. -/
def RGCert.ofExpanded [Fintype FP.toPresentation.Relator]
    (num den : ℕ) (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hneg : (den : ℤ) ^ (FP.maxRelatorDepth + 1)
      - (FP.generatorCount : ℤ) * (num : ℤ) * (den : ℤ) ^ FP.maxRelatorDepth
      + ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
          (FP.relatorDepthMultiplicity q : ℤ) * (num : ℤ) ^ q *
            (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q) < 0) :
    FP.RGCert where
  num := num
  den := den
  num_pos := hnum
  den_pos := hden
  proper := hproper
  cleared_neg := by
    rw [FP.gs_cleared_expanded]
    exact hneg

/-- Direct contradiction wrapper using the expanded histogram inequality. -/
theorem inequalities_expanded_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B num den : ℕ}
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k)
    (hneg : (den : ℤ) ^ (FP.maxRelatorDepth + 1)
      - (FP.generatorCount : ℤ) * (num : ℤ) * (den : ℤ) ^ FP.maxRelatorDepth
      + ∑ q ∈ Finset.range (FP.maxRelatorDepth + 1),
          (FP.relatorDepthMultiplicity q : ℤ) * (num : ℤ) ^ q *
            (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q) < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  let C := RGCert.ofExpanded FP num den hnum hden hproper hneg
  exact FP.inequalities_certificate_mass C hb hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Standalone integer expression for a denominator-cleared GS polynomial value,
parameterized only by a generator count, a maximum depth, and a depth histogram. -/
def clearedGSExpression (gen M : ℕ) (hist : ℕ → ℕ) (num den : ℕ) : ℤ :=
  (den : ℤ) ^ (M + 1) - (gen : ℤ) * (num : ℤ) * (den : ℤ) ^ M +
    ∑ q ∈ Finset.range (M + 1),
      (hist q : ℤ) * (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q)

variable {p : ℕ} (FP : FPres p)

/-- The standalone cleared expression specializes to the formal GS polynomial certificate. -/
theorem gs_cleared_expression
    [Fintype FP.toPresentation.Relator] (num den : ℕ) :
    FP.gsClearedNat num den =
      clearedGSExpression FP.generatorCount FP.maxRelatorDepth
        FP.relatorDepthMultiplicity num den := by
  rw [FP.gs_cleared_expanded]
  rfl

/-- Certificate constructor using the standalone cleared expression. -/
def RGCert.ofExpression [Fintype FP.toPresentation.Relator]
    (num den : ℕ) (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hneg : clearedGSExpression FP.generatorCount FP.maxRelatorDepth
        FP.relatorDepthMultiplicity num den < 0) :
    FP.RGCert := by
  refine RGCert.ofExpanded FP num den hnum hden hproper ?_
  simpa [clearedGSExpression] using hneg

/-- Direct contradiction wrapper using the standalone cleared expression. -/
theorem inequalities_expression_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B num den : ℕ}
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k)
    (hneg : clearedGSExpression FP.generatorCount FP.maxRelatorDepth
        FP.relatorDepthMultiplicity num den < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  let C := RGCert.ofExpression FP num den hnum hden hproper hneg
  exact FP.inequalities_certificate_mass C hb hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- The standalone cleared expression is monotone in the relator histogram when
`num, den` are natural (hence all monomial weights are nonnegative). -/
theorem cleared_expression_hist {gen M : ℕ} {hist hist' : ℕ → ℕ}
    (num den : ℕ) (hh : ∀ q, q ≤ M → hist q ≤ hist' q) :
    clearedGSExpression gen M hist num den ≤
      clearedGSExpression gen M hist' num den := by
  classical
  unfold clearedGSExpression
  have hsum :
      (∑ q ∈ Finset.range (M + 1),
        (hist q : ℤ) * (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q)) ≤
      ∑ q ∈ Finset.range (M + 1),
        (hist' q : ℤ) * (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q) := by
    apply Finset.sum_le_sum
    intro q hq
    have hqle : q ≤ M := by
      have hlt := Finset.mem_range.mp hq
      omega
    have hhist : (hist q : ℤ) ≤ (hist' q : ℤ) := by exact_mod_cast hh q hqle
    have hweight : 0 ≤ (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q) := by
      exact mul_nonneg (pow_nonneg (by exact_mod_cast Nat.zero_le num) q)
        (pow_nonneg (by exact_mod_cast Nat.zero_le den) _)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hhist hweight
  linarith

/-- The standalone cleared expression is antitone in the generator count. -/
theorem cleared_antitone_gen {gen gen' M : ℕ} {hist : ℕ → ℕ}
    (num den : ℕ) (hgen : gen ≤ gen') :
    clearedGSExpression gen' M hist num den ≤
      clearedGSExpression gen M hist num den := by
  classical
  unfold clearedGSExpression
  have hgenz : (gen : ℤ) ≤ (gen' : ℤ) := by exact_mod_cast hgen
  have hweight : 0 ≤ (num : ℤ) * (den : ℤ) ^ M := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le num)
      (pow_nonneg (by exact_mod_cast Nat.zero_le den) M)
  have hmul : (gen : ℤ) * ((num : ℤ) * (den : ℤ) ^ M) ≤
      (gen' : ℤ) * ((num : ℤ) * (den : ℤ) ^ M) :=
    mul_le_mul_of_nonneg_right hgenz hweight
  ring_nf at hmul ⊢
  linarith

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Negativity transfers from a conservative certificate using a lower generator
bound and an upper histogram bound. -/
theorem cleared_expression_bounds {genLower gen M : ℕ}
    {hist histUpper : ℕ → ℕ} {num den : ℕ}
    (hgen : genLower ≤ gen)
    (hhist : ∀ q, q ≤ M → hist q ≤ histUpper q)
    (hneg : clearedGSExpression genLower M histUpper num den < 0) :
    clearedGSExpression gen M hist num den < 0 := by
  have h1 := cleared_expression_hist (gen := gen) (M := M)
    (hist := hist) (hist' := histUpper) num den hhist
  have h2 := cleared_antitone_gen (gen := genLower) (gen' := gen)
    (M := M) (hist := histUpper) num den hgen
  linarith

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Build a certificate from conservative numerical bounds: a lower bound on the
generator count and an upper bound on each histogram entry. -/
def RGCert.ofBounds [Fintype FP.toPresentation.Relator]
    (num den genLower : ℕ) (histUpper : ℕ → ℕ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hhist : ∀ q, q ≤ FP.maxRelatorDepth →
      FP.relatorDepthMultiplicity q ≤ histUpper q)
    (hneg : clearedGSExpression genLower FP.maxRelatorDepth histUpper num den < 0) :
    FP.RGCert := by
  refine RGCert.ofExpression FP num den hnum hden hproper ?_
  exact cleared_expression_bounds (genLower := genLower)
    (gen := FP.generatorCount) (M := FP.maxRelatorDepth)
    (hist := FP.relatorDepthMultiplicity) (histUpper := histUpper)
    (num := num) (den := den) hgen hhist hneg

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Relator part of the standalone cleared GS expression. -/
def clearedGSRelator (M : ℕ) (hist : ℕ → ℕ) (num den : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (M + 1),
    (hist q : ℤ) * (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q)

/-- Base (constant minus generator) part of the cleared expression. -/
def clearedGSBase (gen M num den : ℕ) : ℤ :=
  (den : ℤ) ^ (M + 1) - (gen : ℤ) * (num : ℤ) * (den : ℤ) ^ M

@[simp] theorem cleared_expression_sum
    (gen M : ℕ) (hist : ℕ → ℕ) (num den : ℕ) :
    clearedGSExpression gen M hist num den =
      clearedGSBase gen M num den + clearedGSRelator M hist num den := by
  rfl

/-- If the relator weighted sum is bounded above and the generator count is bounded
below, negativity of the coarse expression transfers to the exact expression. -/
theorem cleared_gs_expression {genLower gen M : ℕ}
    {hist : ℕ → ℕ} {num den : ℕ} {relBound : ℤ}
    (hgen : genLower ≤ gen)
    (hrel : clearedGSRelator M hist num den ≤ relBound)
    (hneg : clearedGSBase genLower M num den + relBound < 0) :
    clearedGSExpression gen M hist num den < 0 := by
  have hgenAnti := cleared_antitone_gen (gen := genLower) (gen' := gen)
    (M := M) (hist := hist) num den hgen
  have hexactBound : clearedGSExpression genLower M hist num den ≤
      clearedGSBase genLower M num den + relBound := by
    simp [cleared_expression_sum]
    linarith
  linarith

variable {p : ℕ} (FP : FPres p)

/-- Certificate constructor from a coarse upper bound on the weighted relator sum. -/
def RGCert.relator_sum_bound [Fintype FP.toPresentation.Relator]
    (num den genLower : ℕ) (relBound : ℤ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hrel : clearedGSRelator FP.maxRelatorDepth FP.relatorDepthMultiplicity num den ≤ relBound)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den + relBound < 0) :
    FP.RGCert := by
  refine RGCert.ofExpression FP num den hnum hden hproper ?_
  exact cleared_gs_expression (genLower := genLower)
    (gen := FP.generatorCount) (M := FP.maxRelatorDepth)
    (hist := FP.relatorDepthMultiplicity) (num := num) (den := den)
    (relBound := relBound) hgen hrel hneg

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Natural denominator-cleared monomial weight `num^q * den^(A-q)`.  This small
standalone abbreviation is useful for coarse certificate estimates. -/
def clearedWeightNat (A num den q : ℕ) : ℕ := num ^ q * den ^ (A - q)

/-- Integer version of the denominator-cleared monomial weight. -/
def clearedWeightInt (A num den q : ℕ) : ℤ := (num : ℤ) ^ q * (den : ℤ) ^ (A - q)

/-- For `num ≤ den`, the cleared weights are antitone in the exponent index. -/
theorem cleared_nat_antitone {num den A q r : ℕ} (hnd : num ≤ den)
    (hqr : q ≤ r) (hrA : r ≤ A) :
    clearedWeightNat A num den r ≤ clearedWeightNat A num den q := by
  unfold clearedWeightNat
  have hr_eq : r = q + (r - q) := (Nat.add_sub_of_le hqr).symm
  have hAq : A - q = (r - q) + (A - r) := by omega
  rw [hr_eq, pow_add, hAq, pow_add]
  have hsub : A - (q + (r - q)) = A - r := by omega
  rw [hsub]
  rw [← Nat.mul_assoc (num ^ q) (den ^ (r - q)) (den ^ (A - r))]
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left hnd _

/-- Integer-cast form of `cleared_nat_antitone`. -/
theorem cleared_int_antitone {num den A q r : ℕ} (hnd : num ≤ den)
    (hqr : q ≤ r) (hrA : r ≤ A) :
    clearedWeightInt A num den r ≤ clearedWeightInt A num den q := by
  unfold clearedWeightInt
  have hn := cleared_nat_antitone (A := A) (num := num) (den := den)
    (q := q) (r := r) hnd hqr hrA
  unfold clearedWeightNat at hn
  exact_mod_cast hn

/-- Coarse bound for the cleared relator sum from a lower depth cutoff and a total
count bound.  If all histogram mass lies in depths at least `q0`, then for
`num ≤ den` every surviving weight is bounded by the weight at `q0`. -/
theorem cleared_gs_weight {M q0 R num den : ℕ}
    {hist : ℕ → ℕ} (hnd : num ≤ den)
    (hsupp : ∀ q, q < q0 → hist q = 0)
    (hcount : (∑ q ∈ Finset.range (M + 1), hist q) ≤ R) :
    clearedGSRelator M hist num den ≤
      (R : ℤ) * ((num : ℤ) ^ q0 * (den : ℤ) ^ (M + 1 - q0)) := by
  classical
  unfold clearedGSRelator
  let W : ℤ := (num : ℤ) ^ q0 * (den : ℤ) ^ (M + 1 - q0)
  have hterm : ∀ q ∈ Finset.range (M + 1),
      (hist q : ℤ) * (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q) ≤
        (hist q : ℤ) * W := by
    intro q hq
    have hqA : q ≤ M + 1 := by
      have := Finset.mem_range.mp hq
      omega
    by_cases hlow : q < q0
    · have hz := hsupp q hlow
      simp [hz, W]
    · have hq0q : q0 ≤ q := by omega
      have hw : (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q) ≤ W := by
        dsimp [W]
        exact cleared_int_antitone (A := M + 1) (num := num) (den := den)
          (q := q0) (r := q) hnd hq0q hqA
      have hhistnon : 0 ≤ (hist q : ℤ) := by exact_mod_cast Nat.zero_le (hist q)
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hw hhistnon
  have hsum := Finset.sum_le_sum hterm
  have hfactor : (∑ q ∈ Finset.range (M + 1), (hist q : ℤ) * W) =
      ((∑ q ∈ Finset.range (M + 1), hist q : ℕ) : ℤ) * W := by
    simp [Finset.sum_mul]
  rw [hfactor] at hsum
  have hcountz : ((∑ q ∈ Finset.range (M + 1), hist q : ℕ) : ℤ) ≤ (R : ℤ) := by
    exact_mod_cast hcount
  have hWnon : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (pow_nonneg (by exact_mod_cast Nat.zero_le num) _)
      (pow_nonneg (by exact_mod_cast Nat.zero_le den) _)
  have hprod := mul_le_mul_of_nonneg_right hcountz hWnon
  linarith

variable {p : ℕ} (FP : FPres p)

/-- Range sum of the depth multiplicity histogram, in the notation used by the
coarse relator-sum bounds. -/
theorem sum_multiplicity_relators
    [Fintype FP.toPresentation.Relator] :
    (∑ q ∈ Finset.range (FP.maxRelatorDepth + 1), FP.relatorDepthMultiplicity q) =
      Nat.card FP.toPresentation.Relator := by
  simpa using FP.sum_finsupp_relators

/-- Certificate constructor from a lower depth cutoff and a coarse total relator
count bound.  This is the formal version of the common estimate
`r(t) ≤ R * t^q0` after denominator clearing. -/
def RGCert.depth_cutoff_countbound [Fintype FP.toPresentation.Relator]
    (num den genLower q0 relCountBound : ℕ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hsupp : ∀ q, q < q0 → FP.relatorDepthMultiplicity q = 0)
    (hcount : Nat.card FP.toPresentation.Relator ≤ relCountBound)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        (relCountBound : ℤ) * ((num : ℤ) ^ q0 *
          (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0)) < 0) :
    FP.RGCert := by
  refine RGCert.relator_sum_bound FP num den genLower
    ((relCountBound : ℤ) * ((num : ℤ) ^ q0 *
      (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0))) hnum hden hproper hgen ?_ hneg
  apply cleared_gs_weight
  · exact Nat.le_of_lt hproper
  · exact hsupp
  · have hsum := FP.sum_multiplicity_relators
    omega

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- A uniform certified lower bound on relator depths kills all histogram entries
below that bound. -/
theorem relator_uniform_lower
    [Fintype FP.toPresentation.Relator] {q0 q : ℕ}
    (hD : ∀ r : FP.toPresentation.Relator, q0 ≤ FP.depths.depth r) (hq : q < q0) :
    FP.relatorDepthMultiplicity q = 0 := by
  classical
  unfold relatorDepthMultiplicity
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro r _ hr
  have := hD r
  omega

/-- Convenience certificate constructor using a uniform relator-depth lower bound
instead of an explicit histogram-support proof. -/
def RGCert.uniform_depth_countbound [Fintype FP.toPresentation.Relator]
    (num den genLower q0 relCountBound : ℕ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ r : FP.toPresentation.Relator, q0 ≤ FP.depths.depth r)
    (hcount : Nat.card FP.toPresentation.Relator ≤ relCountBound)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        (relCountBound : ℤ) * ((num : ℤ) ^ q0 *
          (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0)) < 0) :
    FP.RGCert :=
  RGCert.depth_cutoff_countbound FP num den genLower q0 relCountBound
    hnum hden hproper hgen
    (fun _ hq => FP.relator_uniform_lower hD hq)
    hcount hneg

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- The exact-count specialization of `uniform_depth_countbound`, using the actual
number of relators as the coarse count. -/
def RGCert.ofUniformDepth [Fintype FP.toPresentation.Relator]
    (num den genLower q0 : ℕ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ r : FP.toPresentation.Relator, q0 ≤ FP.depths.depth r)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        (Nat.card FP.toPresentation.Relator : ℤ) * ((num : ℤ) ^ q0 *
          (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0)) < 0) :
    FP.RGCert :=
  RGCert.uniform_depth_countbound FP num den genLower q0
    (Nat.card FP.toPresentation.Relator) hnum hden hproper hgen hD (le_rfl) hneg

/-- Direct GS-inequality contradiction from the classical uniform-depth/count
numerical estimate, stated with positive finite prefix mass. -/
theorem inequalities_uniform_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B num den genLower q0 : ℕ}
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ r : FP.toPresentation.Relator, q0 ≤ FP.depths.depth r)
    (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        (Nat.card FP.toPresentation.Relator : ℤ) * ((num : ℤ) ^ q0 *
          (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0)) < 0) :
    ¬ FP.gsCoefficientInequalities b := by
  let C := RGCert.ofUniformDepth FP num den genLower q0
    hnum hden hproper hgen hD hneg
  exact FP.inequalities_certificate_mass C hb hmass

/-- Bounded failing-degree version of the uniform-depth exact-count criterion,
stated for the truncated sequence supported up to `N`. -/
theorem failure_uniform_mass
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N num den genLower q0 : ℕ}
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ r : FP.toPresentation.Relator, q0 ≤ FP.depths.depth r)
    (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        (Nat.card FP.toPresentation.Relator : ℤ) * ((num : ℤ) ^ q0 *
          (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0)) < 0) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  let C := RGCert.ofUniformDepth FP num den genLower q0
    hnum hden hproper hgen hD hneg
  exact FP.failure_certificate_mass C hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- The cleared relator sum for the zero histogram vanishes. -/
@[simp] theorem cleared_gs_zero (M num den : ℕ) :
    clearedGSRelator M (fun _ => 0) num den = 0 := by
  simp [clearedGSRelator]

/-- The cleared relator sum is additive in the histogram. -/
theorem cleared_gs_add (M num den : ℕ) (hist₁ hist₂ : ℕ → ℕ) :
    clearedGSRelator M (fun q => hist₁ q + hist₂ q) num den =
      clearedGSRelator M hist₁ num den + clearedGSRelator M hist₂ num den := by
  classical
  simp [clearedGSRelator, Nat.cast_add, add_mul, Finset.sum_add_distrib]

/-- Monotonicity of the cleared relator sum in the histogram. -/
theorem cleared_mono_hist {M num den : ℕ} {hist hist' : ℕ → ℕ}
    (hh : ∀ q, q ≤ M → hist q ≤ hist' q) :
    clearedGSRelator M hist num den ≤ clearedGSRelator M hist' num den := by
  classical
  unfold clearedGSRelator
  apply Finset.sum_le_sum
  intro q hq
  have hqle : q ≤ M := by
    have := Finset.mem_range.mp hq
    omega
  have hc : (hist q : ℤ) ≤ (hist' q : ℤ) := by exact_mod_cast hh q hqle
  have hw : 0 ≤ (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q) := by
    exact mul_nonneg (pow_nonneg (by exact_mod_cast Nat.zero_le num) _)
      (pow_nonneg (by exact_mod_cast Nat.zero_le den) _)
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hc hw

/-- A single denominator-cleared relator contribution at depth `q`.  Keeping this
as a named term makes bucket and tail estimates easier to state. -/
def clearedGSTerm (M : ℕ) (hist : ℕ → ℕ) (num den q : ℕ) : ℤ :=
  (hist q : ℤ) * (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q)

/-- The relator contribution restricted to an arbitrary finite set of depths. -/
def clearedGSSum (S : Finset ℕ) (M : ℕ) (hist : ℕ → ℕ)
    (num den : ℕ) : ℤ :=
  ∑ q ∈ S, clearedGSTerm M hist num den q

@[simp] theorem cleared_gs_empty (M : ℕ) (hist : ℕ → ℕ)
    (num den : ℕ) :
    clearedGSSum ∅ M hist num den = 0 := by
  simp [clearedGSSum]

/-- The original relator sum is the restricted sum over the full depth range. -/
theorem cleared_gs_range (M : ℕ) (hist : ℕ → ℕ)
    (num den : ℕ) :
    clearedGSRelator M hist num den =
      clearedGSSum (Finset.range (M + 1)) M hist num den := by
  rfl

/-- Tail/bucket estimate for an arbitrary finite set of depths: if every index in
`S` is at least `q0` and at most `M+1`, then (for `num ≤ den`) every cleared
weight on `S` is bounded by the weight at `q0`. -/
theorem cleared_gs_count {S : Finset ℕ}
    {M q0 R num den : ℕ} {hist : ℕ → ℕ}
    (hnd : num ≤ den)
    (hlo : ∀ q ∈ S, q0 ≤ q)
    (hhi : ∀ q ∈ S, q ≤ M + 1)
    (hcount : (∑ q ∈ S, hist q) ≤ R) :
    clearedGSSum S M hist num den ≤
      (R : ℤ) * ((num : ℤ) ^ q0 * (den : ℤ) ^ (M + 1 - q0)) := by
  classical
  let W : ℤ := (num : ℤ) ^ q0 * (den : ℤ) ^ (M + 1 - q0)
  have hterm : ∀ q ∈ S,
      clearedGSTerm M hist num den q ≤ (hist q : ℤ) * W := by
    intro q hq
    have hw : (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q) ≤ W := by
      dsimp [W]
      exact cleared_int_antitone (A := M + 1) (num := num) (den := den)
        (q := q0) (r := q) hnd (hlo q hq) (hhi q hq)
    have hhistnon : 0 ≤ (hist q : ℤ) := by exact_mod_cast Nat.zero_le (hist q)
    unfold clearedGSTerm
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hw hhistnon
  unfold clearedGSSum
  have hsum := Finset.sum_le_sum hterm
  have hfactor : (∑ q ∈ S, (hist q : ℤ) * W) =
      ((∑ q ∈ S, hist q : ℕ) : ℤ) * W := by
    simp [Finset.sum_mul]
  rw [hfactor] at hsum
  have hcountz : ((∑ q ∈ S, hist q : ℕ) : ℤ) ≤ (R : ℤ) := by
    exact_mod_cast hcount
  have hWnon : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (pow_nonneg (by exact_mod_cast Nat.zero_le num) _)
      (pow_nonneg (by exact_mod_cast Nat.zero_le den) _)
  have hprod := mul_le_mul_of_nonneg_right hcountz hWnon
  linarith

/-- Split a relator sum into an explicitly bounded prefix and a coarse tail.  The
tail is represented by the filtered set `¬ q < q0`, avoiding any dependence on a
particular interval API. -/
theorem cleared_gs_bound {M q0 Rtail num den : ℕ}
    {hist : ℕ → ℕ} {prefixBound : ℤ}
    (hnd : num ≤ den)
    (hprefix : clearedGSSum
        ((Finset.range (M + 1)).filter (fun q => q < q0)) M hist num den ≤
        prefixBound)
    (htailcount : (∑ q ∈ (Finset.range (M + 1)).filter (fun q => ¬ q < q0),
        hist q) ≤ Rtail) :
    clearedGSRelator M hist num den ≤
      prefixBound + (Rtail : ℤ) *
        ((num : ℤ) ^ q0 * (den : ℤ) ^ (M + 1 - q0)) := by
  classical
  let S : Finset ℕ := Finset.range (M + 1)
  let P : ℕ → Prop := fun q => q < q0
  have htail : clearedGSSum (S.filter (fun q => ¬ P q)) M hist num den ≤
      (Rtail : ℤ) * ((num : ℤ) ^ q0 * (den : ℤ) ^ (M + 1 - q0)) := by
    apply cleared_gs_count (S := S.filter (fun q => ¬ P q))
      (M := M) (q0 := q0) (R := Rtail) (num := num) (den := den) (hist := hist)
    · exact hnd
    · intro q hq
      have hn : ¬ P q := (Finset.mem_filter.mp hq).2
      dsimp [P] at hn
      omega
    · intro q hq
      have hmem : q ∈ S := (Finset.mem_filter.mp hq).1
      dsimp [S] at hmem
      have := Finset.mem_range.mp hmem
      omega
    · dsimp [S, P]
      simpa using htailcount
  have hdecomp :
      clearedGSSum (S.filter P) M hist num den +
        clearedGSSum (S.filter (fun q => ¬ P q)) M hist num den =
      clearedGSRelator M hist num den := by
    dsimp [clearedGSSum, clearedGSTerm, clearedGSRelator]
    simpa [S, P] using
      (Finset.sum_filter_add_sum_filter_not (s := S) (p := P)
        (f := fun q => (hist q : ℤ) * (num : ℤ) ^ q *
          (den : ℤ) ^ (M + 1 - q)))
  have hp : clearedGSSum (S.filter P) M hist num den ≤ prefixBound := by
    dsimp [S, P]
    simpa using hprefix
  linarith

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Pointwise bounds on an arbitrary finite set bound the restricted relator sum. -/
theorem cleared_gs_pointwise {S : Finset ℕ} {M num den : ℕ}
    {hist : ℕ → ℕ} {bound : ℕ → ℤ}
    (hb : ∀ q ∈ S, clearedGSTerm M hist num den q ≤ bound q) :
    clearedGSSum S M hist num den ≤ ∑ q ∈ S, bound q := by
  classical
  unfold clearedGSSum
  exact Finset.sum_le_sum hb

/-- A generic pointwise upper-bound principle for cleared relator sums.  This is a
small adapter for externally supplied bucket or computer-generated bounds. -/
theorem cleared_relator_pointwise {M num den : ℕ} {hist : ℕ → ℕ}
    {bound : ℕ → ℤ}
    (hb : ∀ q, q ≤ M →
      (hist q : ℤ) * (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q) ≤ bound q) :
    clearedGSRelator M hist num den ≤
      ∑ q ∈ Finset.range (M + 1), bound q := by
  classical
  unfold clearedGSRelator
  apply Finset.sum_le_sum
  intro q hq
  have hqle : q ≤ M := by
    have := Finset.mem_range.mp hq
    omega
  exact hb q hqle

/-- A certificate constructor from arbitrary pointwise upper bounds on each depth
contribution. -/
def RGCert.relator_pointwise_bounds {p : ℕ} (FP : FPres p)
    [Fintype FP.toPresentation.Relator]
    (num den genLower : ℕ) (bound : ℕ → ℤ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hb : ∀ q, q ≤ FP.maxRelatorDepth →
      (FP.relatorDepthMultiplicity q : ℤ) * (num : ℤ) ^ q *
        (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q) ≤ bound q)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        (∑ q ∈ Finset.range (FP.maxRelatorDepth + 1), bound q) < 0) :
    FP.RGCert := by
  refine RGCert.relator_sum_bound FP num den genLower
    (∑ q ∈ Finset.range (FP.maxRelatorDepth + 1), bound q)
    hnum hden hproper hgen ?_ hneg
  exact cleared_relator_pointwise hb

/-- Certificate constructor from upper bounds on each depth multiplicity, stated
in relator-sum form.  Compared with `ofBounds`, this exposes the weighted sum
that external certificate generators usually compute. -/
def RGCert.ofMultiplicityBounds {p : ℕ} (FP : FPres p)
    [Fintype FP.toPresentation.Relator]
    (num den genLower : ℕ) (histUpper : ℕ → ℕ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hhist : ∀ q, q ≤ FP.maxRelatorDepth →
      FP.relatorDepthMultiplicity q ≤ histUpper q)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        clearedGSRelator FP.maxRelatorDepth histUpper num den < 0) :
    FP.RGCert := by
  refine RGCert.relator_sum_bound FP num den genLower
    (clearedGSRelator FP.maxRelatorDepth histUpper num den)
    hnum hden hproper hgen ?_ hneg
  exact cleared_mono_hist hhist

/-- Certificate constructor from an explicitly bounded low-depth prefix and a
coarse count bound on the remaining tail.  This is convenient for hybrid
computer/human certificates: enumerate the few shallow buckets exactly, then use
monotonicity of the cleared weights for the tail. -/
def RGCert.prefix_tail_bound {p : ℕ} (FP : FPres p)
    [Fintype FP.toPresentation.Relator]
    (num den genLower q0 tailCount : ℕ) (prefixBound : ℤ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hprefix : clearedGSSum
        ((Finset.range (FP.maxRelatorDepth + 1)).filter (fun q => q < q0))
        FP.maxRelatorDepth FP.relatorDepthMultiplicity num den ≤ prefixBound)
    (htailcount : (∑ q ∈ (Finset.range (FP.maxRelatorDepth + 1)).filter
        (fun q => ¬ q < q0), FP.relatorDepthMultiplicity q) ≤ tailCount)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        (prefixBound + (tailCount : ℤ) * ((num : ℤ) ^ q0 *
          (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0))) < 0) :
    FP.RGCert := by
  refine RGCert.relator_sum_bound FP num den genLower
    (prefixBound + (tailCount : ℤ) * ((num : ℤ) ^ q0 *
      (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0)))
    hnum hden hproper hgen ?_ hneg
  exact cleared_gs_bound
    (M := FP.maxRelatorDepth) (q0 := q0) (Rtail := tailCount)
    (num := num) (den := den) (hist := FP.relatorDepthMultiplicity)
    (prefixBound := prefixBound) (Nat.le_of_lt hproper) hprefix htailcount

/-- Variant of `prefix_tail_bound` where the prefix bound is supplied pointwise.
This is often the most compact interface for certificate search output. -/
def RGCert.prefix_tail_pointwisebounds {p : ℕ}
    (FP : FPres p) [Fintype FP.toPresentation.Relator]
    (num den genLower q0 tailCount : ℕ) (lowBound : ℕ → ℤ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hb : ∀ q ∈ (Finset.range (FP.maxRelatorDepth + 1)).filter (fun q => q < q0),
      clearedGSTerm FP.maxRelatorDepth FP.relatorDepthMultiplicity num den q ≤
        lowBound q)
    (htailcount : (∑ q ∈ (Finset.range (FP.maxRelatorDepth + 1)).filter
        (fun q => ¬ q < q0), FP.relatorDepthMultiplicity q) ≤ tailCount)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        ((∑ q ∈ (Finset.range (FP.maxRelatorDepth + 1)).filter (fun q => q < q0),
            lowBound q) +
          (tailCount : ℤ) * ((num : ℤ) ^ q0 *
            (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0))) < 0) :
    FP.RGCert := by
  refine RGCert.prefix_tail_bound FP num den genLower q0 tailCount
    (∑ q ∈ (Finset.range (FP.maxRelatorDepth + 1)).filter (fun q => q < q0),
      lowBound q) hnum hden hproper hgen ?_ htailcount hneg
  exact cleared_gs_pointwise hb

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Arithmetic core of the classical depth-two GS test: at `t = 2/d`, the
quadratic bound `1 - d t + r t^2` is negative when `4r < d^2`.  The statement is
in denominator-cleared integer form and includes the harmless maximum-depth
factor. -/
theorem cleared_gs_neg {d r M : ℕ} (hd : 0 < d)
    (hM : 1 ≤ M) (hineq : 4 * r < d * d) :
    clearedGSBase d M 2 d +
      (r : ℤ) * ((2 : ℤ) ^ 2 * (d : ℤ) ^ (M + 1 - 2)) < 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
  simp [clearedGSBase]
  ring_nf
  have hineqz : (4 * (r : ℤ)) < (d : ℤ) * (d : ℤ) := by
    exact_mod_cast hineq
  have hneg : (r : ℤ) * 4 - (d : ℤ) ^ 2 < 0 := by
    ring_nf
    linarith
  have hpowpos : 0 < (d : ℤ) ^ k := pow_pos (by exact_mod_cast hd) k
  nlinarith

variable {p : ℕ} (FP : FPres p)

/-- A packaged classical depth-two quadratic GS certificate.  If there are at
least `d` generators, at most `r` relators, all relators have depth at least two,
`4r < d^2`, and the recorded maximum depth is at least one, then the rational
point `2/d` gives a certificate. -/
def RGCert.depth_two_quadraticbound
    [Fintype FP.toPresentation.Relator] (d r : ℕ)
    (hd2 : 2 < d) (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) : FP.RGCert := by
  refine RGCert.uniform_depth_countbound FP 2 d d 2 r
    (by decide) (by omega) hd2 hgen hD hcount ?_
  exact cleared_gs_neg (d := d) (r := r)
    (M := FP.maxRelatorDepth) (by omega) hM hquad

/-- Direct contradiction form of the classical depth-two quadratic GS test. -/
theorem not_inequalities_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B d r : ℕ}
    (hd2 : 2 < d) (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d)
    (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k) :
    ¬ FP.gsCoefficientInequalities b := by
  let C := RGCert.depth_two_quadraticbound FP d r hd2 hM hgen hD hcount hquad
  exact FP.inequalities_certificate_mass C hb hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Truncated failing-degree form of the classical depth-two quadratic GS test. -/
theorem failure_truncate_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N d r : ℕ}
    (hd2 : 2 < d) (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d)
    (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  let C := RGCert.depth_two_quadraticbound FP d r hd2 hM hgen hD hcount hquad
  exact FP.failure_certificate_mass C hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Depth-two quadratic certificate using the named `degreeOneSilent` predicate. -/
def RGCert.degree_onesilent_quadraticbound
    [Fintype FP.toPresentation.Relator] (d r : ℕ)
    (hd2 : 2 < d) (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : d ≤ FP.generatorCount)
    (hsilent : FP.depths.degreeOneSilent)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) : FP.RGCert :=
  RGCert.depth_two_quadraticbound FP d r hd2 hM hgen hsilent hcount hquad

/-- Direct contradiction form of the degree-one-silent quadratic criterion. -/
theorem gs_inequalities_silent
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B d r : ℕ}
    (hd2 : 2 < d) (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : d ≤ FP.generatorCount)
    (hsilent : FP.depths.degreeOneSilent)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d)
    (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k) :
    ¬ FP.gsCoefficientInequalities b := by
  exact FP.not_inequalities_bound
    hd2 hM hgen hsilent hcount hquad hb hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- If a histogram has no mass below `q0` and the whole summation range is below
`q0`, its cleared relator sum is zero. -/
theorem cleared_gs_max {M q0 num den : ℕ}
    {hist : ℕ → ℕ} (hsupp : ∀ q, q < q0 → hist q = 0) (hM : M < q0) :
    clearedGSRelator M hist num den = 0 := by
  classical
  unfold clearedGSRelator
  apply Finset.sum_eq_zero
  intro q hq
  have hqle : q ≤ M := by
    have := Finset.mem_range.mp hq
    omega
  have hz := hsupp q (lt_of_le_of_lt hqle hM)
  simp [hz]

/-- The depth-two test's base term is already negative at `M = 0` and `t=2/d`. -/
theorem cleared_m_0 {d : ℕ} (hd : 0 < d) :
    clearedGSBase d 0 2 d < 0 := by
  simp [clearedGSBase]
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd
  nlinarith

variable {p : ℕ} (FP : FPres p)

/-- Variant of the classical depth-two quadratic certificate with no separate
`1 ≤ maxRelatorDepth` hypothesis.  If the recorded maximum depth is zero, the
uniform depth-two hypothesis forces the relator contribution to vanish, and the
base term alone is negative at `t=2/d`. -/
def RGCert.depth_two_quadraticbounda
    [Fintype FP.toPresentation.Relator] (d r : ℕ)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) : FP.RGCert := by
  by_cases hM : 1 ≤ FP.maxRelatorDepth
  · exact RGCert.depth_two_quadraticbound FP d r hd2 hM hgen hD hcount hquad
  · have hM0 : FP.maxRelatorDepth = 0 := by omega
    refine RGCert.relator_sum_bound FP 2 d d 0
      (by decide) (by omega) hd2 hgen ?_ ?_
    · rw [hM0]
      have hsupp : ∀ q, q < 2 → FP.relatorDepthMultiplicity q = 0 := by
        intro q hq
        exact FP.relator_uniform_lower hD hq
      simp [cleared_gs_max (M := 0) (q0 := 2)
        (num := 2) (den := d) (hist := FP.relatorDepthMultiplicity) hsupp (by omega)]
    · rw [hM0]
      simpa using (cleared_m_0 (d := d) (by omega))

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Direct contradiction form of the depth-two quadratic criterion, with the
maximum-depth edge case handled automa. -/
theorem inequalities_quadratic_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B d r : ℕ}
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d)
    (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k) :
    ¬ FP.gsCoefficientInequalities b := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact FP.inequalities_certificate_mass C hb hmass

/-- Degree-one-silent version of the edge-case-safe depth-two quadratic criterion. -/
theorem inequalities_silent_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B d r : ℕ}
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hsilent : FP.depths.degreeOneSilent)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d)
    (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k) :
    ¬ FP.gsCoefficientInequalities b := by
  exact FP.inequalities_quadratic_bound
    hd2 hgen hsilent hcount hquad hb hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Truncated failing-degree form of the edge-case-safe depth-two quadratic test. -/
theorem failure_seq_bound
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N d r : ℕ}
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d)
    (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact FP.failure_certificate_mass C hmass

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Successor recursion for finite prefix masses of a natural sequence. -/
theorem prefix_nat_succ {b : ℕ → ℕ} (B : ℕ) :
    (∑ k ∈ Finset.range ((B + 1) + 1), b k) =
      (∑ k ∈ Finset.range (B + 1), b k) + b (B + 1) := by
  simp [Finset.sum_range_succ]

/-- Prefix masses of a natural sequence are monotone in the cutoff. -/
theorem nat_mass_mono {b : ℕ → ℕ} {B C : ℕ} (hBC : B ≤ C) :
    (∑ k ∈ Finset.range (B + 1), b k) ≤
      ∑ k ∈ Finset.range (C + 1), b k := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hBC))
  · intro x _ _
    exact Nat.zero_le _

/-- A one-step prefix extension is monotone. -/
theorem nat_mass_succ {b : ℕ → ℕ} (B : ℕ) :
    (∑ k ∈ Finset.range (B + 1), b k) ≤
      ∑ k ∈ Finset.range ((B + 1) + 1), b k := by
  rw [prefix_nat_succ (b := b) B]
  exact Nat.le_add_right _ _

/-- A positive newly-added coefficient makes the next prefix strictly larger. -/
theorem mass_succ_pos {b : ℕ → ℕ} {B : ℕ}
    (hpos : 0 < b (B + 1)) :
    (∑ k ∈ Finset.range (B + 1), b k) <
      ∑ k ∈ Finset.range ((B + 1) + 1), b k := by
  rw [prefix_nat_succ (b := b) B]
  omega

/-- A one-step prefix stabilizes exactly when the newly-added coefficient is zero. -/
theorem mass_succ_self {b : ℕ → ℕ} {B : ℕ} :
    ((∑ k ∈ Finset.range ((B + 1) + 1), b k) =
      ∑ k ∈ Finset.range (B + 1), b k) ↔ b (B + 1) = 0 := by
  rw [prefix_nat_succ (b := b) B]
  omega

/-- Forward orientation of one-step prefix stabilization. -/
theorem coeff_mass_self {b : ℕ → ℕ} {B : ℕ}
    (h : (∑ k ∈ Finset.range ((B + 1) + 1), b k) =
      ∑ k ∈ Finset.range (B + 1), b k) :
    b (B + 1) = 0 :=
  (mass_succ_self (b := b) (B := B)).mp h

/-- Prefix masses stabilize after a support bound. -/
theorem prefix_mass_support {b : ℕ → ℕ} {B C : ℕ}
    (hb : SSBound b B) (hBC : B ≤ C) :
    (∑ k ∈ Finset.range (C + 1), b k) =
      ∑ k ∈ Finset.range (B + 1), b k := by
  exact range_support_bound hb (le_rfl) hBC

/-- Symmetric orientation of prefix-mass stabilization after a support bound. -/
theorem mass_support_bound {b : ℕ → ℕ} {B C : ℕ}
    (hb : SSBound b B) (hBC : B ≤ C) :
    (∑ k ∈ Finset.range (B + 1), b k) =
      ∑ k ∈ Finset.range (C + 1), b k :=
  (prefix_mass_support hb hBC).symm

/-- Prefix masses at any two cutoffs beyond a common support bound are equal. -/
theorem prefix_mass_bound {b : ℕ → ℕ} {B M N : ℕ}
    (hb : SSBound b B) (hM : B ≤ M) (hN : B ≤ N) :
    (∑ k ∈ Finset.range (M + 1), b k) =
      ∑ k ∈ Finset.range (N + 1), b k :=
  sum_support_bound hb hM hN

/-- A positive zeroth coefficient gives positive finite prefix mass in every prefix. -/
theorem mass_pos_zero {b : ℕ → ℕ} {B : ℕ} (hb0 : 0 < b 0) :
    0 < ∑ k ∈ Finset.range (B + 1), b k := by
  classical
  have hmem : 0 ∈ Finset.range (B + 1) := by simp
  have hle : b 0 ≤ ∑ k ∈ Finset.range (B + 1), b k := by
    exact Finset.single_le_sum (by intro x _; exact Nat.zero_le _) hmem
  exact lt_of_lt_of_le hb0 hle

/-- A positive zeroth coefficient makes every prefix mass at least one. -/
theorem prefix_nat_mass {b : ℕ → ℕ} {B : ℕ} (hb0 : 0 < b 0) :
    1 ≤ ∑ k ∈ Finset.range (B + 1), b k :=
  Nat.succ_le_iff.mpr (mass_pos_zero (B := B) hb0)

variable {p : ℕ} (FP : FPres p)

/-- Certificate contradiction wrapper using only positivity of the zeroth coefficient. -/
theorem inequalities_certificate_coeff
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {B : ℕ}
    (C : FP.RGCert) (hb : SSBound b B) (hb0 : 0 < b 0) :
    ¬ FP.gsCoefficientInequalities b := by
  exact FP.inequalities_certificate_mass C hb
    (mass_pos_zero (B := B) hb0)

/-- Truncated failing-degree wrapper using positivity of the zeroth coefficient. -/
theorem failure_seq_certificate
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N : ℕ}
    (C : FP.RGCert) (hb0 : 0 < b 0) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  exact FP.failure_certificate_mass C
    (mass_pos_zero (B := N) hb0)

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- A compact package for the finite-support coefficient data expected from a
finite filtered quotient in the eventual GS argument.  It deliberately contains
only the algebraic bookkeeping hypotheses: finite support, positive degree-zero
mass, and the coefficientwise GS inequalities. -/
structure FiniteGSSequence (FP : FPres p) [Fintype FP.toPresentation.Relator] where
  coeff : ℕ → ℕ
  bound : ℕ
  support : SSBound coeff bound
  coeff_zero_pos : 0 < coeff 0
  inequalities : FP.gsCoefficientInequalities coeff

/-- Package a truncated natural sequence as finite GS coefficient data, assuming its
zeroth coefficient is positive and the truncated sequence satisfies the inequalities. -/
def gs_sequence_truncate [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} (N : ℕ) (hb0 : 0 < b 0)
    (hineq : FP.gsCoefficientInequalities (truncateSeq b N)) :
    FiniteGSSequence (p := p) FP where
  coeff := truncateSeq b N
  bound := N
  support := seq_support_truncate b N
  coeff_zero_pos := by
    simpa [truncate_apply_le b (Nat.zero_le N)] using hb0
  inequalities := hineq

/-- Nonempty form of `gs_sequence_truncate`. -/
theorem nonempty_sequence_truncate [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} (N : ℕ) (hb0 : 0 < b 0)
    (hineq : FP.gsCoefficientInequalities (truncateSeq b N)) :
    Nonempty (FiniteGSSequence (p := p) FP) :=
  ⟨FP.gs_sequence_truncate N hb0 hineq⟩

/-- A rational GS certificate rules out any finite normalized coefficient sequence
satisfying the coefficientwise inequalities. -/
theorem no_gs_certificate
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) :
    ¬ Nonempty (FiniteGSSequence (p := p) FP) := by
  rintro ⟨S⟩
  have hnot := FP.inequalities_certificate_coeff
    C S.support S.coeff_zero_pos
  exact hnot S.inequalities

/-- The edge-case-safe depth-two quadratic numerical criterion rules out finite
normalized coefficient data directly. -/
theorem no_sequence_bound
    [Fintype FP.toPresentation.Relator] {d r : ℕ}
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ Nonempty (FiniteGSSequence (p := p) FP) := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact FP.no_gs_certificate C

/-- A rational certificate rules out GS inequalities for any truncation whose zeroth
coefficient is positive. -/
theorem inequalities_seq_certificate
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert)
    {b : ℕ → ℕ} {N : ℕ} (hb0 : 0 < b 0) :
    ¬ FP.gsCoefficientInequalities (truncateSeq b N) := by
  intro hineq
  exact (FP.no_gs_certificate C)
    (FP.nonempty_sequence_truncate N hb0 hineq)

/-- Depth-two quadratic obstruction for inequalities on a truncated sequence with
positive zeroth coefficient. -/
theorem inequalities_truncate_seq
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ} {N d r : ℕ}
    (hb0 : 0 < b 0)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ FP.gsCoefficientInequalities (truncateSeq b N) := by
  intro hineq
  exact (FP.no_sequence_bound
    (d := d) (r := r) hd2 hgen hD hcount hquad)
    (FP.nonempty_sequence_truncate N hb0 hineq)


end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Typeclass-style empty-instance version of the certificate obstruction. -/
@[reducible] def sequence_empty_certificate
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) :
    IsEmpty (FiniteGSSequence (p := p) FP) :=
  ⟨fun S => (FP.no_gs_certificate C) ⟨S⟩⟩

/-- Typeclass-style empty-instance version of the quadratic obstruction. -/
@[reducible] def sequence_empty_bound
    [Fintype FP.toPresentation.Relator] {d r : ℕ}
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    IsEmpty (FiniteGSSequence (p := p) FP) :=
  ⟨fun S => (FP.no_sequence_bound
    hd2 hgen hD hcount hquad) ⟨S⟩⟩

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Existential form of the finite normalized coefficient-data obstruction. -/
theorem supported_gs_certificate
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) :
    ¬ ∃ (b : ℕ → ℕ) (B : ℕ), SSBound b B ∧ 0 < b 0 ∧
      FP.gsCoefficientInequalities b := by
  rintro ⟨b, B, hb, hb0, hineq⟩
  exact (FP.no_gs_certificate C)
    ⟨⟨b, B, hb, hb0, hineq⟩⟩

/-- Existential form specialized to the edge-case-safe quadratic criterion. -/
theorem supported_gs_bound
    [Fintype FP.toPresentation.Relator] {d r : ℕ}
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ ∃ (b : ℕ → ℕ) (B : ℕ), SSBound b B ∧ 0 < b 0 ∧
      FP.gsCoefficientInequalities b := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact FP.supported_gs_certificate C

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Existential obstruction in the common normalization `b 0 = 1`. -/
theorem gs_sequence_certificate
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) :
    ¬ ∃ (b : ℕ → ℕ) (B : ℕ), SSBound b B ∧ b 0 = 1 ∧
      FP.gsCoefficientInequalities b := by
  rintro ⟨b, B, hb, hb0, hineq⟩
  apply FP.supported_gs_certificate C
  refine ⟨b, B, hb, ?_, hineq⟩
  omega

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)

/-- Normalization-`b 0 = 1` existential obstruction specialized to the quadratic test. -/
theorem gs_sequence_bound
    [Fintype FP.toPresentation.Relator] {d r : ℕ}
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ ∃ (b : ℕ → ℕ) (B : ℕ), SSBound b B ∧ b 0 = 1 ∧
      FP.gsCoefficientInequalities b := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact FP.gs_sequence_certificate C

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- General depth-two denominator-cleared quadratic negativity: for `M ≥ 1`, the
cleared expression factors by `d^(M-1)` times the usual quadratic numerator. -/
theorem cleared_gs_quadratic {gen r m d M : ℕ}
    (hd : 0 < d) (hM : 1 ≤ M)
    (hquad : (d : ℤ) ^ 2 - (gen : ℤ) * (m : ℤ) * (d : ℤ) +
        (r : ℤ) * (m : ℤ) ^ 2 < 0) :
    clearedGSBase gen M m d +
      (r : ℤ) * ((m : ℤ) ^ 2 * (d : ℤ) ^ (M + 1 - 2)) < 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
  simp [clearedGSBase]
  ring_nf at hquad ⊢
  have hp : 0 < (d : ℤ) ^ k := pow_pos (by exact_mod_cast hd) k
  nlinarith

variable {p : ℕ} (FP : FPres p)

/-- General depth-two certificate at a rational point `m/d`, from the integer
quadratic numerator inequality. -/
def RGCert.depth_two_quadratic
    [Fintype FP.toPresentation.Relator] (m d genLower relCountBound : ℕ)
    (hm : 0 < m) (hd : 0 < d) (hproper : m < d)
    (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ relCountBound)
    (hquad : (d : ℤ) ^ 2 - (genLower : ℤ) * (m : ℤ) * (d : ℤ) +
        (relCountBound : ℤ) * (m : ℤ) ^ 2 < 0) :
    FP.RGCert := by
  refine RGCert.uniform_depth_countbound FP m d genLower 2 relCountBound
    hm hd hproper hgen hD hcount ?_
  exact cleared_gs_quadratic (gen := genLower)
    (r := relCountBound) (m := m) (d := d) (M := FP.maxRelatorDepth) hd hM hquad

/-- Direct contradiction wrapper for the general rational depth-two quadratic
certificate. -/
theorem gs_inequalities_quadratic
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ}
    {B m d genLower relCountBound : ℕ}
    (hm : 0 < m) (hd : 0 < d) (hproper : m < d)
    (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ relCountBound)
    (hquad : (d : ℤ) ^ 2 - (genLower : ℤ) * (m : ℤ) * (d : ℤ) +
        (relCountBound : ℤ) * (m : ℤ) ^ 2 < 0)
    (hb : SSBound b B)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1), b k) :
    ¬ FP.gsCoefficientInequalities b := by
  let C := RGCert.depth_two_quadratic FP m d genLower relCountBound
    hm hd hproper hM hgen hD hcount hquad
  exact FP.inequalities_certificate_mass C hb hmass

/-- Normalized finite-sequence obstruction wrapper for the general rational
depth-two quadratic certificate. -/
theorem gs_sequence_quadratic
    [Fintype FP.toPresentation.Relator] {m d genLower relCountBound : ℕ}
    (hm : 0 < m) (hd : 0 < d) (hproper : m < d)
    (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ relCountBound)
    (hquad : (d : ℤ) ^ 2 - (genLower : ℤ) * (m : ℤ) * (d : ℤ) +
        (relCountBound : ℤ) * (m : ℤ) ^ 2 < 0) :
    ¬ ∃ (b : ℕ → ℕ) (B : ℕ), SSBound b B ∧ b 0 = 1 ∧
      FP.gsCoefficientInequalities b := by
  let C := RGCert.depth_two_quadratic FP m d genLower relCountBound
    hm hd hproper hM hgen hD hcount hquad
  exact FP.gs_sequence_certificate C

/-- Bounded failing-degree wrapper for the general rational depth-two quadratic
certificate. -/
theorem failure_seq_quadratic
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ}
    {N m d genLower relCountBound : ℕ}
    (hm : 0 < m) (hd : 0 < d) (hproper : m < d)
    (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ relCountBound)
    (hquad : (d : ℤ) ^ 2 - (genLower : ℤ) * (m : ℤ) * (d : ℤ) +
        (relCountBound : ℤ) * (m : ℤ) ^ 2 < 0)
    (hmass : 0 < ∑ k ∈ Finset.range (N + 1), b k) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  let C := RGCert.depth_two_quadratic FP m d genLower relCountBound
    hm hd hproper hM hgen hD hcount hquad
  exact FP.failure_certificate_mass C hmass

/-- Zero-coefficient-positive specialization of the general rational quadratic-at-point
contradiction for finitely supported sequences. -/
theorem gs_inequalities_coeff
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ}
    {B m d genLower relCountBound : ℕ}
    (hm : 0 < m) (hd : 0 < d) (hproper : m < d)
    (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ relCountBound)
    (hquad : (d : ℤ) ^ 2 - (genLower : ℤ) * (m : ℤ) * (d : ℤ) +
        (relCountBound : ℤ) * (m : ℤ) ^ 2 < 0)
    (hb : SSBound b B) (hb0 : 0 < b 0) :
    ¬ FP.gsCoefficientInequalities b := by
  apply FP.gs_inequalities_quadratic
    (m := m) (d := d) (genLower := genLower) (relCountBound := relCountBound)
    hm hd hproper hM hgen hD hcount hquad hb
  exact mass_pos_zero (B := B) hb0

/-- Zero-coefficient-positive failing-degree wrapper for the general rational
quadratic-at-point certificate. -/
theorem failure_truncate_seq
    [Fintype FP.toPresentation.Relator] {b : ℕ → ℕ}
    {N m d genLower relCountBound : ℕ}
    (hm : 0 < m) (hd : 0 < d) (hproper : m < d)
    (hM : 1 ≤ FP.maxRelatorDepth)
    (hgen : genLower ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ relCountBound)
    (hquad : (d : ℤ) ^ 2 - (genLower : ℤ) * (m : ℤ) * (d : ℤ) +
        (relCountBound : ℤ) * (m : ℤ) ^ 2 < 0)
    (hb0 : 0 < b 0) :
    ∃ n ∈ Finset.range (N + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (truncateSeq b N) n := by
  apply FP.failure_seq_quadratic
    (m := m) (d := d) (genLower := genLower) (relCountBound := relCountBound)
    hm hd hproper hM hgen hD hcount hquad
  exact mass_pos_zero (B := N) hb0

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-!
# Bounded GS coefficient sequences

The finite-support obstruction above is useful when an augmentation ideal is
nilpotent.  For the filtered Vinberg form of Golod--Shafarevich, the natural
coefficient sequence is instead a sequence of augmentation-layer prefix ranks.
If the presented group is finite, those prefixes are uniformly bounded but need
not be finitely supported.  This section isolates the bounded-sequence
bookkeeping needed for that endgame.
-/

/-- A pointwise natural upper bound for a coefficient sequence. -/
def SUBound (b : ℕ → ℕ) (B : ℕ) : Prop :=
  ∀ n, b n ≤ B

/-- A natural coefficient sequence is bounded if it has some pointwise upper
bound. -/
def SBounde (b : ℕ → ℕ) : Prop :=
  ∃ B, SUBound b B

/-- Project a pointwise coefficient bound at one degree. -/
theorem SUBound.coeff_le {b : ℕ → ℕ} {B : ℕ}
    (hb : SUBound b B) (n : ℕ) :
    b n ≤ B :=
  hb n

/-- A coefficient sequence bounded by `B` is also bounded by every larger
natural number. -/
theorem SUBound.mono {b : ℕ → ℕ} {B C : ℕ}
    (hb : SUBound b B) (hBC : B ≤ C) :
    SUBound b C := by
  intro n
  exact le_trans (hb n) hBC

/-- Transport a pointwise sequence bound across equality of sequences. -/
theorem SUBound.congr {b c : ℕ → ℕ} {B : ℕ}
    (hb : SUBound b B) (h : ∀ n, c n = b n) :
    SUBound c B := by
  intro n
  rw [h n]
  exact hb n

/-- A pointwise smaller sequence inherits an upper bound. -/
theorem SUBound.of_le {b c : ℕ → ℕ} {B : ℕ}
    (hb : SUBound b B) (hcb : ∀ n, c n ≤ b n) :
    SUBound c B := by
  intro n
  exact le_trans (hcb n) (hb n)

/-- The zero coefficient sequence is bounded by zero. -/
@[simp] theorem seq_upper_bound :
    SUBound (fun _ : ℕ => 0) 0 := by
  intro n
  exact le_rfl

/-- A constant sequence is bounded by its constant value. -/
@[simp] theorem seq_upper_const (a : ℕ) :
    SUBound (fun _ : ℕ => a) a := by
  intro n
  exact le_rfl

/-- Pointwise addition adds upper bounds. -/
theorem SUBound.add {b c : ℕ → ℕ} {B C : ℕ}
    (hb : SUBound b B) (hc : SUBound c C) :
    SUBound (fun n => b n + c n) (B + C) := by
  intro n
  exact Nat.add_le_add (hb n) (hc n)

/-- Taking pointwise maxima combines two upper bounds. -/
theorem SUBound.pointwise_max {b c : ℕ → ℕ} {B C : ℕ}
    (hb : SUBound b B) (hc : SUBound c C) :
    SUBound (fun n => max (b n) (c n)) (max B C) := by
  intro n
  exact max_le_max (hb n) (hc n)

/-- A pointwise minimum inherits the bound from its left input. -/
theorem SUBound.pointwise_min_left {b c : ℕ → ℕ} {B : ℕ}
    (hb : SUBound b B) :
    SUBound (fun n => min (b n) (c n)) B := by
  intro n
  exact le_trans (min_le_left (b n) (c n)) (hb n)

/-- A pointwise minimum inherits the bound from its right input. -/
theorem SUBound.pointwise_min_right {b c : ℕ → ℕ} {C : ℕ}
    (hc : SUBound c C) :
    SUBound (fun n => min (b n) (c n)) C := by
  intro n
  exact le_trans (min_le_right (b n) (c n)) (hc n)

/-- Multiplication by a fixed scalar multiplies a pointwise upper bound. -/
theorem SUBound.const_mul {b : ℕ → ℕ} {B : ℕ}
    (a : ℕ) (hb : SUBound b B) :
    SUBound (fun n => a * b n) (a * B) := by
  intro n
  exact Nat.mul_le_mul_left a (hb n)

/-- Right-scalar form of `SUBound.const_mul`. -/
theorem SUBound.mul_const {b : ℕ → ℕ} {B : ℕ}
    (hb : SUBound b B) (a : ℕ) :
    SUBound (fun n => b n * a) (B * a) := by
  intro n
  exact Nat.mul_le_mul_right a (hb n)

/-- Truncating a sequence preserves any upper bound. -/
theorem SUBound.truncateSeq {b : ℕ → ℕ} {B : ℕ}
    (hb : SUBound b B) (N : ℕ) :
    SUBound (truncateSeq b N) B := by
  intro n
  by_cases hn : n ≤ N
  · rw [truncate_apply_le b hn]
    exact hb n
  · rw [truncate_seq b (Nat.lt_of_not_ge hn)]
    exact Nat.zero_le B

/-- A finitely supported sequence is bounded by its total mass through a support
bound. -/
theorem SSBound.upper_bound_prefixmass {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    SUBound b (∑ k ∈ Finset.range (B + 1), b k) := by
  intro n
  by_cases hn : n ≤ B
  · have hmem : n ∈ Finset.range (B + 1) := by
      simp
      omega
    exact Finset.single_le_sum (fun k _hk => Nat.zero_le (b k)) hmem
  · have hgt : B < n := Nat.lt_of_not_ge hn
    rw [hb n hgt]
    exact Nat.zero_le _

/-- Every finitely supported sequence is bounded. -/
theorem SSBound.bounded {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    SBounde b :=
  ⟨∑ k ∈ Finset.range (B + 1), b k, hb.upper_bound_prefixmass⟩

/-- The zero sequence is bounded. -/
@[simp] theorem seqBounded_zero :
    SBounde (fun _ : ℕ => 0) :=
  ⟨0, seq_upper_bound⟩

/-- Every constant natural sequence is bounded. -/
@[simp] theorem seqBounded_const (a : ℕ) :
    SBounde (fun _ : ℕ => a) :=
  ⟨a, seq_upper_const a⟩

/-- Pointwise equality transports boundedness. -/
theorem SBounde.congr {b c : ℕ → ℕ}
    (hb : SBounde b) (h : ∀ n, c n = b n) :
    SBounde c := by
  rcases hb with ⟨B, hB⟩
  exact ⟨B, hB.congr h⟩

/-- A pointwise smaller sequence inherits boundedness. -/
theorem SBounde.of_le {b c : ℕ → ℕ}
    (hb : SBounde b) (hcb : ∀ n, c n ≤ b n) :
    SBounde c := by
  rcases hb with ⟨B, hB⟩
  exact ⟨B, hB.of_le hcb⟩

/-- Pointwise sums of bounded sequences are bounded. -/
theorem SBounde.add {b c : ℕ → ℕ}
    (hb : SBounde b) (hc : SBounde c) :
    SBounde (fun n => b n + c n) := by
  rcases hb with ⟨B, hB⟩
  rcases hc with ⟨C, hC⟩
  exact ⟨B + C, hB.add hC⟩

/-- Pointwise maxima of bounded sequences are bounded. -/
theorem SBounde.pointwise_max {b c : ℕ → ℕ}
    (hb : SBounde b) (hc : SBounde c) :
    SBounde (fun n => max (b n) (c n)) := by
  rcases hb with ⟨B, hB⟩
  rcases hc with ⟨C, hC⟩
  exact ⟨max B C, hB.pointwise_max hC⟩

/-- Truncating any bounded sequence remains bounded. -/
theorem SBounde.truncateSeq {b : ℕ → ℕ}
    (hb : SBounde b) (N : ℕ) :
    SBounde (truncateSeq b N) := by
  rcases hb with ⟨B, hB⟩
  exact ⟨B, hB.truncateSeq N⟩

/-- Finite support implies boundedness through the support-bound API. -/
theorem seq_support_bound {b : ℕ → ℕ} {B : ℕ}
    (hb : SSBound b B) :
    SBounde b :=
  hb.bounded

variable {p : ℕ} (FP : FPres p)

/-- A compact package for the bounded positive coefficient data used by the
filtered Vinberg endgame. -/
structure BoundedGSSequence
    (FP : FPres p) [Fintype FP.toPresentation.Relator] where
  coeff : ℕ → ℕ
  bound : ℕ
  upperBound : SUBound coeff bound
  coeff_zero_pos : 0 < coeff 0
  inequalities : FP.gsCoefficientInequalities coeff

/-- Package a sequence with an explicit bound as bounded GS data. -/
def sequence_upper_bound
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {B : ℕ}
    (hbound : SUBound b B)
    (hb0 : 0 < b 0)
    (hineq : FP.gsCoefficientInequalities b) :
    BoundedGSSequence (p := p) FP where
  coeff := b
  bound := B
  upperBound := hbound
  coeff_zero_pos := hb0
  inequalities := hineq

/-- Package an existentially bounded sequence as bounded GS data. -/
theorem nonempty_gs_sequence
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ}
    (hbounded : SBounde b)
    (hb0 : 0 < b 0)
    (hineq : FP.gsCoefficientInequalities b) :
    Nonempty (BoundedGSSequence (p := p) FP) := by
  rcases hbounded with ⟨B, hB⟩
  exact ⟨FP.sequence_upper_bound hB hb0 hineq⟩

/-!
## Rational boundary tails

For a finitely supported coefficient sequence, the rational-evaluation
contradiction above follows by summing every coefficient of the Cauchy product.
For a merely bounded sequence, summing through degree `N` leaves a finite
boundary strip. Its width is controlled by the degree of the GS polynomial,
while its entries are controlled by the sequence bound. At a rational point
strictly between zero and one, that boundary strip decays geometrically.

The definitions below expose that strip explicitly. This keeps the remaining
analytic input separate from the formal GS recurrence and from the group theory
which produces the recurrence.
-/

/-- Rational geometrically weighted coefficient mass through degree `N`. -/
noncomputable def ratWeightedPrefix
    (b : ℕ → ℕ) (x : ℚ) (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1), (b k : ℚ) * x ^ k

/-- Unfold a rational weighted coefficient prefix. -/
theorem rat_coefficient_prefix
    (b : ℕ → ℕ) (x : ℚ) (N : ℕ) :
    ratWeightedPrefix b x N =
      ∑ k ∈ Finset.range (N + 1), (b k : ℚ) * x ^ k :=
  rfl

/-- The degree-zero weighted prefix is the degree-zero coefficient. -/
@[simp] theorem rat_weighted_coefficient
    (b : ℕ → ℕ) (x : ℚ) :
    ratWeightedPrefix b x 0 = b 0 := by
  simp [ratWeightedPrefix]

/-- Adding one degree to a weighted prefix adds exactly one monomial. -/
theorem rat_weighted_succ
    (b : ℕ → ℕ) (x : ℚ) (N : ℕ) :
    ratWeightedPrefix b x (N + 1) =
      ratWeightedPrefix b x N + (b (N + 1) : ℚ) * x ^ (N + 1) := by
  simp [ratWeightedPrefix, Finset.sum_range_succ, Nat.add_assoc]

/-- Weighted coefficient prefixes are nonnegative at a nonnegative point. -/
theorem rat_weighted_nonneg
    {b : ℕ → ℕ} {x : ℚ} (hx : 0 ≤ x) (N : ℕ) :
    0 ≤ ratWeightedPrefix b x N := by
  classical
  unfold ratWeightedPrefix
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (by exact_mod_cast Nat.zero_le (b k)) (pow_nonneg hx k)

/-- The initial coefficient is a lower bound for every weighted prefix at a
nonnegative point. -/
theorem rat_weighted_prefix
    {b : ℕ → ℕ} {x : ℚ} (hx : 0 ≤ x) (N : ℕ) :
    (b 0 : ℚ) ≤ ratWeightedPrefix b x N := by
  classical
  unfold ratWeightedPrefix
  have hmem : 0 ∈ Finset.range (N + 1) := by simp
  have hle :
      (b 0 : ℚ) * x ^ 0 ≤
        ∑ k ∈ Finset.range (N + 1), (b k : ℚ) * x ^ k := by
    exact Finset.single_le_sum
      (fun k _hk =>
        mul_nonneg (by exact_mod_cast Nat.zero_le (b k)) (pow_nonneg hx k))
      hmem
  simpa using hle

/-- A positive zeroth coefficient makes every weighted prefix positive at a
nonnegative point. -/
theorem rat_pos_coeff
    {b : ℕ → ℕ} {x : ℚ} (hx : 0 ≤ x) (hb0 : 0 < b 0) (N : ℕ) :
    0 < ratWeightedPrefix b x N := by
  have hb0q : (0 : ℚ) < b 0 := by exact_mod_cast hb0
  exact lt_of_lt_of_le hb0q
    (rat_weighted_prefix hx N)

/-- Rational geometrically weighted GS-balance mass through degree `N`. -/
noncomputable def ratBalancePrefix
    [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N + 1), (FP.gsCoefficientBalance b n : ℚ) * x ^ n

/-- Unfold a rational weighted balance prefix. -/
theorem rat_balance_prefix
    [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (x : ℚ) (N : ℕ) :
    FP.ratBalancePrefix b x N =
      ∑ n ∈ Finset.range (N + 1),
        (FP.gsCoefficientBalance b n : ℚ) * x ^ n :=
  rfl

/-- Weighted balance prefixes are nonnegative whenever all GS coefficient
inequalities hold. -/
theorem rat_nonneg_inequalities
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {x : ℚ}
    (hx : 0 ≤ x)
    (hineq : FP.gsCoefficientInequalities b)
    (N : ℕ) :
    0 ≤ FP.ratBalancePrefix b x N := by
  exact FP.balance_nonneg_inequalities hx N hineq

/-- The explicit boundary strip omitted when a finite GS-balance prefix is
compared with the product of the GS polynomial and a coefficient prefix.

For a polynomial monomial of degree `q`, the inner sum contains the final `q`
coefficient terms whose product degrees lie strictly above the cutoff `N`. -/
noncomputable def gsRatBoundary
    [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (x : ℚ) (N : ℕ) : ℚ :=
  ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
    ∑ r ∈ Finset.range q,
      (FP.gsCoeffInt q : ℚ) *
        (b (N + 1 - q + r) : ℚ) * x ^ (N + 1 + r)

/-- Unfold the explicit rational boundary tail. -/
theorem rat_boundary_tail
    [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (x : ℚ) (N : ℕ) :
    FP.gsRatBoundary b x N =
      ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
        ∑ r ∈ Finset.range q,
          (FP.gsCoeffInt q : ℚ) *
            (b (N + 1 - q + r) : ℚ) * x ^ (N + 1 + r) :=
  rfl

/-- The boundary tail vanishes for the zero coefficient sequence. -/
@[simp] theorem gs_rat_seq
    [Fintype FP.toPresentation.Relator]
    (x : ℚ) (N : ℕ) :
    FP.gsRatBoundary (fun _ => 0) x N = 0 := by
  simp [gsRatBoundary]

/-- The boundary tail vanishes at the point zero. -/
@[simp] theorem gs_rat_point
    [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (N : ℕ) :
    FP.gsRatBoundary b 0 N = 0 := by
  classical
  unfold gsRatBoundary
  apply Finset.sum_eq_zero
  intro q hq
  apply Finset.sum_eq_zero
  intro r hr
  have hpos : 0 < N + 1 + r := by omega
  simp [zero_pow (Nat.ne_of_gt hpos)]

/-- Antidiagonals below a total-degree cutoff, filtered by a first-coordinate
bound, enumerate the corresponding finite triangle. -/
theorem antidiagonal_fst_triangle
    {R : Type} [AddCommMonoid R]
    (A N : ℕ) (f : ℕ → ℕ → R) :
    (∑ n ∈ Finset.range (N + 1),
      ∑ ij ∈ (Finset.antidiagonal n).filter (fun ij : ℕ × ℕ => ij.1 ≤ A),
        f ij.1 ij.2) =
      ∑ q ∈ Finset.range (A + 1),
        ∑ k ∈ Finset.range (N + 1 - q), f q k := by
  classical
  rw [← Finset.sum_sigma (s := Finset.range (N + 1))
      (t := fun n => (Finset.antidiagonal n).filter
        (fun ij : ℕ × ℕ => ij.1 ≤ A))
      (f := fun x : Sigma (fun _ : ℕ => ℕ × ℕ) => f x.2.1 x.2.2)]
  rw [← Finset.sum_sigma (s := Finset.range (A + 1))
      (t := fun q => Finset.range (N + 1 - q))
      (f := fun x : Sigma (fun _ : ℕ => ℕ) => f x.1 x.2)]
  apply Finset.sum_bij (fun x _hx => ⟨x.2.1, x.2.2⟩)
  · intro x hx
    rw [Finset.mem_sigma] at hx ⊢
    rcases hx with ⟨hn, hij⟩
    rw [Finset.mem_filter] at hij
    rcases hij with ⟨hanti, hqA⟩
    have hsum : x.2.1 + x.2.2 = x.1 :=
      Finset.mem_antidiagonal.mp hanti
    constructor
    · simp
      omega
    · simp
      have hnlt := Finset.mem_range.mp hn
      omega
  · intro x hx y hy hxy
    rcases x with ⟨nx, ix⟩
    rcases y with ⟨ny, iy⟩
    simp only at hxy
    have hfst : ix.1 = iy.1 := by
      exact congrArg Sigma.fst hxy
    have hsnd : ix.2 = iy.2 := by
      exact congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.2) hxy
    have hix : ix = iy := Prod.ext hfst hsnd
    rw [Finset.mem_sigma] at hx hy
    have hxanti : ix ∈ Finset.antidiagonal nx :=
      (Finset.mem_filter.mp hx.2).1
    have hyanti : iy ∈ Finset.antidiagonal ny :=
      (Finset.mem_filter.mp hy.2).1
    have hnx : ix.1 + ix.2 = nx := Finset.mem_antidiagonal.mp hxanti
    have hny : iy.1 + iy.2 = ny := Finset.mem_antidiagonal.mp hyanti
    subst iy
    have hn : nx = ny := by omega
    subst ny
    subst nx
    rfl
  · intro y hy
    rcases y with ⟨q, k⟩
    rw [Finset.mem_sigma] at hy
    rcases hy with ⟨hq, hk⟩
    refine ⟨⟨q + k, (q, k)⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · simp at hq hk ⊢
        omega
      · rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_antidiagonal.mpr rfl
        · simp at hq ⊢
          omega
    · rfl
  · intro x hx
    rfl

/-- Split a finite rectangle into its total-degree triangle and the boundary
strip above that triangle. -/
theorem triangle_boundary_rectangle
    {R : Type} [AddCommMonoid R]
    (A N : ℕ) (hA : A ≤ N + 1) (f : ℕ → ℕ → R) :
    (∑ q ∈ Finset.range (A + 1),
      ∑ k ∈ Finset.range (N + 1 - q), f q k) +
      (∑ q ∈ Finset.range (A + 1),
        ∑ r ∈ Finset.range q, f q (N + 1 - q + r)) =
    ∑ q ∈ Finset.range (A + 1),
      ∑ k ∈ Finset.range (N + 1), f q k := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hqle : q ≤ N + 1 := by
    have hqA : q ≤ A := by
      have hqlt := Finset.mem_range.mp hq
      omega
    exact le_trans hqA hA
  rw [← Finset.sum_range_add]
  rw [Nat.sub_add_cancel hqle]

/-- The exact finite Cauchy-product identity for a bounded-prefix cutoff.

This is a finite reindexing statement. It has no positivity assumptions, no
coefficient inequalities, and no asymptotic argument. -/
theorem rat_balance_boundary
    [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (x : ℚ) (N : ℕ)
    (hdepth : FP.maxRelatorDepth + 1 ≤ N + 1) :
    FP.ratBalancePrefix b x N =
      FP.gsEvalRat x * ratWeightedPrefix b x N -
        FP.gsRatBoundary b x N := by
  classical
  let A := FP.maxRelatorDepth + 1
  let f : ℕ → ℕ → ℚ := fun q k =>
    (FP.gsCoeffInt q : ℚ) * (b k : ℚ) * x ^ (q + k)
  have hA : A ≤ N + 1 := by
    simpa [A] using hdepth
  have hprefix :
      FP.ratBalancePrefix b x N =
        ∑ q ∈ Finset.range (A + 1),
          ∑ k ∈ Finset.range (N + 1 - q), f q k := by
    unfold ratBalancePrefix
    calc
      (∑ n ∈ Finset.range (N + 1),
          (FP.gsCoefficientBalance b n : ℚ) * x ^ n) =
          ∑ n ∈ Finset.range (N + 1),
            ∑ ij ∈ (Finset.antidiagonal n).filter
                (fun ij : ℕ × ℕ => ij.1 ≤ A),
              f ij.1 ij.2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [FP.balance_antidiagonal_support b n]
        push_cast
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ij hij
        have hanti : ij ∈ Finset.antidiagonal n :=
          (Finset.mem_filter.mp hij).1
        have hsum : ij.1 + ij.2 = n :=
          Finset.mem_antidiagonal.mp hanti
        simp only [f]
        rw [hsum]
      _ = ∑ q ∈ Finset.range (A + 1),
          ∑ k ∈ Finset.range (N + 1 - q), f q k := by
        exact
          antidiagonal_fst_triangle A N f
  have hboundary :
      (∑ q ∈ Finset.range (A + 1),
        ∑ r ∈ Finset.range q, f q (N + 1 - q + r)) =
          FP.gsRatBoundary b x N := by
    unfold gsRatBoundary
    apply Finset.sum_congr rfl
    intro q hq
    have hqle : q ≤ N + 1 := by
      have hqA : q ≤ A := by
        have hqlt := Finset.mem_range.mp hq
        omega
      exact le_trans hqA hA
    apply Finset.sum_congr rfl
    intro r hr
    have hexp : q + (N + 1 - q + r) = N + 1 + r := by
      rw [← Nat.add_assoc, Nat.add_sub_of_le hqle]
    simp only [f]
    rw [hexp]
  have hrectangle :
      (∑ q ∈ Finset.range (A + 1),
        ∑ k ∈ Finset.range (N + 1), f q k) =
          FP.gsEvalRat x * ratWeightedPrefix b x N := by
    unfold gsEvalRat ratWeightedPrefix
    simp only [A]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [f]
    rw [pow_add]
    ring
  rw [hprefix]
  have hsplit :=
    triangle_boundary_rectangle A N hA f
  rw [hboundary, hrectangle] at hsplit
  linarith

/-- A packaged cutoff at which the explicit rational boundary tail is smaller
than a requested positive tolerance. -/
structure RationalBoundaryWitness
    [Fintype FP.toPresentation.Relator]
    (b : ℕ → ℕ) (x ε : ℚ) where
  cutoff : ℕ
  depth_le : FP.maxRelatorDepth + 1 ≤ cutoff + 1
  tail_abs_lt : |FP.gsRatBoundary b x cutoff| < ε

/-- Geometric decay of the explicit boundary strip.

This is the isolated analytic frontier. It only says that finitely many
bounded coefficient terms multiplied by powers of a rational number in
`[0, 1)` eventually become small. It does not mention GS inequalities,
positivity of the initial coefficient, or unboundedness. -/
theorem boundary_witness_bound
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {B : ℕ} {x ε : ℚ}
    (hx : 0 ≤ x)
    (hx1 : x < 1)
    (hbound : SUBound b B)
    (hε : 0 < ε) :
    Nonempty (RationalBoundaryWitness FP b x ε) := by
  classical
  let C : ℚ :=
    ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
      ∑ _r ∈ Finset.range q,
        |(FP.gsCoeffInt q : ℚ)| * (B : ℚ)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one (div_pos hε hC1) hx1
  let N := max FP.maxRelatorDepth n
  refine ⟨{
    cutoff := N
    depth_le := ?_
    tail_abs_lt := ?_
  }⟩
  · dsimp [N]
    omega
  · have htail_le :
        |FP.gsRatBoundary b x N| ≤ C * x ^ (N + 1) := by
      rw [FP.rat_boundary_tail]
      calc
        |∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
            ∑ r ∈ Finset.range q,
              (FP.gsCoeffInt q : ℚ) *
                (b (N + 1 - q + r) : ℚ) * x ^ (N + 1 + r)| ≤
            ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
              |∑ r ∈ Finset.range q,
                (FP.gsCoeffInt q : ℚ) *
                  (b (N + 1 - q + r) : ℚ) * x ^ (N + 1 + r)| := by
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q ∈ Finset.range (FP.maxRelatorDepth + 2),
              ∑ r ∈ Finset.range q,
                |(FP.gsCoeffInt q : ℚ)| * (B : ℚ) *
                  x ^ (N + 1) := by
          apply Finset.sum_le_sum
          intro q hq
          calc
            |∑ r ∈ Finset.range q,
                (FP.gsCoeffInt q : ℚ) *
                  (b (N + 1 - q + r) : ℚ) * x ^ (N + 1 + r)| ≤
                ∑ r ∈ Finset.range q,
                  |(FP.gsCoeffInt q : ℚ) *
                    (b (N + 1 - q + r) : ℚ) * x ^ (N + 1 + r)| := by
              exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ r ∈ Finset.range q,
                  |(FP.gsCoeffInt q : ℚ)| * (B : ℚ) *
                    x ^ (N + 1) := by
              apply Finset.sum_le_sum
              intro r hr
              calc
                |(FP.gsCoeffInt q : ℚ) *
                    (b (N + 1 - q + r) : ℚ) * x ^ (N + 1 + r)| =
                    |(FP.gsCoeffInt q : ℚ)| *
                      (b (N + 1 - q + r) : ℚ) *
                        (x ^ (N + 1) * x ^ r) := by
                  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hx, pow_add]
                  rw [abs_of_nonneg (show
                    (0 : ℚ) ≤ (b (N + 1 - q + r) : ℚ) by positivity)]
                _ ≤ |(FP.gsCoeffInt q : ℚ)| * (B : ℚ) *
                      (x ^ (N + 1) * 1) := by
                  gcongr
                  · exact_mod_cast hbound (N + 1 - q + r)
                  · exact pow_le_one₀ hx (le_of_lt hx1)
                _ = |(FP.gsCoeffInt q : ℚ)| * (B : ℚ) *
                      x ^ (N + 1) := by ring
        _ = C * x ^ (N + 1) := by
          simp only [C, Finset.sum_mul]
    have hpow :
        x ^ (N + 1) ≤ x ^ n := by
      apply pow_right_anti₀ hx (le_of_lt hx1)
      dsimp [N]
      omega
    calc
      |FP.gsRatBoundary b x N| ≤ C * x ^ (N + 1) := htail_le
      _ ≤ (C + 1) * x ^ n := by
        have hpow_nonneg : 0 ≤ x ^ n := pow_nonneg hx n
        nlinarith [mul_nonneg hC (pow_nonneg hx (N + 1))]
      _ < ε := by
        simpa [mul_comm] using (lt_div_iff₀ hC1).mp hn

/-- Projection form of geometric boundary-tail decay. -/
theorem gs_rat_boundary
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {B : ℕ} {x ε : ℚ}
    (hx : 0 ≤ x)
    (hx1 : x < 1)
    (hbound : SUBound b B)
    (hε : 0 < ε) :
    ∃ N, FP.maxRelatorDepth + 1 ≤ N + 1 ∧
      |FP.gsRatBoundary b x N| < ε := by
  rcases
      FP.boundary_witness_bound
        hx hx1 hbound hε with
    ⟨W⟩
  exact ⟨W.cutoff, W.depth_le, W.tail_abs_lt⟩

/-- Negativity of the GS polynomial and positivity of the initial coefficient
produce a positive tolerance for the tail estimate. -/
theorem neg_coeff_pos
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {x : ℚ}
    (hneg : FP.gsEvalRat x < 0)
    (hb0 : 0 < b 0) :
    0 < -(FP.gsEvalRat x * (b 0 : ℚ)) := by
  have hb0q : (0 : ℚ) < b 0 := by exact_mod_cast hb0
  have hmul : FP.gsEvalRat x * (b 0 : ℚ) < 0 :=
    mul_neg_of_neg_of_pos hneg hb0q
  linarith

/-- At a nonnegative point, multiplying by a negative GS-polynomial value
reverses the lower bound supplied by the initial coefficient. -/
theorem rat_weighted_coeff
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {x : ℚ}
    (hx : 0 ≤ x)
    (hneg : FP.gsEvalRat x < 0)
    (N : ℕ) :
    FP.gsEvalRat x * ratWeightedPrefix b x N ≤
      FP.gsEvalRat x * (b 0 : ℚ) := by
  apply mul_le_mul_of_nonpos_left
  · exact rat_weighted_prefix hx N
  · exact le_of_lt hneg

/-- A sufficiently small explicit boundary tail forces a negative weighted
GS-balance prefix. -/
theorem rat_balance_small
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {x : ℚ} {N : ℕ}
    (hx : 0 ≤ x)
    (hneg : FP.gsEvalRat x < 0)
    (hdepth : FP.maxRelatorDepth + 1 ≤ N + 1)
    (htail :
      |FP.gsRatBoundary b x N| <
        -(FP.gsEvalRat x * (b 0 : ℚ))) :
    FP.ratBalancePrefix b x N < 0 := by
  rw [FP.rat_balance_boundary
    b x N hdepth]
  have hmain :=
    FP.rat_weighted_coeff
      (b := b) hx hneg N
  have htailLower : -|FP.gsRatBoundary b x N| ≤
      FP.gsRatBoundary b x N :=
    neg_abs_le _
  linarith

/-- A bounded positive sequence and a negative rational GS-polynomial
evaluation produce a negative finite weighted balance prefix. -/
theorem rat_balance_bound
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {B : ℕ} {x : ℚ}
    (hx : 0 ≤ x)
    (hx1 : x < 1)
    (hneg : FP.gsEvalRat x < 0)
    (hbound : SUBound b B)
    (hb0 : 0 < b 0) :
    ∃ N, FP.ratBalancePrefix b x N < 0 := by
  have hε :
      0 < -(FP.gsEvalRat x * (b 0 : ℚ)) :=
    FP.neg_coeff_pos hneg hb0
  rcases
      FP.gs_rat_boundary
        hx hx1 hbound hε with
    ⟨N, hdepth, htail⟩
  exact
    ⟨N, FP.rat_balance_small
      hx hneg hdepth htail⟩

/-- A bounded positive sequence cannot satisfy all GS coefficient inequalities
when the GS polynomial has a negative rational value in `[0, 1)`. -/
theorem inequalities_rat_bound
    [Fintype FP.toPresentation.Relator]
    {b : ℕ → ℕ} {B : ℕ} {x : ℚ}
    (hx : 0 ≤ x)
    (hx1 : x < 1)
    (hneg : FP.gsEvalRat x < 0)
    (hbound : SUBound b B)
    (hb0 : 0 < b 0) :
    ¬ FP.gsCoefficientInequalities b := by
  intro hineq
  rcases
      FP.rat_balance_bound
        hx hx1 hneg hbound hb0 with
    ⟨N, hprefixNeg⟩
  have hprefixNonneg :=
    FP.rat_nonneg_inequalities hx hineq N
  linarith

/-- Certificate-packaged bounded-sequence contradiction. -/
theorem inequalities_certificate_tail
    [Fintype FP.toPresentation.Relator]
    (C : FP.RGCert)
    {b : ℕ → ℕ} {B : ℕ}
    (hbound : SUBound b B)
    (hb0 : 0 < b 0) :
    ¬ FP.gsCoefficientInequalities b := by
  exact
    FP.inequalities_rat_bound
      (le_of_lt C.point_pos) C.point_lt_one C.eval_neg hbound hb0

/-- The isolated arithmetic frontier for the bounded Vinberg endgame.

A negative rational GS certificate forces every positive coefficient sequence
satisfying the GS recurrence to exceed each proposed natural upper bound.  This
statement is purely arithmetic: it has no group, augmentation ideal, Fox
calculus, or finiteness hypothesis. -/
theorem certificate_gs_inequalities
    [Fintype FP.toPresentation.Relator]
    (C : FP.RGCert)
    {b : ℕ → ℕ}
    (hb0 : 0 < b 0)
    (hineq : FP.gsCoefficientInequalities b)
    (B : ℕ) :
    ∃ n, B < b n := by
  by_contra hnone
  have hbound : SUBound b B := by
    intro n
    exact Nat.le_of_not_gt (fun hn => hnone ⟨n, hn⟩)
  exact
    (FP.inequalities_certificate_tail
      C hbound hb0) hineq

/-- A negative rational certificate rules out a positive GS sequence with an
explicit pointwise upper bound. -/
theorem inequalities_certificate_bound
    [Fintype FP.toPresentation.Relator]
    (C : FP.RGCert)
    {b : ℕ → ℕ} {B : ℕ}
    (hbound : SUBound b B)
    (hb0 : 0 < b 0) :
    ¬ FP.gsCoefficientInequalities b := by
  intro hineq
  rcases
      FP.certificate_gs_inequalities
        C hb0 hineq B with
    ⟨n, hn⟩
  exact (not_lt_of_ge (hbound n)) hn

/-- Existentially bounded form of the rational-certificate obstruction. -/
theorem inequalities_certificate_bounded
    [Fintype FP.toPresentation.Relator]
    (C : FP.RGCert)
    {b : ℕ → ℕ}
    (hbounded : SBounde b)
    (hb0 : 0 < b 0) :
    ¬ FP.gsCoefficientInequalities b := by
  rcases hbounded with ⟨B, hB⟩
  exact
    FP.inequalities_certificate_bound
      C hB hb0

/-- A rational certificate rules out every packaged bounded positive GS
sequence. -/
theorem no_sequence_certificate
    [Fintype FP.toPresentation.Relator]
    (C : FP.RGCert) :
    ¬ Nonempty (BoundedGSSequence (p := p) FP) := by
  rintro ⟨S⟩
  exact
    (FP.inequalities_certificate_bound
      C S.upperBound S.coeff_zero_pos) S.inequalities

/-- Existential form of the bounded positive GS-sequence obstruction. -/
theorem not_gs_certificate
    [Fintype FP.toPresentation.Relator]
    (C : FP.RGCert) :
    ¬ ∃ (b : ℕ → ℕ), SBounde b ∧ 0 < b 0 ∧
      FP.gsCoefficientInequalities b := by
  rintro ⟨b, hb, hb0, hineq⟩
  exact
    (FP.inequalities_certificate_bounded
      C hb hb0) hineq

/-- Normalized existential form of the bounded-sequence obstruction. -/
theorem not_sequence_certificate
    [Fintype FP.toPresentation.Relator]
    (C : FP.RGCert) :
    ¬ ∃ (b : ℕ → ℕ), SBounde b ∧ b 0 = 1 ∧
      FP.gsCoefficientInequalities b := by
  rintro ⟨b, hb, hb0, hineq⟩
  apply FP.not_gs_certificate C
  refine ⟨b, hb, ?_, hineq⟩
  omega

end
end FPres
end Towers
