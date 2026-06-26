import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Milne, Algebraic Number Theory, Remark 7.7

An algebraically closed field contains an `n`th root of every element.  If an
absolute value takes some nonzero element to a value strictly below one, the
values of these roots converge to one without ever being one.  Consequently
the value range is not discrete.  This is the mechanism in Milne's example of
the extended `p`-adic absolute value on `Q^al`.
-/

namespace Towers.NumberTheory.Milne

open Filter Polynomial Real Topology

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- The absolute values of successively higher roots of `c` converge to one. -/
theorem tendsto_closed_roots
    (v : AbsoluteValue K ℝ) {c : K} (hc : c ≠ 0) :
    ∃ root : ℕ → K,
      (∀ n, root n ^ (n + 1) = c) ∧
        Tendsto (fun n ↦ v (root n)) atTop (𝓝 1) := by
  choose root hroot using fun n ↦
    IsAlgClosed.exists_pow_nat_eq c (Nat.succ_pos n)
  refine ⟨root, hroot, ?_⟩
  have hvalue (n : ℕ) :
      v (root n) = (v c) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
    have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
    calc
      v (root n) = (v (root n) ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (v.nonneg _) hn).symm
      _ = (v c) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
        rw [← map_pow, hroot]
  have hinv :
      Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  have hrpow :
      Tendsto (fun x : ℝ ↦ (v c) ^ x) (𝓝 0) (𝓝 1) := by
    simpa using
      (continuousAt_const_rpow (a := v c) (b := 0) (v.ne_zero hc)).tendsto
  rw [show (fun n ↦ v (root n)) =
      fun n ↦ (v c) ^ (((n + 1 : ℕ) : ℝ)⁻¹) by
        funext n
        exact hvalue n]
  exact hrpow.comp hinv

/-- **Milne, Remark 7.7.** The value range of a nontrivial absolute value on
an algebraically closed field is not discrete.  It suffices to exhibit one
nonzero element whose value is strictly below one. -/
theorem discrete_alg_closed
    (v : AbsoluteValue K ℝ) {c : K} (hc : c ≠ 0) (hc_lt_one : v c < 1) :
    ¬ DiscreteTopology (Set.range v) := by
  obtain ⟨root, hroot, htendsto⟩ :=
    tendsto_closed_roots v hc
  let values : ℕ → Set.range v := fun n ↦
    ⟨v (root n), ⟨root n, rfl⟩⟩
  let oneValue : Set.range v := ⟨1, ⟨1, map_one v⟩⟩
  have hvalues : Tendsto values atTop (𝓝 oneValue) := by
    rw [tendsto_subtype_rng]
    simpa [values, oneValue] using htendsto
  intro hdiscrete
  letI : DiscreteTopology (Set.range v) := hdiscrete
  rw [nhds_discrete, tendsto_pure] at hvalues
  obtain ⟨n, hn⟩ := hvalues.exists
  have hpow_lt : v (root n) ^ (n + 1) < 1 := by
    rw [← map_pow, hroot]
    exact hc_lt_one
  have hroot_lt : v (root n) < 1 := by
    by_contra hnot
    exact (not_le_of_gt hpow_lt) (one_le_pow₀ (le_of_not_gt hnot))
  exact hroot_lt.ne (congrArg Subtype.val hn)

end

end Towers.NumberTheory.Milne
