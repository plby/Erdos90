import Towers.NumberTheory.Locals.NondiscreteAlgebraicClosure
import Mathlib.NumberTheory.Padics.Complex

/-!
# Milne, Remark 7.7: the nonzero value group

The tracked Chapter 7 theorem proves non-discreteness for the full range of an absolute value.
This file records the sharper statements appearing in Milne: the value group of the nonzero
elements is itself non-discrete, and the value group of the `p`-adic algebraic closure is exactly
the group of rational powers of `p`.
-/

namespace Towers.NumberTheory.Milne

open Filter Polynomial Real Topology

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- If an absolute value on an algebraically closed field takes a nonzero value below one,
then its nonzero value group is not discrete. -/
theorem absolute_discrete_closed
    (v : AbsoluteValue K ℝ) {c : K} (hc : c ≠ 0) (hc_lt_one : v c < 1) :
    ¬ DiscreteTopology (Set.range fun x : Kˣ ↦ v (x : K)) := by
  obtain ⟨root, hroot, htendsto⟩ :=
    tendsto_closed_roots v hc
  have hroot_ne (n : ℕ) : root n ≠ 0 := by
    intro hz
    have hn := hroot n
    rw [hz, zero_pow (Nat.succ_ne_zero n)] at hn
    exact hc hn.symm
  let rootUnit : ℕ → Kˣ := fun n ↦ Units.mk0 (root n) (hroot_ne n)
  let values : ℕ → Set.range (fun x : Kˣ ↦ v (x : K)) := fun n ↦
    ⟨v (root n), ⟨rootUnit n, rfl⟩⟩
  let oneValue : Set.range (fun x : Kˣ ↦ v (x : K)) :=
    ⟨1, ⟨1, map_one v⟩⟩
  have hvalues : Tendsto values atTop (𝓝 oneValue) := by
    rw [tendsto_subtype_rng]
    simpa [values, oneValue] using htendsto
  intro hdiscrete
  letI : DiscreteTopology (Set.range fun x : Kˣ ↦ v (x : K)) := hdiscrete
  rw [nhds_discrete, tendsto_pure] at hvalues
  obtain ⟨n, hn⟩ := hvalues.exists
  have hpow_lt : v (root n) ^ (n + 1) < 1 := by
    rw [← map_pow, hroot]
    exact hc_lt_one
  have hroot_lt : v (root n) < 1 := by
    by_contra hnot
    exact (not_le_of_gt hpow_lt) (one_le_pow₀ (le_of_not_gt hnot))
  exact hroot_lt.ne (congrArg Subtype.val hn)

/-- Milne's Remark 7.7 in its intrinsic form: a nontrivial absolute value on an
algebraically closed field has a nondiscrete nonzero value group. -/
theorem absolute_discrete_nontrivial
    (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    ¬ DiscreteTopology (Set.range fun x : Kˣ ↦ v (x : K)) := by
  obtain ⟨c, hc, hc_lt_one⟩ := hv.exists_abv_lt_one
  exact absolute_discrete_closed v hc hc_lt_one

/-- Every nonzero norm in the `p`-adic algebraic closure is a rational power of `p`.

Indeed, the spectral norm of an algebraic element is the degree-th root of the norm of the
constant coefficient of its minimal polynomial.  The norm of a nonzero element of `ℚ_[p]` is
an integral power of `p`. -/
theorem alg_cl_rpow
    (p : ℕ) [Fact p.Prime] (x : (PadicAlgCl p)ˣ) :
    ∃ q : ℚ, ‖(x : PadicAlgCl p)‖ = (p : ℝ) ^ (q : ℝ) := by
  let a : ℚ_[p] := (minpoly ℚ_[p] (x : PadicAlgCl p)).coeff 0
  let n : ℕ := (minpoly ℚ_[p] (x : PadicAlgCl p)).natDegree
  have hx : (x : PadicAlgCl p) ≠ 0 := Units.ne_zero x
  have ha : a ≠ 0 := by
    exact minpoly.coeff_zero_ne_zero
      (Algebra.IsAlgebraic.isAlgebraic (x : PadicAlgCl p)).isIntegral hx
  have hn : n ≠ 0 := by
    exact (minpoly.natDegree_pos
      (Algebra.IsAlgebraic.isAlgebraic (x : PadicAlgCl p)).isIntegral).ne'
  refine ⟨(((-a.valuation : ℤ) : ℚ) / n), ?_⟩
  rw [← PadicAlgCl.spectralNorm_eq,
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow]
  change ‖a‖ ^ (1 / (n : ℝ)) = _
  rw [Padic.norm_eq_zpow_neg_valuation ha, ← Real.rpow_intCast,
    ← Real.rpow_mul (by positivity : 0 ≤ (p : ℝ))]
  congr 1
  push_cast
  ring

/-- Every rational power of `p` occurs as the norm of a nonzero element of the `p`-adic
algebraic closure. -/
theorem padic_cl_rpow
    (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∃ x : (PadicAlgCl p)ˣ, ‖(x : PadicAlgCl p)‖ = (p : ℝ) ^ (q : ℝ) := by
  let c : PadicAlgCl p := (p : PadicAlgCl p) ^ (-q.num)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq c q.den_pos
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hc : c ≠ 0 := zpow_ne_zero _ hp0
  have hy0 : y ≠ 0 := by
    intro h
    apply hc
    rw [← hy, h, zero_pow q.den_ne_zero]
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply (pow_left_inj₀ (norm_nonneg y)
    (Real.rpow_nonneg (by positivity) _) q.den_ne_zero).mp
  have hynorm := congrArg norm hy
  have hpnorm : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    rw [show (p : PadicAlgCl p) =
      algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) by simp,
      PadicAlgCl.norm_extends, Padic.norm_p]
  rw [norm_pow, norm_zpow, hpnorm] at hynorm
  rw [hynorm, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (p : ℝ))]
  rw [inv_zpow, ← zpow_neg]
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  norm_num
  exact_mod_cast (Rat.mul_den_eq_num q).symm

/-- **Milne, Remark 7.7.** The nonzero value group of the canonical `p`-adic algebraic closure
is exactly the group of rational powers of `p`. -/
theorem cl_rpow_rat (p : ℕ) [Fact p.Prime] :
    Set.range (fun x : (PadicAlgCl p)ˣ ↦ ‖(x : PadicAlgCl p)‖) =
      Set.range (fun q : ℚ ↦ (p : ℝ) ^ (q : ℝ)) := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨q, hq⟩ := alg_cl_rpow p x
    exact ⟨q, hq.symm⟩
  · rintro ⟨q, rfl⟩
    exact padic_cl_rpow p q

end

end Towers.NumberTheory.Milne
