import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Milne, Algebraic Number Theory, Theorem 4.17

This file records Blichfeldt's theorem in Milne's pointwise form: a measurable set whose
measure is larger than a fundamental domain contains two distinct points whose difference
belongs to the lattice.
-/

namespace Towers.NumberTheory.Milne

open MeasureTheory Set

open scoped Pointwise

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E]
  {μ : Measure E} {L : AddSubgroup E} [Countable L]
  [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
  {D S : Set E}

/-- **Milne, Theorem 4.17 (Blichfeldt).** If `D` is a fundamental domain for a
countable lattice `L` and the measurable set `S` has measure larger than `D`, then `S`
contains distinct points whose difference belongs to `L`.

Milne applies this with a full lattice in a finite-dimensional real vector space and with
`D` a fundamental parallelepiped.  The fundamental-domain formulation is slightly more
general and isolates exactly the hypotheses used in the proof. -/
theorem distinct_points_lattice
    (fund : IsAddFundamentalDomain L D μ) (hS : NullMeasurableSet S μ)
    (hμ : μ D < μ S) :
    ∃ α ∈ S, ∃ β ∈ S, α ≠ β ∧ β - α ∈ L := by
  obtain ⟨x, y, hxy, hdisj⟩ :=
    MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd fund hS hμ
  obtain ⟨_, ⟨α, hα, rfl⟩, β, hβ, hβα⟩ := Set.not_disjoint_iff.mp hdisj
  simp_rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm _ β,
    ← sub_eq_sub_iff_add_eq_add, ← AddSubgroup.coe_sub] at hβα
  refine ⟨α, hα, β, hβ, ?_, ?_⟩
  · intro hαβ
    apply hxy
    have hzero : ((x - y : L) : E) = 0 := by
      rw [← hβα, hαβ, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (by simpa using hzero))
  · rw [hβα]
    exact (x - y).property

section HalfDifference

open MeasureTheory.Measure Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  {nu : Measure V} [IsAddHaarMeasure nu]
  {Gamma : AddSubgroup V} [Countable Gamma]
  {F T : Set V}

/-- **Milne, Remark 4.18.** Suppose that `T` contains half the difference of any two
of its points.  If its volume is strictly greater than `2 ^ n` times the volume of a
fundamental domain of a lattice, then `T` contains a nonzero lattice point.

This is the intermediate form of Minkowski's argument in the source.  It is strictly
weaker than assuming that `T` is convex and symmetric about the origin. -/
theorem lattice_point_half
    (fund : IsAddFundamentalDomain Gamma F nu)
    (hT : ∀ a ∈ T, ∀ b ∈ T, (2 : ℝ)⁻¹ • (a - b) ∈ T)
    (hTmeas : NullMeasurableSet T nu)
    (hvolume : nu F * 2 ^ finrank ℝ V < nu T) :
    ∃ x : Gamma, x ≠ 0 ∧ (x : V) ∈ T := by
  have hhalfVolume : nu F < nu ((2 : ℝ)⁻¹ • T) := by
    rw [addHaar_smul_of_nonneg nu (by positivity : 0 ≤ (2 : ℝ)⁻¹) T,
      ← ENNReal.mul_lt_mul_iff_left (pow_ne_zero (finrank ℝ V) (two_ne_zero' _))
        (by finiteness),
      mul_right_comm, ENNReal.ofReal_pow (by positivity : 0 ≤ (2 : ℝ)⁻¹),
      ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2)]
    norm_num
    rwa [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow,
      one_mul]
  obtain ⟨a, ha, b, hb, hab, hba⟩ :=
    distinct_points_lattice fund
      (NullMeasurableSet.const_smul hTmeas (2 : ℝ)⁻¹) hhalfVolume
  have haT : (2 : ℝ) • a ∈ T :=
    (Set.mem_inv_smul_set_iff₀ (two_ne_zero' ℝ) T a).mp ha
  have hbT : (2 : ℝ) • b ∈ T :=
    (Set.mem_inv_smul_set_iff₀ (two_ne_zero' ℝ) T b).mp hb
  refine ⟨⟨b - a, hba⟩, ?_, ?_⟩
  · intro hzero
    apply hab
    exact (sub_eq_zero.mp (congrArg Subtype.val hzero)).symm
  · simpa [smul_sub] using hT ((2 : ℝ) • b) hbT ((2 : ℝ) • a) haT

end HalfDifference

end Towers.NumberTheory.Milne
