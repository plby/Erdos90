import Submission.ClassField.EulerProducts.OrderedPartialSum
import Submission.ClassField.EulerProducts.RayUnitSubgroup

/-!
# Chapter VI, Section 2, Corollary 2.9

This file defines the partial zeta function of an actual ray class: its
coefficient at `n` is the number of integral ideals in that ray class whose
absolute norm is `n`.  The elementary fibre-counting lemma below identifies
the coefficient partial sums with the counting function of Proposition 2.8.
Consequently its geometry-of-numbers estimate feeds directly into the Abel
summation continuation of Proposition 2.5.
-/

namespace Submission.CField.EProduc

open Complex Filter Finset Ideal IsDedekindDomain NumberField Set Topology
open scoped nonZeroDivisors
open Submission.CField.RCGroups

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Integral ideals in the ray class `k` having absolute norm exactly `n`.
These are precisely the objects contributing to the `n`th coefficient of
Milne's partial zeta function. -/
def RayIdealsNorm (m : Modulus K)
    (k : RayClassGroup K m) (n : ℕ) :=
  {I : {I : IIPrime K m // rayIntegralIdeal K I = k} //
    absNorm I.1.ideal = n}

/-- Every exact-norm fibre is finite. -/
theorem ray_ideals_norm (m : Modulus K)
    (k : RayClassGroup K m) (n : ℕ) :
    Finite (RayIdealsNorm K m k n) := by
  letI : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq n).fintype
  let f : RayIdealsNorm K m k n →
      {I : Ideal (𝓞 K) // absNorm I = n} := fun I ↦ ⟨I.1.1.ideal, I.2⟩
  exact Finite.of_injective f (fun I J hIJ ↦ by
    rcases I with ⟨⟨⟨Ii, hIi0, hIiPrime⟩, hIiClass⟩, hIiNorm⟩
    rcases J with ⟨⟨⟨Ji, hJi0, hJiPrime⟩, hJiClass⟩, hJiNorm⟩
    simp only [f, Subtype.mk.injEq] at hIJ
    subst Ji
    rfl)

/-- The coefficient sequence of the ray-class partial zeta function. -/
def partialZetaCoefficients (m : Modulus K)
    (k : RayClassGroup K m) (n : ℕ) : ℂ :=
  Nat.card (RayIdealsNorm K m k n)

/-- The actual ray-class partial zeta function
`ζ(s,k) = ∑_{a ≥ 0, a ∈ k} N(a)^{-s}`, initially represented by its
ordered Dirichlet series. -/
def rayPartialZeta (m : Modulus K)
    (k : RayClassGroup K m) : ℂ → ℂ :=
  orderedValue (partialZetaCoefficients K m k)

/-- The meromorphic continuation selected by Proposition 2.5. -/
def partialZetaContinuation (m : Modulus K)
    (k : RayClassGroup K m) : ℂ → ℂ :=
  continuation (partialZetaCoefficients K m k)
    (rayCountingConstant K m)

/-- The holomorphic part after subtracting the simple polar term. -/
def partialHolomorphicPart (m : Modulus K)
    (k : RayClassGroup K m) : ℂ → ℂ :=
  holomorphicPart (partialZetaCoefficients K m k)
    (rayCountingConstant K m)

/-- Ideals in `k` of norm at most a natural number are the disjoint union of
their exact positive-norm fibres. -/
theorem ray_count_coefficients (m : Modulus K)
    (k : RayClassGroup K m) (N : ℕ) :
    rayIdealCount K m k (N : ℝ) =
      ∑ n ∈ Finset.Icc 1 N, Nat.card (RayIdealsNorm K m k n) := by
  let A := {I : IIPrime K m // rayIntegralIdeal K I = k}
  let norm : A → ℕ := fun I ↦ absNorm I.1.ideal
  have hfiniteFiber : ∀ n ∈ Finset.Icc 1 N, Set.Finite {I : A | norm I = n} := by
    intro n hn
    let f : {I : A | norm I = n} →
        RayIdealsNorm K m k n := fun I ↦
      ⟨I.1, I.2⟩
    letI : Finite (RayIdealsNorm K m k n) :=
      ray_ideals_norm K m k n
    letI : Finite {I : A | norm I = n} := Finite.of_injective f (fun I J hIJ ↦ by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : RayIdealsNorm K m k n ↦
        (z.1.1 : IIPrime K m)) hIJ)
    exact Set.toFinite _
  have hsum :
      (∑ n ∈ Finset.Icc 1 N,
        Nat.card (RayIdealsNorm K m k n)) =
      ∑ n ∈ Finset.Icc 1 N, Nat.card {I : A // norm I = n} := by
    apply Finset.sum_congr rfl
    intro n hn
    apply Nat.card_congr
    dsimp only [RayIdealsNorm, A, norm]
    exact Equiv.refl _
  rw [hsum, ← Finset.card_preimage_eq_sum_card_image_eq hfiniteFiber]
  apply Nat.card_congr
  let toFun : RayIntegralIdeals K m k (N : ℝ) →
      norm ⁻¹' (↑(Finset.Icc 1 N) : Set ℕ) :=
    fun I ↦ ⟨⟨I.1, I.2.1⟩, by
      change absNorm I.1.ideal ∈ Finset.Icc 1 N
      apply Finset.mem_Icc.mpr
      constructor
      · apply Nat.one_le_iff_ne_zero.mpr
        intro hzero
        exact I.1.ne_zero (Ideal.absNorm_eq_zero_iff.mp hzero)
      · exact_mod_cast I.2.2⟩
  let invFun : norm ⁻¹' (↑(Finset.Icc 1 N) : Set ℕ) →
      RayIntegralIdeals K m k (N : ℝ) := fun I ↦
    ⟨I.1.1, I.1.2, by
      have hle : norm I.1 ≤ N := (Finset.mem_Icc.mp I.2).2
      exact_mod_cast hle⟩
  exact {
    toFun := toFun
    invFun := invFun
    left_inv := fun I ↦ by cases I; rfl
    right_inv := fun I ↦ by cases I; rfl }

/-- Thus the ordinary coefficient partial sum used in Proposition 2.5 is
exactly the ray-class counting function at a natural argument. -/
theorem coefficient_partial_ray (m : Modulus K)
    (k : RayClassGroup K m) (N : ℕ) :
    orderedCoefficientPartial
        (partialZetaCoefficients K m k) N =
      (rayIdealCount K m k (N : ℝ) : ℂ) := by
  simp only [orderedCoefficientPartial,
    partialZetaCoefficients, ← Nat.cast_sum]
  rw [← ray_count_coefficients K m k N]

/-- The source exponent `1 - 1/d` lies strictly below one. -/
theorem ray_error_exponent :
    1 - 1 / (numberFieldDegree K : ℝ) < 1 := by
  have hd : 0 < (numberFieldDegree K : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hinv : 0 < 1 / (numberFieldDegree K : ℝ) := one_div_pos.mpr hd
  linarith

/-- Proposition 2.8 is exactly the coefficient partial-sum estimate required
by Proposition 2.5. -/
theorem partial_zeta_estimate
    (m : Modulus K) (k : RayClassGroup K m)
    (hgeometry : GeometryNumbersEstimate K m k) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖orderedCoefficientPartial
          (partialZetaCoefficients K m k) N -
        (rayCountingConstant K m : ℂ) * (N : ℂ)‖ ≤
      C * (N : ℝ) ^ (1 - 1 / (numberFieldDegree K : ℝ)) := by
  obtain ⟨C, hC⟩ := hgeometry
  have hCnonneg : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have h' :
        |(rayIdealCount K m k 1 : ℝ) - rayCountingConstant K m| ≤ C := by
      simpa using h
    have habs : 0 ≤
        |(rayIdealCount K m k 1 : ℝ) - rayCountingConstant K m| :=
      abs_nonneg _
    exact habs.trans h'
  refine ⟨C, ?_⟩
  intro N
  rcases N with _ | N
  · simpa [orderedCoefficientPartial] using
      (mul_nonneg hCnonneg
        (Real.rpow_nonneg (x := (0 : ℝ)) (by norm_num)
          (1 - 1 / (numberFieldDegree K : ℝ))))
  · rw [coefficient_partial_ray K m k (N + 1)]
    rw [show (rayIdealCount K m k ((N + 1 : ℕ) : ℝ) : ℂ) =
        (((rayIdealCount K m k ((N + 1 : ℕ) : ℝ) : ℕ) : ℝ) : ℂ) by
          norm_num]
    have hreal :
        ‖((rayIdealCount K m k ((N + 1 : ℕ) : ℝ) : ℝ) : ℂ) -
            (rayCountingConstant K m : ℂ) * ((N + 1 : ℕ) : ℂ)‖ =
          |(rayIdealCount K m k ((N + 1 : ℕ) : ℝ) : ℝ) -
            rayCountingConstant K m * ((N + 1 : ℕ) : ℝ)| := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hreal]
    exact hC ((N + 1 : ℕ) : ℝ) (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))

/-- Literal analytic conclusion of Corollary 2.9.  The continuation agrees
with the defining partial zeta series on `Re(s)>1`, is holomorphic throughout
`Re(s)>1-1/d` away from `1`, and at `1` has the displayed simple-pole
expansion and residue `g_m`. -/
def RayIdealsConclusion (m : Modulus K)
    (k : RayClassGroup K m) : Prop :=
  let b := 1 - 1 / (numberFieldDegree K : ℝ)
  (∀ s : ℂ, 1 < s.re →
    partialZetaContinuation K m k s = rayPartialZeta K m k s) ∧
  MeromorphicOn (partialZetaContinuation K m k) {s : ℂ | b < s.re} ∧
  DifferentiableOn ℂ (partialZetaContinuation K m k)
    ({s : ℂ | b < s.re} \ {1}) ∧
  DifferentiableOn ℂ (partialHolomorphicPart K m k)
    {s : ℂ | b < s.re} ∧
  (∀ s : ℂ, partialZetaContinuation K m k s =
    (rayCountingConstant K m : ℂ) / (s - 1) +
      partialHolomorphicPart K m k s) ∧
  Tendsto
    (fun s : ℂ ↦ (s - 1) * partialZetaContinuation K m k s)
    (𝓝[≠] 1) (𝓝 (rayCountingConstant K m : ℂ))

/-- Proposition 2.5 applied to the precise counting estimate of Proposition
2.8 proves Corollary 2.9.  The two arguments are exactly the already-isolated
ordinary Abel-summation theorem and ray-class geometry-of-numbers theorem;
no hypothesis is added to Milne's corollary. -/
theorem abel_euler_convergence
    (hAbel : OrdinaryConvergenceBridge)
    (h28 : RayCountingAsymptotic K) :
    (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k) := by
  intro m k
  let b : ℝ := 1 - 1 / (numberFieldDegree K : ℝ)
  obtain ⟨C, hgrowth⟩ := partial_zeta_estimate K m k (h28 m k)
  have h25 := partial_ordinary_convergence hAbel
    (partialZetaCoefficients K m k)
    (rayCountingConstant K m : ℂ) C b
    (ray_error_exponent K) hgrowth
  rcases h25 with ⟨hagree, hmero, hhol, hexpansion, hresidue⟩
  refine ⟨?_, hmero, ?_, hhol, hexpansion, hresidue⟩
  · intro s hs
    exact hagree s hs
  · intro s hs
    have hsDomain : b < s.re := hs.1
    have hsOne : s ≠ 1 := by
      simpa only [Set.mem_singleton_iff] using hs.2
    have hpole : DifferentiableAt ℂ
        (fun z : ℂ ↦ (rayCountingConstant K m : ℂ) / (z - 1)) s :=
      (differentiableAt_const
        (c := (rayCountingConstant K m : ℂ))).div
        (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ))))
        (sub_ne_zero.mpr hsOne)
    rw [show partialZetaContinuation K m k =
        fun z ↦ (rayCountingConstant K m : ℂ) / (z - 1) +
          partialHolomorphicPart K m k z by rfl]
    exact hpole.differentiableWithinAt.add
      ((hhol s hsDomain).mono (fun _ hz ↦ hz.1))

end

end Submission.CField.EProduc
