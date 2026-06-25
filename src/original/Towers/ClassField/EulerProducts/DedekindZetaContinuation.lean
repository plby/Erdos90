import Towers.ClassField.EulerProducts.IntegralIdealsNorm

/-!
# Milne, Class Field Theory, Corollary VI.2.12

The Dedekind zeta continuation is obtained exactly as in the source: sum the
partial zeta continuations over the ray classes for the trivial modulus.  The
common residue is then identified with Mathlib's Dedekind-zeta residue by
restricting the complex residue limit to real `s > 1`, where Mathlib proves
the analytic class-number formula.

The sole interface not presently packaged is the initial-half-plane identity
that regroups the absolutely convergent ideal series by its (trivial-modulus)
ray classes.  `DedekindZetaDecomposition` isolates precisely that
identity; it contains no continuation or residue assertion.
-/

namespace Towers.CField.EProduc

open Complex Filter Finset Ideal IsDedekindDomain NumberField
  NumberField.InfinitePlace NumberField.Units Set Topology
open Towers.CField.RCGroups

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The continuation in Corollary 2.12, constructed by summing the partial
zeta continuations for the ordinary ideal classes (`m = 1`). -/
def dedekindZetaContinuation : ℂ → ℂ :=
  fun s ↦ ∑ᶠ k : RayClassGroup K (1 : Modulus K),
    partialZetaContinuation K 1 k s

/-- Its holomorphic part, obtained by summing the holomorphic parts of the
partial zeta functions. -/
def dedekindHolomorphicPart : ℂ → ℂ :=
  fun s ↦ ∑ᶠ k : RayClassGroup K (1 : Modulus K),
    partialHolomorphicPart K 1 k s

/-- Before identifying constants, the sum of the partial-zeta residues is
the number of trivial-modulus ray classes times their common residue. -/
def dedekindZetaRay : ℝ :=
  Nat.card (RayClassGroup K (1 : Modulus K)) *
    rayCountingConstant K 1

/-- The initial series for Dedekind zeta is the finite sum of the initial
partial-zeta series.  This is exactly the absolutely-convergent regrouping
step in Milne's one-line proof. -/
def DedekindZetaDecomposition : Prop :=
  ∀ s : ℂ, 1 < s.re →
    dedekindZeta K s =
      ∑ᶠ k : RayClassGroup K (1 : Modulus K),
        rayPartialZeta K 1 k s

/-- The complete missing trivial-modulus interface: the ray class group is
finite and the absolutely convergent Dedekind-zeta series regroups over it. -/
structure DedekindZetaBridge : Prop where
  rayClassGroup : Finite (RayClassGroup K (1 : Modulus K))
  decomposition : DedekindZetaDecomposition K

/-- The summed continuation has the expected expansion with the as-yet
unidentified sum of the common partial-zeta residues. -/
theorem dedekind_continuation_expansion
    [Finite (RayClassGroup K (1 : Modulus K))]
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k)) (s : ℂ) :
    dedekindZetaContinuation K s =
      (dedekindZetaRay K : ℂ) / (s - 1) +
        dedekindHolomorphicPart K s := by
  letI : Fintype (RayClassGroup K (1 : Modulus K)) := Fintype.ofFinite _
  simp only [dedekindZetaContinuation,
    dedekindHolomorphicPart, finsum_eq_sum_of_fintype]
  calc
    ∑ k : RayClassGroup K (1 : Modulus K),
        partialZetaContinuation K 1 k s =
      ∑ k : RayClassGroup K (1 : Modulus K),
        ((rayCountingConstant K 1 : ℂ) / (s - 1) +
          partialHolomorphicPart K 1 k s) := by
        apply sum_congr rfl
        intro k hk
        exact (h29 1 k).2.2.2.2.1 s
    _ = (∑ _k : RayClassGroup K (1 : Modulus K),
          (rayCountingConstant K 1 : ℂ) / (s - 1)) +
        ∑ k : RayClassGroup K (1 : Modulus K),
          partialHolomorphicPart K 1 k s := by
        rw [sum_add_distrib]
    _ = (dedekindZetaRay K : ℂ) / (s - 1) +
        ∑ k : RayClassGroup K (1 : Modulus K),
          partialHolomorphicPart K 1 k s := by
        simp [dedekindZetaRay, nsmul_eq_mul]
        ring

/-- The global holomorphic part is holomorphic on Milne's half-plane. -/
theorem differentiable_holomorphic_part
    [Finite (RayClassGroup K (1 : Modulus K))]
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k)) :
    DifferentiableOn ℂ (dedekindHolomorphicPart K)
      {s : ℂ | 1 - 1 / (numberFieldDegree K : ℝ) < s.re} := by
  letI : Fintype (RayClassGroup K (1 : Modulus K)) := Fintype.ofFinite _
  intro s hs
  have heq : dedekindHolomorphicPart K =
      fun z ↦ ∑ k : RayClassGroup K (1 : Modulus K),
        partialHolomorphicPart K 1 k z := by
    funext z
    simp [dedekindHolomorphicPart, finsum_eq_sum_of_fintype]
  rw [heq]
  exact DifferentiableWithinAt.fun_sum fun k hk ↦
    (h29 1 k).2.2.2.1 s hs

/-- The summed continuation is meromorphic on the full source half-plane. -/
theorem meromorphic_dedekind_continuation
    [Finite (RayClassGroup K (1 : Modulus K))]
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k)) :
    MeromorphicOn (dedekindZetaContinuation K)
      {s : ℂ | 1 - 1 / (numberFieldDegree K : ℝ) < s.re} := by
  letI : Fintype (RayClassGroup K (1 : Modulus K)) := Fintype.ofFinite _
  intro s hs
  have heq : dedekindZetaContinuation K =
      fun z ↦ ∑ k : RayClassGroup K (1 : Modulus K),
        partialZetaContinuation K 1 k z := by
    funext z
    simp [dedekindZetaContinuation, finsum_eq_sum_of_fintype]
  rw [heq]
  exact MeromorphicAt.fun_sum fun k hk ↦ (h29 1 k).2.1 s hs

/-- Away from `1`, the summed continuation is holomorphic. -/
theorem differentiable_dedekind_punctured
    [Finite (RayClassGroup K (1 : Modulus K))]
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k)) :
    DifferentiableOn ℂ (dedekindZetaContinuation K)
      ({s : ℂ | 1 - 1 / (numberFieldDegree K : ℝ) < s.re} \ {1}) := by
  letI : Fintype (RayClassGroup K (1 : Modulus K)) := Fintype.ofFinite _
  intro s hs
  have heq : dedekindZetaContinuation K =
      fun z ↦ ∑ k : RayClassGroup K (1 : Modulus K),
        partialZetaContinuation K 1 k z := by
    funext z
    simp [dedekindZetaContinuation, finsum_eq_sum_of_fintype]
  rw [heq]
  exact DifferentiableWithinAt.fun_sum fun k hk ↦
    (h29 1 k).2.2.1 s hs

/-- Summing the partial-zeta residue limits gives the preliminary residue of
the Dedekind-zeta continuation. -/
theorem dedekind_continuation_residue
    [Finite (RayClassGroup K (1 : Modulus K))]
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k)) :
    Tendsto
      (fun s : ℂ ↦ (s - 1) * dedekindZetaContinuation K s)
      (𝓝[≠] 1) (𝓝 (dedekindZetaRay K : ℂ)) := by
  letI : Fintype (RayClassGroup K (1 : Modulus K)) := Fintype.ofFinite _
  have hsum : Tendsto
      (fun s : ℂ ↦ ∑ k : RayClassGroup K (1 : Modulus K),
        (s - 1) * partialZetaContinuation K 1 k s)
      (𝓝[≠] 1)
      (𝓝 (∑ _k : RayClassGroup K (1 : Modulus K),
        (rayCountingConstant K 1 : ℂ))) := by
    classical
    induction (Finset.univ : Finset (RayClassGroup K (1 : Modulus K))) using
        Finset.induction with
    | empty => simp
    | @insert k t hk ih =>
        simpa [Finset.sum_insert hk] using
          ((h29 1 k).2.2.2.2.2.add ih)
  simpa [dedekindZetaContinuation, dedekindZetaRay,
    finsum_eq_sum_of_fintype, Finset.mul_sum, nsmul_eq_mul] using hsum

/-- The only missing regrouping bridge gives agreement with the actual
Dedekind zeta function on its initial half-plane. -/
theorem dedekind_zeta_continuation
    [Finite (RayClassGroup K (1 : Modulus K))]
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k))
    (hdecomp : DedekindZetaDecomposition K)
    (s : ℂ) (hs : 1 < s.re) :
    dedekindZetaContinuation K s = dedekindZeta K s := by
  letI : Fintype (RayClassGroup K (1 : Modulus K)) := Fintype.ofFinite _
  rw [hdecomp s hs]
  simp only [dedekindZetaContinuation, finsum_eq_sum_of_fintype]
  apply sum_congr rfl
  intro k hk
  exact (h29 1 k).1 s hs

/-- Restricting a punctured complex neighbourhood of `1` along the real
axis from the right remains inside that punctured neighbourhood. -/
private theorem tendsto_real_nhds :
    Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 1 := ne_of_gt hs
    change (s : ℂ) ≠ 1
    exact_mod_cast hs'

/-- The preliminary sum of partial-zeta residues is exactly Mathlib's
Dedekind-zeta residue.  This avoids inserting a separate ray-class-number
formula: uniqueness of the already-known real residue limit proves it. -/
theorem dedekind_zeta_ray
    [Finite (RayClassGroup K (1 : Modulus K))]
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k))
    (hdecomp : DedekindZetaDecomposition K) :
    dedekindZetaRay K = dedekindZeta_residue K := by
  have hcomplex := (dedekind_continuation_residue K h29).comp
    tendsto_real_nhds
  have hagree :
      (fun s : ℝ ↦ (s - 1) * dedekindZetaContinuation K s) =ᶠ[𝓝[>] 1]
        fun s : ℝ ↦ (s - 1) * dedekindZeta K s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [dedekind_zeta_continuation K h29 hdecomp]
    exact_mod_cast hs
  have hfromPartial : Tendsto
      (fun s : ℝ ↦ (s - 1) * dedekindZeta K s)
      (𝓝[>] 1) (𝓝 (dedekindZetaRay K : ℂ)) :=
    hcomplex.congr' hagree
  have hknown := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have heq : (dedekindZetaRay K : ℂ) =
      (dedekindZeta_residue K : ℂ) :=
    tendsto_nhds_unique hfromPartial hknown
  exact_mod_cast heq

/-- Literal analytic conclusion of Corollary VI.2.12.  Nonvanishing of the
displayed residue makes the at-most-simple meromorphic singularity an actual
simple pole. -/
def DedekindContinuationConclusion : Prop :=
  let b := 1 - 1 / (numberFieldDegree K : ℝ)
  (∀ s : ℂ, 1 < s.re →
    dedekindZetaContinuation K s = dedekindZeta K s) ∧
  MeromorphicOn (dedekindZetaContinuation K) {s : ℂ | b < s.re} ∧
  DifferentiableOn ℂ (dedekindZetaContinuation K)
    ({s : ℂ | b < s.re} \ {1}) ∧
  DifferentiableOn ℂ (dedekindHolomorphicPart K)
    {s : ℂ | b < s.re} ∧
  (∀ s : ℂ, dedekindZetaContinuation K s =
    (dedekindZeta_residue K : ℂ) / (s - 1) +
      dedekindHolomorphicPart K s) ∧
  Tendsto
    (fun s : ℂ ↦ (s - 1) * dedekindZetaContinuation K s)
    (𝓝[≠] 1) (𝓝 (dedekindZeta_residue K : ℂ)) ∧
  dedekindZeta_residue K ≠ 0 ∧
  dedekindZeta_residue K =
    (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
        regulator K * classNumber K) /
      (torsionOrder K * Real.sqrt |discr K|)

/-- Corollary 2.9 and the initial absolutely-convergent ray-class
decomposition prove the exact source conclusion. -/
theorem dedekindContinuationStatement
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k))
    (hbridge : DedekindZetaBridge K) :
    (DedekindContinuationConclusion K) := by
  letI : Finite (RayClassGroup K (1 : Modulus K)) :=
    hbridge.rayClassGroup
  let hdecomp := hbridge.decomposition
  have hres := dedekind_zeta_ray K h29 hdecomp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, dedekindZeta_residue_ne_zero K,
    dedekindZeta_residue_def K⟩
  · exact dedekind_zeta_continuation K h29 hdecomp
  · exact meromorphic_dedekind_continuation K h29
  · exact differentiable_dedekind_punctured K h29
  · exact differentiable_holomorphic_part K h29
  · intro s
    rw [← hres]
    exact dedekind_continuation_expansion K h29 s
  · rw [← hres]
    exact dedekind_continuation_residue K h29

end

end Towers.CField.EProduc
