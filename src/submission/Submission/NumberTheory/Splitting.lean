import Submission.NumberTheory.Ramification


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

namespace SPExist

open UniqueFactorizationMonoid
open scoped NNReal ENNReal IntermediateField nonZeroDivisors

/--
Step 1 in the proof strategy from `SPExist.tex`/`Lemma3ideas.lean`:
choose an algebraic integer whose image generates the whole extension over `ℚ`.

This is the "integral primitive element" input. The eventual proof should start
from `Field.exists_primitive_element ℚ M` and then clear denominators.
-/
theorem primitive_integers_generator
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M] :
    ∃ θ : NumberField.RingOfIntegers M,
      IntermediateField.adjoin ℚ ({(θ : M)} : Set M) = ⊤ := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace M))
  rcases NumberField.InfinitePlace.isReal_or_isComplex w₀ with hw₀ | hw₀
  · let B : ℝ≥0 := ENNReal.toNNReal (NumberField.mixedEmbedding.minkowskiBound M ↑1) +
        (1 : ℝ≥0)
    have hB :
        NumberField.mixedEmbedding.minkowskiBound M ↑1 <
          NumberField.mixedEmbedding.convexBodyLTFactor M * B := by
      calc
        NumberField.mixedEmbedding.minkowskiBound M ↑1 < B := by
          rw [show ((B : ℝ≥0) : ℝ≥0∞) =
              ((ENNReal.toNNReal
                  (NumberField.mixedEmbedding.minkowskiBound M ↑1)) : ℝ≥0∞) + 1 by
                simp [B, ENNReal.coe_add, ENNReal.coe_one]]
          rw [ENNReal.coe_toNNReal (NumberField.mixedEmbedding.minkowskiBound_lt_top M
            (↑1 : (FractionalIdeal (NumberField.RingOfIntegers M)⁰ M)ˣ)).ne]
          simpa using ENNReal.lt_add_right
            (NumberField.mixedEmbedding.minkowskiBound_lt_top M
              (↑1 : (FractionalIdeal (NumberField.RingOfIntegers M)⁰ M)ˣ)).ne one_ne_zero
        _ = 1 * B := by rw [one_mul]
        _ ≤ NumberField.mixedEmbedding.convexBodyLTFactor M * B := by
          gcongr
          exact mod_cast NumberField.mixedEmbedding.one_le_convexBodyLTFactor M
    obtain ⟨θ, hθ, hθbd⟩ :=
      NumberField.mixedEmbedding.exists_primitive_element_lt_of_isReal M hw₀ hB
    have h_alg : (DivisionRing.toRatAlgebra : Algebra ℚ M) = ‹Algebra ℚ M› :=
      Subsingleton.elim _ _
    cases h_alg
    exact ⟨θ, by simpa using hθ⟩
  · let B : ℝ≥0 := ENNReal.toNNReal (NumberField.mixedEmbedding.minkowskiBound M ↑1) +
        (1 : ℝ≥0)
    have hB :
        NumberField.mixedEmbedding.minkowskiBound M ↑1 <
          NumberField.mixedEmbedding.convexBodyLT'Factor M * B := by
      calc
        NumberField.mixedEmbedding.minkowskiBound M ↑1 < B := by
          rw [show ((B : ℝ≥0) : ℝ≥0∞) =
              ((ENNReal.toNNReal
                  (NumberField.mixedEmbedding.minkowskiBound M ↑1)) : ℝ≥0∞) + 1 by
                simp [B, ENNReal.coe_add, ENNReal.coe_one]]
          rw [ENNReal.coe_toNNReal (NumberField.mixedEmbedding.minkowskiBound_lt_top M
            (↑1 : (FractionalIdeal (NumberField.RingOfIntegers M)⁰ M)ˣ)).ne]
          simpa using ENNReal.lt_add_right
            (NumberField.mixedEmbedding.minkowskiBound_lt_top M
              (↑1 : (FractionalIdeal (NumberField.RingOfIntegers M)⁰ M)ˣ)).ne one_ne_zero
        _ = 1 * B := by rw [one_mul]
        _ ≤ NumberField.mixedEmbedding.convexBodyLT'Factor M * B := by
          gcongr
          exact mod_cast NumberField.mixedEmbedding.one_le_convexBodyLT'Factor M
    obtain ⟨θ, hθ, hθbd⟩ :=
      NumberField.mixedEmbedding.exists_primitive_element_lt_of_isComplex M hw₀ hB
    have h_alg : (DivisionRing.toRatAlgebra : Algebra ℚ M) = ‹Algebra ℚ M› :=
      Subsingleton.elim _ _
    cases h_alg
    exact ⟨θ, by simpa using hθ⟩

/--
Step 2 in the proof strategy:
Schur's theorem for values of a nonconstant integer polynomial, already
strengthened to avoid an arbitrary finite bad set.

The intended proof of this helper follows the classical contradiction argument
spelled out in `Lemma3ideas.txt`: assuming only finitely many prime divisors of
values of `f`, choose one nonzero value `A = f a`, form

`G t = f (a + A * P * t) / A`,

and observe that `G t ≡ 1 mod p_i` for every previously listed prime `p_i`,
while for a large `t` the value `G t` has a new prime divisor. After that,
excluding a finite set `bad` and imposing `p > N` is a standard finite-removal
step.
-/
theorem dvd_degree_pos
    (f : Polynomial ℤ) (hf : 0 < f.natDegree) (S : Finset ℕ) :
    ∃ p, Nat.Prime p ∧ p ∉ S ∧ ∃ n : ℤ, (p : ℤ) ∣ f.eval n := by
  classical
  have hnotall : ¬ ∀ z : ℤ, f.eval z = 0 := by
    intro hall
    have hzero : f = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.infinite_univ.mono ?_
      intro z hz
      exact Polynomial.IsRoot.def.mpr (hall z)
    simp [hzero] at hf
  push Not at hnotall
  rcases hnotall with ⟨a, ha⟩
  let A : ℤ := f.eval a
  have hA0 : A ≠ 0 := ha
  let Pn : ℕ := ∏ s ∈ S.erase 0, s
  let P : ℤ := Pn
  have hPn0 : Pn ≠ 0 := by
    dsimp [Pn]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro s hs
    exact (Finset.mem_erase.mp hs).1
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact_mod_cast hPn0
  let c : ℤ := A * P
  have hc0 : c ≠ 0 := mul_ne_zero hA0 hP0
  let F : Polynomial ℤ := f.comp (Polynomial.C c * Polynomial.X + Polynomial.C a)
  have hFdeg : 0 < F.natDegree := by
    dsimp [F]
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_linear hc0, mul_one]
    exact hf
  have hdeg_lt : (Polynomial.C A).degree < F.degree := by
    rw [Polynomial.degree_C hA0]
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hFdeg
  have hsmall : ({x : ℤ | |F.eval x| ≤ |A|} : Set ℤ).Finite := by
    simpa using Polynomial.finite_abs_eval_le_of_degree_lt (P := F) (Q := Polynomial.C A) hdeg_lt
  have hbigset : ({x : ℤ | ¬ |F.eval x| ≤ |A|} : Set ℤ).Infinite := by
    convert (Set.Infinite.diff Set.infinite_univ hsmall) using 1
    ext x
    simp
  have hbigset' : ({x : ℤ | |A| < |F.eval x|} : Set ℤ).Infinite := by
    simpa [not_le] using hbigset
  obtain ⟨t, ht⟩ := hbigset'.nonempty
  have hFbig : |A| < |F.eval t| := ht
  let n : ℤ := c * t + a
  have hF_eval : F.eval t = f.eval n := by
    simp [F, n]
  have hnbig : |A| < |f.eval n| := by
    calc
      |A| < |F.eval t| := hFbig
      _ = |f.eval n| := by rw [hF_eval]
  have hsub : c * t ∣ f.eval n - A := by
    dsimp [n, A]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]
      using (Polynomial.sub_dvd_eval_sub (c * t + a) a f)
  rcases hsub with ⟨k, hk⟩
  let u : ℤ := 1 + P * t * k
  have hk' : f.eval n = A + c * t * k := by
    calc
      f.eval n = (f.eval n - A) + A := by ring
      _ = c * t * k + A := by rw [hk]
      _ = A + c * t * k := by ring
  have hfu : f.eval n = A * u := by
    calc
      f.eval n = A + c * t * k := hk'
      _ = A * u := by
        dsimp [u, c]
        ring
  have hu_abs_gt_one : 1 < |u| := by
    have hmul : |A| < |A| * |u| := by
      simpa [hfu, abs_mul, mul_comm, mul_left_comm, mul_assoc] using hnbig
    by_contra hu
    have hu_le : |u| ≤ 1 := le_of_not_gt hu
    have hmul_le : |A| * |u| ≤ |A| * 1 := by gcongr
    have : |A| * |u| ≤ |A| := by simpa using hmul_le
    linarith
  have hu_natAbs_gt_one : 1 < u.natAbs := by
    rwa [Int.abs_eq_natAbs, Nat.one_lt_cast] at hu_abs_gt_one
  obtain ⟨p, hp, hpu_nat⟩ := Nat.exists_prime_and_dvd (ne_of_gt hu_natAbs_gt_one)
  have hpu : (p : ℤ) ∣ u := Int.natCast_dvd.mpr hpu_nat
  have hp_not_S : p ∉ S := by
    intro hpS
    have hp_mem : p ∈ S.erase 0 := by
      simp [hpS, hp.ne_zero]
    have hpdvdPn : p ∣ Pn := by
      dsimp [Pn]
      exact Finset.dvd_prod_of_mem id hp_mem
    have hpdvdP : (p : ℤ) ∣ P := by
      exact Int.natCast_dvd.mpr hpdvdPn
    have hpdvd_rest : (p : ℤ) ∣ P * t * k := by
      simpa [mul_assoc] using dvd_mul_of_dvd_left hpdvdP (t * k)
    have hpdvd_one : (p : ℤ) ∣ 1 := by
      have : (p : ℤ) ∣ u - P * t * k := dvd_sub hpu hpdvd_rest
      simpa [u, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
        mul_left_comm] using this
    exact hp.not_dvd_one (Int.natCast_dvd.mp hpdvd_one)
  refine ⟨p, hp, hp_not_S, n, ?_⟩
  rw [hfu]
  exact dvd_mul_of_dvd_right hpu A

/--
Schur's theorem with both a finite bad set and a lower bound baked into the
conclusion.
-/
theorem not_dvd_pos
    (f : Polynomial ℤ) (hf : 0 < f.natDegree) (bad : Finset ℕ) :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ p ∉ bad ∧ ∃ n : ℤ, (p : ℤ) ∣ f.eval n := by
  intro N
  let S : Finset ℕ := bad ∪ Finset.range (N + 1)
  rcases dvd_degree_pos f hf S with ⟨p, hp, hpS, n, hdiv⟩
  have hp_not_bad : p ∉ bad := by
    intro hpbad
    exact hpS (by simp [S, hpbad])
  have hp_gt : p > N := by
    have hp_not_range : p ∉ Finset.range (N + 1) := by
      intro hpRange
      exact hpS (by simp [S, hpRange])
    exact lt_of_not_ge (fun hNp => hp_not_range (Finset.mem_range.mpr (Nat.lt_succ_of_le hNp)))
  exact ⟨p, hp_gt, hp, hp_not_bad, n, hdiv⟩

/--
Kummer-Dedekind bridge step:
if `p` does not divide the exponent of the integral primitive element `θ` and
`minpoly ℤ θ` has a root modulo `p`, then there is a prime ideal above `p`
with inertia degree `1`.

This isolates the part of Step 3 that is already directly available in Mathlib:
the bijection between prime ideals over `p` and irreducible factors of the
reduced minpoly, together with the formula identifying inertia degree with the
degree of the corresponding factor.
-/
theorem not_dvd_exponent
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M]
    {θ : NumberField.RingOfIntegers M} {p : ℕ} (hp : Nat.Prime p)
    (hexp : ¬ p ∣ RingOfIntegers.exponent θ)
    {n : ℤ} (hn : (p : ℤ) ∣ (minpoly ℤ θ).eval n) :
    ∃ P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers M),
      Ideal.inertiaDeg (Ideal.rationalPrimeIdeal p) P = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Q : Polynomial (ZMod p) := Polynomial.X - Polynomial.C (n : ZMod p)
  have hQ_mem : Q ∈ RingOfIntegers.monicFactorsMod θ p := by
    rw [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset,
      Polynomial.mem_normalizedFactors_iff]
    · refine ⟨Polynomial.irreducible_X_sub_C (n : ZMod p), Polynomial.monic_X_sub_C _, ?_⟩
      dsimp [Q]
      rw [Polynomial.dvd_iff_isRoot]
      rw [Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_at_intCast]
      rcases hn with ⟨m, hm⟩
      exact by
        simpa [map_mul] using congrArg (Int.castRingHom (ZMod p)) hm
    · exact Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral)
  let P : Ideal (NumberField.RingOfIntegers M) :=
    ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := M) (θ := θ) (p := p) hexp).symm
      ⟨Q, hQ_mem⟩ : Ideal (NumberField.RingOfIntegers M))
  refine ⟨P, ?_, ?_⟩
  · dsimp [P, Ideal.rationalPrimeIdeal]
    exact (((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      (K := M) (θ := θ) (p := p) hexp).symm ⟨Q, hQ_mem⟩).prop)
  · calc
      Ideal.inertiaDeg (Ideal.rationalPrimeIdeal p) P
        = Q.natDegree := by
            simpa [P, Ideal.rationalPrimeIdeal] using
              (NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
                (K := M) (θ := θ) (p := p) hexp hQ_mem)
      _ = 1 := by
        dsimp [Q]
        exact Polynomial.natDegree_X_sub_C (n : ZMod p)

/--
Kummer-Dedekind plus a multiplicity-one hypothesis:
if the linear factor coming from a root mod `p` appears with multiplicity `1`,
then the corresponding prime above `p` has both inertia degree `1` and
ramification index `1`.

This is the exact local statement we will want after a later squarefreeness or
discriminant-avoidance lemma.
-/
theorem not_dvd_multiplicity
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M]
    {θ : NumberField.RingOfIntegers M} {p : ℕ} (hp : Nat.Prime p)
    (hexp : ¬ p ∣ RingOfIntegers.exponent θ)
    {n : ℤ} (hn : (p : ℤ) ∣ (minpoly ℤ θ).eval n)
    (hmult :
      multiplicity (Polynomial.X - Polynomial.C (n : ZMod p))
        ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) = 1) :
    ∃ P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers M),
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal p) P = 1 ∧
        Ideal.inertiaDeg (Ideal.rationalPrimeIdeal p) P = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Q : Polynomial (ZMod p) := Polynomial.X - Polynomial.C (n : ZMod p)
  have hQ_mem : Q ∈ RingOfIntegers.monicFactorsMod θ p := by
    rw [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset,
      Polynomial.mem_normalizedFactors_iff]
    · refine ⟨Polynomial.irreducible_X_sub_C (n : ZMod p), Polynomial.monic_X_sub_C _, ?_⟩
      dsimp [Q]
      rw [Polynomial.dvd_iff_isRoot]
      rw [Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_at_intCast]
      rcases hn with ⟨m, hm⟩
      exact by
        simpa [map_mul] using congrArg (Int.castRingHom (ZMod p)) hm
    · exact Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral)
  let P : Ideal (NumberField.RingOfIntegers M) :=
    ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := M) (θ := θ) (p := p) hexp).symm
      ⟨Q, hQ_mem⟩ : Ideal (NumberField.RingOfIntegers M))
  refine ⟨P, ?_, ?_, ?_⟩
  · dsimp [P, Ideal.rationalPrimeIdeal]
    exact (((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      (K := M) (θ := θ) (p := p) hexp).symm ⟨Q, hQ_mem⟩).prop)
  · simpa [P, Q, Ideal.rationalPrimeIdeal] using
      (NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
        (K := M) (θ := θ) (p := p) hexp hQ_mem).trans hmult
  · calc
      Ideal.inertiaDeg (Ideal.rationalPrimeIdeal p) P
        = Q.natDegree := by
            simpa [P, Ideal.rationalPrimeIdeal] using
              (NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
                (K := M) (θ := θ) (p := p) hexp hQ_mem)
      _ = 1 := by
        dsimp [Q]
        exact Polynomial.natDegree_X_sub_C (n : ZMod p)

/--
For a monic separable polynomial over a field, the discriminant is nonzero.

This is the field-level fact behind the later integer-valued discriminant
avoidance: in characteristic zero, the minimal polynomial of an algebraic
integer is separable after passing to `ℚ`.
-/
theorem discr_monic_separable
    {K : Type*} [Field K] (f : Polynomial K) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) (hsep : f.Separable) :
    f.discr ≠ 0 := by
  have hdeg_pos : 0 < f.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
  have hres_ne_zero : f.resultant f.derivative ≠ 0 := by
    intro hzero
    exact ((Polynomial.resultant_eq_zero_iff).mp hzero).2 hsep
  have hdeg_deriv_le : f.derivative.natDegree ≤ f.natDegree - 1 := by
    simpa using Polynomial.natDegree_derivative_le (p := f)
  have hrel :=
    Polynomial.resultant_add_right_deg
      (f := f) (g := f.derivative) (m := f.natDegree) (n := f.derivative.natDegree)
      (k := (f.natDegree - 1) - f.derivative.natDegree) le_rfl
  have hrel' :
      f.resultant f.derivative f.natDegree (f.natDegree - 1) = f.resultant f.derivative := by
    simpa [Nat.add_sub_of_le hdeg_deriv_le, hf.coeff_natDegree] using hrel
  intro hdiscr
  apply hres_ne_zero
  rw [← hrel', Polynomial.resultant_deriv (f := f) hdeg_pos, hf.leadingCoeff, hdiscr]
  simp

/--
The polynomial discriminant commutes with coefficient maps, at least in the
monic case that arises for minimal polynomials.
-/
theorem discr_monic
    {K : Type*} [Field K] (φ : ℤ →+* K) (f : Polynomial ℤ) (hf : f.Monic) :
    (f.map φ).discr = φ f.discr := by
  by_cases h0 : f.natDegree = 0
  · obtain rfl := Polynomial.eq_one_of_monic_natDegree_zero hf h0
    have hmap : Polynomial.map φ (1 : Polynomial ℤ) = 1 := by
      simp
    have hK : Polynomial.discr (1 : Polynomial K) = 1 := by
      simpa using (Polynomial.discr_C (1 : K))
    have hZ : φ (Polynomial.discr (1 : Polynomial ℤ)) = 1 := by
      simpa using congrArg φ (Polynomial.discr_C (1 : ℤ))
    rw [hmap, hK, hZ]
  let g : Polynomial K := f.map φ
  have hg_monic : g.Monic := hf.map φ
  have hnatdeg_map : g.natDegree = f.natDegree := by
    simpa [g] using hf.natDegree_map φ
  have hdeg_pos : 0 < f.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h0)
  have hgdeg_pos : 0 < g.degree := by
    exact Polynomial.natDegree_pos_iff_degree_pos.mp (hnatdeg_map ▸ Nat.pos_of_ne_zero h0)
  have hres_map :
      g.resultant g.derivative g.natDegree (g.natDegree - 1) =
        φ (f.resultant f.derivative f.natDegree (f.natDegree - 1)) := by
    rw [hnatdeg_map]
    dsimp [g]
    rw [Polynomial.derivative_map]
    exact Polynomial.resultant_map_map
      (f := f) (g := f.derivative) (m := f.natDegree) (n := f.natDegree - 1) (φ := φ)
  have h1 := Polynomial.resultant_deriv (f := g) hgdeg_pos
  rw [hg_monic.leadingCoeff] at h1
  have h2 := congrArg φ (Polynomial.resultant_deriv (f := f) hdeg_pos)
  rw [← hres_map, hf.leadingCoeff, ← hnatdeg_map] at h2
  simp only [map_mul, map_pow, map_neg, map_one] at h2
  have hs : ((-1 : K) ^ (g.natDegree * (g.natDegree - 1) / 2)) ≠ 0 := by
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  exact mul_left_cancel₀ hs (by
    rw [h1] at h2
    simpa [mul_assoc] using h2)

/--
For a monic integer polynomial, nonvanishing of the discriminant modulo `p`
forces the reduction mod `p` to be squarefree.

This is the clean formal bridge from "avoid the finitely many prime divisors of
the discriminant" to "every linear factor occurs with multiplicity `1`".
-/
theorem squarefree_monic_discr
    (f : Polynomial ℤ) (hf : f.Monic) {p : ℕ} (hp : Nat.Prime p)
    (hdisc : ¬ p ∣ Int.natAbs f.discr) :
    Squarefree (f.map (Int.castRingHom (ZMod p))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let g : Polynomial (ZMod p) := f.map φ
  by_cases h0 : f.natDegree = 0
  · obtain rfl := Polynomial.eq_one_of_monic_natDegree_zero hf h0
    simp
  have hg_monic : g.Monic := hf.map φ
  have hg_ne_zero : g ≠ 0 := hg_monic.ne_zero
  have hnatdeg_map : g.natDegree = f.natDegree := by
    simpa [g, φ] using hf.natDegree_map φ
  have hnatdeg_pos : 0 < f.natDegree := Nat.pos_of_ne_zero h0
  have hdeg_pos : 0 < f.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hnatdeg_pos
  have hg_natdeg_pos : 0 < g.natDegree := by
    rw [hnatdeg_map]
    exact hnatdeg_pos
  have hgdeg_pos : 0 < g.degree := by
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hg_natdeg_pos
  have hres_map :
      g.resultant g.derivative g.natDegree (g.natDegree - 1) =
        φ (f.resultant f.derivative f.natDegree (f.natDegree - 1)) := by
    rw [hnatdeg_map]
    dsimp [g, φ]
    rw [Polynomial.derivative_map]
    exact Polynomial.resultant_map_map
      (f := f) (g := f.derivative) (m := f.natDegree) (n := f.natDegree - 1) (φ := φ)
  have hdiscr_map :
      g.discr = φ f.discr := by
    simpa [g, φ] using discr_monic φ f hf
  have hdiscr_ne_zero : φ f.discr ≠ 0 := by
    intro hzero
    have hdiv_int : (p : ℤ) ∣ f.discr := (ZMod.intCast_zmod_eq_zero_iff_dvd f.discr p).mp hzero
    have hdiv_nat : p ∣ Int.natAbs f.discr := by
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.2 hdiv_int)
    exact hdisc hdiv_nat
  have hres_big_ne_zero :
      g.resultant g.derivative g.natDegree (g.natDegree - 1) ≠ 0 := by
    rw [Polynomial.resultant_deriv (f := g) hgdeg_pos, hg_monic.leadingCoeff, hdiscr_map]
    have hs : ((-1 : ZMod p) ^ (g.natDegree * (g.natDegree - 1) / 2)) ≠ 0 := by
      exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    simpa [mul_assoc] using mul_ne_zero hs hdiscr_ne_zero
  have hres_ne_zero : g.resultant g.derivative ≠ 0 := by
    have hdeg_deriv_le : g.derivative.natDegree ≤ g.natDegree - 1 := by
      simpa using Polynomial.natDegree_derivative_le (p := g)
    have hrel :=
      Polynomial.resultant_add_right_deg
        (f := g) (g := g.derivative) (m := g.natDegree) (n := g.derivative.natDegree)
        (k := (g.natDegree - 1) - g.derivative.natDegree) le_rfl
    have hrel' :
        g.resultant g.derivative g.natDegree (g.natDegree - 1) = g.resultant g.derivative := by
      simpa [Nat.add_sub_of_le hdeg_deriv_le, hg_monic.coeff_natDegree] using hrel
    exact hrel' ▸ hres_big_ne_zero
  have hsep : g.Separable := by
    have hcoprime : IsCoprime g g.derivative := by
      apply not_not.mp
      intro hnot
      have hzero : g.resultant g.derivative = 0 := by
        exact (Polynomial.resultant_eq_zero_iff).2 ⟨Or.inl hg_ne_zero, hnot⟩
      exact hres_ne_zero hzero
    exact hcoprime
  exact hsep.squarefree

/--
Outside the primes dividing the exponent and the discriminant, a root of the
reduced minpoly gives a prime above `p` with ramification index `1` and
inertia degree `1`.

This is the finished local Kummer-Dedekind package we want for the eventual
finite bad set.
-/
theorem dvd_exponent_discr
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M]
    {θ : NumberField.RingOfIntegers M} {p : ℕ} (hp : Nat.Prime p)
    (hexp : ¬ p ∣ RingOfIntegers.exponent θ)
    (hdisc : ¬ p ∣ Int.natAbs (minpoly ℤ θ).discr)
    {n : ℤ} (hn : (p : ℤ) ∣ (minpoly ℤ θ).eval n) :
    ∃ P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers M),
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal p) P = 1 ∧
        Ideal.inertiaDeg (Ideal.rationalPrimeIdeal p) P = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Q : Polynomial (ZMod p) := Polynomial.X - Polynomial.C (n : ZMod p)
  have hQ_mem : Q ∈ RingOfIntegers.monicFactorsMod θ p := by
    rw [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset,
      Polynomial.mem_normalizedFactors_iff]
    · refine ⟨Polynomial.irreducible_X_sub_C (n : ZMod p), Polynomial.monic_X_sub_C _, ?_⟩
      dsimp [Q]
      rw [Polynomial.dvd_iff_isRoot]
      rw [Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_at_intCast]
      rcases hn with ⟨m, hm⟩
      exact by
        simpa [map_mul] using congrArg (Int.castRingHom (ZMod p)) hm
    · exact Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have hsq :
      Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
    exact squarefree_monic_discr
      (minpoly ℤ θ) (minpoly.monic θ.isIntegral) hp hdisc
  have hmap_ne_zero : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) ≠ 0 := by
    exact Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have hnodup :
      Multiset.Nodup (normalizedFactors ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))) := by
    exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hmap_ne_zero).mp hsq
  have hQ_mem' : Q ∈ normalizedFactors ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
    simpa [RingOfIntegers.monicFactorsMod] using hQ_mem
  have hmult :
      multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) = 1 := by
    rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
      (Polynomial.irreducible_X_sub_C (n : ZMod p)) hmap_ne_zero,
      (Polynomial.monic_X_sub_C (n : ZMod p)).normalize_eq_self]
    exact Multiset.count_eq_one_of_mem hnodup hQ_mem'
  exact not_dvd_multiplicity
    M hp hexp hn hmult

/--
The integer discriminant of `minpoly ℤ θ` is nonzero.

This is the arithmetic input needed to package the discriminant exceptions into
a finite set of prime divisors.
-/
theorem abs_discr_minpoly
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M]
    {θ : NumberField.RingOfIntegers M} :
    Int.natAbs (minpoly ℤ θ).discr ≠ 0 := by
  have hθ_intQ : IsIntegral ℚ (θ : M) := Algebra.IsIntegral.isIntegral (R := ℚ) (θ : M)
  have hminpoly_coe : minpoly ℤ (θ : M) = minpoly ℤ θ :=
    NumberField.RingOfIntegers.minpoly_coe θ
  let g : Polynomial ℚ := (minpoly ℤ (θ : M)).map (Int.castRingHom ℚ)
  have hg_eq : g = minpoly ℚ (θ : M) := by
    simpa [g] using
      (minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) θ.isIntegral_coe).symm
  have hgdeg_pos : 0 < g.natDegree := by
    rw [hg_eq]
    simpa using minpoly.natDegree_pos hθ_intQ
  have hg_sep : g.Separable := by
    rw [hg_eq]
    exact (minpoly.irreducible hθ_intQ).separable
  have hg_monic : g.Monic := by
    rw [hg_eq]
    exact minpoly.monic hθ_intQ
  have hg_discr_ne_zero : g.discr ≠ 0 := by
    apply discr_monic_separable
      g hg_monic hgdeg_pos hg_sep
  intro hzero
  apply hg_discr_ne_zero
  rw [discr_monic
      (Int.castRingHom ℚ) (minpoly ℤ (θ : M))
      (minpoly.monic θ.isIntegral_coe),
    hminpoly_coe,
    Int.natAbs_eq_zero.mp hzero, map_zero]

/--
If `θ` is a primitive integral generator of `M/ℚ`, then its Kummer-Dedekind
exponent is nonzero.

The proof follows the standard discriminant trick available in Mathlib:
the discriminant of the `ℚ`-power basis generated by `θ` is a nonzero integer,
and `discr * z` lies in `ℤ[θ]` for every algebraic integer `z`, so that
discriminant belongs to the conductor and hence gives a positive witness for the
`sInf` defining `RingOfIntegers.exponent θ`.
-/
theorem exponent_ne_primitive
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M]
    {θ : NumberField.RingOfIntegers M}
    (hθ_prim : IntermediateField.adjoin ℚ ({(θ : M)} : Set M) = ⊤) :
    RingOfIntegers.exponent θ ≠ 0 := by
  classical
  have hθ_intQ : IsIntegral ℚ (θ : M) := Algebra.IsIntegral.isIntegral (R := ℚ) (θ : M)
  have hθ_algQ : IsAlgebraic ℚ (θ : M) := hθ_intQ.isAlgebraic
  have hθ_prim' : Algebra.adjoin ℚ ({(θ : M)} : Set M) = ⊤ := by
    apply Algebra.adjoin_eq_top_of_intermediateField (S := ({(θ : M)} : Set M))
    · intro x hx
      simpa [Set.mem_singleton_iff.mp hx] using hθ_algQ
    · exact hθ_prim
  let B : PowerBasis ℚ M :=
    PowerBasis.ofAdjoinEqTop hθ_intQ hθ_prim'
  have hBint : IsIntegral ℤ B.gen := by
    simpa [B] using θ.isIntegral_coe
  have hdiscr_int : IsIntegral ℤ (Algebra.discr ℚ B.basis) := by
    apply Algebra.discr_isIntegral (K := ℚ) (R := ℤ) (b := B.basis)
    intro i
    simpa [B.basis_eq_pow i] using hBint.pow (i : ℕ)
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdiscr_int
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    apply Algebra.discr_not_zero_of_basis (K := ℚ) B.basis
    rw [← hr, hr0, map_zero]
  have hmem_coe :
      (algebraMap ℤ M r) ∈ IsLocalization.coeSubmodule (S := M) (conductor ℤ θ) := by
    rw [mem_coeSubmodule_conductor]
    intro z
    have hrM : (algebraMap ℤ M r) = algebraMap ℚ M (Algebra.discr ℚ B.basis) := by
      simpa [IsScalarTower.algebraMap_apply] using congrArg (algebraMap ℚ M) hr
    rw [hrM]
    simpa [B, Algebra.smul_def] using
      (Algebra.discr_mul_isIntegral_mem_adjoin (K := ℚ) (R := ℤ) (L := M)
        (B := B) hBint (z := (z : M)) z.isIntegral_coe)
  obtain ⟨c, hc, hc_eq⟩ :=
    (IsLocalization.mem_coeSubmodule (S := M) (I := conductor ℤ θ)).mp hmem_coe
  have hcast_mem : (algebraMap ℤ (NumberField.RingOfIntegers M) r) ∈ conductor ℤ θ := by
    have hc_cast : c = algebraMap ℤ (NumberField.RingOfIntegers M) r := by
      exact NumberField.RingOfIntegers.coe_injective (K := M) (by
        simpa [IsScalarTower.algebraMap_apply] using hc_eq)
    simpa [hc_cast] using hc
  have hnatAbs_mem :
      ((Int.natAbs r : ℕ) : NumberField.RingOfIntegers M) ∈ conductor ℤ θ := by
    cases r with
    | ofNat n =>
        simpa using hcast_mem
    | negSucc n =>
        simpa using (show
          -(algebraMap ℤ (NumberField.RingOfIntegers M) (Int.negSucc n)) ∈ conductor ℤ θ from
            neg_mem hcast_mem)
  have hs_nonempty :
      Set.Nonempty
        {d : ℕ | 0 < d ∧ (d : NumberField.RingOfIntegers M) ∈ conductor ℤ θ} := by
    refine ⟨Int.natAbs r, ?_⟩
    exact ⟨Int.natAbs_pos.mpr hr_ne_zero, hnatAbs_mem⟩
  rw [RingOfIntegers.exponent_eq_sInf]
  exact (Nat.sInf_mem hs_nonempty).1.ne'

/--
Step 3 from `Lemma3ideas.lean`, packaged in a Mathlib-friendly way.

For an integral primitive element `θ`, there is a finite bad set of rational
primes containing the user-specified exclusion set `T` such that outside this
bad set, every prime divisor of a value of `minpoly ℤ θ` produces a prime ideal
above `p` with ramification index `1` and inertia degree `1`.

The eventual proof should combine the Kummer-Dedekind API in
`Mathlib/NumberTheory/NumberField/Ideal/KummerDedekind.lean` with the finite
list of primes dividing the relevant exponent/discriminant data.

Concretely, the plan is:

1. enlarge `T` by the primes dividing `RingOfIntegers.exponent θ`,
2. enlarge again by the primes for which `(minpoly ℤ (θ : M)) mod p` is not
   squarefree, for example by using the discriminant of the minpoly,
3. if `p ∉ bad` and `p ∣ (minpoly ℤ (θ : M)).eval n`, then `X - C (n mod p)` is
   a linear factor of the reduction modulo `p`,
4. Kummer-Dedekind then gives a prime `P` above `p` whose inertia degree is the
   degree of that factor, hence `1`,
5. the squarefree/discriminant avoidance forces the multiplicity of that factor
   to be `1`, so the corresponding ramification index is also `1`.
-/
theorem bad_primitive_element
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M]
    (T : Finset ℕ) {θ : NumberField.RingOfIntegers M}
    (hθ_prim : IntermediateField.adjoin ℚ ({(θ : M)} : Set M) = ⊤) :
    ∃ bad : Finset ℕ,
      T ⊆ bad ∧
      ∀ {p : ℕ}, Nat.Prime p → p ∉ bad →
        ∀ {n : ℤ}, (p : ℤ) ∣ (minpoly ℤ θ).eval n →
          ∃ P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers M),
            Ideal.ramificationIdx (Ideal.rationalPrimeIdeal p) P = 1 ∧
            Ideal.inertiaDeg (Ideal.rationalPrimeIdeal p) P = 1 := by
  classical
  let expFactors : Finset ℕ := (RingOfIntegers.exponent θ).primeFactors
  let discrFactors : Finset ℕ := (Int.natAbs (minpoly ℤ θ).discr).primeFactors
  let bad : Finset ℕ := T ∪ expFactors ∪ discrFactors
  refine ⟨bad, ?_, ?_⟩
  · intro p hpT
    simp [bad, hpT]
  · intro p hp hpbad n hdiv
    have hexp0 : RingOfIntegers.exponent θ ≠ 0 :=
      exponent_ne_primitive M hθ_prim
    have hdiscr0 : Int.natAbs (minpoly ℤ θ).discr ≠ 0 :=
      abs_discr_minpoly M
    have hp_not_expFactors : p ∉ expFactors := by
      intro hp_exp
      exact hpbad (by simp [bad, expFactors, discrFactors, hp_exp])
    have hp_not_discrFactors : p ∉ discrFactors := by
      intro hp_discr
      exact hpbad (by simp [bad, expFactors, discrFactors, hp_discr])
    have hexp : ¬ p ∣ RingOfIntegers.exponent θ := by
      intro hp_dvd
      apply hp_not_expFactors
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hp_dvd, hexp0⟩
    have hdiscr : ¬ p ∣ Int.natAbs (minpoly ℤ θ).discr := by
      intro hp_dvd
      apply hp_not_discrFactors
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hp_dvd, hdiscr0⟩
    exact dvd_exponent_discr
      M hp hexp hdiscr hdiv

/--
Step 4 from `Lemma3ideas.lean`:
in a finite Galois extension, one prime above `p` with `e = 1` and `f = 1`
forces complete splitting, because all primes above `p` have the same
ramification and inertia data and the Galois fundamental identity gives the
correct number of primes above `p`.
-/
theorem splits_completely_galois
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M] [IsGalois ℚ M]
    {p : ℕ} (hp : Nat.Prime p)
    (hP :
      ∃ P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers M),
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal p) P = 1 ∧
        Ideal.inertiaDeg (Ideal.rationalPrimeIdeal p) P = 1) :
    splitsCompletely M p := by
  classical
  have h_alg : (DivisionRing.toRatAlgebra : Algebra ℚ M) = ‹Algebra ℚ M› :=
    Subsingleton.elim _ _
  cases h_alg
  rcases hP with ⟨P, hP, hPe, hPf⟩
  have hp0 : Ideal.rationalPrimeIdeal p ≠ ⊥ := rational_ne_bot hp
  haveI : (Ideal.rationalPrimeIdeal p).IsMaximal := rational_ideal_maximal hp
  haveI : P.IsPrime := Ideal.isPrime_of_prime <| Ideal.prime_of_mem_primesOver hp0 hP
  haveI : P.LiesOver (Ideal.rationalPrimeIdeal p) := hP.2
  have hramIn :
      Ideal.ramificationIdxIn (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers M) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p := Ideal.rationalPrimeIdeal p)
      (P := P) (B := NumberField.RingOfIntegers M) (G := Gal(M/ℚ))]
    exact hPe
  have hinIn :
      Ideal.inertiaDegIn (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers M) = 1 := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg (p := Ideal.rationalPrimeIdeal p)
      (P := P) (B := NumberField.RingOfIntegers M) (G := Gal(M/ℚ))]
    exact hPf
  have hcard :
      (Ideal.primesOver (Ideal.rationalPrimeIdeal p) (NumberField.RingOfIntegers M)).ncard =
        Module.finrank ℚ M := by
    have hmain :=
      Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
        (p := Ideal.rationalPrimeIdeal p) (B := NumberField.RingOfIntegers M) (G := Gal(M/ℚ)) hp0
    rw [hramIn, hinIn, one_mul, mul_one, IsGalois.card_aut_eq_finrank] at hmain
    exact hmain
  refine ⟨hcard, ?_⟩
  intro Q hQ
  haveI : Q.IsPrime := Ideal.isPrime_of_prime <| Ideal.prime_of_mem_primesOver hp0 hQ
  haveI : Q.LiesOver (Ideal.rationalPrimeIdeal p) := hQ.2
  have hramQ :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal p) Q = 1 := by
    rw [← hramIn, Ideal.ramificationIdxIn_eq_ramificationIdx (p := Ideal.rationalPrimeIdeal p)
      (P := Q) (B := NumberField.RingOfIntegers M) (G := Gal(M/ℚ))]
  have hinQ : Ideal.inertiaDeg (Ideal.rationalPrimeIdeal p) Q = 1 := by
    rw [← hinIn, Ideal.inertiaDegIn_eq_inertiaDeg (p := Ideal.rationalPrimeIdeal p)
      (P := Q) (B := NumberField.RingOfIntegers M) (G := Gal(M/ℚ))]
  exact ⟨hramQ, hinQ⟩

/--
Phase 1.5 of the autoformalization of Standard Lemma 3 from `SPExist.tex`.

This is still the same theorem statement as before, but the proof is now
organized explicitly around the four helper steps from `Lemma3ideas.lean`.
That gives a realistic roadmap for the next proof pass:

1. choose an integral primitive element `θ`,
2. apply Schur to `minpoly ℤ θ`,
3. use a finite bad set plus Kummer-Dedekind to produce one prime over `p`
   with `e = 1` and `f = 1`,
4. upgrade to complete splitting by the Galois ramification/inertia API.
-/
theorem not_splits_completely
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M] [IsGalois ℚ M]
    (T : Finset ℕ) :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ p ∉ T ∧ splitsCompletely M p := by
  intro N
  obtain ⟨θ, hθ_prim⟩ := primitive_integers_generator M
  let f : Polynomial ℤ := minpoly ℤ θ
  have hf : 0 < f.natDegree := by
    simpa [f] using minpoly.natDegree_pos θ.isIntegral
  obtain ⟨bad, hTbad, hbad_spec⟩ :=
    bad_primitive_element M T hθ_prim
  obtain ⟨p, hpN, hpprime, hpbad, n, hdiv⟩ :=
    not_dvd_pos f hf bad N
  have hp_not_mem_T : p ∉ T := by
    intro hpT
    exact hpbad (hTbad hpT)
  have hp_split : splitsCompletely M p := by
    apply splits_completely_galois M hpprime
    exact hbad_spec hpprime hpbad hdiv
  exact ⟨p, hpN, hpprime, hp_not_mem_T, hp_split⟩

theorem prime_splits_completely
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M] [IsGalois ℚ M] :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ splitsCompletely M p := by
  intro N
  obtain ⟨p, hpN, hpprime, _hp_not_mem, hp_split⟩ :=
    not_splits_completely M (∅ : Finset ℕ) N
  exact ⟨p, hpN, hpprime, hp_split⟩

end SPExist

-- Lemma 4

theorem splits_completely_conditions
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    {q : ℕ} (hq : Nat.Prime q)
    (Q : Ideal (NumberField.RingOfIntegers K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.rationalPrimeIdeal q)]
    (heQ : Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) Q = 1)
    (hfQ : Ideal.inertiaDeg (Ideal.rationalPrimeIdeal q) Q = 1) :
    splitsCompletely K q := by
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ K (NumberField.RingOfIntegers K)
  letI : IsGaloisGroup Gal(K/ℚ) ℤ (NumberField.RingOfIntegers K) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(K/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers K) (K := ℚ) (L := K)
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  have hramifIn : qI.ramificationIdxIn (NumberField.RingOfIntegers K) = 1 := by
    calc
      qI.ramificationIdxIn (NumberField.RingOfIntegers K)
        = Ideal.ramificationIdx qI Q := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx (p := qI) (P := Q) (G := Gal(K/ℚ))
      _ = 1 := heQ
  have hinertiaIn : qI.inertiaDegIn (NumberField.RingOfIntegers K) = 1 := by
    calc
      qI.inertiaDegIn (NumberField.RingOfIntegers K)
        = Ideal.inertiaDeg qI Q := by
            exact Ideal.inertiaDegIn_eq_inertiaDeg (p := qI) (P := Q) (G := Gal(K/ℚ))
      _ = 1 := hfQ
  refine ⟨?_, ?_⟩
  · have hcount := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := qI) hqI0 (NumberField.RingOfIntegers K) (Gal(K/ℚ))
    have hcardG : Nat.card Gal(K/ℚ) = Module.finrank ℚ K := by
      simpa using IsGaloisGroup.card_eq_finrank (G := Gal(K/ℚ)) (K := ℚ) (L := K)
    rw [hcardG, hramifIn, hinertiaIn] at hcount
    simpa [qI] using hcount
  · intro P hP
    letI : P.IsPrime := hP.1
    letI : P.LiesOver qI := hP.2
    constructor
    · calc
        Ideal.ramificationIdx qI P
          = Ideal.ramificationIdx qI Q := by
              exact Ideal.ramificationIdx_eq_of_isGaloisGroup
                (p := qI) (P := P) (Q := Q) (G := Gal(K/ℚ))
        _ = 1 := heQ
    · calc
        Ideal.inertiaDeg qI P = Ideal.inertiaDeg qI Q := by
          exact Ideal.inertiaDeg_eq_of_isGaloisGroup
            (p := qI) (P := P) (Q := Q) (G := Gal(K/ℚ))
        _ = 1 := hfQ

theorem deg_arith_frob
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    {q : ℕ} (hq : Nat.Prime q)
    (Q : Ideal (NumberField.RingOfIntegers K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(K/ℚ)) (hσ : IsArithFrobAt ℤ σ Q) (hσ1 : σ = 1) :
    Ideal.inertiaDeg (Ideal.rationalPrimeIdeal q) Q = 1 := by
  let p : Ideal ℤ := Q.under ℤ
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (rational_ne_bot hq) Q
  have hp0 : p ≠ ⊥ := by
    exact mt Ideal.eq_bot_of_comap_eq_bot hQ0
  have hpprime : p.IsPrime := inferInstance
  letI : p.IsMaximal := hpprime.isMaximal hp0
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  haveI : Finite (ℤ ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hp0
  letI : Fintype (ℤ ⧸ p) := Fintype.ofFinite (ℤ ⧸ p)
  letI : Q.IsMaximal := Ideal.IsPrime.isMaximal (show Q.IsPrime from inferInstance) hQ0
  letI : Field (NumberField.RingOfIntegers K ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (NumberField.RingOfIntegers K ⧸ Q) :=
    Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  have hrestrict_id : hσ.restrict = 1 := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [AlgHom.IsArithFrobAt.restrict_mk, hσ1]
  have hrestrict_frob :
      hσ.restrict =
        FiniteField.frobeniusAlgHom (ℤ ⧸ p) (NumberField.RingOfIntegers K ⧸ Q) := by
    ext x
    simp [p, AlgHom.IsArithFrobAt.restrict_apply, Nat.card_eq_fintype_card]
  have hfinrank : Module.finrank (ℤ ⧸ p) (NumberField.RingOfIntegers K ⧸ Q) = 1 := by
    have horder :
        orderOf
          (FiniteField.frobeniusAlgHom
            (ℤ ⧸ p) (NumberField.RingOfIntegers K ⧸ Q)) = 1 := by
      rw [← hrestrict_frob, hrestrict_id]
      exact orderOf_one
    rw [FiniteField.orderOf_frobeniusAlgHom] at horder
    exact horder
  have hp_eq : Ideal.rationalPrimeIdeal q = p := by
    exact Ideal.LiesOver.over (P := Q) (p := Ideal.rationalPrimeIdeal q)
  letI : Q.LiesOver p := ⟨by simp [p]⟩
  calc
    Ideal.inertiaDeg (Ideal.rationalPrimeIdeal q) Q
      = Ideal.inertiaDeg p Q := by
          simp [hp_eq]
    _ = Module.finrank (ℤ ⧸ p) (NumberField.RingOfIntegers K ⧸ Q) := by
          exact Ideal.inertiaDeg_algebraMap (p := p) (P := Q)
    _ = 1 := hfinrank

theorem arith_frob_deg
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    {q : ℕ} (hq : Nat.Prime q)
    (Q : Ideal (NumberField.RingOfIntegers K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(K/ℚ)) (hσ : IsArithFrobAt ℤ σ Q)
    (hfQ : Ideal.inertiaDeg (Ideal.rationalPrimeIdeal q) Q = 1) :
    IsArithFrobAt ℤ (1 : Gal(K/ℚ)) Q := by
  let p : Ideal ℤ := Q.under ℤ
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (rational_ne_bot hq) Q
  have hp0 : p ≠ ⊥ := by
    exact mt Ideal.eq_bot_of_comap_eq_bot hQ0
  have hpprime : p.IsPrime := inferInstance
  letI : p.IsMaximal := hpprime.isMaximal hp0
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  haveI : Finite (ℤ ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hp0
  letI : Fintype (ℤ ⧸ p) := Fintype.ofFinite (ℤ ⧸ p)
  letI : Q.IsMaximal := Ideal.IsPrime.isMaximal (show Q.IsPrime from inferInstance) hQ0
  letI : Field (NumberField.RingOfIntegers K ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (NumberField.RingOfIntegers K ⧸ Q) :=
    Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  have hp_eq : Ideal.rationalPrimeIdeal q = p := by
    exact Ideal.LiesOver.over (P := Q) (p := Ideal.rationalPrimeIdeal q)
  have hfinrank : Module.finrank (ℤ ⧸ p) (NumberField.RingOfIntegers K ⧸ Q) = 1 := by
    simpa [p, hp_eq] using hfQ
  have hfrob_id :
      FiniteField.frobeniusAlgHom (ℤ ⧸ p) (NumberField.RingOfIntegers K ⧸ Q) = 1 := by
    apply (orderOf_eq_one_iff).mp
    rw [FiniteField.orderOf_frobeniusAlgHom, hfinrank]
  have hrestrict_frob :
      hσ.restrict =
        FiniteField.frobeniusAlgHom (ℤ ⧸ p) (NumberField.RingOfIntegers K ⧸ Q) := by
    ext x
    simp [p, AlgHom.IsArithFrobAt.restrict_apply, Nat.card_eq_fintype_card]
  have hrestrict_id : hσ.restrict = 1 := by
    rw [hrestrict_frob, hfrob_id]
  intro x
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
  change
    Ideal.Quotient.mk Q (((1 : Gal(K/ℚ)) • x)) -
        (Ideal.Quotient.mk Q x) ^ Nat.card (ℤ ⧸ Ideal.under ℤ Q) = 0
  apply sub_eq_zero.mpr
  calc
    Ideal.Quotient.mk Q (((1 : Gal(K/ℚ)) • x)) = Ideal.Quotient.mk Q x := by
      simp
    _ = hσ.restrict (Ideal.Quotient.mk Q x) := by
        simp [hrestrict_id]
    _ = (Ideal.Quotient.mk Q x) ^ Nat.card (ℤ ⧸ Ideal.under ℤ Q) := by
        exact hσ.restrict_apply (Ideal.Quotient.mk Q x)

lemma hom_gal_restrict
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (σ : Gal(K/ℚ)) (x : NumberField.RingOfIntegers K) :
    MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers K) σ x =
      galRestrict ℤ ℚ K (NumberField.RingOfIntegers K) σ x := by
  apply Subtype.ext
  exact (algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := K)
    (B := NumberField.RingOfIntegers K) σ x).symm

/--
The profinite Galois-theoretic core of Lemma 4: an automorphism in `Gal(L/ℚ)`
is trivial if and only if all of its restrictions to finite Galois intermediate
fields are trivial.
-/
theorem gal_restrict_all
    (L : Type*) [Field L] [Algebra ℚ L] [IsGalois ℚ L]
    (σ : Gal(L/ℚ)) :
    σ = 1 ↔
      ∀ E : FiniteGaloisIntermediateField ℚ L, σ ∈ E.fixingSubgroup := by
  constructor
  · intro h E
    simp [h]
  · intro h
    ext x
    let E : FiniteGaloisIntermediateField ℚ L :=
      FiniteGaloisIntermediateField.adjoin ℚ ({x} : Set L)
    have hx : x ∈ E.toIntermediateField := by
      exact (FiniteGaloisIntermediateField.subset_adjoin (k := ℚ) ({x} : Set L)) (by simp)
    exact (IntermediateField.mem_fixingSubgroup_iff (K := E.toIntermediateField) σ).mp (h E) x hx

/--
Lemma 4 from `Lemma4.tex`: in a finite Galois extension of `ℚ`, an unramified
rational prime `q` splits completely if and only if any chosen arithmetic
Frobenius at a prime `Q` above `q` is the identity.
-/
theorem completely_arith_frob
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    {q : ℕ} (hq : Nat.Prime q)
    (Q : Ideal (NumberField.RingOfIntegers K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.rationalPrimeIdeal q)] [Algebra.IsUnramifiedAt ℤ Q]
    (σ : Gal(K/ℚ)) (hσ : IsArithFrobAt ℤ σ Q) :
    splitsCompletely K q ↔ σ = 1 := by
  constructor
  · intro hsplit
    have hQmem :
        Q ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) (NumberField.RingOfIntegers K) :=
      ⟨inferInstance, inferInstance⟩
    have hfQ : Ideal.inertiaDeg (Ideal.rationalPrimeIdeal q) Q = 1 := (hsplit.2 Q hQmem).2
    have h1frob : IsArithFrobAt ℤ (1 : Gal(K/ℚ)) Q :=
      arith_frob_deg K hq Q σ hσ hfQ
    have hEq :
        MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers K) σ =
          MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers K) (1 : Gal(K/ℚ)) :=
      hσ.eq_of_isUnramifiedAt h1frob Q.primeCompl_le_nonZeroDivisors
    have hRestrict :
        galRestrict ℤ ℚ K (NumberField.RingOfIntegers K) σ =
          galRestrict ℤ ℚ K (NumberField.RingOfIntegers K) (1 : Gal(K/ℚ)) := by
      ext x
      exact congrArg Subtype.val <|
        calc
          galRestrict ℤ ℚ K (NumberField.RingOfIntegers K) σ x
            = MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers K) σ x := by
                symm
                exact hom_gal_restrict K σ x
          _ = MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers K) (1 : Gal(K/ℚ)) x :=
                DFunLike.congr_fun hEq x
          _ = galRestrict ℤ ℚ K (NumberField.RingOfIntegers K) (1 : Gal(K/ℚ)) x := by
                exact hom_gal_restrict K (1 : Gal(K/ℚ)) x
    exact (galRestrict ℤ ℚ K (NumberField.RingOfIntegers K)).injective hRestrict
  · intro hσ1
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (rational_ne_bot hq) Q
    refine splits_completely_conditions K hq Q ?_ ?_
    · simpa [Ideal.LiesOver.over (P := Q) (p := Ideal.rationalPrimeIdeal q)] using
        (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ) (p := Q) hQ0)
    · exact deg_arith_frob K hq Q σ hσ hσ1

/-- If a rational prime splits completely in a finite Galois extension `M/ℚ`,
then it also splits completely in any finite Galois intermediate field. -/
theorem splits_completely_intermediate
    {M : Type*} [Field M] [NumberField M] [Algebra ℚ M] [IsGalois ℚ M]
    (E : IntermediateField ℚ M) [FiniteDimensional ℚ ↥E] [IsGalois ℚ ↥E]
    {q : ℕ} (hq : Nat.Prime q) (hM : splitsCompletely M q) :
    splitsCompletely ↥E q := by
  letI : IsScalarTower ℤ ℚ ↥E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    simp
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ ↥E (𝓞 ↥E)
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ M (𝓞 M)
  letI := IsIntegralClosure.MulSemiringAction (𝓞 ↥E) ↥E M (𝓞 M)
  letI : IsGaloisGroup Gal(↥E/ℚ) ℚ ↥E := inferInstance
  letI : IsGaloisGroup Gal(M/ℚ) ℚ M := inferInstance
  letI : IsGaloisGroup Gal(M / ↥E) ↥E M := inferInstance
  letI : IsGaloisGroup Gal(↥E/ℚ) ℤ (𝓞 ↥E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(↥E/ℚ)) (A := ℤ)
      (B := 𝓞 ↥E) (K := ℚ) (L := ↥E)
  letI : IsGaloisGroup Gal(M/ℚ) ℤ (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(M/ℚ)) (A := ℤ)
      (B := 𝓞 M) (K := ℚ) (L := M)
  letI : IsGaloisGroup Gal(M / ↥E) (𝓞 ↥E) (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(M / ↥E)) (A := 𝓞 ↥E)
      (B := 𝓞 M) (K := ↥E) (L := M)
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsPrime := rational_prime_ideal hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  obtain ⟨⟨P, hPprime, hPover⟩⟩ := qI.nonempty_primesOver (S := 𝓞 ↥E)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver qI := hPover
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := P)
  obtain ⟨⟨Q, hQprime, hQoverP⟩⟩ := P.nonempty_primesOver (S := 𝓞 M)
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver P := hQoverP
  have hQ :
      Q ∈ Ideal.primesOver qI (𝓞 M) := by
    exact ⟨hQprime, Ideal.LiesOver.trans Q P qI⟩
  letI : Q.LiesOver qI := hQ.2
  have hramMIn : qI.ramificationIdxIn (𝓞 M) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 M)
        = Ideal.ramificationIdx qI Q := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := Q) (G := Gal(M/ℚ))
      _ = 1 := (hM.2 Q hQ).1
  have hinMIn : qI.inertiaDegIn (𝓞 M) = 1 := by
    calc
      qI.inertiaDegIn (𝓞 M)
        = Ideal.inertiaDeg qI Q := by
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              (p := qI) (P := Q) (G := Gal(M/ℚ))
      _ = 1 := (hM.2 Q hQ).2
  have hramEIn : qI.ramificationIdxIn (𝓞 ↥E) = 1 := by
    have hmul :=
      Ideal.ramificationIdxIn_mul_ramificationIdxIn'
        (p := qI) P (Gal(↥E/ℚ)) (𝓞 M) (Gal(M/ℚ)) (Gal(M/↥E))
    have hmul1 : qI.ramificationIdxIn (𝓞 ↥E) * P.ramificationIdxIn (𝓞 M) = 1 := by
      rwa [hramMIn] at hmul
    exact Nat.eq_one_of_mul_eq_one_right hmul1
  have hinEIn : qI.inertiaDegIn (𝓞 ↥E) = 1 := by
    have hmul :=
      Ideal.inertiaDegIn_mul_inertiaDegIn
        (p := qI) P (Gal(↥E/ℚ)) (𝓞 M) (Gal(M/ℚ)) (Gal(M/↥E))
    have hmul1 : qI.inertiaDegIn (𝓞 ↥E) * P.inertiaDegIn (𝓞 M) = 1 := by
      rwa [hinMIn] at hmul
    exact Nat.eq_one_of_mul_eq_one_right hmul1
  have hPe :
      Ideal.ramificationIdx qI P = 1 := by
    calc
      Ideal.ramificationIdx qI P
        = qI.ramificationIdxIn (𝓞 ↥E) := by
            symm
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := P) (G := Gal(↥E/ℚ))
      _ = 1 := hramEIn
  have hPf :
      Ideal.inertiaDeg qI P = 1 := by
    calc
      Ideal.inertiaDeg qI P = qI.inertiaDegIn (𝓞 ↥E) := by
        symm
        exact Ideal.inertiaDegIn_eq_inertiaDeg
          (p := qI) (P := P) (G := Gal(↥E/ℚ))
      _ = 1 := hinEIn
  exact splits_completely_conditions ↥E hq P hPe hPf

/-- Complete splitting is preserved by `ℚ`-algebra equivalence between finite Galois
extensions. -/
theorem splits_completely_alg
    {K L : Type*} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]
    [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    (e : K ≃ₐ[ℚ] L) {q : ℕ} (hq : Nat.Prime q)
    (hK : splitsCompletely K q) :
    splitsCompletely L q := by
  have h_algK : (DivisionRing.toRatAlgebra : Algebra ℚ K) = ‹Algebra ℚ K› :=
    Subsingleton.elim _ _
  have h_algL : (DivisionRing.toRatAlgebra : Algebra ℚ L) = ‹Algebra ℚ L› :=
    Subsingleton.elim _ _
  cases h_algK
  cases h_algL
  let e0 : 𝓞 K ≃ₐ[ℤ] 𝓞 L := (e.restrictScalars ℤ).mapIntegralClosure
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsPrime := rational_prime_ideal hq
  obtain ⟨⟨P, hPprime, hPover⟩⟩ := qI.nonempty_primesOver (S := 𝓞 K)
  let Q : Ideal (𝓞 L) := Ideal.map e0 P
  letI : P.IsPrime := hPprime
  letI : P.LiesOver qI := hPover
  have hQ :
      Q ∈ Ideal.primesOver qI (𝓞 L) := by
    exact ⟨inferInstance, inferInstance⟩
  letI : Q.IsPrime := Ideal.isPrime_of_prime <| Ideal.prime_of_mem_primesOver hqI0 hQ
  letI : Q.LiesOver qI := hQ.2
  have hPe :
      Ideal.ramificationIdx qI P = 1 := (hK.2 P ⟨hPprime, hPover⟩).1
  have hPf :
      Ideal.inertiaDeg qI P = 1 := (hK.2 P ⟨hPprime, hPover⟩).2
  have hQe :
      Ideal.ramificationIdx qI Q = 1 := by
    calc
      Ideal.ramificationIdx qI Q
        = Ideal.ramificationIdx qI P := by
            simpa [Q] using (Ideal.ramificationIdx_map_eq (p := qI) (P := P) e0)
      _ = 1 := hPe
  have hQf :
      Ideal.inertiaDeg qI Q = 1 := by
    calc
      Ideal.inertiaDeg qI Q = Ideal.inertiaDeg qI P := by
        simpa [Q] using (Ideal.inertiaDeg_map_eq (p := qI) (P := P) e0)
      _ = 1 := hPf
  exact splits_completely_conditions (K := L) hq Q hQe hQf

/-- Complete splitting descends along a `ℚ`-algebra embedding into a finite Galois
extension by passing to the field range. -/
theorem splits_completely_hom
    {K M : Type*} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]
    [Field M] [NumberField M] [Algebra ℚ M] [IsGalois ℚ M]
    (f : K →ₐ[ℚ] M) {q : ℕ} (hq : Nat.Prime q)
    (hM : splitsCompletely M q) :
    splitsCompletely K q := by
  have h_algK : (DivisionRing.toRatAlgebra : Algebra ℚ K) = ‹Algebra ℚ K› :=
    Subsingleton.elim _ _
  have h_algM : (DivisionRing.toRatAlgebra : Algebra ℚ M) = ‹Algebra ℚ M› :=
    Subsingleton.elim _ _
  cases h_algK
  cases h_algM
  have e : K ≃ₐ[ℚ] ↥(f.fieldRange) := by
    simpa [AlgHom.fieldRange_toSubalgebra f] using (AlgEquiv.ofInjectiveField f)
  letI : FiniteDimensional ℚ ↥(f.fieldRange) :=
    FiniteDimensional.of_surjective e.toLinearEquiv.toLinearMap e.surjective
  letI : NumberField ↥(f.fieldRange) := NumberField.of_module_finite ℚ ↥(f.fieldRange)
  letI : IsGalois ℚ ↥(f.fieldRange) := IsGalois.of_algEquiv e
  have hE : splitsCompletely ↥(f.fieldRange) q :=
    splits_completely_intermediate f.fieldRange hq hM
  exact splits_completely_alg e.symm hq hE

-- Lemma 5

end Submission
