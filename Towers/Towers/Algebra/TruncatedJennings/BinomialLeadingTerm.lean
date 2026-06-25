import Towers.Algebra.PowerSeries
import Towers.Algebra.TruncatedJennings.FilteredQuotient
import Towers.Algebra.TruncatedJennings.OrderedWords


open Filter
open scoped Pointwise EuclideanGeometry Topology BigOperators

noncomputable section

universe u v

namespace Towers
namespace TJennin

/-- Natural binomial coefficients are the coefficients of the integral binomial series with a
natural exponent. -/
lemma choose_binomial_series
    {p : ℕ} [Fact p.Prime]
    (N j : ℕ) :
    ((Nat.choose N j : ℕ) : ZMod p) =
      PowerSeries.coeff j
        (PowerSeries.binomialSeries (ZMod p) (N : ℤ)) := by
  rw [PowerSeries.binomialSeries_coeff]
  rw [Ring.choose_natCast]
  simp

/-- The coefficient of `X^(p^v)` in `(1+X)^(p^v u)` over `ZMod p` is `u`. -/
lemma cast_choose_self
    {p : ℕ} [Fact p.Prime]
    (v u : ℕ) :
    ((Nat.choose (p ^ v * u) (p ^ v) : ℕ) : ZMod p) =
      (u : ZMod p) := by
  have hcoeff :=
    PowerSeries.coeff_int_self
      (Fact.out : Nat.Prime p) v (u : ℤ)
  have hbridge :
      ((Nat.choose (p ^ v * u) (p ^ v) : ℕ) : ZMod p) =
        PowerSeries.coeff (p ^ v)
          (PowerSeries.binomialSeries (ZMod p)
            (((p ^ v : ℕ) : ℤ) * (u : ℤ))) := by
    rw [PowerSeries.binomialSeries_coeff]
    have hmul :
        (((p ^ v : ℕ) : ℤ) * (u : ℤ)) =
          ((p ^ v * u : ℕ) : ℤ) := by
      norm_num
    rw [hmul, Ring.choose_natCast]
    simp
  exact hbridge.trans (by simpa using hcoeff)

/-- The coefficients strictly between the constant term and `X^(p^v)` vanish in
`(1+X)^(p^v u)` over `ZMod p`. -/
lemma cast_choose_pos
    {p : ℕ} [Fact p.Prime]
    {v u j : ℕ}
    (hj0 : 0 < j)
    (hjq : j < p ^ v) :
    ((Nat.choose (p ^ v * u) j : ℕ) : ZMod p) = 0 := by
  have hcoeff :=
    PowerSeries.binomial_int_pos
      (Fact.out : Nat.Prime p) (v := v) (u := (u : ℤ)) hj0 hjq
  have hbridge :
      ((Nat.choose (p ^ v * u) j : ℕ) : ZMod p) =
        PowerSeries.coeff j
          (PowerSeries.binomialSeries (ZMod p)
            (((p ^ v : ℕ) : ℤ) * (u : ℤ))) := by
    rw [PowerSeries.binomialSeries_coeff]
    have hmul :
        (((p ^ v : ℕ) : ℤ) * (u : ℤ)) =
          ((p ^ v * u : ℕ) : ℤ) := by
      norm_num
    rw [hmul, Ring.choose_natCast]
    simp
  exact hbridge.trans hcoeff

/-- Binomial expansion of `(1 + Y)^N` over a `ZMod p`-algebra. -/
lemma range_choose_smul
    {p : ℕ} [Fact p.Prime]
    {A : Type*} [Semiring A] [Algebra (ZMod p) A]
    (Y : A)
    (N : ℕ) :
    (1 + Y) ^ N =
      ∑ j ∈ Finset.range (N + 1),
        ((Nat.choose N j : ℕ) : ZMod p) • Y ^ j := by
  calc
    (1 + Y) ^ N = (Y + 1) ^ N := by rw [add_comm]
    _ =
        ∑ j ∈ Finset.range (N + 1),
          ((Nat.choose N j : ℕ) : ZMod p) • Y ^ j := by
          rw [Commute.add_pow (Commute.one_right Y)]
          apply Finset.sum_congr rfl
          intro j _hj
          simp only [one_pow, mul_one]
          rw [Algebra.smul_def, Algebra.commutes]
          simp

namespace MBData

/-- A single Hall augmentation variable `U_i = [h_i]-1` has Hall/Jennings weight `r_i`. -/
lemma sub_high_weight
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (i : Fin R.r) :
    groupAlgebraSub p Q (R.gen i) ∈ B.highWeightSpan (R.weight i) := by
  let a : B.ι := B.monomialIndex.symm (singleJenningsExponent (p := p) i)
  have ha_weight : B.weight a = R.weight i := by
    calc
      B.weight a = expWeight R.weight (B.monomialIndex a) := B.weight_apply a
      _ = expWeight R.weight (singleJenningsExponent (p := p) i) := by
            simp [a]
      _ = R.weight i := exp_single_exponent (p := p) R.weight i
  have hbasis_mem : B.basis a ∈ B.highWeightSpan (R.weight i) := by
    exact B.basis_high_span (by rw [ha_weight])
  have hbasis_eq : B.basis a = groupAlgebraSub p Q (R.gen i) := by
    rw [B.basis_apply a]
    simp [a, monomial_single_exponent]
  simpa [hbasis_eq] using hbasis_mem

namespace HMData

/-- Powers of one Hall augmentation variable have the expected filtered lower bound. -/
lemma pow_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (i : Fin R.r)
    (j : ℕ) :
    groupAlgebraSub p Q (R.gen i) ^ j ∈
      B.highWeightSpan (R.weight i * j) := by
  induction j with
  | zero =>
      simpa using M.one_high_zero
  | succ j ih =>
      have hletter :
          groupAlgebraSub p Q (R.gen i) ∈ B.highWeightSpan (R.weight i) :=
        B.sub_high_weight i
      have hmul := M.mul_mem_high ih hletter
      simpa [pow_succ, Nat.mul_succ] using hmul

/-- If `q < j`, then the `j`th power of `U_i` lies in weights strictly above
`r_i q`. -/
lemma sub_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (i : Fin R.r)
    {q j : ℕ}
    (hqj : q < j) :
    groupAlgebraSub p Q (R.gen i) ^ j ∈
      B.highWeightSpan (R.weight i * q + 1) := by
  have hpow :
      groupAlgebraSub p Q (R.gen i) ^ j ∈
        B.highWeightSpan (R.weight i * j) :=
    M.pow_high_span i j
  have hle_succ :
      R.weight i * q + 1 ≤ R.weight i * (q + 1) := by
    rw [Nat.mul_succ]
    exact Nat.add_le_add_left (R.weight_pos i) (R.weight i * q)
  have hle_mul :
      R.weight i * (q + 1) ≤ R.weight i * j :=
    Nat.mul_le_mul_left (R.weight i) (Nat.succ_le_of_lt hqj)
  exact
    basis_high_antitone
      (p := p) (Q := Q) (B := B.basis) (wt := B.weight)
      (le_trans hle_succ hle_mul) hpow

/-- The binomial leading-term theorem for one Hall augmentation variable.

For `U_i = [h_i] - 1`, exponent `e = p^v u`, and `p ∤ u`, the difference between
`[h_i]^e` and `1 + ū U_i^(p^v)` lies in the span of Hall/Jennings weight strictly larger than
`r_i p^v`. -/
theorem leading_remainder_high
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (i : Fin R.r)
    (v u : ℕ)
    (hu : ¬ p ∣ u) :
    denseGeneratorsElement p Q (R.gen i) ^ (p ^ v * u) -
        (1 + (u : ZMod p) •
          groupAlgebraSub p Q (R.gen i) ^ (p ^ v)) ∈
      B.highWeightSpan (R.weight i * p ^ v + 1) := by
  let U : denseGroupAlgebra p Q :=
    groupAlgebraSub p Q (R.gen i)
  let q : ℕ := p ^ v
  let N : ℕ := q * u
  let W : Submodule (ZMod p) (denseGroupAlgebra p Q) :=
    B.highWeightSpan (R.weight i * q + 1)
  have hq_pos : 0 < q := pow_pos (Fact.out : Nat.Prime p).pos v
  have hu_pos : 0 < u := by
    by_contra h
    have hu_zero : u = 0 := Nat.eq_zero_of_not_pos h
    exact hu (by rw [hu_zero]; exact Nat.dvd_zero p)
  have h0_mem : 0 ∈ Finset.range (N + 1) := by
    simp
  have hq_mem : q ∈ Finset.range (N + 1) := by
    have hq_le_N : q ≤ N := by
      have hone_le_u : 1 ≤ u := Nat.succ_le_of_lt hu_pos
      simpa [N, q, Nat.mul_comm] using
        Nat.mul_le_mul_left q hone_le_u
    simp [hq_le_N]
  have hq_ne_zero : q ≠ 0 := Nat.ne_of_gt hq_pos
  have hq_ne_zero' : q ≠ 0 := hq_ne_zero
  have hbinom :
      denseGeneratorsElement p Q (R.gen i) ^ N =
        ∑ j ∈ Finset.range (N + 1),
          ((Nat.choose N j : ℕ) : ZMod p) • U ^ j := by
    have hcanon :
        denseGeneratorsElement p Q (R.gen i) =
          1 + U := by
      simp [U]
    rw [hcanon]
    exact
      range_choose_smul
        (p := p) (Y := U) N
  let term : ℕ → denseGroupAlgebra p Q :=
    fun j => ((Nat.choose N j : ℕ) : ZMod p) • U ^ j
  have hterm_zero : term 0 = (1 : denseGroupAlgebra p Q) := by
    simp [term, N]
  have hterm_q : term q = (u : ZMod p) • U ^ q := by
    have hcoeff :
        ((Nat.choose N q : ℕ) : ZMod p) = (u : ZMod p) := by
      simpa [N, q] using
        cast_choose_self (p := p) v u
    simp [term, hcoeff]
  let S : Finset ℕ := Finset.range (N + 1)
  let T : Finset ℕ := (S.erase 0).erase q
  have hq_mem_erase : q ∈ S.erase 0 := by
    exact (Finset.mem_erase).2 ⟨hq_ne_zero', by simpa [S] using hq_mem⟩
  have hsplit0 :
      ∑ j ∈ S, term j = term 0 + ∑ j ∈ S.erase 0, term j := by
    have h := Finset.sum_erase_add S term h0_mem
    simpa [add_comm] using h.symm
  have hsplitq :
      ∑ j ∈ S.erase 0, term j = term q + ∑ j ∈ T, term j := by
    have h := Finset.sum_erase_add (S.erase 0) term hq_mem_erase
    simpa [T, add_comm] using h.symm
  have hT_mem : ∑ j ∈ T, term j ∈ W := by
    refine W.sum_mem ?_
    intro j hj
    have hjT : j ∈ (S.erase 0).erase q := by simpa [T] using hj
    rcases (Finset.mem_erase).1 hjT with ⟨hjq_ne, hjS0⟩
    rcases (Finset.mem_erase).1 hjS0 with ⟨hj0_ne, hjS⟩
    have hj0 : 0 < j := Nat.pos_of_ne_zero hj0_ne
    rcases lt_trichotomy j q with hjq_lt | hjq_eq | hqj_lt
    · have hcoeff :
          ((Nat.choose N j : ℕ) : ZMod p) = 0 := by
        simpa [N, q] using
          cast_choose_pos
            (p := p) (v := v) (u := u) hj0 hjq_lt
      simp [term, hcoeff, W]
    · exact False.elim (hjq_ne hjq_eq)
    · have hpow :
          U ^ j ∈ B.highWeightSpan (R.weight i * q + 1) := by
        simpa [U, q] using
          M.sub_high_span i hqj_lt
      exact W.smul_mem _ hpow
  have hsum :
      ∑ j ∈ Finset.range (N + 1), term j =
        1 + (u : ZMod p) • U ^ q + ∑ j ∈ T, term j := by
    calc
      ∑ j ∈ Finset.range (N + 1), term j =
          ∑ j ∈ S, term j := by rfl
      _ = term 0 + ∑ j ∈ S.erase 0, term j := hsplit0
      _ = term 0 + (term q + ∑ j ∈ T, term j) := by rw [hsplitq]
      _ = 1 + (u : ZMod p) • U ^ q + ∑ j ∈ T, term j := by
            rw [hterm_zero, hterm_q]
            abel
  have hremainder :
      denseGeneratorsElement p Q (R.gen i) ^ N -
          (1 + (u : ZMod p) • U ^ q) =
        ∑ j ∈ T, term j := by
    rw [hbinom, hsum]
    abel
  simpa [N, q, U, W] using by
    rw [hremainder]
    exact hT_mem

/-- The same Hall augmentation leading-term theorem with a separately named exponent
`e = p^v u`. This is the form used when applying the binomial expansion after extracting the
`p`-adic order of the exponent. -/
theorem binomial_leading_remainder
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (i : Fin R.r)
    {e : ℕ}
    (v u : ℕ)
    (he : e = p ^ v * u)
    (hu : ¬ p ∣ u) :
    denseGeneratorsElement p Q (R.gen i) ^ e -
        (1 + (u : ZMod p) •
          groupAlgebraSub p Q (R.gen i) ^ (p ^ v)) ∈
      B.highWeightSpan (R.weight i * p ^ v + 1) := by
  subst e
  exact M.leading_remainder_high i v u hu

/-- Equivalent existence form of `leading_remainder_high`: the
omitted terms may be collected into a single element of strictly higher Hall/Jennings weight. -/
theorem binomial_leading_weight
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (i : Fin R.r)
    (v u : ℕ)
    (hu : ¬ p ∣ u) :
    ∃ higher : denseGroupAlgebra p Q,
      higher ∈ B.highWeightSpan (R.weight i * p ^ v + 1) ∧
        denseGeneratorsElement p Q (R.gen i) ^ (p ^ v * u) =
          1 + (u : ZMod p) •
            groupAlgebraSub p Q (R.gen i) ^ (p ^ v) + higher := by
  let higher :=
    denseGeneratorsElement p Q (R.gen i) ^ (p ^ v * u) -
      (1 + (u : ZMod p) •
        groupAlgebraSub p Q (R.gen i) ^ (p ^ v))
  refine ⟨higher, ?_, ?_⟩
  · exact M.leading_remainder_high i v u hu
  · dsimp [higher]
    abel

/-- Existence form of the Hall augmentation leading-term theorem with a separately named
exponent `e = p^v u`. -/
theorem binomial_leading_higher
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (i : Fin R.r)
    {e : ℕ}
    (v u : ℕ)
    (he : e = p ^ v * u)
    (hu : ¬ p ∣ u) :
    ∃ higher : denseGroupAlgebra p Q,
      higher ∈ B.highWeightSpan (R.weight i * p ^ v + 1) ∧
        denseGeneratorsElement p Q (R.gen i) ^ e =
          1 + (u : ZMod p) •
            groupAlgebraSub p Q (R.gen i) ^ (p ^ v) + higher := by
  subst e
  exact M.binomial_leading_weight i v u hu

/-- If `p ∤ u`, then the displayed leading scalar `ū` is nonzero in `ZMod p`. -/
lemma binomial_leading_scalar
    {p : ℕ} [Fact p.Prime]
    {u : ℕ}
    (hu : ¬ p ∣ u) :
    (u : ZMod p) ≠ 0 := by
  intro hzero
  have hdiv : p ∣ u :=
    (CharP.cast_eq_zero_iff (ZMod p) p u).1 hzero
  exact hu hdiv

/-- If the initial form of `U_i^(p^v)` is nonzero at weight `r_i p^v`, then multiplying by the
nonzero scalar `ū` preserves that nonvanishing. This is the filtered-linear-algebra
nonvanishing step used after the leading-term expansion. -/
lemma leading_smul_high
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (i : Fin R.r)
    (v u : ℕ)
    (hu : ¬ p ∣ u)
    (hpow :
      groupAlgebraSub p Q (R.gen i) ^ (p ^ v) ∉
        B.highWeightSpan (R.weight i * p ^ v + 1)) :
    (u : ZMod p) • groupAlgebraSub p Q (R.gen i) ^ (p ^ v) ∉
      B.highWeightSpan (R.weight i * p ^ v + 1) := by
  intro hlead
  let c : ZMod p := (u : ZMod p)
  have hc : c ≠ 0 := binomial_leading_scalar (p := p) hu
  have hrescale :
      c⁻¹ •
          (c • groupAlgebraSub p Q (R.gen i) ^ (p ^ v)) ∈
        B.highWeightSpan (R.weight i * p ^ v + 1) :=
    (B.highWeightSpan (R.weight i * p ^ v + 1)).smul_mem _ hlead
  have hscalar : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have hrescale_eq :
      c⁻¹ •
          (c • groupAlgebraSub p Q (R.gen i) ^ (p ^ v)) =
        groupAlgebraSub p Q (R.gen i) ^ (p ^ v) := by
    rw [smul_smul, hscalar, one_smul]
  exact hpow (by simpa [hrescale_eq] using hrescale)

end HMData

end MBData

end TJennin
end Towers
