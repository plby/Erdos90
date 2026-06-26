import Towers.NumberTheory.Quadratic.ContinuedFractionUnits
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.NumberTheory.Pell

/-!
# Milne, Algebraic Number Theory, minimality of quadratic continued-fraction units

This file develops the minimality half of Milne's continued-fraction construction of real
quadratic fundamental units.  The first step is to identify the first column of the integral
continuant matrix with Mathlib's canonical convergent, with the indexing convention used in
Milne: a block of length `s` gives the `(s - 1)`st convergent.
-/

namespace Towers.NumberTheory.Milne

open GenContFract

@[ext]
theorem ICMobius.ext
    {M N : ICMobius}
    (ha : M.a = N.a) (hb : M.b = N.b)
    (hc : M.c = N.c) (hd : M.d = N.d) :
    M = N := by
  cases M
  cases N
  simp_all

theorem continued_mobius_pos
    {qs : List ℤ} (hqs : ∀ q ∈ qs, 0 < q) :
    0 < (integralContinuedMobius qs).a := by
  have hrat : ∀ q ∈ qs.map (fun q : ℤ ↦ (q : ℚ)), 0 < q := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    exact_mod_cast hqs z hz
  have ha := (mobius_coeffs_nonneg hrat).1
  rw [continued_mobius_cast] at ha
  change (0 : ℚ) < ((integralContinuedMobius qs).a : ℚ) at ha
  exact_mod_cast ha

theorem continued_mobius_c
    {q : ℤ} {qs : List ℤ} (hqs : ∀ r ∈ q :: qs, 0 < r) :
    0 < (integralContinuedMobius (q :: qs)).c := by
  have hrat :
      ∀ r ∈ (q :: qs).map (fun r : ℤ ↦ (r : ℚ)), 0 < r := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
    exact_mod_cast hqs z hz
  have hc := mobius_c_pos hrat
  change
    (0 : ℚ) <
      (continuedFractionMobius
        ((q :: qs).map (fun r : ℤ ↦ (r : ℚ)))).c at hc
  rw [continued_mobius_cast] at hc
  change
    (0 : ℚ) <
      ((integralContinuedMobius (q :: qs)).c : ℚ) at hc
  exact_mod_cast hc

theorem continued_mobius_det (qs : List ℤ) :
    (integralContinuedMobius qs).det = 1 ∨
      (integralContinuedMobius qs).det = -1 := by
  rw [fraction_mobius_det]
  rcases Nat.even_or_odd qs.length with h | h
  · exact Or.inl (Even.neg_one_pow h)
  · exact Or.inr (Odd.neg_one_pow h)

theorem continued_mobius_column (qs : List ℤ) :
    IsCoprime (integralContinuedMobius qs).a
      (integralContinuedMobius qs).c := by
  let M := integralContinuedMobius qs
  rcases continued_mobius_det qs with hdet | hdet
  · refine ⟨M.d, -M.b, ?_⟩
    have : M.a * M.d - M.b * M.c = 1 := by
      simpa only [M, ICMobius.det] using hdet
    nlinarith
  · refine ⟨-M.d, M.b, ?_⟩
    have : M.a * M.d - M.b * M.c = -1 := by
      simpa only [M, ICMobius.det] using hdet
    nlinarith

theorem mobius_d_nonneg
    {qs : List ℤ} (hqs : ∀ q ∈ qs, 0 < q) :
    0 ≤ (integralContinuedMobius qs).d := by
  have hrat : ∀ q ∈ qs.map (fun q : ℤ ↦ (q : ℚ)), 0 < q := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    exact_mod_cast hqs z hz
  have hd := (mobius_coeffs_nonneg hrat).2.2.2
  rw [continued_mobius_cast] at hd
  change (0 : ℚ) ≤ ((integralContinuedMobius qs).d : ℚ) at hd
  exact_mod_cast hd

/-- Appending a final quotient performs the usual forward continuant recurrence. -/
theorem continued_mobius_append (qs : List ℤ) (r : ℤ) :
    integralContinuedMobius (qs ++ [r]) =
      let M := integralContinuedMobius qs
      ⟨r * M.a + M.b, M.a, r * M.c + M.d, M.c⟩ := by
  induction qs with
  | nil =>
      simp [integralContinuedMobius,
        ICMobius.prepend]
  | cons q qs ih =>
      simp only [List.cons_append, integralContinuedMobius, ih]
      apply ICMobius.ext
      all_goals simp only [ICMobius.prepend]
      all_goals ring

theorem complete_int_shift (x : ℝ) (m n k : ℕ) :
    completeIntBlock (completeQuotient m x) n k =
      completeIntBlock x (m + n) k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      simp only [completeIntBlock]
      have hhead :
          completeQuotient n (completeQuotient m x) =
            completeQuotient (m + n) x := by
        exact (completeQuotient_add x m n).symm
      rw [hhead]
      apply congrArg (List.cons ⌊completeQuotient (m + n) x⌋)
      simpa only [Nat.add_assoc] using ih (n + 1)

theorem complete_int_snoc (x : ℝ) (n k : ℕ) :
    completeIntBlock x n (k + 1) =
      completeIntBlock x n k ++
        [⌊completeQuotient (n + k) x⌋] := by
  induction k generalizing n with
  | zero => simp [completeIntBlock]
  | succ k ih =>
      apply congrArg (List.cons ⌊completeQuotient n x⌋)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (n + 1)

private theorem complete_pos_start
    {x : ℝ} (hx : Irrational x) {n k : ℕ} (hn : 1 ≤ n) :
    ∀ q ∈ completeIntBlock x n k, 0 < q := by
  induction k generalizing n with
  | zero => simp [completeIntBlock]
  | succ k ih =>
      intro q hq
      simp only [completeIntBlock, List.mem_cons] at hq
      rcases hq with rfl | hq
      · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
        exact zero_lt_one.trans_le (floor_complete_succ hx j)
      · exact ih (by omega) q hq

/-- The first column of the integral continuant matrix for the first `n + 1` complete
quotients represents the `n`th canonical rational convergent. -/
theorem mobius_column_convergent
    {x : ℝ} (hx : Irrational x) (n : ℕ) :
    let M := integralContinuedMobius
      (completeIntBlock x 0 (n + 1))
    ((M.a : ℚ) / M.c) = x.convergent n := by
  induction n generalizing x with
  | zero =>
      simp [completeIntBlock, integralContinuedMobius,
        ICMobius.prepend, completeQuotient,
        Real.convergent]
  | succ n ih =>
      let y := completeQuotient 1 x
      let T := integralContinuedMobius
        (completeIntBlock y 0 (n + 1))
      have hy : Irrational y := irrational_completeQuotient hx 1
      have hshift :
          completeIntBlock x 1 (n + 1) =
            completeIntBlock y 0 (n + 1) := by
        simpa [y] using (complete_int_shift x 1 0 (n + 1)).symm
      have hTpos : 0 < T.a := by
        apply continued_mobius_pos
        rw [show completeIntBlock y 0 (n + 1) =
          completeIntBlock x 1 (n + 1) from hshift.symm]
        exact complete_pos_start hx (by norm_num)
      have hih : ((T.a : ℚ) / T.c) = y.convergent n := by
        simpa only [T] using ih hy
      rw [show n.succ + 1 = (n + 1) + 1 by omega,
        completeIntBlock, hshift]
      change
        (((⌊x⌋ * T.a + T.c : ℤ) : ℚ) / (T.a : ℚ)) =
          x.convergent (n + 1)
      rw [Real.convergent_succ]
      change
        (((⌊x⌋ * T.a + T.c : ℤ) : ℚ) / (T.a : ℚ)) =
          (⌊x⌋ : ℚ) + (y.convergent n)⁻¹
      rw [← hih]
      push_cast
      field_simp [ne_of_gt hTpos]

/-- Real-valued form of the preceding theorem, stated using Mathlib's canonical convergents. -/
theorem cont_convergent_column
    {x : ℝ} (hx : Irrational x) (n : ℕ) :
    let M := integralContinuedMobius
      (completeIntBlock x 0 (n + 1))
    (GenContFract.of x).convs n = (M.a : ℝ) / M.c := by
  let M := integralContinuedMobius
    (completeIntBlock x 0 (n + 1))
  rw [Real.convs_eq_convergent]
  have hrat :
      ((M.a : ℚ) / M.c) = x.convergent n := by
    simpa only [M] using
      mobius_column_convergent hx n
  exact_mod_cast hrat.symm

/-- A block of positive length gives Milne's period-minus-one convergent. -/
theorem cont_fract_column
    {x : ℝ} (hx : Irrational x) {s : ℕ} (hs : 0 < s) :
    let M := integralContinuedMobius
      (completeIntBlock x 0 s)
    (GenContFract.of x).convs (s - 1) = (M.a : ℝ) / M.c := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simpa only [Nat.succ_sub_one] using
    cont_convergent_column hx n

/-- The denominators in the initial continuant columns of `√d` are monotone. -/
theorem sqrt_c_monotone
    {d : ℕ} (hd : ¬IsSquare d) :
    Monotone fun n : ℕ ↦
      (integralContinuedMobius
        (completeIntBlock (Real.sqrt d) 0 (n + 1))).c := by
  apply monotone_nat_of_le_succ
  intro n
  let qs := completeIntBlock (Real.sqrt d) 0 (n + 1)
  let M := integralContinuedMobius qs
  let r := ⌊completeQuotient (n + 1) (Real.sqrt d)⌋
  have hqsPos : ∀ q ∈ qs, 0 < q := by
    simpa only [qs] using complete_sqrt_pos hd (n + 1)
  have hcNonneg : 0 ≤ M.c := by
    have hcPos : 0 < M.c := by
      change 0 <
        (integralContinuedMobius
          (⌊completeQuotient 0 (Real.sqrt d)⌋ ::
            completeIntBlock (Real.sqrt d) 1 n)).c
      apply continued_mobius_c
      simpa only [qs, completeIntBlock] using hqsPos
    exact hcPos.le
  have hdNonneg : 0 ≤ M.d :=
    mobius_d_nonneg hqsPos
  have hrPos : 0 < r := by
    have hpos :=
      complete_sqrt_pos hd (n + 2) r
    apply hpos
    rw [complete_int_snoc]
    simp [r]
  have hrOne : 1 ≤ r := by omega
  conv_rhs =>
    rw [complete_int_snoc,
      continued_mobius_append]
  dsimp only [M, r, qs] at hcNonneg hdNonneg hrOne ⊢
  simp only [Nat.zero_add] at ⊢
  nlinarith

/-- A least positive period of a sequence divides every positive period. -/
theorem Function.Periodic.dvd_least_nat
    {α : Type*} {f : ℕ → α} {s r : ℕ}
    (hs : 0 < s) (hperiodS : Function.Periodic f s)
    (hleast : ∀ p, 0 < p → Function.Periodic f p → s ≤ p)
    (hperiodR : Function.Periodic f r) :
    s ∣ r := by
  have hrem : Function.Periodic f (r % s) := by
    intro n
    calc
      f (n + r % s) = f ((n + r % s) % s) :=
        (hperiodS.map_mod_nat (n + r % s)).symm
      _ = f ((n + r) % s) := by
        congr 1
        simp [Nat.add_mod]
      _ = f (n + r) := hperiodS.map_mod_nat (n + r)
      _ = f n := hperiodR n
  have hmod : r % s = 0 := by
    by_contra hne
    have hpos : 0 < r % s := Nat.pos_of_ne_zero hne
    have hle := hleast (r % s) hpos hrem
    exact (not_le_of_gt (Nat.mod_lt r hs)) hle
  exact Nat.dvd_of_mod_eq_zero hmod

/-- If a complete quotient is the original irrational plus an integer, then its canonical
partial denominators are periodic with that block length. -/
theorem part_dens_complete
    {x : ℝ} (hx : Irrational x) {s : ℕ} (hs : 0 < s) {k : ℤ}
    (hreset : completeQuotient s x = x + k) :
    Function.Periodic
      (fun n ↦ (GenContFract.of x).partDens.get? n) s := by
  have hnext :
      completeQuotient 1 x = completeQuotient (s + 1) x := by
    change (Int.fract x)⁻¹ =
      (Int.fract (completeQuotient s x))⁻¹
    rw [hreset, Int.fract_add_intCast]
  have hcqPeriod :
      Function.Periodic (fun n ↦ completeQuotient (1 + n) x) s := by
    have h := complete_quotient_periodic x
      (m := 1) (n := s + 1) (by omega) hnext
    simpa only [Nat.add_sub_cancel_left] using h
  have hnot : ¬(GenContFract.of x).Terminates := by
    rw [continued_terminates_irrational]
    simpa [Irrational, eq_comm] using hx
  intro n
  change
    (GenContFract.of x).partDens.get? (n + s) =
      (GenContFract.of x).partDens.get? n
  rw [part_dens_head hnot,
    part_dens_head hnot]
  apply congrArg (fun y : ℝ ↦ some (GenContFract.of y).h)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    hcqPeriod n

/-- A positive period of the canonical partial denominators makes the complete quotient at the
end of the block equal to the original number plus an integer. -/
theorem part_dens_periodic
    {x : ℝ} (hx : Irrational x) {s : ℕ}
    (hperiod :
      Function.Periodic
        (fun n ↦ (GenContFract.of x).partDens.get? n) s) :
    ∃ k : ℤ, completeQuotient s x = x + k := by
  have hnot : ¬(GenContFract.of x).Terminates := by
    rw [continued_terminates_irrational]
    simpa [Irrational, eq_comm] using hx
  have hnext :
      completeQuotient 1 x = completeQuotient (s + 1) x := by
    have hperiod' :
        Function.Periodic
          (fun n ↦ (GenContFract.of x).partDens.get? (0 + n)) s := by
      simpa only [Nat.zero_add] using hperiod
    simpa only [Nat.zero_add, Nat.add_assoc] using
      complete_dens_periodic
        (x := x) (N := 0) (p := s) hnot hperiod'
  have hfract :
      Int.fract (completeQuotient s x) = Int.fract x := by
    change (Int.fract x)⁻¹ =
      (Int.fract (completeQuotient s x))⁻¹ at hnext
    have h := congrArg Inv.inv hnext
    simpa only [inv_inv] using h.symm
  let k := ⌊completeQuotient s x⌋ - ⌊x⌋
  refine ⟨k, ?_⟩
  calc
    completeQuotient s x =
        Int.fract (completeQuotient s x) +
          ⌊completeQuotient s x⌋ := (Int.fract_add_floor _).symm
    _ = Int.fract x + ⌊completeQuotient s x⌋ := by rw [hfract]
    _ = x + k := by
      dsimp only [k]
      push_cast
      linarith [Int.fract_add_floor x]

/-- The first column of a square-root period block satisfies Milne's signed Pell equation. -/
theorem period_pell_identity
    {d s : ℕ} (hd : ¬IsSquare d) (hs : 0 < s)
    (hperiod :
      Function.Periodic
        (fun n ↦
          (GenContFract.of (Real.sqrt d)).partDens.get? n) s) :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt d) 0 s)
    M.a ^ 2 - (d : ℤ) * M.c ^ 2 = (-1 : ℤ) ^ s := by
  obtain ⟨k, hreset⟩ :=
    part_dens_periodic
      (quadratic_irrational_cast hd).irrational hperiod
  exact sqrt_reset_identity hd
    (by
      have hsqrtPos : 0 < Real.sqrt d := by
        apply Real.sqrt_pos.2
        have : 0 < d := by
          by_contra hd0
          have : d = 0 := Nat.eq_zero_of_not_pos hd0
          exact hd (by simp [this])
        exact_mod_cast this
      rw [← hreset]
      simpa only [Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr hs.ne')] using
        (complete_succ_one
          (quadratic_irrational_cast hd).irrational (s - 1)).trans'
            zero_lt_one) hreset

/-- A Pell-type first column of an initial square-root block has the sign prescribed by the
continuant determinant. -/
theorem pell_identity_det
    {d s : ℕ} (hd : ¬IsSquare d) (hs : 0 < s)
    (hpell :
      let M := integralContinuedMobius
        (completeIntBlock (Real.sqrt d) 0 s)
      M.a ^ 2 - (d : ℤ) * M.c ^ 2 = 1 ∨
        M.a ^ 2 - (d : ℤ) * M.c ^ 2 = -1) :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt d) 0 s)
    M.a ^ 2 - (d : ℤ) * M.c ^ 2 = M.det := by
  let x : ℝ := Real.sqrt d
  let qs := completeIntBlock x 0 s
  let M := integralContinuedMobius qs
  let t := completeQuotient s x
  have hxirr : Irrational x :=
    (quadratic_irrational_cast hd).irrational
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have hqsPos : ∀ q ∈ qs, 0 < q := by
    simpa only [qs, x] using complete_sqrt_pos hd (n + 1)
  have haPos : 0 < M.a :=
    continued_mobius_pos hqsPos
  have hcPos : 0 < M.c := by
    change 0 <
      (integralContinuedMobius
        (⌊completeQuotient 0 x⌋ ::
          completeIntBlock x 1 n)).c
    apply continued_mobius_c
    simpa only [qs, completeIntBlock] using hqsPos
  have hxPos : 0 < x := by
    dsimp only [x]
    exact Real.sqrt_pos.2 (by
      have : 0 < d := by
        by_contra hd0
        have : d = 0 := Nat.eq_zero_of_not_pos hd0
        exact hd (by simp [this])
      exact_mod_cast this)
  have htPos : 0 < t := by
    dsimp only [t]
    simpa only [Nat.zero_add] using
      (complete_succ_one hxirr n).trans' zero_lt_one
  have hratPos :
      ∀ q ∈ qs.map (fun q : ℤ ↦ (q : ℚ)), 0 < q := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    exact_mod_cast hqsPos z hz
  have hfix :
      finiteContinuedFraction (qs.map (fun q : ℤ ↦ (q : ℚ))) t = x := by
    rw [complete_rat_cast]
    simpa only [qs, t, x, Nat.zero_add] using
      continued_fraction_complete x 0 (n + 1)
  have heval := continued_fraction_mobius hratPos htPos
  rw [continued_mobius_cast] at heval
  change
    finiteContinuedFraction (qs.map (fun q : ℤ ↦ (q : ℚ))) t =
      ((M.a : ℝ) * t + M.b) / ((M.c : ℝ) * t + M.d) at heval
  have hdenPos : 0 < (M.c : ℝ) * t + M.d := by
    have h := continued_mobius_den hratPos htPos
    rw [continued_mobius_cast] at h
    exact h
  rw [hfix, eq_div_iff (ne_of_gt hdenPos)] at heval
  have hcRPos : (0 : ℝ) < M.c := by exact_mod_cast hcPos
  have haRPos : (0 : ℝ) < M.a := by exact_mod_cast haPos
  have hsumPos : 0 < x + (M.a : ℝ) / M.c := by positivity
  have hrightPos :
      0 < (M.c : ℝ) * ((M.c : ℝ) * t + M.d) := by positivity
  have hxSq : x ^ 2 = d := by
    dsimp only [x]
    rw [Real.sq_sqrt]
    positivity
  have hnormProduct :
      (x - (M.a : ℝ) / M.c) *
          (x + (M.a : ℝ) / M.c) * (M.c : ℝ) ^ 2 =
        -((M.a ^ 2 - (d : ℤ) * M.c ^ 2 : ℤ) : ℝ) := by
    field_simp [hcRPos.ne']
    push_cast
    nlinarith [hxSq]
  have hdetProduct :
      (x - (M.a : ℝ) / M.c) *
          ((M.c : ℝ) * ((M.c : ℝ) * t + M.d)) =
        -(M.det : ℝ) := by
    field_simp [hcRPos.ne']
    simp only [ICMobius.det]
    push_cast
    nlinarith [heval]
  have hnorm :
      M.a ^ 2 - (d : ℤ) * M.c ^ 2 = 1 ∨
        M.a ^ 2 - (d : ℤ) * M.c ^ 2 = -1 := by
    simpa only [M, qs, x] using hpell
  have hdet := continued_mobius_det qs
  have hfactorPos :
      0 < (x + (M.a : ℝ) / M.c) * (M.c : ℝ) ^ 2 := by positivity
  rcases hnorm with hnorm | hnorm
  · rcases hdet with hdet | hdet
    · exact hnorm.trans hdet.symm
    · exfalso
      have hleftNeg :
          x - (M.a : ℝ) / M.c < 0 := by
        have hprodNeg :
            (x - (M.a : ℝ) / M.c) *
                ((x + (M.a : ℝ) / M.c) * (M.c : ℝ) ^ 2) < 0 := by
          rw [← mul_assoc, hnormProduct, hnorm]
          norm_num
        rcases (mul_neg_iff.mp hprodNeg) with h | h
        · exact (not_lt_of_ge hfactorPos.le h.2).elim
        · exact h.1
      have hleftPos :
          0 < x - (M.a : ℝ) / M.c := by
        apply (mul_pos_iff_of_pos_right hrightPos).mp
        rw [hdetProduct, hdet]
        norm_num
      linarith
  · rcases hdet with hdet | hdet
    · exfalso
      have hleftPos :
          0 < x - (M.a : ℝ) / M.c := by
        apply (mul_pos_iff_of_pos_right hfactorPos).mp
        rw [← mul_assoc, hnormProduct, hnorm]
        norm_num
      have hleftNeg :
          x - (M.a : ℝ) / M.c < 0 := by
        have hprodNeg :
            (x - (M.a : ℝ) / M.c) *
                ((M.c : ℝ) * ((M.c : ℝ) * t + M.d)) < 0 := by
          rw [hdetProduct, hdet]
          norm_num
        rcases (mul_neg_iff.mp hprodNeg) with h | h
        · exact (not_lt_of_ge hrightPos.le h.2).elim
        · exact h.1
      linarith
    · exact hnorm.trans hdet.symm

/-- Converse to `sqrt_reset_identity` for the signed norm dictated by
the continuant determinant.

If the first column of an initial square-root block has norm equal to the determinant of the
block, then the next complete quotient is `√d` plus an integer. -/
theorem reset_pell_identity
    {d s : ℕ} (hd : ¬IsSquare d) (hs : 0 < s)
    (hpell :
      let M := integralContinuedMobius
        (completeIntBlock (Real.sqrt d) 0 s)
      M.a ^ 2 - (d : ℤ) * M.c ^ 2 = M.det) :
    ∃ k : ℤ, completeQuotient s (Real.sqrt d) = Real.sqrt d + k := by
  let x : ℝ := Real.sqrt d
  let qs := completeIntBlock x 0 s
  let M := integralContinuedMobius qs
  let t := completeQuotient s x
  have hxirr : Irrational x :=
    (quadratic_irrational_cast hd).irrational
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have hqsPos : ∀ q ∈ qs, 0 < q := by
    simpa only [qs, x] using complete_sqrt_pos hd (n + 1)
  have hcPos : 0 < M.c := by
    change 0 <
      (integralContinuedMobius
        (⌊completeQuotient 0 x⌋ ::
          completeIntBlock x 1 n)).c
    apply continued_mobius_c
    simpa only [qs, completeIntBlock] using hqsPos
  have htPos : 0 < t := by
    dsimp only [t]
    simpa only [Nat.zero_add] using
      (complete_succ_one hxirr n).trans' zero_lt_one
  have hratPos :
      ∀ q ∈ qs.map (fun q : ℤ ↦ (q : ℚ)), 0 < q := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    exact_mod_cast hqsPos z hz
  have hfix :
      finiteContinuedFraction (qs.map (fun q : ℤ ↦ (q : ℚ))) t = x := by
    rw [complete_rat_cast]
    simpa only [qs, t, x, Nat.zero_add] using
      continued_fraction_complete x 0 (n + 1)
  have heval := continued_fraction_mobius hratPos htPos
  rw [continued_mobius_cast] at heval
  change
    finiteContinuedFraction (qs.map (fun q : ℤ ↦ (q : ℚ))) t =
      ((M.a : ℝ) * t + M.b) / ((M.c : ℝ) * t + M.d) at heval
  have hdenPos : 0 < (M.c : ℝ) * t + M.d := by
    have h := continued_mobius_den hratPos htPos
    rw [continued_mobius_cast] at h
    exact h
  rw [hfix, eq_div_iff (ne_of_gt hdenPos)] at heval
  have htLinear :
      ((M.c : ℝ) * x - M.a) * t = M.b - M.d * x := by
    nlinarith [heval]
  have hcoeffNe : (M.c : ℝ) * x - M.a ≠ 0 := by
    intro hzero
    apply hxirr.ne_rat ((M.a : ℚ) / M.c)
    have hcNe : (M.c : ℝ) ≠ 0 := by exact_mod_cast hcPos.ne'
    push_cast
    field_simp [hcNe]
    nlinarith
  have hxSq : x ^ 2 = d := by
    dsimp only [x]
    rw [Real.sq_sqrt]
    positivity
  have hpell' : M.a ^ 2 - (d : ℤ) * M.c ^ 2 = M.det := by
    simpa only [M, qs, x] using hpell
  have hdetSq : M.det ^ 2 = 1 := by
    have hdet := fraction_mobius_det qs
    rw [complete_int_length] at hdet
    rw [hdet]
    rcases Nat.even_or_odd (n + 1) with hn | hn
    · rw [Even.neg_one_pow hn]
      norm_num
    · rw [Odd.neg_one_pow hn]
      norm_num
  let k : ℤ := M.det * (M.d * M.c * (d : ℤ) - M.a * M.b)
  refine ⟨k, ?_⟩
  change t = x + k
  apply (mul_left_cancel₀ hcoeffNe)
  rw [htLinear]
  dsimp only [k]
  push_cast
  have hpellR :
      (M.a : ℝ) ^ 2 - (d : ℝ) * (M.c : ℝ) ^ 2 = M.det := by
    exact_mod_cast hpell'
  have hdetSqR : (M.det : ℝ) ^ 2 = 1 := by
    exact_mod_cast hdetSq
  have hscale :
      (M.det : ℝ) *
          ((M.det : ℝ) * x +
            ((M.d : ℝ) * M.c * d - M.a * M.b)) =
        x + (M.det : ℝ) * ((M.d : ℝ) * M.c * d - M.a * M.b) := by
    calc
      (M.det : ℝ) *
          ((M.det : ℝ) * x +
            ((M.d : ℝ) * M.c * d - M.a * M.b)) =
          (M.det : ℝ) ^ 2 * x +
            (M.det : ℝ) * ((M.d : ℝ) * M.c * d - M.a * M.b) := by ring
      _ = x + (M.det : ℝ) * ((M.d : ℝ) * M.c * d - M.a * M.b) := by
        rw [hdetSqR]
        ring
  have hinner :
      ((M.c : ℝ) * x - M.a) *
          ((M.det : ℝ) * x +
            ((M.d : ℝ) * M.c * d - M.a * M.b)) =
        (M.det : ℝ) * (M.b - M.d * x) := by
    have hzero :
        (((M.c : ℝ) * x - M.a) *
              ((M.det : ℝ) * x +
                ((M.d : ℝ) * M.c * d - M.a * M.b)) -
            (M.det : ℝ) * (M.b - M.d * x)) = 0 := by
      calc
        ((M.c : ℝ) * x - M.a) *
              ((M.det : ℝ) * x +
                ((M.d : ℝ) * M.c * d - M.a * M.b)) -
            (M.det : ℝ) * (M.b - M.d * x) =
            (M.det : ℝ) * M.c * (x ^ 2 - d) +
              (M.b - M.d * x) *
                ((M.a : ℝ) ^ 2 - d * (M.c : ℝ) ^ 2 - M.det) := by
          simp only [ICMobius.det]
          push_cast
          ring
        _ = 0 := by rw [hxSq, hpellR]; ring
    linarith
  symm
  calc
    ((M.c : ℝ) * x - M.a) *
        (x + (M.det : ℝ) * ((M.d : ℝ) * M.c * d - M.a * M.b)) =
        ((M.c : ℝ) * x - M.a) *
          ((M.det : ℝ) *
            ((M.det : ℝ) * x +
              ((M.d : ℝ) * M.c * d - M.a * M.b))) := by rw [hscale]
    _ = (M.det : ℝ) *
        (((M.c : ℝ) * x - M.a) *
          ((M.det : ℝ) * x +
            ((M.d : ℝ) * M.c * d - M.a * M.b))) := by ring
    _ = (M.det : ℝ) ^ 2 * (M.b - M.d * x) := by rw [hinner]; ring
    _ = M.b - M.d * x := by rw [hdetSqR]; ring

/-- Legendre's approximation theorem applied to a Pell-type solution.

Every positive integral solution of `p² - d q² = ±1` occurs as a canonical convergent of
`√d`.  The Pell equation also proves that `p / q` is already in lowest terms, so the
denominator appearing in Legendre's theorem is exactly `q`. -/
theorem pell_ratio_convergent
    {d : ℕ} {p q : ℤ}
    (hd : 2 ≤ d) (hp : 0 < p) (hq : 0 < q)
    (hPell :
      p ^ 2 - (d : ℤ) * q ^ 2 = 1 ∨
        p ^ 2 - (d : ℤ) * q ^ 2 = -1) :
    ∃ n : ℕ,
      (GenContFract.of (Real.sqrt d)).convs n =
        (((p : ℚ) / q : ℚ) : ℝ) := by
  let r : ℚ := (p : ℚ) / q
  have hpq : IsCoprime p q := by
    rcases hPell with hplus | hminus
    · refine ⟨p, -(d : ℤ) * q, ?_⟩
      nlinarith
    · refine ⟨-p, (d : ℤ) * q, ?_⟩
      nlinarith
  have hpqNat : Nat.Coprime p.natAbs q.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hpq
  have hdenZ : (r.den : ℤ) = q := by
    dsimp [r]
    exact Rat.den_div_eq_of_coprime hq hpqNat
  have hdenR : (r.den : ℝ) = q := by
    exact_mod_cast hdenZ
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqSqR : (0 : ℝ) < (q : ℝ) ^ 2 := sq_pos_of_pos hqR
  have hsqrtSq : Real.sqrt d ^ 2 = (d : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrtGtOne : (1 : ℝ) < Real.sqrt d := by
    have hsqrtNonneg := Real.sqrt_nonneg (d : ℝ)
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hqSqZ : (1 : ℤ) ≤ q ^ 2 := by nlinarith
  have hdZ : (2 : ℤ) ≤ d := by exact_mod_cast hd
  have hmul : 2 * q ^ 2 ≤ (d : ℤ) * q ^ 2 :=
    mul_le_mul_of_nonneg_right hdZ (sq_nonneg q)
  have hpSqGe : q ^ 2 ≤ p ^ 2 := by
    rcases hPell with hplus | hminus <;> nlinarith
  have hpGe : q ≤ p := by
    nlinarith
  have hrGeOneQ : (1 : ℚ) ≤ r := by
    dsimp [r]
    exact (one_le_div₀ (show (0 : ℚ) < q by exact_mod_cast hq)).2
      (by exact_mod_cast hpGe)
  have hrGeOne : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrGeOneQ
  have hsum : (2 : ℝ) < Real.sqrt d + (r : ℝ) := by linarith
  have hnormReal :
      |(p : ℝ) ^ 2 - (d : ℝ) * (q : ℝ) ^ 2| = 1 := by
    rcases hPell with hplus | hminus
    · have hplusR :
          (p : ℝ) ^ 2 - (d : ℝ) * (q : ℝ) ^ 2 = 1 := by
        exact_mod_cast hplus
      rw [hplusR, abs_one]
    · have hminusR :
          (p : ℝ) ^ 2 - (d : ℝ) * (q : ℝ) ^ 2 = -1 := by
        exact_mod_cast hminus
      rw [hminusR, abs_neg, abs_one]
  have hrCast : (r : ℝ) = (p : ℝ) / (q : ℝ) := by
    simp [r]
  have habsRat :
      |(d : ℝ) - (r : ℝ) ^ 2| = 1 / (q : ℝ) ^ 2 := by
    rw [hrCast]
    have hid :
        (d : ℝ) - ((p : ℝ) / (q : ℝ)) ^ 2 =
          -((p : ℝ) ^ 2 - (d : ℝ) * (q : ℝ) ^ 2) / (q : ℝ) ^ 2 := by
      field_simp
      ring
    rw [hid, abs_div, abs_neg, hnormReal, abs_pow, abs_of_pos hqR]
  have hprod :
      |Real.sqrt d - (r : ℝ)| * (Real.sqrt d + (r : ℝ)) =
        1 / (q : ℝ) ^ 2 := by
    calc
      |Real.sqrt d - (r : ℝ)| * (Real.sqrt d + (r : ℝ)) =
          |Real.sqrt d - (r : ℝ)| * |Real.sqrt d + (r : ℝ)| := by
            rw [abs_of_pos (lt_trans (by norm_num) hsum)]
      _ = |(Real.sqrt d - (r : ℝ)) * (Real.sqrt d + (r : ℝ))| := by
            rw [abs_mul]
      _ = |(d : ℝ) - (r : ℝ) ^ 2| := by
            congr 1
            nlinarith
      _ = 1 / (q : ℝ) ^ 2 := habsRat
  have hdiffPos : 0 < |Real.sqrt d - (r : ℝ)| := by
    by_contra h
    have hz : |Real.sqrt d - (r : ℝ)| = 0 :=
      le_antisymm (le_of_not_gt h) (abs_nonneg _)
    rw [hz, zero_mul] at hprod
    have : (0 : ℝ) < 1 / (q : ℝ) ^ 2 := one_div_pos.mpr hqSqR
    linarith
  have htwice :
      2 * |Real.sqrt d - (r : ℝ)| < 1 / (q : ℝ) ^ 2 := by
    have hm := mul_lt_mul_of_pos_left hsum hdiffPos
    rw [hprod] at hm
    nlinarith
  have happ :
      |Real.sqrt d - (r : ℝ)| <
        1 / (2 * (r.den : ℝ) ^ 2) := by
    rw [hdenR]
    rw [show 1 / (2 * (q : ℝ) ^ 2) =
        (1 / (q : ℝ) ^ 2) / 2 by ring]
    exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by nlinarith)
  simpa [r] using Real.exists_convs_eq_rat happ

/-- Every positive Pell-type solution produces a square-root reset, and its coordinates are
exactly the first column of the corresponding continuant matrix. -/
theorem sqrt_reset_pell
    {d : ℕ} {p q : ℤ} (hdge : 2 ≤ d) (hd : ¬IsSquare d)
    (hp : 0 < p) (hq : 0 < q)
    (hpell :
      p ^ 2 - (d : ℤ) * q ^ 2 = 1 ∨
        p ^ 2 - (d : ℤ) * q ^ 2 = -1) :
    ∃ n : ℕ, ∃ k : ℤ,
      let M := integralContinuedMobius
        (completeIntBlock (Real.sqrt d) 0 (n + 1))
      M.a = p ∧ M.c = q ∧
        completeQuotient (n + 1) (Real.sqrt d) = Real.sqrt d + k := by
  obtain ⟨n, hconv⟩ := pell_ratio_convergent hdge hp hq hpell
  let qs := completeIntBlock (Real.sqrt d) 0 (n + 1)
  let M := integralContinuedMobius qs
  have hqsPos : ∀ z ∈ qs, 0 < z := by
    simpa only [qs] using complete_sqrt_pos hd (n + 1)
  have hcPos : 0 < M.c := by
    change 0 <
      (integralContinuedMobius
        (⌊completeQuotient 0 (Real.sqrt d)⌋ ::
          completeIntBlock (Real.sqrt d) 1 n)).c
    apply continued_mobius_c
    simpa only [qs, completeIntBlock] using hqsPos
  have hfirst :
      (GenContFract.of (Real.sqrt d)).convs n =
        (M.a : ℝ) / M.c := by
    simpa only [M, qs] using
      cont_convergent_column
        (quadratic_irrational_cast hd).irrational n
  have hrat :
      ((M.a : ℚ) / M.c) = (p : ℚ) / q := by
    exact_mod_cast hfirst.symm.trans hconv
  have hMcopNat : Nat.Coprime M.a.natAbs M.c.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp
      (by simpa only [M] using
        continued_mobius_column qs)
  have hpq : IsCoprime p q := by
    rcases hpell with hplus | hminus
    · refine ⟨p, -(d : ℤ) * q, ?_⟩
      nlinarith
    · refine ⟨-p, (d : ℤ) * q, ?_⟩
      nlinarith
  have hpqNat : Nat.Coprime p.natAbs q.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hpq
  obtain ⟨ha, hc⟩ :=
    Rat.div_int_inj hcPos hq hMcopNat hpqNat hrat
  have hpellM :
      M.a ^ 2 - (d : ℤ) * M.c ^ 2 = 1 ∨
        M.a ^ 2 - (d : ℤ) * M.c ^ 2 = -1 := by
    simpa only [ha, hc] using hpell
  have hpellDet :
      M.a ^ 2 - (d : ℤ) * M.c ^ 2 = M.det := by
    simpa only [M, qs] using
      pell_identity_det hd (Nat.succ_pos n) hpellM
  obtain ⟨k, hreset⟩ :=
    reset_pell_identity hd (Nat.succ_pos n)
      (by simpa only [M, qs] using hpellDet)
  exact ⟨n, k, ha, hc, hreset⟩

/-- The denominator at the end of a least square-root period is no larger than the denominator
of any positive solution of either signed Pell equation. -/
theorem period_continuant_pell
    {d s : ℕ} (hdge : 2 ≤ d) (hd : ¬IsSquare d) (hs : 0 < s)
    (hperiod :
      Function.Periodic
        (fun n ↦
          (GenContFract.of (Real.sqrt d)).partDens.get? n) s)
    (hleast :
      ∀ p, 0 < p →
        Function.Periodic
          (fun n ↦
            (GenContFract.of (Real.sqrt d)).partDens.get? n) p →
        s ≤ p)
    {p q : ℤ} (hp : 0 < p) (hq : 0 < q)
    (hpell :
      p ^ 2 - (d : ℤ) * q ^ 2 = 1 ∨
        p ^ 2 - (d : ℤ) * q ^ 2 = -1) :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt d) 0 s)
    M.c ≤ q := by
  let M := integralContinuedMobius
    (completeIntBlock (Real.sqrt d) 0 s)
  change M.c ≤ q
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  obtain ⟨n, k, hTa, hTc, hreset⟩ :=
    sqrt_reset_pell hdge hd hp hq hpell
  let T := integralContinuedMobius
    (completeIntBlock (Real.sqrt d) 0 (n + 1))
  have hperiodT :
      Function.Periodic
        (fun m ↦
          (GenContFract.of (Real.sqrt d)).partDens.get? m) (n + 1) :=
    part_dens_complete
      (quadratic_irrational_cast hd).irrational
      (Nat.succ_pos n) hreset
  have hsDvd : j + 1 ∣ n + 1 :=
    Function.Periodic.dvd_least_nat
      (Nat.succ_pos j) hperiod hleast hperiodT
  have hsLe : j + 1 ≤ n + 1 :=
    Nat.le_of_dvd (Nat.succ_pos n) hsDvd
  have hcLe : M.c ≤ T.c := by
    have hmono := sqrt_c_monotone hd
      (show j ≤ n by omega)
    simpa only [M, T] using hmono
  rw [← hTc]
  exact hcLe

/-- An even least period rules out positive solutions of the negative Pell equation. -/
theorem pell_even_period
    {d s : ℕ} (hdge : 2 ≤ d) (hd : ¬IsSquare d) (hs : 0 < s)
    (hperiod :
      Function.Periodic
        (fun n ↦
          (GenContFract.of (Real.sqrt d)).partDens.get? n) s)
    (hleast :
      ∀ p, 0 < p →
        Function.Periodic
          (fun n ↦
            (GenContFract.of (Real.sqrt d)).partDens.get? n) p →
        s ≤ p)
    (hseven : Even s) :
    ¬∃ p q : ℤ, 0 < p ∧ 0 < q ∧
      p ^ 2 - (d : ℤ) * q ^ 2 = -1 := by
  rintro ⟨p, q, hp, hq, hpell⟩
  obtain ⟨n, k, hTa, hTc, hreset⟩ :=
    sqrt_reset_pell
      hdge hd hp hq (Or.inr hpell)
  let T := integralContinuedMobius
    (completeIntBlock (Real.sqrt d) 0 (n + 1))
  have hperiodT :
      Function.Periodic
        (fun m ↦
          (GenContFract.of (Real.sqrt d)).partDens.get? m) (n + 1) :=
    part_dens_complete
      (quadratic_irrational_cast hd).irrational
      (Nat.succ_pos n) hreset
  have hsDvd : s ∣ n + 1 :=
    Function.Periodic.dvd_least_nat hs hperiod hleast hperiodT
  obtain ⟨r, hr⟩ := hsDvd
  have hnEven : Even (n + 1) := by
    rw [hr]
    exact hseven.mul_right r
  have hpellT : T.a ^ 2 - (d : ℤ) * T.c ^ 2 = -1 := by
    change T.a = p at hTa
    change T.c = q at hTc
    rw [hTa, hTc]
    exact hpell
  have hpellDet : T.a ^ 2 - (d : ℤ) * T.c ^ 2 = T.det := by
    simpa only [T] using
      pell_identity_det hd (Nat.succ_pos n) (Or.inr hpellT)
  have hdet : T.det = 1 := by
    rw [show T.det = (-1 : ℤ) ^ (n + 1) by
      simpa only [T, complete_int_length] using
        fraction_mobius_det
          (completeIntBlock (Real.sqrt d) 0 (n + 1))]
    exact Even.neg_one_pow hnEven
  rw [hpellT, hdet] at hpellDet
  norm_num at hpellDet

/-- For an even least period, the period endpoint is the fundamental positive solution of
the ordinary Pell equation. -/
theorem period_continuant_even
    {d s : ℕ} (hdge : 2 ≤ d) (hd : ¬IsSquare d) (hs : 0 < s)
    (hperiod :
      Function.Periodic
        (fun n ↦
          (GenContFract.of (Real.sqrt d)).partDens.get? n) s)
    (hleast :
      ∀ p, 0 < p →
        Function.Periodic
          (fun n ↦
            (GenContFract.of (Real.sqrt d)).partDens.get? n) p →
        s ≤ p)
    (hseven : Even s) :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt d) 0 s)
    ∃ hpell : M.a ^ 2 - (d : ℤ) * M.c ^ 2 = 1,
      Pell.IsFundamental (Pell.Solution₁.mk M.a M.c hpell) := by
  let qs := completeIntBlock (Real.sqrt d) 0 s
  let M := integralContinuedMobius qs
  have hqsPos : ∀ q ∈ qs, 0 < q := by
    simpa only [qs] using complete_sqrt_pos hd s
  have haPos : 0 < M.a :=
    continued_mobius_pos hqsPos
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have hcPos : 0 < M.c := by
    change 0 <
      (integralContinuedMobius
        (⌊completeQuotient 0 (Real.sqrt d)⌋ ::
          completeIntBlock (Real.sqrt d) 1 j)).c
    apply continued_mobius_c
    simpa only [qs, completeIntBlock] using hqsPos
  have hpellSigned :
      M.a ^ 2 - (d : ℤ) * M.c ^ 2 = (-1 : ℤ) ^ (j + 1) := by
    simpa only [M, qs] using
      period_pell_identity hd (Nat.succ_pos j) hperiod
  have hseven' : Even (j + 1) := by simpa only using hseven
  have hpell : M.a ^ 2 - (d : ℤ) * M.c ^ 2 = 1 := by
    rw [hpellSigned, Even.neg_one_pow hseven']
  refine ⟨hpell, ?_⟩
  have haOne : 1 < M.a := by
    have hdZ : (2 : ℤ) ≤ d := by exact_mod_cast hdge
    have hcSq : 1 ≤ M.c ^ 2 := by nlinarith
    nlinarith
  refine ⟨haOne, hcPos, ?_⟩
  intro b hb
  have hbPos : 0 < b.x := zero_lt_one.trans hb
  have hbyNe : b.y ≠ 0 := Pell.Solution₁.y_ne_zero_of_one_lt_x hb
  have hqPos : 0 < |b.y| := abs_pos.mpr hbyNe
  have hbPellAbs :
      b.x ^ 2 - (d : ℤ) * |b.y| ^ 2 = 1 := by
    simpa only [sq_abs] using b.prop
  have hcAbs : M.c ≤ |b.y| := by
    simpa only [M, qs] using
      period_continuant_pell hdge hd (Nat.succ_pos j)
        hperiod hleast hbPos hqPos (Or.inl hbPellAbs)
  have hcSqLe : M.c ^ 2 ≤ b.y ^ 2 := by
    have h := (sq_le_sq₀ hcPos.le (abs_nonneg b.y)).2 hcAbs
    simpa only [sq_abs] using h
  have hdNonneg : (0 : ℤ) ≤ d := by exact_mod_cast (Nat.zero_le d)
  have hmul :
      (d : ℤ) * M.c ^ 2 ≤ (d : ℤ) * b.y ^ 2 :=
    mul_le_mul_of_nonneg_left hcSqLe hdNonneg
  have hsqLe : M.a ^ 2 ≤ b.x ^ 2 := by
    nlinarith [hpell, b.prop]
  change M.a ≤ b.x
  exact (sq_le_sq₀ haPos.le hbPos.le).1 hsqLe

end Towers.NumberTheory.Milne
