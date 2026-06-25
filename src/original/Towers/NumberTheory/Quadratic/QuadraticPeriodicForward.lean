import Towers.NumberTheory.Quadratic.PeriodicContinuedFractions

/-!
# Milne, Algebraic Number Theory, forward Lagrange theorem

This file develops the conjugate-orbit and reduced-state steps in the forward direction of
Lagrange's theorem.  The same continued-fraction digits are applied to the other root of an
integral quadratic equation.  Unless the two roots coincide, that companion orbit must
eventually become negative; from then on the oriented quadratic states are reduced.
-/

namespace Towers.NumberTheory.Milne

open GenContFract

/-- Apply the continued-fraction digits of `x` to a second starting point `y`. -/
noncomputable def companionQuotient : ℕ → ℝ → ℝ → ℝ
  | 0, _, y => y
  | n + 1, x, y =>
      (companionQuotient n x y - (⌊completeQuotient n x⌋ : ℝ))⁻¹

theorem complete_succ_one {x : ℝ} (hx : Irrational x) (n : ℕ) :
    1 < completeQuotient (n + 1) x := by
  rw [completeQuotient]
  exact (one_lt_inv₀ (Int.fract_pos.mpr
    ((irrational_completeQuotient hx n).ne_int ⌊completeQuotient n x⌋))).mpr
    (Int.fract_lt_one _)

theorem floor_complete_succ {x : ℝ} (hx : Irrational x) (n : ℕ) :
    1 ≤ ⌊completeQuotient (n + 1) x⌋ := by
  rw [Int.le_floor]
  exact_mod_cast (complete_succ_one hx n).le

/-- Two irrational canonical continued fractions with the same complete-quotient floors agree. -/
theorem cont_fract_floor {x y : ℝ}
    (hx : Irrational x) (hy : Irrational y)
    (hfloor : ∀ n : ℕ, ⌊completeQuotient n x⌋ = ⌊completeQuotient n y⌋) :
    GenContFract.of x = GenContFract.of y := by
  have hnotx : ¬(GenContFract.of x).Terminates := by
    rw [continued_terminates_irrational]
    simpa [Irrational, eq_comm] using hx
  have hnoty : ¬(GenContFract.of y).Terminates := by
    rw [continued_terminates_irrational]
    simpa [Irrational, eq_comm] using hy
  apply GenContFract.ext
  · rw [GenContFract.of_h_eq_floor, GenContFract.of_h_eq_floor]
    exact_mod_cast hfloor 0
  · apply Stream'.Seq.ext
    intro n
    have hnx : ¬(GenContFract.of x).TerminatedAt n := fun hn => hnotx ⟨n, hn⟩
    have hny : ¬(GenContFract.of y).TerminatedAt n := fun hn => hnoty ⟨n, hn⟩
    obtain ⟨px, hpx⟩ := Option.ne_none_iff_exists'.mp hnx
    obtain ⟨py, hpy⟩ := Option.ne_none_iff_exists'.mp hny
    rw [hpx, hpy]
    congr 1
    have hbx := GenContFract.partDen_eq_s_b hpx
    have hby := GenContFract.partDen_eq_s_b hpy
    have hpdx := part_dens_head hnotx n
    have hpdy := part_dens_head hnoty n
    rw [GenContFract.of_h_eq_floor] at hpdx hpdy
    have hb : px.b = py.b := by
      apply Option.some.inj
      rw [← hbx, ← hby, hpdx, hpdy, hfloor (n + 1)]
    have hax := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hpx).1
    have hay := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hpy).1
    cases px
    cases py
    simp_all

theorem companionQuotient_succ (x y : ℝ) (n : ℕ) :
    companionQuotient (n + 1) x y =
      (companionQuotient n x y - (⌊completeQuotient n x⌋ : ℝ))⁻¹ := by
  rfl

/-- Unless the companion starts at the same point, its orbit under the digits of `x` eventually
crosses the negative real axis. -/
theorem companion_quotient_neg {x y : ℝ}
    (hx : Irrational x) (hy : Irrational y) (hxy : x ≠ y) :
    ∃ n : ℕ, 1 ≤ n ∧ companionQuotient n x y < 0 := by
  by_contra hnone
  push Not at hnone
  have hnneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ companionQuotient n x y := by
    intro n hn
    exact hnone n hn
  have hgt : ∀ n : ℕ, 1 ≤ n →
      (⌊completeQuotient n x⌋ : ℝ) < companionQuotient n x y := by
    intro n hn
    let z := companionQuotient n x y - (⌊completeQuotient n x⌋ : ℝ)
    have hzinv : 0 ≤ z⁻¹ := by
      simpa only [companionQuotient_succ, z] using hnneg (n + 1) (by omega)
    have hz : 0 ≤ z := inv_nonneg.mp hzinv
    have hz0 : z ≠ 0 := by
      intro hz0
      have hnext : companionQuotient (n + 1) x y = 0 := by
        rw [companionQuotient_succ, show companionQuotient n x y -
          (⌊completeQuotient n x⌋ : ℝ) = z from rfl, hz0, inv_zero]
      have haInt : 1 ≤ ⌊completeQuotient (n + 1) x⌋ :=
        floor_complete_succ hx n
      have ha : 0 < (⌊completeQuotient (n + 1) x⌋ : ℝ) := by
        exact_mod_cast (zero_lt_one.trans_le haInt)
      have hneg : companionQuotient (n + 2) x y < 0 := by
        rw [show n + 2 = (n + 1) + 1 by omega, companionQuotient_succ, hnext]
        exact inv_lt_zero.mpr (by linarith)
      exact (not_lt_of_ge (hnneg (n + 2) (by omega))) hneg
    exact sub_pos.mp (lt_of_le_of_ne hz (Ne.symm hz0))
  have hfloor : ∀ n : ℕ, 1 ≤ n →
      ⌊companionQuotient n x y⌋ = ⌊completeQuotient n x⌋ := by
    intro n hn
    rw [Int.floor_eq_iff]
    constructor
    · exact (hgt n hn).le
    · have hnextgt : 1 < companionQuotient (n + 1) x y := by
        have haInt : 1 ≤ ⌊completeQuotient (n + 1) x⌋ := by
          simpa only [show n + 1 = (n - 1 + 1) + 1 by omega] using
            floor_complete_succ hx (n - 1 + 1)
        have ha : 1 ≤ (⌊completeQuotient (n + 1) x⌋ : ℝ) := by exact_mod_cast haInt
        exact lt_of_le_of_lt ha (hgt (n + 1) (by omega))
      have hinv : (companionQuotient (n + 1) x y)⁻¹ < 1 :=
        inv_lt_one_of_one_lt₀ hnextgt
      have heq : companionQuotient n x y - (⌊completeQuotient n x⌋ : ℝ) =
          (companionQuotient (n + 1) x y)⁻¹ := by
        rw [companionQuotient_succ, inv_inv]
      linarith
  let Y := companionQuotient 1 x y
  have horbit : ∀ k : ℕ, completeQuotient k Y = companionQuotient (k + 1) x y := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [completeQuotient, ih, Int.fract, hfloor (k + 1) (by omega)]
        simpa only [Nat.add_assoc] using (companionQuotient_succ x y (k + 1)).symm
  have hfloorXY : ∀ k : ℕ,
      ⌊completeQuotient k (completeQuotient 1 x)⌋ = ⌊completeQuotient k Y⌋ := by
    intro k
    rw [← completeQuotient_add, horbit]
    simpa only [Nat.add_comm] using (hfloor (k + 1) (by omega)).symm
  have hYirr : Irrational Y := by
    dsimp [Y]
    rw [companionQuotient, irrational_inv_iff]
    exact irrational_sub_intCast_iff.mpr hy
  have hcf : GenContFract.of (completeQuotient 1 x) = GenContFract.of Y :=
    cont_fract_floor
      (irrational_completeQuotient hx 1) hYirr hfloorXY
  have htail : completeQuotient 1 x = Y := cont_fract_injective hcf
  dsimp [Y] at htail
  rw [completeQuotient, companionQuotient] at htail
  have := congrArg Inv.inv htail
  simp only [inv_inv, completeQuotient, companionQuotient, Int.fract] at this
  exact hxy (by linarith)

/-- Integral coefficients of a quadratic equation. -/
structure QState where
  A : ℤ
  B : ℤ
  C : ℤ

def QState.eval (S : QState) (z : ℝ) : ℝ :=
  (S.A : ℝ) * z ^ 2 + (S.B : ℝ) * z + S.C

def QState.discr (S : QState) : ℤ :=
  S.B ^ 2 - 4 * S.A * S.C

/-- Substitute `a + 1 / X` and negate all coefficients.  The negation chooses the orientation
which remains positive-leading once the two roots straddle the interval endpoint `a`. -/
def QState.step (S : QState) (a : ℤ) : QState where
  A := -(S.A * a ^ 2 + S.B * a + S.C)
  B := -(2 * S.A * a + S.B)
  C := -S.A

theorem QState.discr_step (S : QState) (a : ℤ) :
    (S.step a).discr = S.discr := by
  simp only [QState.step, QState.discr]
  ring

theorem QState.eval_step_invsub {S : QState} {a : ℤ} {z : ℝ}
    (hz : S.eval z = 0) (hza : z - (a : ℝ) ≠ 0) :
    (S.step a).eval ((z - (a : ℝ))⁻¹) = 0 := by
  simp only [QState.eval, QState.step] at hz ⊢
  push_cast
  field_simp
  nlinarith

theorem QState.step_reduced {S : QState} {a : ℤ} {u v : ℝ}
    (hA : 0 < S.A) (hu : S.eval u = 0) (hv : S.eval v = 0)
    (hva : v < (a : ℝ)) (hau : (a : ℝ) < u) :
    0 < (S.step a).A ∧ (S.step a).C < 0 := by
  have huv : u ≠ v := ne_of_gt (hva.trans hau)
  have hfactor : (u - v) * ((S.A : ℝ) * (u + v) + S.B) = 0 := by
    simp only [QState.eval] at hu hv
    nlinarith
  have hsum : (S.A : ℝ) * (u + v) + S.B = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr huv)
  have heval : (S.A : ℝ) * (a : ℝ) ^ 2 + S.B * (a : ℝ) + S.C =
      (S.A : ℝ) * ((a : ℝ) - u) * ((a : ℝ) - v) := by
    simp only [QState.eval] at hu
    nlinarith
  have hAreal : 0 < (S.A : ℝ) := by exact_mod_cast hA
  have hval : (S.A : ℝ) * (a : ℝ) ^ 2 + S.B * (a : ℝ) + S.C < 0 := by
    rw [heval]
    have hleft : (a : ℝ) - u < 0 := sub_neg.mpr hau
    have hright : 0 < (a : ℝ) - v := sub_pos.mpr hva
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hAreal hleft) hright
  constructor
  · simp only [QState.step]
    exact_mod_cast (neg_pos.mpr hval)
  · simp only [QState.step]
    omega

theorem companion_neg_step {x y : ℝ} (hx : Irrational x) {n : ℕ}
    (hn : 1 ≤ n) (hneg : companionQuotient n x y < 0) :
    -1 < companionQuotient (n + 1) x y ∧ companionQuotient (n + 1) x y < 0 := by
  have haInt : 1 ≤ ⌊completeQuotient n x⌋ := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact floor_complete_succ hx k
  have ha : 1 ≤ (⌊completeQuotient n x⌋ : ℝ) := by exact_mod_cast haInt
  rw [companionQuotient_succ]
  constructor
  · let d := companionQuotient n x y - (⌊completeQuotient n x⌋ : ℝ)
    have hd : d < -1 := by dsimp [d]; linarith
    have hpos : 1 < -d := by linarith
    change -1 < d⁻¹
    rw [show d = -(-d) by ring, inv_neg]
    exact neg_lt_neg (inv_lt_one_of_one_lt₀ hpos)
  · exact inv_lt_zero.mpr (by linarith)

def QState.neg (S : QState) : QState :=
  ⟨-S.A, -S.B, -S.C⟩

theorem QState.eval_neg (S : QState) (z : ℝ) :
    S.neg.eval z = -S.eval z := by
  simp only [QState.neg, QState.eval]
  push_cast
  ring

theorem QState.discr_neg (S : QState) : S.neg.discr = S.discr := by
  simp only [QState.neg, QState.discr]
  ring

noncomputable def quadraticStateTail (S : QState) (x : ℝ) (N : ℕ) :
    ℕ → QState
  | 0 => S
  | k + 1 => (quadraticStateTail S x N k).step ⌊completeQuotient (N + k) x⌋

theorem quadratic_state_discr (S : QState) (x : ℝ) (N k : ℕ) :
    (quadraticStateTail S x N k).discr = S.discr := by
  induction k with
  | zero => rfl
  | succ k ih => rw [quadraticStateTail, QState.discr_step, ih]

theorem irrational_companionQuotient {x y : ℝ} (hy : Irrational y) (n : ℕ) :
    Irrational (companionQuotient n x y) := by
  induction n with
  | zero => exact hy
  | succ n ih =>
      rw [companionQuotient, irrational_inv_iff]
      exact irrational_sub_intCast_iff.mpr ih

theorem quadratic_state_roots {S : QState} {x y : ℝ}
    (hx : Irrational x) (hy : Irrational y) {N : ℕ}
    (hrootx : S.eval (completeQuotient N x) = 0)
    (hrooty : S.eval (companionQuotient N x y) = 0) (k : ℕ) :
    (quadraticStateTail S x N k).eval (completeQuotient (N + k) x) = 0 ∧
      (quadraticStateTail S x N k).eval (companionQuotient (N + k) x y) = 0 := by
  induction k with
  | zero => simpa using ⟨hrootx, hrooty⟩
  | succ k ih =>
      constructor
      · rw [quadraticStateTail]
        have hne : completeQuotient (N + k) x -
            (⌊completeQuotient (N + k) x⌋ : ℝ) ≠ 0 := by
          rw [← Int.fract]
          exact (Int.fract_pos.mpr
            ((irrational_completeQuotient hx (N + k)).ne_int _)).ne'
        have h := QState.eval_step_invsub ih.1 hne
        simpa only [completeQuotient, Int.fract, Nat.add_assoc] using h
      · rw [quadraticStateTail]
        have hne : companionQuotient (N + k) x y -
            (⌊completeQuotient (N + k) x⌋ : ℝ) ≠ 0 := by
          exact sub_ne_zero.mpr ((irrational_companionQuotient hy (N + k)).ne_int _)
        have h := QState.eval_step_invsub ih.2 hne
        simpa only [companionQuotient_succ, Nat.add_assoc] using h

/-- Clearing denominators in the minimal polynomial also produces its distinct real companion
root explicitly. -/
theorem IQIrrati.exists_quadr_tworo
    {x : ℝ} (hx : IQIrrati x) :
    ∃ A B C : ℤ, ∃ y : ℝ, 0 < A ∧ Irrational y ∧ x ≠ y ∧
      (A : ℝ) * x ^ 2 + (B : ℝ) * x + C = 0 ∧
      (A : ℝ) * y ^ 2 + (B : ℝ) * y + C = 0 := by
  obtain ⟨A, B, C, hA, hrootx⟩ := hx.exists_int_quadr
  let q : ℚ := -(B : ℚ) / (A : ℚ)
  let y : ℝ := (q : ℝ) - x
  have hy : Irrational y := by
    dsimp [y]
    exact irrational_ratCast_sub_iff.mpr hx.irrational
  have hxy : x ≠ y := by
    intro heq
    apply hx.irrational.ne_rat (q / 2)
    dsimp [y] at heq
    push_cast
    linarith
  have hrooty : (A : ℝ) * y ^ 2 + (B : ℝ) * y + C = 0 := by
    have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
    calc
      (A : ℝ) * y ^ 2 + (B : ℝ) * y + C =
          (A : ℝ) * x ^ 2 + (B : ℝ) * x + C := by
        dsimp [y, q]
        push_cast
        field_simp [hA0]
        ring
      _ = 0 := hrootx
  exact ⟨A, B, C, y, hA, hy, hxy, hrootx, hrooty⟩

/-- The forward direction of Lagrange's theorem: every real quadratic irrational has an
eventually periodic canonical continued fraction. -/
theorem continued_eventually_irrational
    {x : ℝ} (hx : IQIrrati x) :
    ContinuedEventuallyPeriodic x := by
  obtain ⟨A, B, C, y, hA, hy, hxy, hrootx, hrooty⟩ :=
    hx.exists_quadr_tworo
  let S0 : QState := ⟨A, B, C⟩
  obtain ⟨N, hN, hcompN⟩ := companion_quotient_neg hx.irrational hy hxy
  let SN := quadraticStateTail S0 x 0 N
  have hrootsN' := quadratic_state_roots (S := S0) (x := x) (y := y)
    hx.irrational hy (N := 0) (by exact hrootx) (by exact hrooty) N
  have hrootsN : SN.eval (completeQuotient N x) = 0 ∧
      SN.eval (companionQuotient N x y) = 0 := by
    simpa only [SN, Nat.zero_add] using hrootsN'
  have hdisc0 : 0 < S0.discr := by
    simpa only [S0, QState.discr] using
      quadratic_discriminant_pos hx.irrational hA hrootx
  have hdiscN : SN.discr = S0.discr := by
    simpa only [SN] using quadratic_state_discr S0 x 0 N
  have hSNA : SN.A ≠ 0 := by
    intro hzero
    have hB : SN.B ≠ 0 := by
      intro hBzero
      rw [QState.discr, hzero, hBzero] at hdiscN
      norm_num at hdiscN
      omega
    apply (irrational_completeQuotient hx.irrational N).ne_rat
      (-SN.C / SN.B)
    simp only [QState.eval, hzero, Int.cast_zero, zero_mul, zero_add] at hrootsN
    push_cast
    field_simp
    linarith [hrootsN.1]
  let T : QState := if 0 < SN.A then SN else SN.neg
  have hTA : 0 < T.A := by
    dsimp [T]
    split_ifs with hpos
    · exact hpos
    · simp only [QState.neg]
      omega
  have hTx : T.eval (completeQuotient N x) = 0 := by
    dsimp [T]
    split_ifs
    · exact hrootsN.1
    · rw [QState.eval_neg, hrootsN.1, neg_zero]
  have hTy : T.eval (companionQuotient N x y) = 0 := by
    dsimp [T]
    split_ifs
    · exact hrootsN.2
    · rw [QState.eval_neg, hrootsN.2, neg_zero]
  have hTdisc : T.discr = S0.discr := by
    dsimp [T]
    split_ifs
    · exact hdiscN
    · rw [QState.discr_neg, hdiscN]
  have hcompNeg : ∀ k : ℕ, companionQuotient (N + k) x y < 0 := by
    intro k
    induction k with
    | zero => simpa using hcompN
    | succ k ih =>
        have hstep := companion_neg_step hx.irrational
          (n := N + k) (by omega) ih
        simpa only [Nat.add_assoc] using hstep.2
  have hstraddle : ∀ m : ℕ, N ≤ m →
      companionQuotient m x y < (⌊completeQuotient m x⌋ : ℝ) ∧
        (⌊completeQuotient m x⌋ : ℝ) < completeQuotient m x := by
    intro m hNm
    have hm : 1 ≤ m := hN.trans hNm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hfloor : 1 ≤ (⌊completeQuotient (k + 1) x⌋ : ℝ) := by
      exact_mod_cast floor_complete_succ hx.irrational k
    constructor
    · have hneg : companionQuotient (k + 1) x y < 0 := by
        rw [show k + 1 = N + ((k + 1) - N) by omega]
        exact hcompNeg _
      linarith
    · exact lt_of_le_of_ne (Int.floor_le _)
        (Ne.symm ((irrational_completeQuotient hx.irrational (k + 1)).ne_int _))
  have htailRoots : ∀ k : ℕ,
      (quadraticStateTail T x N k).eval (completeQuotient (N + k) x) = 0 ∧
        (quadraticStateTail T x N k).eval (companionQuotient (N + k) x y) = 0 :=
    quadratic_state_roots hx.irrational hy hTx hTy
  have hredSucc : ∀ k : ℕ,
      0 < (quadraticStateTail T x N (k + 1)).A ∧
        (quadraticStateTail T x N (k + 1)).C < 0 := by
    intro k
    induction k with
    | zero =>
        rw [quadraticStateTail]
        exact QState.step_reduced hTA hTx hTy
          (hstraddle N le_rfl).1 (hstraddle N le_rfl).2
    | succ k ih =>
        rw [quadraticStateTail]
        have hs := hstraddle (N + (k + 1)) (by omega)
        exact QState.step_reduced ih.1 (htailRoots (k + 1)).1
          (htailRoots (k + 1)).2 hs.1 hs.2
  have hstate : ∀ n : ℕ, N + 1 ≤ n → ∃ A' B' C' : ℤ,
      0 < A' ∧ C' < 0 ∧ B' ^ 2 - 4 * A' * C' = S0.discr ∧
        (A' : ℝ) * completeQuotient n x ^ 2 +
          (B' : ℝ) * completeQuotient n x + C' = 0 := by
    intro n hn
    let k := n - N
    have hk : 1 ≤ k := by dsimp [k]; omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
    let S := quadraticStateTail T x N k
    have hred : 0 < S.A ∧ S.C < 0 := by
      have hkform : k = j + 1 := by omega
      rw [show S = quadraticStateTail T x N k from rfl, hkform]
      exact hredSucc j
    refine ⟨S.A, S.B, S.C, hred.1, hred.2, ?_, ?_⟩
    · change S.discr = S0.discr
      rw [show S.discr = T.discr by
        simpa only [S] using quadratic_state_discr T x N k, hTdisc]
    · change S.eval (completeQuotient n x) = 0
      have hroot := (htailRoots k).1
      rw [show N + k = n by dsimp [k]; omega] at hroot
      exact hroot
  have hnot : ¬(GenContFract.of x).Terminates := by
    rw [continued_terminates_irrational]
    simpa [Irrational, eq_comm] using hx.irrational
  exact continued_periodic_states
    hnot S0.discr (N + 1) hstate

/-- **Lagrange's theorem.** For an irrational real number, the canonical continued fraction is
eventually periodic exactly when the number has degree two over `ℚ`. -/
theorem continued_periodic_irrational
    {x : ℝ} (hx : Irrational x) :
    ContinuedEventuallyPeriodic x ↔ IQIrrati x := by
  constructor
  · exact irrational_continued_periodic hx
  · exact continued_eventually_irrational

/-- The continued fraction of the square root of a nonsquare natural number is eventually
periodic. -/
theorem sqrt_continued_periodic
    {d : ℕ} (hd : ¬IsSquare d) :
    ContinuedEventuallyPeriodic (Real.sqrt d) :=
  continued_eventually_irrational
    (quadratic_irrational_cast hd)

end Towers.NumberTheory.Milne
