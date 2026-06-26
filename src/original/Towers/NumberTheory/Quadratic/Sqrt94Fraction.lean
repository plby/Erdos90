import Towers.NumberTheory.Quadratic.QuadraticPellExamples
import Towers.NumberTheory.Quadratic.ContinuedFractionUnits
import Mathlib.Tactic.NormNum.IsSquare

/-!
# Milne, Algebraic Number Theory, the continued fraction of sqrt(94)

This file verifies the complete 16-term period used in Milne's Pell-equation example.
-/

namespace Towers.NumberTheory.Milne

open GenContFract

private noncomputable def r : ℝ := Real.sqrt 94

private noncomputable def q (m d : ℤ) : ℝ := (r + m) / d

lemma stream_shift {v : ℝ} {i j : ℕ}
    (h : IntFractPair.stream v i = IntFractPair.stream v j) (n : ℕ) :
    IntFractPair.stream v (i + n) = IntFractPair.stream v (j + n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [Nat.add_succ, Nat.add_succ, IntFractPair.stream, IntFractPair.stream, ih]

lemma stream_step {v x y : ℝ} {n : ℕ} {a : ℤ}
    (hs : IntFractPair.stream v n = some (IntFractPair.of x))
    (hfloor : ⌊x⌋ = a) (hne : x ≠ a) (hnext : (x - a)⁻¹ = y) :
    IntFractPair.stream v (n + 1) = some (IntFractPair.of y) := by
  have hfr : (IntFractPair.of x).fr ≠ 0 := by
    change x - ↑⌊x⌋ ≠ 0
    rw [hfloor]
    exact sub_ne_zero.mpr hne
  rw [IntFractPair.stream_succ_of_some hs hfr]
  congr 2
  simpa [IntFractPair.of, Int.fract, hfloor] using hnext

lemma r_sq : r ^ 2 = 94 := by
  simp [r, Real.sq_sqrt]

lemma r_lower : (9 : ℝ) < r := by
  have hr : (0 : ℝ) ≤ r := by simp [r]
  nlinarith [r_sq]

lemma r_upper : r < (10 : ℝ) := by
  have hr : (0 : ℝ) ≤ r := by simp [r]
  nlinarith [r_sq]

lemma floor_q (m d a : ℤ) (hd : 0 < d)
    (hl : a * d - m ≤ 9)
    (hu : 10 ≤ (a + 1) * d - m) :
    ⌊q m d⌋ = a := by
  rw [Int.floor_eq_iff]
  dsimp [q]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hdR).2
    have hlR : ((a * d - m : ℤ) : ℝ) ≤ 9 := by exact_mod_cast hl
    push_cast at hlR ⊢
    linarith [r_lower]
  · apply (div_lt_iff₀ hdR).2
    have huR : r < ((a + 1) * d - m : ℤ) := by
      exact_mod_cast r_upper.trans_le (by exact_mod_cast hu)
    push_cast at huR ⊢
    linarith

lemma q_ne_floor (m d a : ℤ) (hd : 0 < d) (h : a * d - m ≤ 9) :
    q m d ≠ a := by
  dsimp [q]
  intro heq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have : r + m = a * d := by
    apply (div_eq_iff (ne_of_gt hdR)).mp
    exact heq
  have hR : (a * d - m : ℤ) ≤ (9 : ℝ) := by exact_mod_cast h
  push_cast at this hR
  nlinarith [r_lower]

lemma next_q (m d a m' d' : ℤ)
    (hd0 : d ≠ 0) (hd'0 : d' ≠ 0)
    (hm : m' = a * d - m) (hd : d' * d = 94 - m' ^ 2)
    (hrm : r ≠ m') :
    (q m d - a)⁻¹ = q m' d' := by
  dsimp [q]
  have hd0R : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hd'0R : (d' : ℝ) ≠ 0 := by exact_mod_cast hd'0
  have hden : r + m - a * d ≠ 0 := by
    intro h
    have hmR : (m' : ℝ) = a * d - m := by exact_mod_cast hm
    push_cast at h hmR
    apply hrm
    linarith
  have hsub : (r + (m : ℝ)) / d - a = (r + m - a * d) / d := by
    field_simp [hd0R]
  rw [hsub]
  have hmR : (m' : ℝ) = a * d - m := by exact_mod_cast hm
  have hdR : (d' : ℝ) * d = 94 - m' ^ 2 := by exact_mod_cast hd
  push_cast at hmR hdR
  have hdeneq : r + (m : ℝ) - a * d = r - m' := by linarith
  have hden2 : r - (m' : ℝ) ≠ 0 := sub_ne_zero.mpr hrm
  rw [hdeneq]
  rw [inv_div]
  field_simp [hden2, hd0R, hd'0R]
  ring_nf at hdR ⊢
  nlinarith [r_sq]

lemma r_ne_small (m : ℤ) (hm : m ≤ 9) : r ≠ m := by
  have hmR : (m : ℝ) ≤ 9 := by exact_mod_cast hm
  exact ne_of_gt (hmR.trans_lt r_lower)

lemma sqrt_94_stream :
    IntFractPair.stream r 1 = some (IntFractPair.of (q 9 13)) ∧
    IntFractPair.stream r 2 = some (IntFractPair.of (q 4 6)) ∧
    IntFractPair.stream r 3 = some (IntFractPair.of (q 8 5)) ∧
    IntFractPair.stream r 4 = some (IntFractPair.of (q 7 9)) ∧
    IntFractPair.stream r 5 = some (IntFractPair.of (q 2 10)) ∧
    IntFractPair.stream r 6 = some (IntFractPair.of (q 8 3)) ∧
    IntFractPair.stream r 7 = some (IntFractPair.of (q 7 15)) ∧
    IntFractPair.stream r 8 = some (IntFractPair.of (q 8 2)) ∧
    IntFractPair.stream r 9 = some (IntFractPair.of (q 8 15)) ∧
    IntFractPair.stream r 10 = some (IntFractPair.of (q 7 3)) ∧
    IntFractPair.stream r 11 = some (IntFractPair.of (q 8 10)) ∧
    IntFractPair.stream r 12 = some (IntFractPair.of (q 2 9)) ∧
    IntFractPair.stream r 13 = some (IntFractPair.of (q 7 5)) ∧
    IntFractPair.stream r 14 = some (IntFractPair.of (q 8 6)) ∧
    IntFractPair.stream r 15 = some (IntFractPair.of (q 4 13)) ∧
    IntFractPair.stream r 16 = some (IntFractPair.of (q 9 1)) ∧
    IntFractPair.stream r 17 = some (IntFractPair.of (q 9 13)) := by
  have h0 : IntFractPair.stream r 0 = some (IntFractPair.of (q 0 1)) := by
    simpa [q] using IntFractPair.stream_zero r
  have h1 := stream_step h0
    (floor_q 0 1 9 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 0 1 9 (by norm_num) (by norm_num))
    (next_q 0 1 9 9 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 9 (by norm_num)))
  have h2 := stream_step h1
    (floor_q 9 13 1 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 9 13 1 (by norm_num) (by norm_num))
    (next_q 9 13 1 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 4 (by norm_num)))
  have h3 := stream_step h2
    (floor_q 4 6 2 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 4 6 2 (by norm_num) (by norm_num))
    (next_q 4 6 2 8 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 8 (by norm_num)))
  have h4 := stream_step h3
    (floor_q 8 5 3 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 8 5 3 (by norm_num) (by norm_num))
    (next_q 8 5 3 7 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 7 (by norm_num)))
  have h5 := stream_step h4
    (floor_q 7 9 1 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 7 9 1 (by norm_num) (by norm_num))
    (next_q 7 9 1 2 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 2 (by norm_num)))
  have h6 := stream_step h5
    (floor_q 2 10 1 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 2 10 1 (by norm_num) (by norm_num))
    (next_q 2 10 1 8 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 8 (by norm_num)))
  have h7 := stream_step h6
    (floor_q 8 3 5 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 8 3 5 (by norm_num) (by norm_num))
    (next_q 8 3 5 7 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 7 (by norm_num)))
  have h8 := stream_step h7
    (floor_q 7 15 1 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 7 15 1 (by norm_num) (by norm_num))
    (next_q 7 15 1 8 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 8 (by norm_num)))
  have h9 := stream_step h8
    (floor_q 8 2 8 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 8 2 8 (by norm_num) (by norm_num))
    (next_q 8 2 8 8 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 8 (by norm_num)))
  have h10 := stream_step h9
    (floor_q 8 15 1 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 8 15 1 (by norm_num) (by norm_num))
    (next_q 8 15 1 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 7 (by norm_num)))
  have h11 := stream_step h10
    (floor_q 7 3 5 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 7 3 5 (by norm_num) (by norm_num))
    (next_q 7 3 5 8 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 8 (by norm_num)))
  have h12 := stream_step h11
    (floor_q 8 10 1 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 8 10 1 (by norm_num) (by norm_num))
    (next_q 8 10 1 2 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 2 (by norm_num)))
  have h13 := stream_step h12
    (floor_q 2 9 1 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 2 9 1 (by norm_num) (by norm_num))
    (next_q 2 9 1 7 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 7 (by norm_num)))
  have h14 := stream_step h13
    (floor_q 7 5 3 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 7 5 3 (by norm_num) (by norm_num))
    (next_q 7 5 3 8 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 8 (by norm_num)))
  have h15 := stream_step h14
    (floor_q 8 6 2 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 8 6 2 (by norm_num) (by norm_num))
    (next_q 8 6 2 4 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 4 (by norm_num)))
  have h16 := stream_step h15
    (floor_q 4 13 1 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 4 13 1 (by norm_num) (by norm_num))
    (next_q 4 13 1 9 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 9 (by norm_num)))
  have h17 := stream_step h16
    (floor_q 9 1 18 (by norm_num) (by norm_num) (by norm_num))
    (q_ne_floor 9 1 18 (by norm_num) (by norm_num))
    (next_q 9 1 18 9 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r_ne_small 9 (by norm_num)))
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17⟩

/-- The endpoint of the displayed sixteen-term block is the standard square-root reset state. -/
theorem sqrt_94_sixteen :
    completeQuotient 16 (Real.sqrt 94) = Real.sqrt 94 + 9 := by
  change completeQuotient 16 r = r + 9
  rcases sqrt_94_stream with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h16, _⟩
  have hcanonical := fract_stream_complete
    (quadratic_irrational_cast (d := 94) (by norm_num)).irrational 16
  have hpairs :
      IntFractPair.of (completeQuotient 16 r) = IntFractPair.of (q 9 1) :=
    Option.some.inj (hcanonical.symm.trans h16)
  have := int_fract_injective hpairs
  simpa [q] using this

/-- The general continuant theorem recovers the signed Pell identity at the end of
Milne's sixteen-term period. -/
theorem continuant_pell_identity :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt 94) 0 16)
    M.a ^ 2 - 94 * M.c ^ 2 = 1 := by
  simpa using sqrt_reset_identity
    (d := 94) (s := 16) (k := 9) (by norm_num)
    (by positivity) sqrt_94_sixteen

lemma partDens_get?_eq_stream (v : ℝ) (n : ℕ) :
    (GenContFract.of v).partDens.get? n =
      (IntFractPair.stream v (n + 1)).map (fun p ↦ (p.b : ℝ)) := by
  unfold GenContFract.of GenContFract.partDens IntFractPair.seq1
  simp [Stream'.Seq.map_get?, Stream'.Seq.get?_tail, Function.comp_def]

lemma den_stream_floor {v x : ℝ} {n : ℕ} {a : ℤ}
    (hs : IntFractPair.stream v (n + 1) = some (IntFractPair.of x))
    (hf : ⌊x⌋ = a) :
    (GenContFract.of v).partDens.get? n = some (a : ℝ) := by
  rw [partDens_get?_eq_stream, hs]
  simp [IntFractPair.of, hf]

lemma sqrt_94_period :
    (GenContFract.of r).partDens.get? 0 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 1 = some ((2 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 2 = some ((3 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 3 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 4 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 5 = some ((5 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 6 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 7 = some ((8 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 8 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 9 = some ((5 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 10 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 11 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 12 = some ((3 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 13 = some ((2 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 14 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of r).partDens.get? 15 = some ((18 : ℤ) : ℝ) := by
  rcases sqrt_94_stream with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, _⟩
  exact ⟨
    den_stream_floor h1 (floor_q 9 13 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h2 (floor_q 4 6 2 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h3 (floor_q 8 5 3 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h4 (floor_q 7 9 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h5 (floor_q 2 10 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h6 (floor_q 8 3 5 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h7 (floor_q 7 15 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h8 (floor_q 8 2 8 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h9 (floor_q 8 15 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h10 (floor_q 7 3 5 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h11 (floor_q 8 10 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h12 (floor_q 2 9 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h13 (floor_q 7 5 3 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h14 (floor_q 8 6 2 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h15 (floor_q 4 13 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h16 (floor_q 9 1 18 (by norm_num) (by norm_num) (by norm_num))⟩

lemma stream_periodic :
    Function.Periodic (fun n ↦ IntFractPair.stream r (n + 1)) 16 := by
  rintro n
  rcases sqrt_94_stream with
    ⟨h1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h17⟩
  have hshift := stream_shift (h17.trans h1.symm) n
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift

lemma sqrt_94_dens :
    Function.Periodic (fun n ↦ (GenContFract.of r).partDens.get? n) 16 := by
  intro n
  change (GenContFract.of r).partDens.get? (n + 16) =
    (GenContFract.of r).partDens.get? n
  rw [partDens_get?_eq_stream, partDens_get?_eq_stream]
  have hs : IntFractPair.stream r (n + 16 + 1) =
      IntFractPair.stream r (n + 1) := by
    simpa [Nat.add_assoc] using stream_periodic n
  rw [hs]

/-- Sixteen is the least positive period of the continued fraction of `√94`. -/
theorem sqrt_94_least :
    Function.Periodic
        (fun n ↦
          (GenContFract.of (Real.sqrt 94)).partDens.get? n) 16 ∧
      ∀ p, 0 < p →
        Function.Periodic
          (fun n ↦
            (GenContFract.of (Real.sqrt 94)).partDens.get? n) p →
        16 ≤ p := by
  refine ⟨by simpa [r] using sqrt_94_dens, ?_⟩
  intro p hp hperiod
  change Function.Periodic
    (fun n ↦ (GenContFract.of r).partDens.get? n) p at hperiod
  by_contra hnot
  have hp15 : p ≤ 15 := by omega
  rcases sqrt_94_period with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15⟩
  interval_cases p
  · have h := hperiod 0; norm_num at h; rw [h1, h0] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h2, h0] at h; norm_num at h
  · have h := hperiod 1; norm_num at h; rw [h4, h1] at h; norm_num at h
  · have h := hperiod 1; norm_num at h; rw [h5, h1] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h5, h0] at h; norm_num at h
  · have h := hperiod 1; norm_num at h; rw [h7, h1] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h7, h0] at h; norm_num at h
  · have h := hperiod 1; norm_num at h; rw [h9, h1] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h9, h0] at h; norm_num at h
  · have h := hperiod 1; norm_num at h; rw [h11, h1] at h; norm_num at h
  · have h := hperiod 1; norm_num at h; rw [h12, h1] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h12, h0] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h13, h0] at h; norm_num at h
  · have h := hperiod 1; norm_num at h; rw [h15, h1] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h15, h0] at h; norm_num at h

lemma sqrt_94_periodic :
    ContinuedEventuallyPeriodic
      (Real.sqrt (94 : ℝ)) := by
  refine ⟨0, 16, by norm_num, ?_⟩
  simpa [r] using sqrt_94_dens

private def fifteenthConvergentReal : GenContFract ℝ :=
  ⟨9, Stream'.Seq.ofList
    ([1, 2, 3, 1, 1, 5, 1, 8, 1, 5, 1, 1, 3, 2, 1].map fun b : ℝ =>
      (GenContFract.Pair.mk 1 b))⟩

private lemma cont_fract_get?_eq_pair_of_partDen {v b : ℝ} {n : ℕ}
    (h : (GenContFract.of v).partDens.get? n = some b) :
    (GenContFract.of v).s.get? n = some ⟨1, b⟩ := by
  obtain ⟨gp, hgp, hgb⟩ := GenContFract.exists_s_b_of_partDen h
  have hga := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp).1
  rw [hgp]
  congr 2
  cases gp
  simp_all

private lemma convs_aux_get?_eq {s t : Stream'.Seq (GenContFract.Pair ℝ)} {n : ℕ}
    (h : ∀ i < n, s.get? i = t.get? i) :
    GenContFract.convs'Aux s n = GenContFract.convs'Aux t n := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih =>
      have hhead : s.head = t.head := by
        simpa only [Stream'.Seq.head] using h 0 (Nat.zero_lt_succ n)
      have htail : ∀ i < n, s.tail.get? i = t.tail.get? i := by
        intro i hi
        rw [Stream'.Seq.get?_tail, Stream'.Seq.get?_tail]
        exact h (i + 1) (Nat.add_lt_add_right hi 1)
      simp only [GenContFract.convs'Aux, hhead]
      split
      · rfl
      · rw [ih htail]

private lemma convs_head_get?_eq {g₁ g₂ : GenContFract ℝ} {n : ℕ}
    (hh : g₁.h = g₂.h) (hs : ∀ i < n, g₁.s.get? i = g₂.s.get? i) :
    g₁.convs' n = g₂.convs' n := by
  rw [GenContFract.convs', GenContFract.convs', hh,
    convs_aux_get?_eq hs]

set_option maxRecDepth 10000 in
/-- Milne's displayed rational number is the actual fifteenth convergent of the canonical
continued fraction of `√94`. -/
theorem sqrt_fifteenth_convergent :
    (GenContFract.of (Real.sqrt (94 : ℝ))).convs 15 =
      ((2143295 : ℚ) / 221064 : ℝ) := by
  have hprefix : ∀ i < 15,
      (GenContFract.of r).s.get? i = fifteenthConvergentReal.s.get? i := by
    intro i hi
    rcases sqrt_94_period with
      ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, _⟩
    have s0 := cont_fract_get?_eq_pair_of_partDen h0
    have s1 := cont_fract_get?_eq_pair_of_partDen h1
    have s2 := cont_fract_get?_eq_pair_of_partDen h2
    have s3 := cont_fract_get?_eq_pair_of_partDen h3
    have s4 := cont_fract_get?_eq_pair_of_partDen h4
    have s5 := cont_fract_get?_eq_pair_of_partDen h5
    have s6 := cont_fract_get?_eq_pair_of_partDen h6
    have s7 := cont_fract_get?_eq_pair_of_partDen h7
    have s8 := cont_fract_get?_eq_pair_of_partDen h8
    have s9 := cont_fract_get?_eq_pair_of_partDen h9
    have s10 := cont_fract_get?_eq_pair_of_partDen h10
    have s11 := cont_fract_get?_eq_pair_of_partDen h11
    have s12 := cont_fract_get?_eq_pair_of_partDen h12
    have s13 := cont_fract_get?_eq_pair_of_partDen h13
    have s14 := cont_fract_get?_eq_pair_of_partDen h14
    interval_cases i <;>
      norm_num [fifteenthConvergentReal, Stream'.Seq.ofList, Stream'.map,
        Stream'.tail, Stream'.get] <;>
      first
      | simpa using s0
      | simpa using s1
      | simpa using s2
      | simpa using s3
      | simpa using s4
      | simpa using s5
      | simpa using s6
      | simpa using s7
      | simpa using s8
      | simpa using s9
      | simpa using s10
      | simpa using s11
      | simpa using s12
      | simpa using s13
      | simpa using s14
  have heq : (GenContFract.of r).convs' 15 = fifteenthConvergentReal.convs' 15 := by
    apply convs_head_get?_eq
    · simpa [r] using sqrt_94_head
    · exact hprefix
  have hpositive : ∀ {gp : GenContFract.Pair ℝ} {m : ℕ}, m < 15 →
      fifteenthConvergentReal.s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b := by
    intro gp m hm hgp
    interval_cases m <;>
      norm_num [fifteenthConvergentReal, Stream'.Seq.ofList, Stream'.map,
        Stream'.tail, Stream'.get] at hgp <;>
      subst gp <;> norm_num
  calc
    (GenContFract.of (Real.sqrt (94 : ℝ))).convs 15 =
        (GenContFract.of r).convs' 15 := by
      rw [show Real.sqrt (94 : ℝ) = r by rfl, GenContFract.of_convs_eq_convs']
    _ = fifteenthConvergentReal.convs' 15 := heq
    _ = fifteenthConvergentReal.convs 15 :=
      (GenContFract.convs_eq_convs' hpositive).symm
    _ = ((2143295 : ℚ) / 221064 : ℝ) := by
      norm_num [fifteenthConvergentReal, GenContFract.convs, GenContFract.nums,
        GenContFract.dens, GenContFract.conts, GenContFract.contsAux,
        GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen,
        Stream'.Seq.ofList, Stream'.map, Stream'.tail, Stream'.get]

end Towers.NumberTheory.Milne
