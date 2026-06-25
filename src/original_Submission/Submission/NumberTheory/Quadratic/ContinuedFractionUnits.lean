import Submission.NumberTheory.Quadratic.QuadraticPeriodicForward
import Submission.NumberTheory.Quadratic.QuadraticUnitExamples

/-!
# Milne, Algebraic Number Theory, continued fractions and quadratic units

This file supplies the algebraic bridge used in Milne's continued-fraction description of
fundamental units.  A finite block is represented by its integral continuant matrix.  If the block
returns `√d` when its final tail is `√d + a`, the first column of that matrix satisfies the
Pell-type equation with sign given by the parity of the block length.
-/

namespace Submission.NumberTheory.Milne

open GenContFract

/-- The integral linear-fractional matrix attached to a finite simple continued-fraction block. -/
structure ICMobius where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

/-- Prepending an integral quotient changes `M(x)` into `q + 1 / M(x)`. -/
def ICMobius.prepend
    (q : ℤ) (M : ICMobius) :
    ICMobius :=
  ⟨q * M.a + M.c, q * M.b + M.d, M.a, M.b⟩

/-- The integral continuant matrix associated to a list of integral quotients. -/
def integralContinuedMobius : List ℤ → ICMobius
  | [] => ⟨1, 0, 0, 1⟩
  | q :: qs => (integralContinuedMobius qs).prepend q

/-- Determinant of an integral continuant matrix. -/
def ICMobius.det (M : ICMobius) : ℤ :=
  M.a * M.d - M.b * M.c

@[simp]
theorem ICMobius.det_prepend
    (q : ℤ) (M : ICMobius) :
    (M.prepend q).det = -M.det := by
  simp only [ICMobius.prepend,
    ICMobius.det]
  ring

/-- The determinant of a simple continued-fraction block alternates with its length. -/
theorem fraction_mobius_det (qs : List ℤ) :
    (integralContinuedMobius qs).det = (-1 : ℤ) ^ qs.length := by
  induction qs with
  | nil => norm_num [integralContinuedMobius,
      ICMobius.det]
  | cons q qs ih =>
      rw [integralContinuedMobius,
        ICMobius.det_prepend, ih, List.length_cons, pow_succ]
      ring

/-- Casting the integral continuant matrix gives the rational matrix used by
`finiteContinuedFraction`. -/
theorem continued_mobius_cast (qs : List ℤ) :
    continuedFractionMobius (qs.map (fun q : ℤ ↦ (q : ℚ))) =
      let M := integralContinuedMobius qs
      ⟨M.a, M.b, M.c, M.d⟩ := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.map_cons, continuedFractionMobius,
        integralContinuedMobius, ih, CFMobius.prepend,
        ICMobius.prepend]
      norm_cast

private theorem irrational_int_linear
    {x : ℝ} (hx : Irrational x) {a b : ℤ}
    (h : (a : ℝ) * x + b = 0) :
    a = 0 ∧ b = 0 := by
  by_cases ha : a = 0
  · subst a
    simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h
    exact ⟨rfl, h⟩
  · exfalso
    apply hx.ne_rat ((-b : ℚ) / a)
    push_cast
    field_simp
    nlinarith

/-- The algebraic heart of the continued-fraction solution of Pell's equation.

If a positive integral block sends the tail `√d + k` back to `√d`, then the first column
`(p,q)` of its continuant matrix satisfies `p² - d q² = (-1)^s`, where `s` is the block length. -/
theorem sqrt_pell_identity
    {d : ℕ} (hd : ¬IsSquare d) {k : ℤ} {qs : List ℤ}
    (hqs : ∀ q ∈ qs, 0 < q)
    (htail : 0 < Real.sqrt d + k)
    (hfix : finiteContinuedFraction (qs.map (fun q : ℤ ↦ (q : ℚ)))
      (Real.sqrt d + k) = Real.sqrt d) :
    let M := integralContinuedMobius qs
    M.a ^ 2 - (d : ℤ) * M.c ^ 2 = (-1 : ℤ) ^ qs.length := by
  let x : ℝ := Real.sqrt d
  let M := integralContinuedMobius qs
  have hdpos : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    apply hd
    simp [this]
  have hxpos : 0 < x := by
    dsimp [x]
    exact Real.sqrt_pos.2 (by exact_mod_cast hdpos)
  have htail' : 0 < x + k := by simpa [x] using htail
  have hratPos : ∀ q ∈ qs.map (fun q : ℤ ↦ (q : ℚ)), 0 < q := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    exact_mod_cast hqs z hz
  have heval := continued_fraction_mobius hratPos htail'
  rw [continued_mobius_cast] at heval
  change finiteContinuedFraction (qs.map (fun q : ℤ ↦ (q : ℚ))) (x + k) =
    (((M.a : ℚ) : ℝ) * (x + k) + M.b) /
      (((M.c : ℚ) : ℝ) * (x + k) + M.d) at heval
  have hdenPos :
      0 < (M.c : ℝ) * (x + k) + M.d := by
    simpa [M, continued_mobius_cast] using
      continued_mobius_den hratPos htail'
  have hsq : x ^ 2 = d := by
    dsimp [x]
    rw [Real.sq_sqrt]
    positivity
  have hlinear :
      (((M.c * k + M.d - M.a : ℤ) : ℝ) * x +
        ((M.c * d - M.a * k - M.b : ℤ) : ℝ)) = 0 := by
    rw [hfix] at heval
    change x =
      ((M.a : ℝ) * (x + k) + M.b) /
        ((M.c : ℝ) * (x + k) + M.d) at heval
    rw [eq_div_iff (ne_of_gt hdenPos)] at heval
    push_cast at heval ⊢
    calc
      (M.c * k + M.d - M.a) * x + (M.c * d - M.a * k - M.b) =
          (x * (M.c * (x + k) + M.d) - (M.a * (x + k) + M.b)) +
            M.c * (d - x ^ 2) := by ring
      _ = 0 := by rw [heval, sub_self, hsq, sub_self, mul_zero, add_zero]
  have hxirr : Irrational x := by
    exact (quadratic_irrational_cast hd).irrational
  obtain ⟨hcoeff, hconst⟩ := irrational_int_linear hxirr hlinear
  have hD : M.d = M.a - M.c * k := by omega
  have hB : M.b = M.c * d - M.a * k := by omega
  calc
    M.a ^ 2 - (d : ℤ) * M.c ^ 2 = M.det := by
      simp only [ICMobius.det, hD, hB]
      ring
    _ = (-1 : ℤ) ^ qs.length := fraction_mobius_det qs

/-- The integral quotients in a finite run of the canonical continued-fraction algorithm. -/
noncomputable def completeIntBlock (x : ℝ) (n : ℕ) : ℕ → List ℤ
  | 0 => []
  | k + 1 => ⌊completeQuotient n x⌋ :: completeIntBlock x (n + 1) k

theorem complete_rat_cast (x : ℝ) (n k : ℕ) :
    (completeIntBlock x n k).map (fun q : ℤ ↦ (q : ℚ)) =
      completeQuotientBlock x n k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      simp only [completeIntBlock, completeQuotientBlock, List.map_cons,
        ih]

/-- The integer/fraction state at step `n` is the state of the `n`th complete quotient. -/
theorem fract_stream_complete
    {x : ℝ} (hx : Irrational x) (n : ℕ) :
    IntFractPair.stream x n =
      some (IntFractPair.of (completeQuotient n x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hfr : (IntFractPair.of (completeQuotient n x)).fr ≠ 0 := by
        change Int.fract (completeQuotient n x) ≠ 0
        intro hzero
        rw [Int.fract] at hzero
        exact (irrational_completeQuotient hx n).ne_int
          ⌊completeQuotient n x⌋ (sub_eq_zero.mp hzero)
      rw [IntFractPair.stream_succ_of_some ih hfr]
      congr 2

/-- The integer/fraction decomposition remembers the original real number. -/
theorem int_fract_injective :
    Function.Injective (IntFractPair.of : ℝ → IntFractPair ℝ) := by
  intro x y h
  have hb := congrArg IntFractPair.b h
  have hfr := congrArg IntFractPair.fr h
  simp only [IntFractPair.of] at hb hfr
  calc
    x = Int.fract x + ⌊x⌋ := (Int.fract_add_floor x).symm
    _ = Int.fract y + ⌊y⌋ := by rw [hfr, hb]
    _ = y := Int.fract_add_floor y

@[simp]
theorem complete_int_length (x : ℝ) (n k : ℕ) :
    (completeIntBlock x n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      simp only [completeIntBlock, List.length_cons, ih]

private theorem floor_sqrt_pos {d : ℕ} (hd : ¬IsSquare d) :
    0 < ⌊Real.sqrt d⌋ := by
  have hdpos : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    exact hd (by simp [this])
  have hdge : 2 ≤ d := by
    have hdne : d ≠ 1 := by
      intro h
      apply hd
      simp [h]
    omega
  rw [Int.floor_pos]
  have : (1 : ℝ) < Real.sqrt d := by
    rw [Real.lt_sqrt (by norm_num)]
    exact_mod_cast hdge
  exact this.le

theorem complete_sqrt_pos
    {d : ℕ} (hd : ¬IsSquare d) (s : ℕ) :
    ∀ q ∈ completeIntBlock (Real.sqrt d) 0 s, 0 < q := by
  have hxirr : Irrational (Real.sqrt d) :=
    (quadratic_irrational_cast hd).irrational
  have hfloor : ∀ n : ℕ, 0 < ⌊completeQuotient n (Real.sqrt d)⌋ := by
    intro n
    cases n with
    | zero => exact floor_sqrt_pos hd
    | succ n =>
        exact zero_lt_one.trans_le (floor_complete_succ hxirr n)
  have aux : ∀ n k : ℕ,
      ∀ q ∈ completeIntBlock (Real.sqrt d) n k, 0 < q := by
    intro n k
    induction k generalizing n with
    | zero => simp [completeIntBlock]
    | succ k ih =>
        intro q hq
        simp only [completeIntBlock, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hfloor n
        · exact ih (n + 1) q hq
  exact aux 0 s

/-- If the complete quotient after `s` steps is `√d + k`, then the first column of the
`s`-term continuant matrix satisfies the signed Pell equation. -/
theorem sqrt_reset_identity
    {d s : ℕ} (hd : ¬IsSquare d) {k : ℤ}
    (htail : 0 < Real.sqrt d + k)
    (hreset : completeQuotient s (Real.sqrt d) = Real.sqrt d + k) :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt d) 0 s)
    M.a ^ 2 - (d : ℤ) * M.c ^ 2 = (-1 : ℤ) ^ s := by
  let qs := completeIntBlock (Real.sqrt d) 0 s
  have hfix : finiteContinuedFraction
      ((completeIntBlock (Real.sqrt d) 0 s).map
        (fun q : ℤ ↦ (q : ℚ))) (Real.sqrt d + k) = Real.sqrt d := by
    rw [complete_rat_cast, ← hreset]
    simpa only [Nat.zero_add] using
      continued_fraction_complete (Real.sqrt d) 0 s
  simpa only [complete_int_length] using
    sqrt_pell_identity hd
      (complete_sqrt_pos hd s) htail hfix

private theorem neg_pow_or (n : ℕ) :
    (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  rcases Nat.even_or_odd n with hn | hn
  · left
    exact Even.neg_one_pow hn
  · right
    exact Odd.neg_one_pow hn

/-- The endpoint furnished by a complete-quotient reset is a unit of `ℤ[√d]`. -/
theorem sqrt_complete_reset
    {d s : ℕ} (hd : ¬IsSquare d) {k : ℤ}
    (htail : 0 < Real.sqrt d + k)
    (hreset : completeQuotient s (Real.sqrt d) = Real.sqrt d + k) :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt d) 0 s)
    IsUnit (⟨M.a, M.c⟩ : ℤ√(d : ℤ)) := by
  let M := integralContinuedMobius
    (completeIntBlock (Real.sqrt d) 0 s)
  have hpell : M.a ^ 2 - (d : ℤ) * M.c ^ 2 = (-1 : ℤ) ^ s :=
    sqrt_reset_identity hd htail hreset
  rw [zsqrtd_pell_equation]
  rcases neg_pow_or s with hs | hs
  · left
    exact hpell.trans hs
  · right
    exact hpell.trans hs

end Submission.NumberTheory.Milne
