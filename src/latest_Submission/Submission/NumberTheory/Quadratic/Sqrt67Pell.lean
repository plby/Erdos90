import Submission.NumberTheory.Quadratic.Sqrt94Minimality
import Submission.NumberTheory.Quadratic.ContinuedFractionMinimality
import Submission.NumberTheory.Quadratic.FieldFormSetup

/-!
# Milne, Chapter 5, Exercise 2

The continued fraction of `√67` has period ten, and its ninth convergent gives the
fundamental unit

`48842 + 5967 * √67`.
-/

namespace Submission.NumberTheory.Milne

open GenContFract Pell
open Submission.NumberTheory
open scoped NumberField

local instance : Fact (∀ r : ℚ, r ^ 2 ≠ (67 : ℚ) + 0 * r) :=
  quadraticNonsquareFact (d := (67 : ℤ)) (by norm_num) (by norm_num)

local instance : Module.Finite ℚ (QFModel 67) :=
  quadraticModuleFinite (d := (67 : ℤ)) (by norm_num) (by norm_num)

local instance : NumberField (QFModel 67) :=
  quadraticFieldNumber (d := (67 : ℤ)) (by norm_num) (by norm_num)

/-- The coordinate-preserving equivalence between the two integral models of `ℤ[√67]`. -/
def quadratic67Zsqrtd : QOrd 67 0 ≃+* ℤ√67 where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

/-- The full ring of integers of `ℚ(√67)` is `ℤ[√67]`. -/
noncomputable def sqrt67Integers :
    NumberField.RingOfIntegers (QFModel 67) ≃+* ℤ√67 := by
  let e : NumberField.RingOfIntegers (QFModel 67) ≃+*
      QOrd 67 0 := by
    simpa [quadraticOrderParameter, quadraticParameterB] using
      (integersQuadraticOrder (d := (67 : ℤ))
        (by norm_num) (by norm_num))
  exact e.trans quadratic67Zsqrtd

private noncomputable def sqrt67Real : ℝ := Real.sqrt 67

private noncomputable def sqrt67Quotient (m d : ℤ) : ℝ :=
  (sqrt67Real + m) / d

private theorem sqrt_67_sq : sqrt67Real ^ 2 = 67 := by
  simp [sqrt67Real, Real.sq_sqrt]

private theorem sqrt_67_real : (8 : ℝ) < sqrt67Real := by
  have hr : (0 : ℝ) ≤ sqrt67Real := by simp [sqrt67Real]
  nlinarith [sqrt_67_sq]

private theorem sqrt_67_upper : sqrt67Real < (9 : ℝ) := by
  have hr : (0 : ℝ) ≤ sqrt67Real := by simp [sqrt67Real]
  nlinarith [sqrt_67_sq]

private theorem sqrt_floor_quotient (m d a : ℤ) (hd : 0 < d)
    (hl : a * d - m ≤ 8) (hu : 9 ≤ (a + 1) * d - m) :
    ⌊sqrt67Quotient m d⌋ = a := by
  rw [Int.floor_eq_iff]
  dsimp [sqrt67Quotient]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hdR).2
    have hlR : ((a * d - m : ℤ) : ℝ) ≤ 8 := by exact_mod_cast hl
    push_cast at hlR ⊢
    linarith [sqrt_67_real]
  · apply (div_lt_iff₀ hdR).2
    have huR : sqrt67Real < ((a + 1) * d - m : ℤ) := by
      exact_mod_cast sqrt_67_upper.trans_le (by exact_mod_cast hu)
    push_cast at huR ⊢
    linarith

private theorem sqrt_67_floor (m d a : ℤ) (hd : 0 < d)
    (h : a * d - m ≤ 8) :
    sqrt67Quotient m d ≠ a := by
  dsimp [sqrt67Quotient]
  intro heq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heq' : sqrt67Real + m = a * d := by
    apply (div_eq_iff (ne_of_gt hdR)).mp
    exact heq
  have hR : (a * d - m : ℤ) ≤ (8 : ℝ) := by exact_mod_cast h
  push_cast at heq' hR
  nlinarith [sqrt_67_real]

private theorem sqrt_67_next (m d a m' d' : ℤ)
    (hd0 : d ≠ 0) (hd'0 : d' ≠ 0)
    (hm : m' = a * d - m) (hd : d' * d = 67 - m' ^ 2)
    (hrm : sqrt67Real ≠ m') :
    (sqrt67Quotient m d - a)⁻¹ = sqrt67Quotient m' d' := by
  dsimp [sqrt67Quotient]
  have hd0R : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hd'0R : (d' : ℝ) ≠ 0 := by exact_mod_cast hd'0
  have hden : sqrt67Real + m - a * d ≠ 0 := by
    intro h
    have hmR : (m' : ℝ) = a * d - m := by exact_mod_cast hm
    push_cast at h hmR
    apply hrm
    linarith
  have hsub :
      (sqrt67Real + (m : ℝ)) / d - a =
        (sqrt67Real + m - a * d) / d := by
    field_simp [hd0R]
  rw [hsub]
  have hmR : (m' : ℝ) = a * d - m := by exact_mod_cast hm
  have hdR : (d' : ℝ) * d = 67 - m' ^ 2 := by exact_mod_cast hd
  push_cast at hmR hdR
  have hdeneq : sqrt67Real + (m : ℝ) - a * d = sqrt67Real - m' := by
    linarith
  have hden2 : sqrt67Real - (m' : ℝ) ≠ 0 := sub_ne_zero.mpr hrm
  rw [hdeneq, inv_div]
  field_simp [hden2, hd0R, hd'0R]
  ring_nf at hdR ⊢
  nlinarith [sqrt_67_sq]

private theorem sqrt_67_small (m : ℤ) (hm : m ≤ 8) :
    sqrt67Real ≠ m := by
  have hmR : (m : ℝ) ≤ 8 := by exact_mod_cast hm
  exact ne_of_gt (hmR.trans_lt sqrt_67_real)

private theorem sqrt_67_stream :
    IntFractPair.stream sqrt67Real 1 =
        some (IntFractPair.of (sqrt67Quotient 8 3)) ∧
    IntFractPair.stream sqrt67Real 2 =
        some (IntFractPair.of (sqrt67Quotient 7 6)) ∧
    IntFractPair.stream sqrt67Real 3 =
        some (IntFractPair.of (sqrt67Quotient 5 7)) ∧
    IntFractPair.stream sqrt67Real 4 =
        some (IntFractPair.of (sqrt67Quotient 2 9)) ∧
    IntFractPair.stream sqrt67Real 5 =
        some (IntFractPair.of (sqrt67Quotient 7 2)) ∧
    IntFractPair.stream sqrt67Real 6 =
        some (IntFractPair.of (sqrt67Quotient 7 9)) ∧
    IntFractPair.stream sqrt67Real 7 =
        some (IntFractPair.of (sqrt67Quotient 2 7)) ∧
    IntFractPair.stream sqrt67Real 8 =
        some (IntFractPair.of (sqrt67Quotient 5 6)) ∧
    IntFractPair.stream sqrt67Real 9 =
        some (IntFractPair.of (sqrt67Quotient 7 3)) ∧
    IntFractPair.stream sqrt67Real 10 =
        some (IntFractPair.of (sqrt67Quotient 8 1)) ∧
    IntFractPair.stream sqrt67Real 11 =
        some (IntFractPair.of (sqrt67Quotient 8 3)) := by
  have h0 :
      IntFractPair.stream sqrt67Real 0 =
        some (IntFractPair.of (sqrt67Quotient 0 1)) := by
    simpa [sqrt67Quotient] using IntFractPair.stream_zero sqrt67Real
  have h1 := stream_step h0
    (sqrt_floor_quotient 0 1 8 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 0 1 8 (by norm_num) (by norm_num))
    (sqrt_67_next 0 1 8 8 3 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 8 (by norm_num)))
  have h2 := stream_step h1
    (sqrt_floor_quotient 8 3 5 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 8 3 5 (by norm_num) (by norm_num))
    (sqrt_67_next 8 3 5 7 6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 7 (by norm_num)))
  have h3 := stream_step h2
    (sqrt_floor_quotient 7 6 2 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 7 6 2 (by norm_num) (by norm_num))
    (sqrt_67_next 7 6 2 5 7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 5 (by norm_num)))
  have h4 := stream_step h3
    (sqrt_floor_quotient 5 7 1 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 5 7 1 (by norm_num) (by norm_num))
    (sqrt_67_next 5 7 1 2 9 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 2 (by norm_num)))
  have h5 := stream_step h4
    (sqrt_floor_quotient 2 9 1 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 2 9 1 (by norm_num) (by norm_num))
    (sqrt_67_next 2 9 1 7 2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 7 (by norm_num)))
  have h6 := stream_step h5
    (sqrt_floor_quotient 7 2 7 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 7 2 7 (by norm_num) (by norm_num))
    (sqrt_67_next 7 2 7 7 9 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 7 (by norm_num)))
  have h7 := stream_step h6
    (sqrt_floor_quotient 7 9 1 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 7 9 1 (by norm_num) (by norm_num))
    (sqrt_67_next 7 9 1 2 7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 2 (by norm_num)))
  have h8 := stream_step h7
    (sqrt_floor_quotient 2 7 1 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 2 7 1 (by norm_num) (by norm_num))
    (sqrt_67_next 2 7 1 5 6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 5 (by norm_num)))
  have h9 := stream_step h8
    (sqrt_floor_quotient 5 6 2 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 5 6 2 (by norm_num) (by norm_num))
    (sqrt_67_next 5 6 2 7 3 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 7 (by norm_num)))
  have h10 := stream_step h9
    (sqrt_floor_quotient 7 3 5 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 7 3 5 (by norm_num) (by norm_num))
    (sqrt_67_next 7 3 5 8 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 8 (by norm_num)))
  have h11 := stream_step h10
    (sqrt_floor_quotient 8 1 16 (by norm_num) (by norm_num) (by norm_num))
    (sqrt_67_floor 8 1 16 (by norm_num) (by norm_num))
    (sqrt_67_next 8 1 16 8 3 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (sqrt_67_small 8 (by norm_num)))
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The endpoint of the ten-term period is the standard square-root reset state. -/
theorem sqrt_complete_ten :
    completeQuotient 10 (Real.sqrt 67) = Real.sqrt 67 + 8 := by
  change completeQuotient 10 sqrt67Real = sqrt67Real + 8
  rcases sqrt_67_stream with
    ⟨_, _, _, _, _, _, _, _, _, h10, _⟩
  have hcanonical := fract_stream_complete
    (quadratic_irrational_cast (d := 67) (by norm_num)).irrational 10
  have hpairs :
      IntFractPair.of (completeQuotient 10 sqrt67Real) =
        IntFractPair.of (sqrt67Quotient 8 1) :=
    Option.some.inj (hcanonical.symm.trans h10)
  have := int_fract_injective hpairs
  simpa [sqrt67Quotient] using this

/-- The general continuant theorem recovers the signed Pell identity at the end of
the period in Exercise 5-2. -/
theorem period_continuant_identity :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt 67) 0 10)
    M.a ^ 2 - 67 * M.c ^ 2 = 1 := by
  simpa using sqrt_reset_identity
    (d := 67) (s := 10) (k := 8) (by norm_num)
    (by positivity) sqrt_complete_ten

/-- The first period of the continued fraction of `√67` is
`[5, 2, 1, 1, 7, 1, 1, 2, 5, 16]`. -/
theorem sqrt_67_period :
    (GenContFract.of sqrt67Real).partDens.get? 0 = some ((5 : ℤ) : ℝ) ∧
    (GenContFract.of sqrt67Real).partDens.get? 1 = some ((2 : ℤ) : ℝ) ∧
    (GenContFract.of sqrt67Real).partDens.get? 2 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of sqrt67Real).partDens.get? 3 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of sqrt67Real).partDens.get? 4 = some ((7 : ℤ) : ℝ) ∧
    (GenContFract.of sqrt67Real).partDens.get? 5 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of sqrt67Real).partDens.get? 6 = some ((1 : ℤ) : ℝ) ∧
    (GenContFract.of sqrt67Real).partDens.get? 7 = some ((2 : ℤ) : ℝ) ∧
    (GenContFract.of sqrt67Real).partDens.get? 8 = some ((5 : ℤ) : ℝ) ∧
    (GenContFract.of sqrt67Real).partDens.get? 9 = some ((16 : ℤ) : ℝ) := by
  rcases sqrt_67_stream with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩
  exact ⟨
    den_stream_floor h1
      (sqrt_floor_quotient 8 3 5 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h2
      (sqrt_floor_quotient 7 6 2 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h3
      (sqrt_floor_quotient 5 7 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h4
      (sqrt_floor_quotient 2 9 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h5
      (sqrt_floor_quotient 7 2 7 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h6
      (sqrt_floor_quotient 7 9 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h7
      (sqrt_floor_quotient 2 7 1 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h8
      (sqrt_floor_quotient 5 6 2 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h9
      (sqrt_floor_quotient 7 3 5 (by norm_num) (by norm_num) (by norm_num)),
    den_stream_floor h10
      (sqrt_floor_quotient 8 1 16 (by norm_num) (by norm_num) (by norm_num))⟩

private theorem sqrt_stream_periodic :
    Function.Periodic
      (fun n ↦ IntFractPair.stream sqrt67Real (n + 1)) 10 := by
  intro n
  rcases sqrt_67_stream with
    ⟨h1, _, _, _, _, _, _, _, _, _, h11⟩
  have hshift := stream_shift (h11.trans h1.symm) n
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift

/-- Ten is a period of the canonical continued fraction of `√67`. -/
theorem sqrt_dens_periodic :
    Function.Periodic
      (fun n ↦ (GenContFract.of sqrt67Real).partDens.get? n) 10 := by
  intro n
  change (GenContFract.of sqrt67Real).partDens.get? (n + 10) =
    (GenContFract.of sqrt67Real).partDens.get? n
  rw [partDens_get?_eq_stream, partDens_get?_eq_stream]
  have hs :
      IntFractPair.stream sqrt67Real (n + 10 + 1) =
        IntFractPair.stream sqrt67Real (n + 1) := by
    simpa [Nat.add_assoc] using sqrt_stream_periodic n
  rw [hs]

/-- The least positive period of the continued fraction of `√67` is ten. -/
theorem sqrt_least_period :
    Function.Periodic
        (fun n ↦ (GenContFract.of sqrt67Real).partDens.get? n) 10 ∧
      ∀ p, 0 < p →
        Function.Periodic
          (fun n ↦ (GenContFract.of sqrt67Real).partDens.get? n) p →
        10 ≤ p := by
  refine ⟨sqrt_dens_periodic, ?_⟩
  intro p hp hperiod
  by_contra hnot
  have hp9 : p ≤ 9 := by omega
  rcases sqrt_67_period with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  interval_cases p
  · have h := hperiod 0; norm_num at h; rw [h1, h0] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h2, h0] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h3, h0] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h4, h0] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h5, h0] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h6, h0] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h7, h0] at h; norm_num at h
  · have h := hperiod 1; norm_num at h; rw [h9, h1] at h; norm_num at h
  · have h := hperiod 0; norm_num at h; rw [h9, h0] at h; norm_num at h

private theorem sqrt_67_ten :
    completeIntBlock (Real.sqrt 67) 0 10 =
      [8, 5, 2, 1, 1, 7, 1, 1, 2, 5] := by
  have hnot : ¬(GenContFract.of sqrt67Real).Terminates := by
    rw [continued_terminates_irrational]
    simpa [Irrational, eq_comm, sqrt67Real] using
      (quadratic_irrational_cast (d := 67) (by norm_num)).irrational
  have floor_of_partDen {i : ℕ} {a : ℤ}
      (hpd :
        (GenContFract.of sqrt67Real).partDens.get? i =
          some (a : ℝ)) :
      ⌊completeQuotient (i + 1) sqrt67Real⌋ = a := by
    have hhead := part_dens_head hnot i
    rw [GenContFract.of_h_eq_floor, hpd] at hhead
    exact_mod_cast (Option.some.inj hhead).symm
  rcases sqrt_67_period with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, _⟩
  have hf0 : ⌊completeQuotient 0 sqrt67Real⌋ = 8 := by
    change ⌊sqrt67Real⌋ = 8
    simpa [sqrt67Quotient] using
      sqrt_floor_quotient 0 1 8
        (by norm_num) (by norm_num) (by norm_num)
  have hf1 := floor_of_partDen h0
  have hf2 := floor_of_partDen h1
  have hf3 := floor_of_partDen h2
  have hf4 := floor_of_partDen h3
  have hf5 := floor_of_partDen h4
  have hf6 := floor_of_partDen h5
  have hf7 := floor_of_partDen h6
  have hf8 := floor_of_partDen h7
  have hf9 := floor_of_partDen h8
  change completeIntBlock sqrt67Real 0 10 =
    [8, 5, 2, 1, 1, 7, 1, 1, 2, 5]
  simp only [completeIntBlock, hf0, hf1, hf2, hf3, hf4, hf5,
    hf6, hf7, hf8, hf9]

/-- The finite continued fraction `[8; 5, 2, 1, 1, 7, 1, 1, 2, 5]`. -/
def sqrtNinthConvergent : GenContFract ℚ :=
  ⟨8, Stream'.Seq.ofList
    ([5, 2, 1, 1, 7, 1, 1, 2, 5].map fun b : ℚ =>
      (GenContFract.Pair.mk 1 b))⟩

/-- The period-minus-one convergent used in the solution of Exercise 5-2. -/
theorem sqrt_ninth_convergent :
    sqrtNinthConvergent.convs 9 = (48842 : ℚ) / 5967 := by
  norm_num [sqrtNinthConvergent, GenContFract.convs, GenContFract.nums,
    GenContFract.dens, GenContFract.conts, GenContFract.contsAux,
    GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen,
    Stream'.Seq.ofList, Stream'.map, Stream'.tail, Stream'.get]

/-- The displayed Pell solution for Exercise 5-2. -/
def sqrt67Pell : Pell.Solution₁ 67 :=
  Pell.Solution₁.mk 48842 5967 sqrt_67_identity

@[simp]
theorem sqrt_67_x : sqrt67Pell.x = 48842 := rfl

@[simp]
theorem sqrt_67_y : sqrt67Pell.y = 5967 := rfl

/-- `48842 + 5967√67` is the fundamental positive solution of the Pell equation. -/
theorem sqrt_67_fundamental :
    Pell.IsFundamental sqrt67Pell := by
  let M := integralContinuedMobius
    (completeIntBlock (Real.sqrt 67) 0 10)
  obtain ⟨hpell, hfund⟩ :=
    period_continuant_even
      (d := 67) (s := 10) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [sqrt67Real] using sqrt_dens_periodic)
      (by simpa [sqrt67Real] using sqrt_least_period.2)
      ⟨5, by norm_num⟩
  change Pell.IsFundamental (Pell.Solution₁.mk M.a M.c hpell) at hfund
  have hMa : M.a = 48842 := by
    dsimp only [M]
    rw [sqrt_67_ten]
    norm_num [integralContinuedMobius,
      ICMobius.prepend]
  have hMc : M.c = 5967 := by
    dsimp only [M]
    rw [sqrt_67_ten]
    norm_num [integralContinuedMobius,
      ICMobius.prepend]
  have heq :
      Pell.Solution₁.mk M.a M.c hpell = sqrt67Pell := by
    apply Pell.Solution₁.ext
    · simpa [sqrt67Pell] using hMa
    · simpa [sqrt67Pell] using hMc
  rwa [heq] at hfund

/-- The negative Pell equation for `d = 67` has no integral solutions. -/
theorem sqrt_67_impossible (x y : ℤ) :
    x ^ 2 - 67 * y ^ 2 ≠ -1 := by
  letI : Fact (Nat.Prime 67) := ⟨by decide⟩
  intro h
  have hz : (x : ZMod 67) ^ 2 = -1 := by
    have hz' := congrArg (fun z : ℤ ↦ (z : ZMod 67)) h
    have h67 : (67 : ZMod 67) = 0 := by decide
    simpa [h67] using hz'
  have hmod := ZMod.mod_four_ne_three_of_sq_eq_neg_one hz
  norm_num at hmod

/-- **Milne, Exercise 5-2.** Every unit of `ℤ[√67]` is, up to sign, an integral
power of `48842 + 5967√67`. -/
theorem sqrt_67_pell (z : ℤ√67) (hz : IsUnit z) :
    ∃ m : ℤ,
      z = ((sqrt67Pell ^ m : Pell.Solution₁ 67) : ℤ√67) ∨
      z = -((sqrt67Pell ^ m : Pell.Solution₁ 67) : ℤ√67) := by
  have hnorm : z.re ^ 2 - 67 * z.im ^ 2 = 1 := by
    rw [zsqrtd_pell_equation] at hz
    rcases hz with hplus | hminus
    · exact hplus
    · exact (sqrt_67_impossible z.re z.im hminus).elim
  let a : Pell.Solution₁ 67 := Pell.Solution₁.mk z.re z.im hnorm
  obtain ⟨m, h | h⟩ := sqrt_67_fundamental.eq_zpow_or_neg_zpow a
  · refine ⟨m, Or.inl ?_⟩
    simpa [a] using congrArg (fun w : Pell.Solution₁ 67 ↦ (w : ℤ√67)) h
  · refine ⟨m, Or.inr ?_⟩
    simpa [a] using congrArg (fun w : Pell.Solution₁ 67 ↦ (w : ℤ√67)) h

/-- Exercise 5-2's fundamental unit, transported from `ℤ[√67]` to the full ring of
integers of `ℚ(√67)`. -/
noncomputable def sqrt67Fundamental :
    (NumberField.RingOfIntegers (QFModel 67))ˣ :=
  (Units.mapEquiv sqrt67Integers.toMulEquiv).symm
    (Unitary.toUnits sqrt67Pell)

/-- **Milne, Exercise 5-2, field-level form.** Every unit in the full ring of integers
of `ℚ(√67)` is, up to sign, an integral power of `48842 + 5967√67`. -/
theorem sqrt_6_biquadratic
    (u : (NumberField.RingOfIntegers (QFModel 67))ˣ) :
    ∃ m : ℤ, u = sqrt67Fundamental ^ m ∨
      u = (-1 : (NumberField.RingOfIntegers (QFModel 67))ˣ) *
        sqrt67Fundamental ^ m := by
  let E := Units.mapEquiv sqrt67Integers.toMulEquiv
  have hfund : E sqrt67Fundamental = Unitary.toUnits sqrt67Pell := by
    exact E.apply_symm_apply (Unitary.toUnits sqrt67Pell)
  obtain ⟨m, h | h⟩ :=
    sqrt_67_pell (E u : ℤ√67) (E u).isUnit
  · refine ⟨m, Or.inl ?_⟩
    have hpow :
        ((((Unitary.toUnits sqrt67Pell) ^ m : (ℤ√67)ˣ)) : ℤ√67) =
          ((sqrt67Pell ^ m : Pell.Solution₁ 67) : ℤ√67) := by
      rw [← map_zpow
        (Unitary.toUnits : unitary (ℤ√(67 : ℤ)) →* (ℤ√(67 : ℤ))ˣ)]
      rfl
    have hu : E u = (Unitary.toUnits sqrt67Pell) ^ m := by
      apply Units.ext
      exact h.trans hpow.symm
    apply E.injective
    rw [map_zpow, hfund]
    exact hu
  · refine ⟨m, Or.inr ?_⟩
    have hpow :
        ((((Unitary.toUnits sqrt67Pell) ^ m : (ℤ√67)ˣ)) : ℤ√67) =
          ((sqrt67Pell ^ m : Pell.Solution₁ 67) : ℤ√67) := by
      rw [← map_zpow
        (Unitary.toUnits : unitary (ℤ√(67 : ℤ)) →* (ℤ√(67 : ℤ))ˣ)]
      rfl
    have hu : E u = (-1 : (ℤ√67)ˣ) *
        (Unitary.toUnits sqrt67Pell) ^ m := by
      apply Units.ext
      change (E u : ℤ√67) = -1 *
        ((((Unitary.toUnits sqrt67Pell) ^ m : (ℤ√67)ˣ)) : ℤ√67)
      rw [neg_one_mul]
      exact h.trans (congrArg Neg.neg hpow).symm
    have hnegOne : E (-1) = (-1 : (ℤ√67)ˣ) := by
      apply Units.ext
      change sqrt67Integers (-1) = -1
      simp
    apply E.injective
    rw [map_mul, hnegOne, map_zpow, hfund]
    exact hu

end Submission.NumberTheory.Milne
