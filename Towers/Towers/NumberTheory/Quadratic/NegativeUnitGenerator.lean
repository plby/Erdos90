import Towers.NumberTheory.Quadratic.ContinuedFractionMinimality

/-!
# Milne, Algebraic Number Theory, generators from negative Pell units

This file supplies the group-theoretic half of the odd-period case in Milne's construction of
fundamental units.  A positive solution of the negative Pell equation whose second coefficient
is minimal among all positive Pell-type solutions generates every unit of `ℤ[√d]` up to sign.
-/

namespace Towers.NumberTheory.Milne

/-- The unit `a + c√d` attached to a solution of `a² - dc² = -1`. -/
def zsqrtdNegOne {d a c : ℤ}
    (h : a ^ 2 - d * c ^ 2 = -1) : (ℤ√d)ˣ where
  val := ⟨a, c⟩
  inv := ⟨-a, c⟩
  val_inv := by
    ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> nlinarith
  inv_val := by
    ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> nlinarith

@[simp]
theorem zsqrtd_neg_val {d a c : ℤ}
    (h : a ^ 2 - d * c ^ 2 = -1) :
    ((zsqrtdNegOne h : (ℤ√d)ˣ) : ℤ√d) = ⟨a, c⟩ := rfl

@[simp]
theorem zsqrtd_inv_val {d a c : ℤ}
    (h : a ^ 2 - d * c ^ 2 = -1) :
    (((zsqrtdNegOne h : (ℤ√d)ˣ)⁻¹ : (ℤ√d)ˣ) : ℤ√d) =
      ⟨-a, c⟩ := rfl

/-- Positive-quadrant descent for a minimal solution of the negative Pell equation. -/
theorem quadrant_minimal_pell
    {d a c : ℤ} (hd : 2 ≤ d) (ha : 0 < a) (hc : 0 < c)
    (heta : a ^ 2 - d * c ^ 2 = -1)
    (hmin : ∀ {p q : ℤ}, 0 < p → 0 < q →
      (p ^ 2 - d * q ^ 2 = 1 ∨ p ^ 2 - d * q ^ 2 = -1) → c ≤ q)
    (u : (ℤ√d)ˣ) (hure : 0 < (u : ℤ√d).re)
    (huim : 0 ≤ (u : ℤ√d).im) :
    ∃ n : ℕ, u = zsqrtdNegOne heta ^ n := by
  let eta : (ℤ√d)ˣ := zsqrtdNegOne heta
  lift (u : ℤ√d).im to ℕ using huim with q hq
  induction q using Nat.strong_induction_on generalizing u with
  | h q ih =>
      have hnorm : Zsqrtd.norm (u : ℤ√d) = 1 ∨
          Zsqrtd.norm (u : ℤ√d) = -1 := by
        have habs : (Zsqrtd.norm (u : ℤ√d)).natAbs = 1 :=
          Zsqrtd.norm_eq_one_iff.mpr u.isUnit
        simpa using Int.natAbs_eq_iff.mp habs
      have hnorm' : (u : ℤ√d).re ^ 2 - d * (u : ℤ√d).im ^ 2 = 1 ∨
          (u : ℤ√d).re ^ 2 - d * (u : ℤ√d).im ^ 2 = -1 := by
        rcases hnorm with hplus | hminus
        · left
          rw [Zsqrtd.norm_def] at hplus
          nlinarith
        · right
          rw [Zsqrtd.norm_def] at hminus
          nlinarith
      by_cases hq0 : q = 0
      · subst q
        have huim0 : (u : ℤ√d).im = 0 := hq.symm
        have hure1 : (u : ℤ√d).re = 1 := by
          rcases hnorm' with hplus | hminus
          · have hre : (u : ℤ√d).re = 1 ∨ (u : ℤ√d).re = -1 := by
              apply sq_eq_one_iff.mp
              simpa [huim0] using hplus
            rcases hre with hre | hre
            · exact hre
            · nlinarith
          · rw [huim0] at hminus
            norm_num at hminus
            nlinarith [sq_nonneg (u : ℤ√d).re]
        refine ⟨0, ?_⟩
        apply Units.ext
        apply Zsqrtd.ext
        · simpa using hure1
        · simpa using huim0
      · have hqPosNat : 0 < q := Nat.pos_of_ne_zero hq0
        have huim : 0 ≤ (u : ℤ√d).im := by
          rw [← hq]
          positivity
        have hqPos : 0 < (u : ℤ√d).im := by
          rw [← hq]
          exact_mod_cast hqPosNat
        have hcLe : c ≤ (u : ℤ√d).im :=
          hmin hure hqPos hnorm'
        let v : (ℤ√d)ˣ := u * eta⁻¹
        have hvre : (v : ℤ√d).re =
            d * (u : ℤ√d).im * c - (u : ℤ√d).re * a := by
          simp only [v, eta, Units.val_mul, zsqrtd_inv_val,
            Zsqrtd.re_mul]
          ring
        have hvim : (v : ℤ√d).im =
            (u : ℤ√d).re * c - a * (u : ℤ√d).im := by
          simp only [v, eta, Units.val_mul, zsqrtd_inv_val,
            Zsqrtd.im_mul]
          ring
        have hpcNonneg : 0 ≤ (u : ℤ√d).re * c :=
          (mul_pos hure hc).le
        have haqNonneg : 0 ≤ a * (u : ℤ√d).im :=
          mul_nonneg ha.le huim
        have hvimNonneg : 0 ≤ (v : ℤ√d).im := by
          rw [hvim]
          apply sub_nonneg.mpr
          rcases hnorm' with hplus | hminus
          · apply (sq_le_sq₀ haqNonneg hpcNonneg).1
            calc
              (a * (u : ℤ√d).im) ^ 2 =
                  ((u : ℤ√d).re * c) ^ 2 -
                    (c ^ 2 + (u : ℤ√d).im ^ 2) := by
                nlinarith [hplus, heta]
              _ ≤ ((u : ℤ√d).re * c) ^ 2 := by
                nlinarith [sq_nonneg c, sq_nonneg (u : ℤ√d).im]
          · apply (sq_le_sq₀ haqNonneg hpcNonneg).1
            have hqSq : c ^ 2 ≤ (u : ℤ√d).im ^ 2 :=
              (sq_le_sq₀ hc.le huim).2 hcLe
            nlinarith [hminus, heta]
        have hvrePos : 0 < (v : ℤ√d).re := by
          rw [hvre]
          have hleftNonneg : 0 ≤ (u : ℤ√d).re * a :=
            (mul_pos hure ha).le
          have hrightNonneg : 0 ≤ d * (u : ℤ√d).im * c := by
            positivity
          rw [sub_pos]
          apply (sq_lt_sq₀ hleftNonneg hrightNonneg).1
          rcases hnorm' with hplus | hminus
          · have hqSq : c ^ 2 ≤ (u : ℤ√d).im ^ 2 :=
              (sq_le_sq₀ hc.le huim).2 hcLe
            nlinarith [hplus, heta]
          · nlinarith [hminus, heta, sq_nonneg ((u : ℤ√d).re - a)]
        have hvimLt : (v : ℤ√d).im < (u : ℤ√d).im := by
          rw [hvim, sub_lt_iff_lt_add]
          have hleftNonneg : 0 ≤ (u : ℤ√d).re * c :=
            (mul_pos hure hc).le
          have hrightPos : 0 < (a + 1) * (u : ℤ√d).im := by
            positivity
          have hlt : (u : ℤ√d).re * c < (a + 1) * (u : ℤ√d).im := by
            apply (sq_lt_sq₀ hleftNonneg hrightPos.le).1
            rcases hnorm' with hplus | hminus
            · have hqSq : c ^ 2 ≤ (u : ℤ√d).im ^ 2 :=
                (sq_le_sq₀ hc.le huim).2 hcLe
              nlinarith [hplus, heta]
            · nlinarith [hminus, heta]
          nlinarith
        lift (v : ℤ√d).im to ℕ using hvimNonneg with q' hq'
        have hq'lt : q' < q := by
          exact_mod_cast (show (q' : ℤ) < q by simpa [hq, hq'] using hvimLt)
        obtain ⟨n, hn⟩ := ih q' hq'lt v hvrePos hq'
        refine ⟨n + 1, ?_⟩
        calc
          u = v * eta := by simp [v]
          _ = eta ^ n * eta := by rw [hn]
          _ = eta ^ (n + 1) := by rw [pow_succ]

private theorem zsqrtd_inv_star {d : ℤ}
    (u : (ℤ√d)ˣ) (hnorm : Zsqrtd.norm (u : ℤ√d) = 1) :
    ((u⁻¹ : (ℤ√d)ˣ) : ℤ√d) = star (u : ℤ√d) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [← Zsqrtd.norm_eq_mul_conj, hnorm]
  norm_num

private theorem zsqrtd_val_star {d : ℤ}
    (u : (ℤ√d)ˣ) (hnorm : Zsqrtd.norm (u : ℤ√d) = -1) :
    ((u⁻¹ : (ℤ√d)ˣ) : ℤ√d) = -star (u : ℤ√d) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [mul_neg, ← Zsqrtd.norm_eq_mul_conj, hnorm]
  norm_num

/-- A minimal positive solution of the negative Pell equation generates the full unit group of
`ℤ[√d]`, up to sign. -/
theorem zpow_minimal_pell
    {d a c : ℤ} (hd : 2 ≤ d) (ha : 0 < a) (hc : 0 < c)
    (heta : a ^ 2 - d * c ^ 2 = -1)
    (hmin : ∀ {p q : ℤ}, 0 < p → 0 < q →
      (p ^ 2 - d * q ^ 2 = 1 ∨ p ^ 2 - d * q ^ 2 = -1) → c ≤ q)
    (u : (ℤ√d)ˣ) :
    ∃ n : ℤ, u = zsqrtdNegOne heta ^ n ∨
      u = -zsqrtdNegOne heta ^ n := by
  let eta : (ℤ√d)ˣ := zsqrtdNegOne heta
  have hpositive (w : (ℤ√d)ˣ) (hwre : 0 < (w : ℤ√d).re) :
      ∃ n : ℤ, w = eta ^ n ∨ w = -eta ^ n := by
    have hnorm : Zsqrtd.norm (w : ℤ√d) = 1 ∨
        Zsqrtd.norm (w : ℤ√d) = -1 := by
      have habs : (Zsqrtd.norm (w : ℤ√d)).natAbs = 1 :=
        Zsqrtd.norm_eq_one_iff.mpr w.isUnit
      simpa using Int.natAbs_eq_iff.mp habs
    by_cases hwim : 0 ≤ (w : ℤ√d).im
    · obtain ⟨n, hn⟩ := quadrant_minimal_pell
        hd ha hc heta hmin w hwre hwim
      refine ⟨n, Or.inl ?_⟩
      simpa [eta] using hn
    · have hwimNeg : (w : ℤ√d).im < 0 := lt_of_not_ge hwim
      rcases hnorm with hnorm | hnorm
      · let v : (ℤ√d)ˣ := w⁻¹
        have hvre : 0 < (v : ℤ√d).re := by
          simp only [v, zsqrtd_inv_star w hnorm,
            Zsqrtd.re_star]
          exact hwre
        have hvim : 0 ≤ (v : ℤ√d).im := by
          simp only [v, zsqrtd_inv_star w hnorm,
            Zsqrtd.im_star]
          linarith
        obtain ⟨n, hn⟩ := quadrant_minimal_pell
          hd ha hc heta hmin v hvre hvim
        refine ⟨-(n : ℤ), Or.inl ?_⟩
        calc
          w = v⁻¹ := by simp [v]
          _ = (eta ^ n)⁻¹ := congrArg Inv.inv (by simpa [eta] using hn)
          _ = eta ^ (-(n : ℤ)) := by simp
      · let v : (ℤ√d)ˣ := -w⁻¹
        have hvre : 0 < (v : ℤ√d).re := by
          simp only [v, Units.val_neg,
            zsqrtd_val_star w hnorm,
            Zsqrtd.re_star, neg_neg]
          exact hwre
        have hvim : 0 ≤ (v : ℤ√d).im := by
          simp only [v, Units.val_neg,
            zsqrtd_val_star w hnorm,
            Zsqrtd.im_star, neg_neg]
          linarith
        obtain ⟨n, hn⟩ := quadrant_minimal_pell
          hd ha hc heta hmin v hvre hvim
        have hwinv : w⁻¹ = -eta ^ n := by
          calc
            w⁻¹ = -v := by simp [v]
            _ = -eta ^ n := congrArg Neg.neg (by simpa [eta] using hn)
        refine ⟨-(n : ℤ), Or.inr ?_⟩
        calc
          w = (w⁻¹)⁻¹ := (inv_inv w).symm
          _ = (-eta ^ n)⁻¹ := congrArg Inv.inv hwinv
          _ = -(eta ^ (-(n : ℤ))) := by simp
  by_cases hure : 0 < (u : ℤ√d).re
  · simpa [eta] using hpositive u hure
  · have hnorm : Zsqrtd.norm (u : ℤ√d) = 1 ∨
        Zsqrtd.norm (u : ℤ√d) = -1 := by
      have habs : (Zsqrtd.norm (u : ℤ√d)).natAbs = 1 :=
        Zsqrtd.norm_eq_one_iff.mpr u.isUnit
      simpa using Int.natAbs_eq_iff.mp habs
    have hureNe : (u : ℤ√d).re ≠ 0 := by
      intro hzero
      rcases hnorm with hnorm | hnorm
      · rw [Zsqrtd.norm_def, hzero] at hnorm
        nlinarith [sq_nonneg (u : ℤ√d).im]
      · rw [Zsqrtd.norm_def, hzero] at hnorm
        have himNe : (u : ℤ√d).im ≠ 0 := by
          intro him
          rw [him] at hnorm
          norm_num at hnorm
        have himSq : 1 ≤ (u : ℤ√d).im ^ 2 :=
          (one_le_sq_iff_one_le_abs _).2 (Int.one_le_abs himNe)
        nlinarith
    have hnegure : 0 < ((-u : (ℤ√d)ˣ) : ℤ√d).re := by
      simp only [Units.val_neg, Zsqrtd.re_neg]
      have : (u : ℤ√d).re < 0 := lt_of_le_of_ne (not_lt.mp hure) hureNe
      linarith
    obtain ⟨n, hn | hn⟩ := hpositive (-u) hnegure
    · refine ⟨n, Or.inr ?_⟩
      simpa [eta] using congrArg Neg.neg hn
    · refine ⟨n, Or.inl ?_⟩
      simpa [eta] using congrArg Neg.neg hn

/-- For an odd least period, the period endpoint has norm `-1` and generates every unit of
`ℤ[√d]` up to sign. -/
theorem period_continuant_odd
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
    (hsodd : Odd s) :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt d) 0 s)
    ∃ hpell : M.a ^ 2 - (d : ℤ) * M.c ^ 2 = -1,
      ∀ u : (ℤ√(d : ℤ))ˣ, ∃ n : ℤ,
        u = zsqrtdNegOne hpell ^ n ∨
          u = -zsqrtdNegOne hpell ^ n := by
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
  have hsodd' : Odd (j + 1) := by simpa only using hsodd
  have hpell : M.a ^ 2 - (d : ℤ) * M.c ^ 2 = -1 := by
    rw [hpellSigned, Odd.neg_one_pow hsodd']
  refine ⟨hpell, ?_⟩
  intro u
  apply zpow_minimal_pell
    (d := (d : ℤ)) (a := M.a) (c := M.c) (heta := hpell)
  · exact_mod_cast hdge
  · exact haPos
  · exact hcPos
  · intro p q hp hq hpell'
    simpa only [M, qs] using
      period_continuant_pell hdge hd (Nat.succ_pos j)
        hperiod hleast hp hq hpell'

/-- For an even least period, the period endpoint also generates every unit of `ℤ[√d]` up
to sign.  The even period excludes negative-norm units, so the fundamental ordinary Pell
solution generates the full unit group. -/
theorem sqrt_period_continuant
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
    ∃ v : (ℤ√(d : ℤ))ˣ,
      (v : ℤ√(d : ℤ)) = ⟨M.a, M.c⟩ ∧
      ∀ u : (ℤ√(d : ℤ))ˣ, ∃ n : ℤ,
        u = v ^ n ∨ u = -v ^ n := by
  let M := integralContinuedMobius
    (completeIntBlock (Real.sqrt d) 0 s)
  obtain ⟨hpell, hfund⟩ :=
    period_continuant_even
      hdge hd hs hperiod hleast hseven
  let a : Pell.Solution₁ (d : ℤ) := Pell.Solution₁.mk M.a M.c hpell
  let v : (ℤ√(d : ℤ))ˣ := Unitary.toUnits a
  refine ⟨v, rfl, ?_⟩
  intro u
  have hnorm : Zsqrtd.norm (u : ℤ√(d : ℤ)) = 1 ∨
      Zsqrtd.norm (u : ℤ√(d : ℤ)) = -1 := by
    have habs : (Zsqrtd.norm (u : ℤ√(d : ℤ))).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr u.isUnit
    simpa using Int.natAbs_eq_iff.mp habs
  have hnormOne : Zsqrtd.norm (u : ℤ√(d : ℤ)) = 1 := by
    rcases hnorm with hnorm | hnorm
    · exact hnorm
    · exfalso
      have hminus :
          (u : ℤ√(d : ℤ)).re ^ 2 - (d : ℤ) * (u : ℤ√(d : ℤ)).im ^ 2 = -1 := by
        rw [Zsqrtd.norm_def] at hnorm
        nlinarith
      have himNe : (u : ℤ√(d : ℤ)).im ≠ 0 := by
        intro him
        rw [him] at hminus
        norm_num at hminus
        nlinarith [sq_nonneg (u : ℤ√(d : ℤ)).re]
      have hreNe : (u : ℤ√(d : ℤ)).re ≠ 0 := by
        intro hre
        rw [hre] at hminus
        have himSq : 1 ≤ (u : ℤ√(d : ℤ)).im ^ 2 :=
          (one_le_sq_iff_one_le_abs _).2 (Int.one_le_abs himNe)
        have hdgeZ : (2 : ℤ) ≤ d := by exact_mod_cast hdge
        nlinarith
      exact pell_even_period
        hdge hd hs hperiod hleast hseven
        ⟨|(u : ℤ√(d : ℤ)).re|, |(u : ℤ√(d : ℤ)).im|,
          abs_pos.mpr hreNe, abs_pos.mpr himNe, by
            simpa only [sq_abs] using hminus⟩
  have hprop :
      (u : ℤ√(d : ℤ)).re ^ 2 - (d : ℤ) * (u : ℤ√(d : ℤ)).im ^ 2 = 1 := by
    rw [Zsqrtd.norm_def] at hnormOne
    nlinarith
  let b : Pell.Solution₁ (d : ℤ) :=
    Pell.Solution₁.mk (u : ℤ√(d : ℤ)).re (u : ℤ√(d : ℤ)).im hprop
  have hbu : Unitary.toUnits b = u := Units.ext rfl
  obtain ⟨n, hn | hn⟩ := hfund.eq_zpow_or_neg_zpow b
  · refine ⟨n, Or.inl ?_⟩
    calc
      u = Unitary.toUnits b := hbu.symm
      _ = Unitary.toUnits (a ^ n) := congrArg Unitary.toUnits hn
      _ = (Unitary.toUnits a) ^ n :=
        map_zpow (Unitary.toUnits : unitary (ℤ√(d : ℤ)) →* (ℤ√(d : ℤ))ˣ) a n
      _ = v ^ n := rfl
  · refine ⟨n, Or.inr ?_⟩
    calc
      u = Unitary.toUnits b := hbu.symm
      _ = Unitary.toUnits (-a ^ n) := congrArg Unitary.toUnits hn
      _ = -Unitary.toUnits (a ^ n) := by apply Units.ext; rfl
      _ = -(Unitary.toUnits a) ^ n := by
        exact congrArg Neg.neg
          (map_zpow (Unitary.toUnits : unitary (ℤ√(d : ℤ)) →* (ℤ√(d : ℤ))ˣ) a n)
      _ = -v ^ n := rfl

/-- The period-minus-one convergent gives a generator of `ℤ[√d]ˣ` for either parity of the
least continued-fraction period. -/
theorem unit_period_continuant
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
        s ≤ p) :
    let M := integralContinuedMobius
      (completeIntBlock (Real.sqrt d) 0 s)
    ∃ v : (ℤ√(d : ℤ))ˣ,
      (v : ℤ√(d : ℤ)) = ⟨M.a, M.c⟩ ∧
      ∀ u : (ℤ√(d : ℤ))ˣ, ∃ n : ℤ,
        u = v ^ n ∨ u = -v ^ n := by
  rcases Nat.even_or_odd s with hseven | hsodd
  · exact sqrt_period_continuant
      hdge hd hs hperiod hleast hseven
  · obtain ⟨hpell, hgen⟩ :=
      period_continuant_odd
        hdge hd hs hperiod hleast hsodd
    exact ⟨zsqrtdNegOne hpell, rfl, hgen⟩

end Towers.NumberTheory.Milne
