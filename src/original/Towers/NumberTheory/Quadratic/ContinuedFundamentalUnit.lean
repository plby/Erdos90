import Towers.NumberTheory.Quadratic.NegativeUnitGenerator
import Towers.NumberTheory.Quadratic.QuadraticUnitSuborder

/-!
# Milne, Algebraic Number Theory, the continued-fraction fundamental unit theorem

This file combines the continued-fraction minimality theorem with the comparison between
`ℤ[√d]` and the full half-integral quadratic order.  It formalizes the assertion on page 93:
the period-minus-one convergent is the positive fundamental unit in the integral-basis cases,
and in the remaining half-integral case it is either the fundamental unit or its cube.
-/

namespace Towers.NumberTheory.Milne

/-- The natural-number-indexed form of the inclusion
`ℤ[√(4A+1)] ⊆ ℤ[(1+√(4A+1))/2]`. -/
def zsqrtdHalfQuadratic (A : ℕ) :
    (ℤ√((4 * A + 1 : ℕ) : ℤ))ˣ →*
      (QuadraticAlgebra ℤ (A : ℤ) 1)ˣ := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    zsqrtdHalfOrder (A : ℤ)

/-- The real embedding of `ℤ[(1+√(4A+1))/2]` that sends the distinguished root to
`(1+√(4A+1))/2`. -/
noncomputable def halfRealEmbedding (A : ℕ) :
    QuadraticAlgebra ℤ (A : ℤ) 1 →+* ℝ :=
  (QuadraticAlgebra.lift (R := ℤ) (A := ℝ)
    ⟨(1 + Real.sqrt (4 * (A : ℝ) + 1)) / 2, by
      have hsqrt : Real.sqrt (4 * (A : ℝ) + 1) ^ 2 = 4 * (A : ℝ) + 1 := by
        rw [Real.sq_sqrt]
        positivity
      simp only [Int.cast_natCast, one_smul, Int.smul_one_eq_cast]
      nlinarith⟩).toRingHom

/-- Evaluation of units under the positive real embedding. -/
noncomputable def halfRealNat (A : ℕ) :
    (QuadraticAlgebra ℤ (A : ℤ) 1)ˣ →* ℝ :=
  (Units.coeHom ℝ).comp
    (Units.map (halfRealEmbedding A).toMonoidHom)

@[simp]
theorem half_real_neg (A : ℕ)
    (u : (QuadraticAlgebra ℤ (A : ℤ) 1)ˣ) :
    halfRealNat A (-u) =
      -halfRealNat A u := by
  change halfRealEmbedding A (-u.val) =
    -halfRealEmbedding A u.val
  simp

theorem half_real_zsqrtd
    (A : ℕ) (u : (ℤ√((4 * A + 1 : ℕ) : ℤ))ˣ) :
    halfRealNat A
        (zsqrtdHalfQuadratic A u) =
      (u : ℤ√((4 * A + 1 : ℕ) : ℤ)).re +
        (u : ℤ√((4 * A + 1 : ℕ) : ℤ)).im *
          Real.sqrt (4 * (A : ℝ) + 1) := by
  change halfRealEmbedding A
      (zsqrtdQuadraticOrder (A : ℤ) (u : ℤ√((4 * A + 1 : ℕ) : ℤ))) = _
  change halfRealEmbedding A
      (⟨(u : ℤ√((4 * A + 1 : ℕ) : ℤ)).re - (u : ℤ√((4 * A + 1 : ℕ) : ℤ)).im,
        2 * (u : ℤ√((4 * A + 1 : ℕ) : ℤ)).im⟩ :
          QuadraticAlgebra ℤ (A : ℤ) 1) = _
  rw [QuadraticAlgebra.mk_eq_add_smul_omega]
  simp [halfRealEmbedding, QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_ofNat]
  ring

/-- **Milne, page 93, real quadratic continued-fraction theorem.**

For `d = 4A+1`, let `p/q` be the convergent at the end of the least period of `√d`.
Its unit `p+q√d`, mapped to the full order, is either the positive fundamental unit `ε` or
`ε³`.  If `A` is even, equivalently `d ≡ 1 (mod 8)`, it is `ε` itself. -/
theorem period_convergent_cube
    {A s : ℕ} (hdge : 2 ≤ 4 * A + 1)
    (hd : ¬IsSquare (4 * A + 1)) (hs : 0 < s)
    (hperiod :
      Function.Periodic
        (fun n ↦
          (GenContFract.of
            (Real.sqrt ((4 * A + 1 : ℕ) : ℝ))).partDens.get? n) s)
    (hleast :
      ∀ p, 0 < p →
        Function.Periodic
          (fun n ↦
            (GenContFract.of
              (Real.sqrt ((4 * A + 1 : ℕ) : ℝ))).partDens.get? n) p →
        s ≤ p)
    (ε : (QuadraticAlgebra ℤ (A : ℤ) 1)ˣ)
    (hεgen : ∀ u : (QuadraticAlgebra ℤ (A : ℤ) 1)ˣ, ∃ n : ℤ,
      u = ε ^ n ∨ u = -ε ^ n)
    (hεpos : 1 < halfRealNat A ε) :
    let M := integralContinuedMobius
      (completeIntBlock
        (Real.sqrt ((4 * A + 1 : ℕ) : ℝ)) 0 s)
    ∃ v : (ℤ√((4 * A + 1 : ℕ) : ℤ))ˣ,
      (v : ℤ√((4 * A + 1 : ℕ) : ℤ)) = ⟨M.a, M.c⟩ ∧
      (zsqrtdHalfQuadratic A v = ε ∨
        ε ^ 3 = zsqrtdHalfQuadratic A v) ∧
      (Even A → zsqrtdHalfQuadratic A v = ε) := by
  let M := integralContinuedMobius
    (completeIntBlock
      (Real.sqrt ((4 * A + 1 : ℕ) : ℝ)) 0 s)
  obtain ⟨v, hv, hvgen⟩ :=
    unit_period_continuant hdge hd hs hperiod hleast
  have hqsPos : ∀ q ∈ completeIntBlock
      (Real.sqrt ((4 * A + 1 : ℕ) : ℝ)) 0 s, 0 < q :=
    complete_sqrt_pos hd s
  have haPos : 0 < M.a :=
    continued_mobius_pos hqsPos
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have hcPos : 0 < M.c := by
    change 0 <
      (integralContinuedMobius
        (⌊completeQuotient 0 (Real.sqrt ((4 * A + 1 : ℕ) : ℝ))⌋ ::
          completeIntBlock
            (Real.sqrt ((4 * A + 1 : ℕ) : ℝ)) 1 j)).c
    apply continued_mobius_c
    simpa only [completeIntBlock] using hqsPos
  have hvReal :
      1 < halfRealNat A
        (zsqrtdHalfQuadratic A v) := by
    rw [half_real_zsqrtd, hv]
    have hsqrtPos : 0 < Real.sqrt (4 * (A : ℝ) + 1) := by positivity
    have haPosReal : (0 : ℝ) < M.a := by exact_mod_cast haPos
    have hcPosReal : (0 : ℝ) < M.c := by exact_mod_cast hcPos
    have haOne : (1 : ℝ) ≤ M.a := by exact_mod_cast haPos
    nlinarith [mul_pos hcPosReal hsqrtPos]
  have hcube (u : (QuadraticAlgebra ℤ (A : ℤ) 1)ˣ) :
      ∃ w : (ℤ√((4 * A + 1 : ℕ) : ℤ))ˣ,
        zsqrtdHalfQuadratic A w = u ^ 3 := by
    simpa only [zsqrtdHalfQuadratic, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] using
        zsqrtd_unit_cube (A : ℤ) u
  have hmapNeg (x : (ℤ√((4 * A + 1 : ℕ) : ℤ))ˣ) :
      zsqrtdHalfQuadratic A (-x) =
        -zsqrtdHalfQuadratic A x := by
    apply Units.ext
    change zsqrtdQuadraticOrder (A : ℤ) (-x.val) =
      -zsqrtdQuadraticOrder (A : ℤ) x.val
    exact map_neg (zsqrtdQuadraticOrder (A : ℤ)) x.val
  have hcomparison := generator_or_cube
    (zsqrtdHalfQuadratic A) v ε
    (halfRealNat A)
    hmapNeg
    (half_real_neg A)
    hvgen hεgen hcube hεpos hvReal
  refine ⟨v, hv, hcomparison, ?_⟩
  intro hA
  have hAZ : Even (A : ℤ) := by exact_mod_cast hA
  have hsurj : Function.Surjective (zsqrtdHalfQuadratic A) := by
    simpa only [zsqrtdHalfQuadratic, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] using
        zsqrtd_half_even (A : ℤ) hAZ
  rcases hcomparison with hcomparison | hcomparison
  · exact hcomparison
  · obtain ⟨w, hw⟩ := hsurj ε
    obtain ⟨n, hn | hn⟩ := hvgen w
    · have hpow : ε ^ (1 : ℤ) = ε ^ (3 * n) := by
        calc
          ε ^ (1 : ℤ) = ε := zpow_one ε
          _ = zsqrtdHalfQuadratic A w := hw.symm
          _ = zsqrtdHalfQuadratic A (v ^ n) := by rw [hn]
          _ = (zsqrtdHalfQuadratic A v) ^ n :=
            map_zpow (zsqrtdHalfQuadratic A) v n
          _ = (ε ^ 3) ^ n := by rw [← hcomparison]
          _ = ε ^ (3 * n) := by rw [zpow_mul, zpow_ofNat]
      have hrealPow :
          halfRealNat A ε ^ (1 : ℤ) =
            halfRealNat A ε ^ (3 * n) := by
        simpa only [MonoidHom.map_zpow] using
          congrArg (halfRealNat A) hpow
      have : (1 : ℤ) = 3 * n :=
        (zpow_right_injective₀ (by positivity) hεpos.ne') hrealPow
      omega
    · have hreal :
          halfRealNat A ε =
            -(halfRealNat A ε ^ (3 * n)) := by
        calc
          halfRealNat A ε =
              halfRealNat A
                (zsqrtdHalfQuadratic A w) := by rw [hw]
          _ = halfRealNat A
                (zsqrtdHalfQuadratic A (-v ^ n)) := by rw [hn]
          _ = -halfRealNat A
                (zsqrtdHalfQuadratic A (v ^ n)) := by
              rw [hmapNeg, half_real_neg]
          _ = -(halfRealNat A ε ^ (3 * n)) := by
              rw [map_zpow, map_zpow, ← hcomparison, map_pow, zpow_mul, zpow_ofNat]
      have hright :
          0 < halfRealNat A ε ^ (3 * n) :=
        zpow_pos (by positivity) _
      linarith

end Towers.NumberTheory.Milne
