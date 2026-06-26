import Towers.NumberTheory.Quadratic.QuadraticUnitExamples

/-!
# Milne, Algebraic Number Theory, the integral and half-integral quadratic orders

For `d = 4A + 1`, the full quadratic order is represented by
`QuadraticAlgebra ℤ A 1 = ℤ[(1 + √d) / 2]`.  The suborder `ℤ[√d]` consists exactly of the
elements whose second coordinate is even.  This file proves the elementary exponent-three and
modulo-eight facts behind Milne's description of the fundamental unit.
-/

namespace Towers.NumberTheory.Milne

/-- The inclusion `ℤ[√(4A+1)] ⊆ ℤ[(1+√(4A+1))/2]`. -/
def zsqrtdQuadraticOrder (A : ℤ) :
    ℤ√(4 * A + 1) →+* QuadraticAlgebra ℤ A 1 where
  toFun z := ⟨z.re - z.im, 2 * z.im⟩
  map_zero' := by
    apply QuadraticAlgebra.ext <;> simp
  map_one' := by
    apply QuadraticAlgebra.ext <;>
      norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by
    apply QuadraticAlgebra.ext <;>
      simp only [Zsqrtd.re_add, Zsqrtd.im_add, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add] <;> ring
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, QuadraticAlgebra.re_mul]
      ring
    · simp only [Zsqrtd.im_mul, QuadraticAlgebra.im_mul]
      ring

@[simp]
theorem zsqrtd_half_re (A : ℤ) (z : ℤ√(4 * A + 1)) :
    (zsqrtdQuadraticOrder A z).re = z.re - z.im := rfl

@[simp]
theorem zsqrtd_half_im (A : ℤ) (z : ℤ√(4 * A + 1)) :
    (zsqrtdQuadraticOrder A z).im = 2 * z.im := rfl

theorem zsqrtd_half_injective (A : ℤ) :
    Function.Injective (zsqrtdQuadraticOrder A) := by
  intro x y hxy
  have him := congrArg QuadraticAlgebra.im hxy
  have hre := congrArg QuadraticAlgebra.re hxy
  simp only [zsqrtd_half_im] at him
  simp only [zsqrtd_half_re] at hre
  apply Zsqrtd.ext
  · omega
  · omega

/-- The image of `ℤ[√(4A+1)]` is exactly the even-coordinate suborder. -/
theorem range_zsqrtd_half
    (A : ℤ) (z : QuadraticAlgebra ℤ A 1) :
    z ∈ Set.range (zsqrtdQuadraticOrder A) ↔ Even z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.im, by simp [two_mul]⟩
  · rintro ⟨q, hq⟩
    refine ⟨(⟨z.re + q, q⟩ : ℤ√(4 * A + 1)), ?_⟩
    apply QuadraticAlgebra.ext
    · simp only [zsqrtd_half_re]
      omega
    · simp only [zsqrtd_half_im]
      omega

/-- The suborder embedding preserves the quadratic norm. -/
theorem zsqrtd_half_order
    (A : ℤ) (z : ℤ√(4 * A + 1)) :
    QuadraticAlgebra.norm (zsqrtdQuadraticOrder A z) = Zsqrtd.norm z := by
  simp only [QuadraticAlgebra.norm_def, zsqrtd_half_re,
    zsqrtd_half_im, Zsqrtd.norm_def]
  ring

/-- The inclusion of the integral quadratic suborder reflects units. -/
theorem zsqrtd_half_quadratic
    (A : ℤ) (z : ℤ√(4 * A + 1)) :
    IsUnit (zsqrtdQuadraticOrder A z) ↔ IsUnit z := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit,
    zsqrtd_half_order, ← Zsqrtd.isUnit_iff_norm_isUnit]

/-- The induced inclusion on unit groups. -/
def zsqrtdHalfOrder (A : ℤ) :
    (ℤ√(4 * A + 1))ˣ →* (QuadraticAlgebra ℤ A 1)ˣ :=
  Units.map (zsqrtdQuadraticOrder A).toMonoidHom

/-- The second coordinate of a cube, expressed through trace and norm. -/
theorem half_cube_im (A : ℤ) (z : QuadraticAlgebra ℤ A 1) :
    (z ^ 3).im =
      ((2 * z.re + z.im) ^ 2 - QuadraticAlgebra.norm z) * z.im := by
  rw [QuadraticAlgebra.norm_def]
  simp [pow_succ, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_mul]
  ring

/-- The cube of every unit in a half-integral quadratic order has even second coordinate. -/
theorem cube_im_even
    (A : ℤ) (z : QuadraticAlgebra ℤ A 1) (hz : IsUnit z) :
    Even (z ^ 3).im := by
  have hnorm : QuadraticAlgebra.norm z = 1 ∨ QuadraticAlgebra.norm z = -1 := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff] at hz
    exact hz
  rcases Int.even_or_odd' z.im with ⟨q, hq | hq⟩
  · refine ⟨(((2 * z.re + z.im) ^ 2 - QuadraticAlgebra.norm z) * q), ?_⟩
    rw [half_cube_im, hq]
    ring
  · rcases hnorm with hnorm | hnorm
    · refine ⟨(2 * (z.re + q) * (z.re + q + 1)) * z.im, ?_⟩
      rw [half_cube_im, hq, hnorm]
      ring
    · refine ⟨(2 * (z.re + q) ^ 2 + 2 * (z.re + q) + 1) * z.im, ?_⟩
      rw [half_cube_im, hq, hnorm]
      ring

/-- Cubing any unit of the full half-integral order lands in `ℤ[√(4A+1)]`. -/
theorem half_cube_zsqrtd
    (A : ℤ) (z : QuadraticAlgebra ℤ A 1) (hz : IsUnit z) :
    z ^ 3 ∈ Set.range (zsqrtdQuadraticOrder A) := by
  rw [range_zsqrtd_half]
  exact cube_im_even A z hz

/-- Every unit of the full half-integral order has its cube in the image of the unit group of
`ℤ[√(4A+1)]`. -/
theorem zsqrtd_unit_cube
    (A : ℤ) (u : (QuadraticAlgebra ℤ A 1)ˣ) :
    ∃ v : (ℤ√(4 * A + 1))ˣ,
      zsqrtdHalfOrder A v = u ^ 3 := by
  obtain ⟨z, hz⟩ :=
    half_cube_zsqrtd A
      (u : QuadraticAlgebra ℤ A 1) (Units.isUnit u)
  have hzunit : IsUnit z := by
    rw [← zsqrtd_half_quadratic]
    rw [hz]
    exact Units.isUnit (u ^ 3)
  refine ⟨hzunit.unit, ?_⟩
  apply Units.ext
  change zsqrtdQuadraticOrder A
      (hzunit.unit : ℤ√(4 * A + 1)) =
    ((u ^ 3 : (QuadraticAlgebra ℤ A 1)ˣ) :
      QuadraticAlgebra ℤ A 1)
  rw [hzunit.unit_spec, hz]
  rfl

private theorem eight_odd_even
    {A t n : ℤ} (hA : Even A) (ht : Odd t) (hn : Odd n) :
    8 ∣ t ^ 2 - (4 * A + 1) * n ^ 2 := by
  rcases hA with ⟨j, hj⟩
  rcases ht with ⟨u, hu⟩
  rcases hn with ⟨v, hv⟩
  rcases Int.even_mul_succ_self u with ⟨r, hr⟩
  rcases Int.even_mul_succ_self v with ⟨s, hs⟩
  refine ⟨r - s - j * (v + v + 1) ^ 2, ?_⟩
  rw [hj, hu, hv]
  nlinarith

/-- If `A` is even, every unit of `ℤ[(1+√(4A+1))/2]` already belongs to
`ℤ[√(4A+1)]`.  This is the congruence `d ≡ 1 (mod 8)` case in Milne's statement. -/
theorem half_im_even
    (A : ℤ) (hA : Even A) (z : QuadraticAlgebra ℤ A 1) (hz : IsUnit z) :
    Even z.im := by
  by_contra hnot
  have hn : Odd z.im := Int.not_even_iff_odd.mp hnot
  have ht : Odd (2 * z.re + z.im) := by
    rcases hn with ⟨q, hq⟩
    exact ⟨z.re + q, by omega⟩
  have hdiv : 8 ∣
      (2 * z.re + z.im) ^ 2 - (4 * A + 1) * z.im ^ 2 :=
    eight_odd_even hA ht hn
  obtain ⟨w, hw⟩ := hdiv
  rw [half_pell_equation] at hz
  rcases hz with hz | hz
  · rw [hz] at hw
    omega
  · rw [hz] at hw
    omega

/-- In the `d ≡ 1 (mod 8)` case, every unit of the full ring is in the integral suborder. -/
theorem half_zsqrtd_even
    (A : ℤ) (hA : Even A) (z : QuadraticAlgebra ℤ A 1) (hz : IsUnit z) :
    z ∈ Set.range (zsqrtdQuadraticOrder A) := by
  rw [range_zsqrtd_half]
  exact half_im_even A hA z hz

/-- For `d ≡ 1 (mod 8)`, the inclusion on unit groups is surjective. -/
theorem zsqrtd_half_even
    (A : ℤ) (hA : Even A) :
    Function.Surjective (zsqrtdHalfOrder A) := by
  intro u
  obtain ⟨z, hz⟩ :=
    half_zsqrtd_even A hA
      (u : QuadraticAlgebra ℤ A 1) (Units.isUnit u)
  have hzunit : IsUnit z := by
    rw [← zsqrtd_half_quadratic]
    rw [hz]
    exact Units.isUnit u
  refine ⟨hzunit.unit, ?_⟩
  apply Units.ext
  change zsqrtdQuadraticOrder A
      (hzunit.unit : ℤ√(4 * A + 1)) =
    (u : QuadraticAlgebra ℤ A 1)
  rw [hzunit.unit_spec, hz]

/-- If a rank-one unit subgroup contains every cube, its positive generator is either the
positive generator of the full group or its third power. -/
theorem generator_or_cube
    {G H : Type*} [CommGroup G] [CommGroup H]
    [HasDistribNeg G] [HasDistribNeg H]
    (f : G →* H) (v : G) (ε : H) (ρ : H →* ℝ)
    (hfneg : ∀ x, f (-x) = -f x)
    (hρneg : ∀ x, ρ (-x) = -ρ x)
    (hvgen : ∀ x : G, ∃ n : ℤ, x = v ^ n ∨ x = -v ^ n)
    (hεgen : ∀ x : H, ∃ n : ℤ, x = ε ^ n ∨ x = -ε ^ n)
    (hcube : ∀ x : H, ∃ y : G, f y = x ^ 3)
    (hεpos : 1 < ρ ε) (hvpos : 1 < ρ (f v)) :
    f v = ε ∨ ε ^ 3 = f v := by
  obtain ⟨m, hvm | hvm⟩ := hεgen (f v)
  · have hmPos : 0 < m := by
      by_contra hm
      have hmNonpos : m ≤ 0 := le_of_not_gt hm
      have hpowLe : ρ ε ^ m ≤ 1 := by
        exact zpow_le_one_of_nonpos₀ hεpos.le hmNonpos
      have hmap : ρ (f v) = ρ ε ^ m := by
        rw [hvm, MonoidHom.map_zpow]
      linarith
    obtain ⟨w, hw⟩ := hcube ε
    obtain ⟨n, hwn | hwn⟩ := hvgen w
    · have hpow : ε ^ (3 : ℤ) = ε ^ (m * n) := by
        calc
          ε ^ (3 : ℤ) = ε ^ (3 : ℕ) := by rw [zpow_ofNat]
          _ = f w := hw.symm
          _ = f (v ^ n) := by rw [hwn]
          _ = (f v) ^ n := map_zpow f v n
          _ = (ε ^ m) ^ n := by rw [hvm]
          _ = ε ^ (m * n) := by rw [zpow_mul]
      have hrealPow : ρ ε ^ (3 : ℤ) = ρ ε ^ (m * n) := by
        simpa only [MonoidHom.map_zpow] using congrArg ρ hpow
      have hmn : m * n = 3 :=
        (zpow_right_injective₀ (by positivity : 0 < ρ ε) hεpos.ne') hrealPow |>.symm
      have hnPos : 0 < n := by
        by_contra hn
        have hnNonpos : n ≤ 0 := le_of_not_gt hn
        have := mul_nonpos_of_nonneg_of_nonpos hmPos.le hnNonpos
        omega
      have hmLe : m ≤ 3 := by
        calc
          m = m * 1 := by ring
          _ ≤ m * n := mul_le_mul_of_nonneg_left hnPos (by omega)
          _ = 3 := hmn
      have hm : m = 1 ∨ m = 3 := by
        interval_cases m <;> omega
      rcases hm with rfl | rfl
      · exact Or.inl (by simpa using hvm)
      · exact Or.inr (by simpa only [zpow_ofNat] using hvm.symm)
    · have hreal : ρ ε ^ (3 : ℕ) = -(ρ ε ^ (m * n)) := by
        calc
          ρ ε ^ (3 : ℕ) = ρ (ε ^ (3 : ℕ)) := by rw [map_pow]
          _ = ρ (f w) := by rw [← hw]
          _ = ρ (f (-v ^ n)) := by rw [hwn]
          _ = ρ (-f (v ^ n)) := by rw [hfneg]
          _ = -ρ (f (v ^ n)) := hρneg _
          _ = -ρ ((f v) ^ n) :=
            congrArg (fun x ↦ -ρ x) (map_zpow f v n)
          _ = -(ρ (f v) ^ n) := congrArg Neg.neg (map_zpow ρ (f v) n)
          _ = -((ρ ε ^ m) ^ n) := by rw [hvm, map_zpow]
          _ = -(ρ ε ^ (m * n)) := by rw [zpow_mul]
      have hleft : 0 < ρ ε ^ (3 : ℕ) := by positivity
      have hright : 0 < ρ ε ^ (m * n) := zpow_pos (by positivity) _
      linarith
  · have hreal : ρ (f v) = -(ρ ε ^ m) := by
      calc
        ρ (f v) = ρ (-ε ^ m) := by rw [hvm]
        _ = -ρ (ε ^ m) := hρneg _
        _ = -(ρ ε ^ m) := by rw [map_zpow]
    have hpowPos : 0 < ρ ε ^ m := zpow_pos (by positivity) _
    linarith

end Towers.NumberTheory.Milne
