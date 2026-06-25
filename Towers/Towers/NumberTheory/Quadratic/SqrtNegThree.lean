import Towers.NumberTheory.Eisenstein.Euclidean

/-!
# Milne, Algebraic Number Theory, Example 2.10(b)

Unique factorization fails in `ℤ[√-3]` because
`4 = 2 · 2 = (1 + √-3)(1 - √-3)`.
-/

namespace Towers.NumberTheory.Milne

abbrev SNThree := ℤ√(-3)

namespace SNThree

/-- The natural inclusion
`ℤ[√-3] → ℤ[(1 + √-3) / 2]`, sending `√-3` to `2ω - 1`. -/
def toEisenstein : SNThree →+*
    Towers.NumberTheory.EInts where
  toFun x := ⟨x.re - x.im, 2 * x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by
    ext <;> norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by
    ext <;>
      simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;>
      ring

/-- The natural map from `ℤ[√-3]` to the Eisenstein integers is injective. -/
theorem toEisenstein_injective : Function.Injective toEisenstein := by
  intro x y hxy
  have hre := congrArg QuadraticAlgebra.re hxy
  have him := congrArg QuadraticAlgebra.im hxy
  change x.re - x.im = y.re - y.im at hre
  change 2 * x.im = 2 * y.im at him
  apply Zsqrtd.ext
  · omega
  · omega

/-- The inclusion is proper: the Eisenstein generator `ω` is not in the
image of `ℤ[√-3]`. -/
theorem omega_range_eisenstein :
    Towers.NumberTheory.EInts.omega ∉
      Set.range toEisenstein := by
  rintro ⟨x, hx⟩
  have him := congrArg QuadraticAlgebra.im hx
  change 2 * x.im = 1 at him
  omega

/-- Thus `ℤ[√-3]` is a proper subring of the Eisenstein integers, as stated
in Example 2.10(b). -/
theorem eisenstein_not_surjective :
    ¬ Function.Surjective toEisenstein := by
  intro h
  exact omega_range_eisenstein
    (h Towers.NumberTheory.EInts.omega)

/-- Multiplying an Eisenstein integer by two puts it in the image of
`ℤ[√-3]`. -/
def clearTwo (x : Towers.NumberTheory.EInts) :
    SNThree := ⟨2 * x.re + x.im, x.im⟩

theorem eisenstein_clear_two
    (x : Towers.NumberTheory.EInts) :
    toEisenstein (clearTwo x) = 2 * x := by
  ext <;>
    simp [toEisenstein, clearTwo, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul]

noncomputable instance fractionRingAlgebra :
    Algebra SNThree
      (FractionRing Towers.NumberTheory.EInts) :=
  ((algebraMap Towers.NumberTheory.EInts
      (FractionRing Towers.NumberTheory.EInts)).comp
    toEisenstein).toAlgebra

noncomputable instance fraction_faithful_s :
    FaithfulSMul SNThree
      (FractionRing Towers.NumberTheory.EInts) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  change Function.Injective
    ((algebraMap Towers.NumberTheory.EInts
      (FractionRing Towers.NumberTheory.EInts)).comp
        toEisenstein)
  exact (IsFractionRing.injective
    Towers.NumberTheory.EInts _).comp
      toEisenstein_injective

/-- The two orders in Example 2.10(b) have the same fraction field. -/
noncomputable instance fraction_sqrt_neg :
    IsFractionRing SNThree
      (FractionRing Towers.NumberTheory.EInts) := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective
    Towers.NumberTheory.EInts z
  refine ⟨clearTwo a, clearTwo b, ?_⟩
  change
    z = algebraMap Towers.NumberTheory.EInts _
          (toEisenstein (clearTwo a)) /
        algebraMap Towers.NumberTheory.EInts _
          (toEisenstein (clearTwo b))
  rw [eisenstein_clear_two, eisenstein_clear_two, map_mul, map_mul]
  have htwo :
      algebraMap Towers.NumberTheory.EInts
        (FractionRing Towers.NumberTheory.EInts) 2 ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective
      Towers.NumberTheory.EInts _)]
    norm_num
  rw [mul_div_mul_left _ _ htwo]
  exact hab.symm

/-- A literal isomorphism between the fraction fields, recording Milne's
`ℚ[√-3] = ℚ[(1 + √-3)/2]`. -/
noncomputable def fractionRingEquiv :
    FractionRing SNThree ≃+*
      FractionRing Towers.NumberTheory.EInts :=
  (FractionRing.algEquiv SNThree
    (FractionRing Towers.NumberTheory.EInts)).toRingEquiv

private lemma norm_formula (x : SNThree) :
    x.norm = x.re ^ 2 + 3 * x.im ^ 2 := by
  simp [Zsqrtd.norm_def, pow_two]
  ring

private lemma norm_nonnegative (x : SNThree) : 0 ≤ x.norm := by
  rw [norm_formula]
  positivity

private lemma norm_ne_two (x : SNThree) : x.norm.natAbs ≠ 2 := by
  intro h
  have h' : x.norm = 2 := by
    rw [← Int.natAbs_of_nonneg (norm_nonnegative x)]
    exact_mod_cast h
  rw [norm_formula] at h'
  have him_lower : -1 < x.im := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im + 1)]
  have him_upper : x.im < 1 := by
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im - 1)]
  have him : x.im = 0 := by omega
  rw [him] at h'
  have hsquare : IsSquare (2 : ℤ) :=
    ⟨x.re, by simpa [pow_two] using h'.symm⟩
  norm_num at hsquare

private lemma irreducible_norm_four
    {x : SNThree} (hnorm : x.norm.natAbs = 4) : Irreducible x := by
  rw [irreducible_iff]
  constructor
  · intro hx
    have hone : x.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hx
    omega
  · intro a b hab
    by_contra h
    push Not at h
    have ha1 : a.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.1
    have hb1 : b.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp h.2
    have hprod : a.norm.natAbs * b.norm.natAbs = 2 ^ 2 := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, hnorm]
      norm_num
    have haval := (Nat.prime_two.mul_eq_prime_sq_iff ha1 hb1).mp hprod
    exact norm_ne_two a haval.1

/-- Milne's two displayed factorizations of `4` in `ℤ[√-3]`. -/
theorem four_factorizations :
    (2 : SNThree) * 2 =
      (⟨1, 1⟩ : SNThree) * (⟨1, -1⟩ : SNThree) := by
  ext <;> norm_num

theorem irreducible_two : Irreducible (2 : SNThree) := by
  apply irreducible_norm_four
  norm_num [Zsqrtd.norm_def]

theorem irreducible_add_sqrtd :
    Irreducible (⟨1, 1⟩ : SNThree) := by
  apply irreducible_norm_four
  norm_num [Zsqrtd.norm_def]

theorem irreducible_one_sqrtd :
    Irreducible (⟨1, -1⟩ : SNThree) := by
  apply irreducible_norm_four
  norm_num [Zsqrtd.norm_def]

private lemma sqrtd_dvd_two :
    ¬(⟨1, 1⟩ : SNThree) ∣ (2 : SNThree) := by
  rintro ⟨c, hc⟩
  have him := congrArg Zsqrtd.im hc
  have hre := congrArg Zsqrtd.re hc
  norm_num [Zsqrtd.im_mul] at him
  norm_num [Zsqrtd.re_mul] at hre
  omega

/-- The factor `1 + √-3` is irreducible but not prime. -/
theorem irreducible_not_sqrtd :
    Irreducible (⟨1, 1⟩ : SNThree) ∧
      ¬Prime (⟨1, 1⟩ : SNThree) := by
  refine ⟨irreducible_add_sqrtd, ?_⟩
  intro hprime
  have hdvd : (⟨1, 1⟩ : SNThree) ∣ (2 : SNThree) * 2 :=
    ⟨(⟨1, -1⟩ : SNThree), four_factorizations⟩
  exact (hprime.dvd_mul.mp hdvd).elim
    sqrtd_dvd_two sqrtd_dvd_two

/-- Consequently `ℤ[√-3]` is not a unique-factorization monoid. -/
theorem unique_facto_monoi :
    ¬Nonempty (UniqueFactorizationMonoid SNThree) := by
  rintro ⟨hufd⟩
  letI : UniqueFactorizationMonoid SNThree := hufd
  exact irreducible_not_sqrtd.2
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      irreducible_not_sqrtd.1)

end SNThree

end Towers.NumberTheory.Milne
