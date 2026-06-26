import Submission.ClassField.ArtinLSeries.FermatCubicCount
import Submission.NumberTheory.Eisenstein.Euclidean

/-!
# Uniqueness of Gauss's normalized coefficient

The representation `4p = A² + 27B²` gives an Eisenstein integer

`alpha = (A + 3B * sqrt(-3)) / 2`

of norm `p`.  Primality of `p`, unique factorization in the Eisenstein
integers, and the congruence `A = 1 (mod 3)` determine `alpha` up to
conjugation, which leaves `A` unchanged.
-/

namespace Submission.CField.ALSeries

open Submission.NumberTheory

noncomputable section

private abbrev E := EInts

/-- The integer coefficient `A` recovered from native Eisenstein
coordinates `r + s * omega`, where `omega = (1 + sqrt(-3))/2`. -/
private def gaussCoefficient (x : E) : ℤ :=
  2 * x.re + x.im

@[simp]
private theorem gaussCoefficient_star (x : E) :
    gaussCoefficient (star x) = gaussCoefficient x := by
  simp [gaussCoefficient]
  ring

/-- A solution of `4p = A² + 27B²` produces an Eisenstein integer of
norm `p`, with imaginary coordinate divisible by three and coefficient
`A`. -/
private theorem exists_eisensteinLift
    {p : ℕ} {A B : ℤ}
    (hrep : 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2) :
  ∃ x : E,
      x.norm = (p : ℤ) ∧ x.im = 3 * B ∧ gaussCoefficient x = A := by
  have heven : (2 : ℤ) ∣ A - 3 * B := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (A - 3 * B) 2).mp
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod 2)) hrep
    have hfinite : ∀ q a b : ZMod 2,
        4 * q = a ^ 2 + 27 * b ^ 2 →
          a - 3 * b = 0 := by decide
    push_cast
    apply hfinite (p : ZMod 2) (A : ZMod 2) (B : ZMod 2)
    simpa using hcast
  obtain ⟨r, hr⟩ := heven
  have hA : A = 2 * r + 3 * B := by linarith
  let x : E := ⟨r, 3 * B⟩
  refine ⟨x, ?_, rfl, ?_⟩
  · rw [EInts.norm_formula]
    change r ^ 2 + r * (3 * B) + (3 * B) ^ 2 = (p : ℤ)
    rw [hA] at hrep
    nlinarith
  · change 2 * r + 3 * B = A
    exact hA.symm

/-- An Eisenstein integer whose norm is a rational prime is irreducible. -/
private theorem eisenstein_irreducible_prime
    {p : ℕ} (hp : p.Prime) {x : E} (hxnorm : x.norm = (p : ℤ)) :
    Irreducible x := by
  have hpInt : Prime (p : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  constructor
  · intro hxunit
    apply hpInt.not_unit
    rw [← hxnorm]
    exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hxunit
  · intro a b hab
    have hnorm : a.norm * b.norm = (p : ℤ) := by
      calc
        a.norm * b.norm = (a * b).norm := by rw [map_mul]
        _ = x.norm := by rw [hab]
        _ = (p : ℤ) := hxnorm
    rcases hpInt.irreducible.isUnit_or_isUnit hnorm.symm with ha | hb
    · exact Or.inl (QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr ha)
    · exact Or.inr (QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr hb)

/-- The reduction conditions selecting Gauss's preferred associate. -/
private def GaussNormalizedEisenstein (x : E) : Prop :=
  (x.im : ZMod 3) = 0 ∧ (gaussCoefficient x : ZMod 3) = 1

private theorem gauss_normalized_lift
    {x : E} {A B : ℤ}
    (hxim : x.im = 3 * B) (hxA : gaussCoefficient x = A)
    (hAmod : (A : ZMod 3) = 1) :
    GaussNormalizedEisenstein x := by
  constructor
  · rw [hxim]
    push_cast
    rw [show (3 : ZMod 3) = 0 by decide, zero_mul]
  · rw [hxA]
    exact hAmod

private theorem gaussNormalized_star {x : E}
    (hx : GaussNormalizedEisenstein x) :
    GaussNormalizedEisenstein (star x) := by
  constructor
  · simp only [QuadraticAlgebra.im_star, Int.cast_neg, hx.1, neg_zero]
  · rw [gaussCoefficient_star]
    exact hx.2

/-- Two associated Eisenstein integers satisfying Gauss's congruence
normalization are equal: among the six units only `1` preserves the
reduction `(-1,0)` modulo three. -/
private theorem associated_gauss_normalized
    {x y : E} (hxy : Associated x y)
    (hx : GaussNormalizedEisenstein x)
    (hy : GaussNormalizedEisenstein y) :
    x = y := by
  have hxre : (x.re : ZMod 3) = 2 := by
    have h := hx.2
    simp only [gaussCoefficient, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      hx.1, add_zero] at h
    exact (by decide : ∀ z : ZMod 3, 2 * z = 1 → z = 2) _ h
  have hyre : (y.re : ZMod 3) = 2 := by
    have h := hy.2
    simp only [gaussCoefficient, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      hy.1, add_zero] at h
    exact (by decide : ∀ z : ZMod 3, 2 * z = 1 → z = 2) _ h
  obtain ⟨u, hxu⟩ := hxy
  have hure : (((u : E).re : ℤ) : ZMod 3) = 1 := by
    have h := congrArg (fun z : E ↦ (z.re : ZMod 3)) hxu
    simp only [QuadraticAlgebra.re_mul, Int.cast_add, Int.cast_mul,
      hxre, hx.1, hyre] at h
    have h' : 2 * (((u : E).re : ℤ) : ZMod 3) = 2 := by
      simpa only [Int.cast_neg, Int.cast_one, zero_mul, mul_zero, add_zero] using h
    exact (by decide : ∀ z : ZMod 3, 2 * z = 2 → z = 1) _ h'
  have huim : (((u : E).im : ℤ) : ZMod 3) = 0 := by
    have h := congrArg (fun z : E ↦ (z.im : ZMod 3)) hxu
    simp only [QuadraticAlgebra.im_mul, Int.cast_add, Int.cast_mul,
      hxre, hx.1, mul_zero, hy.1] at h
    have h' : 2 * (((u : E).im : ℤ) : ZMod 3) = 0 := by
      simpa only [zero_mul, add_zero] using h
    exact (by decide : ∀ z : ZMod 3, 2 * z = 0 → z = 0) _ h'
  have hu : (u : E) = 1 := by
    rcases (EInts.isUnit_iff (u : E)).mp u.isUnit with
      hu | hu | hu | hu | hu | hu
    · exact hu
    · exfalso
      rw [hu] at hure
      norm_num [QuadraticAlgebra.re_one] at hure
      exact (by decide : (-1 : ZMod 3) ≠ 1) hure
    · exfalso
      rw [hu] at hure
      norm_num [EInts.omega] at hure
    · exfalso
      rw [hu] at hure
      norm_num [EInts.omega] at hure
    · exfalso
      rw [hu] at huim
      norm_num [EInts.omega, QuadraticAlgebra.im_one] at huim
    · exfalso
      rw [hu] at hure
      norm_num [EInts.omega, QuadraticAlgebra.re_one] at hure
      exact (by decide : (-1 : ZMod 3) ≠ 1) hure
  rw [hu, mul_one] at hxu
  exact hxu

/-- Two norm-`p` Eisenstein lifts are associated either directly or after
conjugating the second lift. -/
private theorem associated_or_star
    {p : ℕ} (hp : p.Prime) {x y : E}
    (hxnorm : x.norm = (p : ℤ)) (hynorm : y.norm = (p : ℤ)) :
    Associated x y ∨ Associated x (star y) := by
  have hxPrime : Prime x :=
    irreducible_iff_prime.mp (eisenstein_irreducible_prime hp hxnorm)
  have hyIrr : Irreducible y :=
    eisenstein_irreducible_prime hp hynorm
  have hystarIrr : Irreducible (star y) :=
    eisenstein_irreducible_prime hp (by simpa using hynorm)
  have hxdivp : x ∣ (p : E) := by
    refine ⟨star x, ?_⟩
    have h := QuadraticAlgebra.algebraMap_norm_eq_mul_star x
    rw [hxnorm] at h
    exact h
  have hyp : (p : E) = y * star y := by
    have h := QuadraticAlgebra.algebraMap_norm_eq_mul_star y
    rw [hynorm] at h
    exact h
  have hxdiv : x ∣ y * star y := by
    rw [← hyp]
    exact hxdivp
  rcases hxPrime.dvd_or_dvd hxdiv with hxy | hxstar
  · exact Or.inl (hxPrime.irreducible.associated_of_dvd hyIrr hxy)
  · exact Or.inr (hxPrime.irreducible.associated_of_dvd hystarIrr hxstar)

/-- The normalized coefficient in Gauss's split-prime representation is
unique. -/
theorem gauss_normalized_unique
    (p : ℕ) [Fact p.Prime]
    (A A' : ℤ)
    (hA : GaussNormalizedCoefficient p A)
    (hA' : GaussNormalizedCoefficient p A') :
    A = A' := by
  obtain ⟨hAmod, B, hrep⟩ := hA
  obtain ⟨hAmod', B', hrep'⟩ := hA'
  obtain ⟨x, hxnorm, hxim, hxA⟩ := exists_eisensteinLift hrep
  obtain ⟨y, hynorm, hyim, hyA⟩ := exists_eisensteinLift hrep'
  have hxnormed := gauss_normalized_lift hxim hxA hAmod
  have hynormed := gauss_normalized_lift hyim hyA hAmod'
  rcases associated_or_star
      (Fact.out : p.Prime) hxnorm hynorm with hxy | hxystar
  · have heq := associated_gauss_normalized hxy hxnormed hynormed
    rw [← hxA, ← hyA, heq]
  · have heq := associated_gauss_normalized hxystar hxnormed
      (gaussNormalized_star hynormed)
    rw [← hxA, ← hyA, heq, gaussCoefficient_star]

/-- The formerly isolated uniqueness bridge is discharged by Eisenstein
unique factorization. -/
theorem gaussNormalizedUniqueness :
    GaussUniquenessBridge := by
  intro p _ _ A A' hA hA'
  exact gauss_normalized_unique p A A' hA hA'

end

end Submission.CField.ALSeries
