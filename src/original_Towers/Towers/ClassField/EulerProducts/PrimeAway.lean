import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Towers.ClassField.RayClassGroups.CountFiniteIdeal

/-!
# Milne, Class Field Theory, Proposition VI.2.7

This file formulates the proposition for ray-class characters of an arbitrary
number field.  An integral ideal prime to the modulus is represented by its
finitely-supported family of exponents at primes away from the modulus.  This
is precisely the unique-factorization model used in Milne's proof.

The project currently has no theorem identifying a sum over those exponent
families with the corresponding product over prime ideals.  The proposition
`NumberEulerBridge` below isolates exactly that analytic
Euler-product theorem, for arbitrary unitary weights on prime ideals.  All
ray-class-specific reductions, including the local geometric-series formula,
are proved here.
-/

namespace Towers.CField.EProduc

open Filter IsDedekindDomain NumberField Topology
open scoped BigOperators nonZeroDivisors

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

open Towers.CField.RCGroups

/-- The finite primes not dividing the finite part of `m`. -/
abbrev PrimeAway (m : Modulus K) :=
  {p : HeightOneSpectrum (𝓞 K) // p ∉ m.finiteSupport}

/-- The free commutative monoid of integral ideals prime to `m`, written in
terms of prime-ideal exponents. -/
abbrev FactorizedIntegralIdeal (m : Modulus K) := PrimeAway K m →₀ ℕ

/-- A complex ray-class character.  We use its canonical unitary realization:
the ray class group is finite, hence every complex-valued group character has
values on the unit circle. -/
abbrev RayDirichletCharacter (m : Modulus K) :=
  RayClassGroup K m →* Circle

/-- A prime away from the modulus, regarded as a nonzero integral ideal prime
to the modulus. -/
def awayIntegralIdeal {m : Modulus K} (p : PrimeAway K m) :
    IIPrime K m where
  ideal := p.1.asIdeal
  ne_zero := p.1.ne_bot
  primeTo := by
    intro q hq
    exact FractionalIdeal.count_maximal_coprime K q (by
      intro hpq
      subst q
      exact p.2 hq)

/-- The ray class of a prime ideal not dividing the modulus. -/
def primeRayClass {m : Modulus K} (p : PrimeAway K m) : RayClassGroup K m :=
  rayIntegralIdeal K (awayIntegralIdeal K p)

/-- The ray class represented by a factorized integral ideal. -/
def factorizedRayClass {m : Modulus K}
    (a : FactorizedIntegralIdeal K m) : RayClassGroup K m :=
  a.prod fun p e ↦ primeRayClass K p ^ e

@[simp]
theorem factorized_ray_zero {m : Modulus K} :
    factorizedRayClass K (0 : FactorizedIntegralIdeal K m) = 1 := by
  simp [factorizedRayClass]

theorem factorized_ray_add {m : Modulus K}
    (a b : FactorizedIntegralIdeal K m) :
    factorizedRayClass K (a + b) =
      factorizedRayClass K a * factorizedRayClass K b := by
  classical
  exact Finsupp.prod_add_index
    (fun _ _ ↦ pow_zero _)
    (fun _ _ m n ↦ pow_add _ m n)

@[simp]
theorem factorized_ray_single {m : Modulus K}
    (p : PrimeAway K m) (e : ℕ) :
    factorizedRayClass K (Finsupp.single p e) = primeRayClass K p ^ e := by
  classical
  simp [factorizedRayClass]

/-- The absolute norm of a factorized integral ideal. -/
def factorizedIdealNorm {m : Modulus K}
    (a : FactorizedIntegralIdeal K m) : ℕ :=
  a.prod fun p e ↦ p.1.asIdeal.absNorm ^ e

@[simp]
theorem factorized_ideal_zero {m : Modulus K} :
    factorizedIdealNorm K (0 : FactorizedIntegralIdeal K m) = 1 := by
  simp [factorizedIdealNorm]

theorem factorized_ideal_add {m : Modulus K}
    (a b : FactorizedIntegralIdeal K m) :
    factorizedIdealNorm K (a + b) =
      factorizedIdealNorm K a * factorizedIdealNorm K b := by
  classical
  exact Finsupp.prod_add_index
    (fun _ _ ↦ pow_zero _)
    (fun _ _ m n ↦ pow_add _ m n)

@[simp]
theorem factorized_ideal_single {m : Modulus K}
    (p : PrimeAway K m) (e : ℕ) :
    factorizedIdealNorm K (Finsupp.single p e) = p.1.asIdeal.absNorm ^ e := by
  classical
  simp [factorizedIdealNorm]

/-- The summand `χ(a) / N(a)^s` in the ray-class Dirichlet series. -/
def rayLSummand {m : Modulus K}
    (χ : RayDirichletCharacter K m) (s : ℂ)
    (a : FactorizedIntegralIdeal K m) : ℂ :=
  a.prod fun p e ↦
    (χ (primeRayClass K p) *
      (p.1.asIdeal.absNorm : ℂ) ^ (-s)) ^ e

/-- Milne's ray-class Dirichlet `L`-series, as a sum over integral ideals
prime to the modulus. -/
def rayLSeries {m : Modulus K}
    (χ : RayDirichletCharacter K m) (s : ℂ) : ℂ :=
  ∑' a : FactorizedIntegralIdeal K m, rayLSummand K χ s a

/-- The quantity `χ(p) N(p)^{-s}` occurring in the Euler factor at `p`. -/
def rayEulerRatio {m : Modulus K}
    (χ : RayDirichletCharacter K m) (s : ℂ)
    (p : PrimeAway K m) : ℂ :=
  χ (primeRayClass K p) * (p.1.asIdeal.absNorm : ℂ) ^ (-s)

@[simp]
theorem l_series_summand {m : Modulus K}
    (χ : RayDirichletCharacter K m) (s : ℂ) :
    rayLSummand K χ s (0 : FactorizedIntegralIdeal K m) = 1 := by
  simp [rayLSummand]

/-- Unique factorization turns each ideal summand into the product of its
prime-power contributions. -/
theorem l_summand_prod {m : Modulus K}
    (χ : RayDirichletCharacter K m) (s : ℂ)
    (a : FactorizedIntegralIdeal K m) :
    rayLSummand K χ s a =
      a.prod fun p e ↦ rayEulerRatio K χ s p ^ e := by
  rfl

/-- The prime-factor definition is the literal summand
`χ(a) * N(a)^(-s)` appearing in Milne's statement. -/
theorem ray_l_summand {m : Modulus K}
    (χ : RayDirichletCharacter K m) (s : ℂ)
    (a : FactorizedIntegralIdeal K m) :
    rayLSummand K χ s a =
      χ (factorizedRayClass K a) *
        (factorizedIdealNorm K a : ℂ) ^ (-s) := by
  classical
  induction a using Finsupp.induction with
  | zero => simp [rayLSummand]
  | @single_add p e a hp he ih =>
      have hcpow :
          ((p.1.asIdeal.absNorm ^ e * factorizedIdealNorm K a : ℕ) : ℂ) ^ (-s) =
            ((p.1.asIdeal.absNorm : ℂ) ^ e) ^ (-s) *
              (factorizedIdealNorm K a : ℂ) ^ (-s) := by
        simpa only [Nat.cast_mul, Nat.cast_pow, ← Complex.ofReal_natCast,
          ← Complex.ofReal_pow] using
          (Complex.mul_cpow_ofReal_nonneg
            (show 0 ≤ (p.1.asIdeal.absNorm : ℝ) ^ e by positivity)
            (Nat.cast_nonneg (factorizedIdealNorm K a)) (-s))
      have ih' :
          (a.prod fun p e ↦
            (χ (primeRayClass K p) *
              (p.1.asIdeal.absNorm : ℂ) ^ (-s)) ^ e) =
            χ (factorizedRayClass K a) *
              (factorizedIdealNorm K a : ℂ) ^ (-s) := ih
      rw [rayLSummand]
      rw [Finsupp.prod_add_index]
      · rw [factorized_ray_add, factorized_ideal_add, map_mul]
        rw [factorized_ray_single, factorized_ideal_single, hcpow]
        simp only [map_pow]
        rw [Finsupp.prod_single_index (by simp)]
        rw [mul_pow]
        simp only [Circle.coe_mul, Circle.coe_pow]
        rw [← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]
        rw [ih']
        ring_nf
      · intro
        simp
      · intro
        simp [pow_add, mul_comm]

/-- The norm of a local ray-class weight is one. -/
@[simp]
theorem ray_character_prime {m : Modulus K}
    (χ : RayDirichletCharacter K m) (p : PrimeAway K m) :
    ‖(χ (primeRayClass K p) : ℂ)‖ = 1 := by
  exact Circle.norm_coe _

/-- On `Re(s) > 1`, the local ratio has norm strictly smaller than one. -/
theorem ray_euler_ratio {m : Modulus K}
    (χ : RayDirichletCharacter K m) {s : ℂ} (hs : 1 < s.re)
    (p : PrimeAway K m) :
    ‖rayEulerRatio K χ s p‖ < 1 := by
  have hpN : (1 : ℝ) < (p.1.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.1
  have hp0 : (0 : ℝ) < (p.1.asIdeal.absNorm : ℝ) := zero_lt_one.trans hpN
  rw [rayEulerRatio, norm_mul, ray_character_prime]
  simp only [one_mul, ← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hpN (by linarith)

/-- The local prime-power series is the expected geometric factor. -/
theorem ray_class_series {m : Modulus K}
    (χ : RayDirichletCharacter K m) {s : ℂ} (hs : 1 < s.re)
    (p : PrimeAway K m) :
    HasSum (fun e : ℕ ↦ rayEulerRatio K χ s p ^ e)
      (1 - rayEulerRatio K χ s p)⁻¹ := by
  exact hasSum_geometric_of_norm_lt_one (ray_euler_ratio K χ hs p)

/-- The one missing analytic API: the Euler-product theorem for the free
commutative monoid of prime ideals of a number field.  It is deliberately
stated for arbitrary unit-circle weights, so no class-field-theoretic content
is hidden in the bridge. -/
def NumberEulerBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (u : PrimeAway K m → Circle)
    (s : ℂ), 1 < s.re →
    HasProd
      (fun p ↦ (1 - (u p : ℂ) * (p.1.asIdeal.absNorm : ℂ) ^ (-s))⁻¹)
      (∑' a : FactorizedIntegralIdeal K m,
        a.prod fun p e ↦ ((u p : ℂ) *
          (p.1.asIdeal.absNorm : ℂ) ^ (-s)) ^ e)

/-- Proposition VI.2.7 in its literal ray-class form. -/
def RayLEuler : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (χ : RayDirichletCharacter K m)
    (s : ℂ), 1 < s.re →
    HasProd
      (fun p : PrimeAway K m ↦
        (1 - χ (primeRayClass K p) *
          (p.1.asIdeal.absNorm : ℂ) ^ (-s))⁻¹)
      (rayLSeries K χ s)

/-- The number-field ideal Euler-product bridge implies Milne's proposition;
all remaining work is definitional or the unique-factorization identity proved
above. -/
theorem number_euler_bridge
    (hEuler : NumberEulerBridge.{u}) :
    RayLEuler.{u} := by
  intro K _ _ m χ s hs
  have h := hEuler K m (fun p ↦ χ (primeRayClass K p)) s hs
  simpa only [rayLSeries, rayEulerRatio,
    l_summand_prod] using h

end

end Towers.CField.EProduc
