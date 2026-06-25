import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Towers.ClassField.RayClassGroups.FiniteCRTFactor


/-!
# Chapter V, Section 1, Theorem 1.7: source-facing statements

The tracked file constructs the finite Chinese-remainder factor. Here we
retain the real sign factors and package the two products displayed in the
source, proving their canonical isomorphism. The sign group `{+,-}` is
modeled canonically by `ℤˣ`.

The other clauses of the source theorem are not silently weakened here.
They require the canonical surjection from `K_m` to these simultaneous real
sign and finite residue factors.  Its surjectivity is precisely the mixed
finite-congruence/real-sign approximation step which is not currently
packaged by the number-field API.  Consequently the ray-element subgroup,
the resulting five-term exact sequence, and the ray class number formula
cannot yet be derived without adding that missing theorem.
-/

namespace Towers.CField.RCGroups

open IsDedekindDomain NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

namespace Modulus

/-- The product of one copy of `{+,-}` for every real prime in the modulus. -/
abbrev realSignFactors (m : Modulus K) :=
  ∀ _w : m.infinite, ℤˣ

/-- The first product displayed in Theorem V.1.7. -/
abbrev localRayFactors (m : Modulus K) :=
  realSignFactors K m ×
    (∀ p : m.finiteSupport,
      (𝓞 K ⧸ p.1.asIdeal ^ m.finite p.1)ˣ)

/-- The second product displayed in Theorem V.1.7. -/
abbrev finiteRayFactors (m : Modulus K) :=
  realSignFactors K m × (𝓞 K ⧸ m.finiteIdeal)ˣ

/-- The two right-hand products in Theorem V.1.7 are canonically
isomorphic: the real sign factors are unchanged and finite CRT combines the
prime-power factors. -/
noncomputable def localRayFinite (m : Modulus K) :
    localRayFactors K m ≃* finiteRayFactors K m :=
  MulEquiv.prodCongr (MulEquiv.refl _)
    (m.finiteUnitsPi K).symm

omit [NumberField K] in
/-- The finite ideal of a modulus is nonzero. -/
theorem ideal_ne_zero (m : Modulus K) : m.finiteIdeal ≠ 0 := by
  classical
  rw [finiteIdeal, Finsupp.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ p.ne_bot

/-- The quotient by the finite part of a modulus is finite. -/
theorem finite_finiteQuotient (m : Modulus K) :
    Finite (𝓞 K ⧸ m.finiteIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient (ideal_ne_zero K m)

/-- The finite quotient unit group in Theorem V.1.7 is finite. -/
theorem finite_quotient_units (m : Modulus K) :
    Finite (𝓞 K ⧸ m.finiteIdeal)ˣ := by
  letI : Finite (𝓞 K ⧸ m.finiteIdeal) := finite_finiteQuotient K m
  exact Finite.of_injective Units.val Units.val_injective

/-- The real-sign product is finite. -/
theorem finite_real_sign (m : Modulus K) :
    Finite (realSignFactors K m) := by
  infer_instance

/-- The second source product is a finite group. -/
theorem finite_ray_factors (m : Modulus K) :
    Finite (finiteRayFactors K m) := by
  letI : Finite (𝓞 K ⧸ m.finiteIdeal)ˣ :=
    finite_quotient_units K m
  infer_instance

/-- The first source product is a finite group. -/
theorem local_ray_factors (m : Modulus K) :
    Finite (localRayFactors K m) := by
  letI : Finite (finiteRayFactors K m) := finite_ray_factors K m
  exact Finite.of_injective (localRayFinite K m)
    (localRayFinite K m).injective

/-- The sign group `{+,-}` has two elements. -/
theorem nat_int_units : Nat.card ℤˣ = 2 := by
  rw [Nat.card_eq_two_iff' (1 : ℤˣ)]
  refine ⟨-1, by norm_num, ?_⟩
  intro u hu
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact (hu rfl).elim
  · rfl

omit [NumberField K] in
/-- The real factors contribute exactly `2 ^ r₀`, where `r₀` is the
number of real primes in the modulus. -/
theorem real_sign_factors (m : Modulus K) :
    Nat.card (realSignFactors K m) = 2 ^ m.infinite.card := by
  rw [Nat.card_pi]
  simp

/-- The part of the order calculation supplied by the two canonical product
decompositions: the real primes contribute `2 ^ r₀`, while all finite
prime-power factors combine into the unit group modulo `m₀`. -/
theorem nat_ray_factors (m : Modulus K) :
    Nat.card (localRayFactors K m) =
      2 ^ m.infinite.card * Nat.card (𝓞 K ⧸ m.finiteIdeal)ˣ := by
  rw [Nat.card_congr (localRayFinite K m).toEquiv,
    Nat.card_prod, real_sign_factors]

end Modulus

end

end Towers.CField.RCGroups
