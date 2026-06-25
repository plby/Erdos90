import Submission.ClassField.RayClassGroups.CountFiniteIdeal
import Submission.ClassField.EulerProducts.PartialZeta

/-!
# Chapter VI, Section 2, Proposition 2.8

This file states Milne's ray-class ideal-counting estimate with the literal
constant appearing in the text.  In particular, the regulator and the number
of roots of unity are taken for `U_{m,1}`, and the norm of a modulus includes
the factor `2 ^ r₀` contributed by its real places.

Mathlib contains the ordinary ideal-class asymptotic, but not the sharp
ray-class geometry-of-numbers estimate with error `O(x ^ (1 - 1 / d))`.
`GeometryNumbersEstimate` below isolates exactly that missing
estimate.  No analytic or class-field-theoretic hypothesis is added to the
source statement.
-/

namespace Submission.CField.EProduc

open Ideal IsDedekindDomain NumberField NumberField.InfinitePlace
  NumberField.Units
open scoped nonZeroDivisors
open Submission.CField.RCGroups

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The units `U_{m,1} = U \cap K_{m,1}`.  For an integral unit, finite
congruence to one is the ordinary congruence modulo the finite ideal `m₀`;
the second condition is positivity at every real place occurring in `m`. -/
def rayUnitSubgroup (m : Modulus K) : Subgroup (𝓞 K)ˣ where
  carrier := {u |
    (u : 𝓞 K) - 1 ∈ m.finiteIdeal ∧
      Modulus.PositiveInfinity (K := K) m
        (algebraMap (𝓞 K) K (u : 𝓞 K))}
  one_mem' := by
    constructor
    · simp
    · simp [Modulus.PositiveInfinity]
  mul_mem' := by
    rintro u v ⟨huFin, huInf⟩ ⟨hvFin, hvInf⟩
    constructor
    · have heq : ((u * v : (𝓞 K)ˣ) : 𝓞 K) - 1 =
          (u : 𝓞 K) * ((v : 𝓞 K) - 1) + ((u : 𝓞 K) - 1) := by
        simp only [Units.val_mul]
        ring
      rw [heq]
      exact m.finiteIdeal.add_mem
        (m.finiteIdeal.mul_mem_left (u : 𝓞 K) hvFin) huFin
    · intro w hw
      simpa only [Units.val_mul, map_mul] using
        mul_pos (huInf w hw) (hvInf w hw)
  inv_mem' := by
    rintro u ⟨huFin, huInf⟩
    constructor
    · have heq : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 =
          -((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((u : 𝓞 K) - 1) := by
        have hinv : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) = 1 := by
          simp
        calc
          ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 =
              ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) -
                ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) := by rw [hinv]
          _ = -((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((u : 𝓞 K) - 1) := by ring
      rw [heq]
      exact m.finiteIdeal.mul_mem_left
        (-((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) huFin
    · intro w hw
      let f : 𝓞 K →+* ℝ :=
        (InfinitePlace.embedding_of_isReal w.property).comp
          (algebraMap (𝓞 K) K)
      have hprod :
          f ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * f (u : 𝓞 K) = 1 := by
        rw [← map_mul]
        simp
      have huPos : 0 < f (u : 𝓞 K) := huInf w hw
      change 0 < f ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
      nlinarith

/-- The roots of unity lying in `U_{m,1}`. -/
def rootsUnity (m : Modulus K) : Subgroup (𝓞 K)ˣ :=
  rayUnitSubgroup K m ⊓ NumberField.Units.torsion K

/-- The roots of unity satisfying the ray conditions form a finite group. -/
theorem finite_roots_unity (m : Modulus K) :
    Finite (rootsUnity K m) := by
  let f : rootsUnity K m → NumberField.Units.torsion K := fun u ↦
    ⟨u.1, u.2.2⟩
  exact Finite.of_injective f (fun u v huv ↦ by
    have huv' : (u.1 : (𝓞 K)ˣ) = v.1 := by
      exact congrArg
        (fun z : NumberField.Units.torsion K ↦ (z : (𝓞 K)ˣ)) huv
    exact Subtype.ext huv')

/-- `w_m`, the number of roots of unity in `K_{m,1}`. -/
def rayRootsUnity (m : Modulus K) : ℕ :=
  Nat.card (rootsUnity K m)

/-- In particular, `w_m` is positive. -/
theorem roots_unity_pos (m : Modulus K) :
    0 < rayRootsUnity K m := by
  letI : Finite (rootsUnity K m) := finite_roots_unity K m
  exact Nat.card_pos

/-- `reg(m) = reg(K) (U : U_{m,1})`, the regulator of the ray-unit
lattice. -/
def rayRegulator (m : Modulus K) : ℝ :=
  regulator K * (rayUnitSubgroup K m).index

/-- `N(m) = N(m₀) 2 ^ r₀`, including the real-prime contribution. -/
def modulusNorm (m : Modulus K) : ℕ :=
  absNorm m.finiteIdeal * 2 ^ m.infinite.card

/-- `d = [K : ℚ]`. -/
def numberFieldDegree : ℕ :=
  Module.finrank ℚ K

/-- The class-independent leading constant in Proposition VI.2.8:

`g_m = 2^r (2π)^s reg(m) /
  (w_m N(m) |Δ_{K/ℚ}|^(1/2))`. -/
def rayCountingConstant (m : Modulus K) : ℝ :=
  (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
      rayRegulator K m) /
    (rayRootsUnity K m * modulusNorm K m * Real.sqrt |discr K|)

/-- The integral ideals in the ray class `k` having numerical norm at most
`x`. -/
def RayIntegralIdeals (m : Modulus K)
    (k : RayClassGroup K m) (x : ℝ) :=
  {I : IIPrime K m //
    rayIntegralIdeal K I = k ∧
      (absNorm I.ideal : ℝ) ≤ x}

/-- `S(x,k)`, the number of integral ideals in the ray class `k` whose
numerical norm is at most `x`. -/
def rayIdealCount (m : Modulus K)
    (k : RayClassGroup K m) (x : ℝ) : ℕ :=
  Nat.card (RayIntegralIdeals K m k x)

/-- The set counted by `S(x,k)` is finite.  Thus `Nat.card` above is a
genuine finite cardinal, not the default value assigned to an infinite
type. -/
theorem ray_integral_ideals (m : Modulus K)
    (k : RayClassGroup K m) (x : ℝ) :
    Finite (RayIntegralIdeals K m k x) := by
  obtain ⟨n : ℕ, hn : x < n⟩ := exists_nat_gt x
  let f : RayIntegralIdeals K m k x →
      {I : Ideal (𝓞 K) // absNorm I ≤ n} := fun I ↦
    ⟨I.1.ideal, by
      exact_mod_cast (I.2.2.trans hn.le)⟩
  have hf : Function.Injective f := by
    intro I J hIJ
    apply Subtype.ext
    cases I with
    | mk I hI =>
      cases J with
      | mk J hJ =>
        cases I with
        | mk Ii hI0 hIprime =>
          cases J with
          | mk Ji hJ0 hJprime =>
            simp only [f] at hIJ
            cases hIJ
            rfl
  letI : Fintype {I : Ideal (𝓞 K) // absNorm I ≤ n} :=
    (Ideal.finite_setOf_absNorm_le n).fintype
  exact Finite.of_injective f hf

/-- The sharp geometry-of-numbers assertion used in the printed proof of
Proposition 2.8.  This is the only unavailable input: it is already the
literal ray-class lattice count, with the explicit `g_m` defined above. -/
def GeometryNumbersEstimate
    (m : Modulus K) (k : RayClassGroup K m) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    |(rayIdealCount K m k x : ℝ) - rayCountingConstant K m * x| ≤
      C * x ^ (1 - 1 / (numberFieldDegree K : ℝ))

/-- **Proposition VI.2.8 (source statement).**  For every modulus and every
ray class, the ideal count has the stated main term and the sharp
`O(x^(1-1/d))` error for every `x ≥ 1`. -/
def RayCountingAsymptotic : Prop :=
  ∀ (m : Modulus K) (k : RayClassGroup K m),
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(rayIdealCount K m k x : ℝ) - rayCountingConstant K m * x| ≤
        C * x ^ (1 - 1 / (numberFieldDegree K : ℝ))

/-- Lang's ray-class geometry-of-numbers count gives Proposition 2.8
without any additional source hypothesis. -/
theorem ray_geometry_numbers
    (hgeometry : ∀ (m : Modulus K) (k : RayClassGroup K m),
      GeometryNumbersEstimate K m k) :
    RayCountingAsymptotic K := by
  exact hgeometry

omit [NumberField K] in
/-- For the trivial modulus, the ray-unit subgroup is the full unit group. -/
@[simp]
theorem ray_unit_one :
    rayUnitSubgroup K (1 : Modulus K) = ⊤ := by
  ext u
  simp [rayUnitSubgroup, Modulus.PositiveInfinity]

/-- For the trivial modulus, `w_m` is the usual number of roots of unity. -/
@[simp]
theorem ray_roots_unity :
    rayRootsUnity K (1 : Modulus K) = torsionOrder K := by
  simp [rayRootsUnity, rootsUnity, torsionOrder,
    Nat.card_eq_fintype_card]

/-- For the trivial modulus, `reg(m)` is the ordinary regulator. -/
@[simp]
theorem rayRegulator_one :
    rayRegulator K (1 : Modulus K) = regulator K := by
  simp [rayRegulator]

/-- The norm of the trivial modulus is one. -/
@[simp]
theorem modulusNorm_one :
    modulusNorm K (1 : Modulus K) = 1 := by
  simp [modulusNorm]

/-- The explicit ray constant specializes exactly to the ordinary
ideal-class counting constant already used by Mathlib. -/
@[simp]
theorem ray_counting_constant :
    rayCountingConstant K (1 : Modulus K) =
      ordinaryCountingConstant K := by
  simp [rayCountingConstant, ordinaryCountingConstant]

end

end Submission.CField.EProduc
