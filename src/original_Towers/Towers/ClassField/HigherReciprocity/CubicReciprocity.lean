import Towers.ClassField.HigherReciprocity.PowerReciprocity
import Towers.NumberTheory.Eisenstein.Euclidean
import Mathlib.RingTheory.Multiplicity

/-!
# Chapter VIII, Section 5, Example 5.13: cubic reciprocity

This file uses the concrete Euclidean-domain model
`Z[omega] = QuadraticAlgebra Z (-1) 1` already developed in Towers.  The
book's primitive cube root is `zeta = omega - 1`, while its prime above
three is the associate `pi = 1 + omega`.

The elementary Eisenstein arithmetic and the literal reciprocity statement
are formalized here.  The only isolated input is the explicit Hilbert-symbol
calculation at `pi`; the deduction from the Power Recip Law is proved.
-/

namespace Towers.CField.HRecip

open scoped BigOperators
open Towers.NumberTheory

noncomputable section

abbrev EIntege := EInts

namespace EIntege

/-- The book's `zeta = (-1 + sqrt(-3))/2`; Towers' `omega` is the primitive
sixth root `(1 + sqrt(-3))/2`. -/
def zeta : EIntege := EInts.omega - 1

/-- The book's chosen prime above three.  In the coordinate model it is
`1 + omega` and differs from `1 - zeta` by a unit. -/
def pi : EIntege := 1 + EInts.omega

@[simp] theorem zeta_re : zeta.re = -1 := by
  simp [zeta, EInts.omega, QuadraticAlgebra.re_one]

@[simp] theorem zeta_im : zeta.im = 1 := by
  simp [zeta, EInts.omega, QuadraticAlgebra.im_one]

@[simp] theorem pi_re : pi.re = 1 := by
  simp [pi, EInts.omega, QuadraticAlgebra.re_one]

@[simp] theorem pi_im : pi.im = 1 := by
  simp [pi, EInts.omega, QuadraticAlgebra.im_one]

/-- `zeta` is a cube root of unity. -/
@[simp] theorem zeta_pow_three : zeta ^ 3 = 1 := by
  ext <;> norm_num [zeta, EInts.omega, pow_succ,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem zeta_ne_one : zeta ≠ 1 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  norm_num [zeta, EInts.omega, QuadraticAlgebra.im_one] at this

/-- The ramification identity `pi^2 = 3 omega`. -/
theorem pi_sq : pi ^ 2 = 3 * EInts.omega := by
  ext <;> norm_num [pi, EInts.omega, pow_succ,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

theorem pi_norm : pi.norm = 3 := by
  norm_num [EInts.norm_formula, pi,
    EInts.omega, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one]

theorem pi_not_unit : ¬ IsUnit pi := by
  rw [EInts.isUnit_iff]
  simp [pi, EInts.omega, QuadraticAlgebra.ext_iff,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- Congruence to `±1` modulo `3 Z[zeta]`, exactly the source's notion of
a primary Eisenstein integer. -/
def IsPrimary (a : EIntege) : Prop :=
  a - 1 ∈ Ideal.span ({(3 : EIntege)} : Set EIntege) ∨
    a + 1 ∈ Ideal.span ({(3 : EIntege)} : Set EIntege)

theorem primary_dvd (a : EIntege) :
    IsPrimary a ↔ (3 : EIntege) ∣ a - 1 ∨
      (3 : EIntege) ∣ a + 1 := by
  simp only [IsPrimary, Ideal.mem_span_singleton]

/-- Coordinate form of `a == ±1 (mod 3)`. -/
theorem primary_coordinates (a : EIntege) :
    IsPrimary a ↔
      (∃ m n : ℤ, a = 1 + 3 * (⟨m, n⟩ : EIntege)) ∨
      (∃ m n : ℤ, a = -(1 + 3 * (⟨m, n⟩ : EIntege))) := by
  rw [primary_dvd]
  constructor
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · left
      refine ⟨x.re, x.im, ?_⟩
      rw [show a = 1 + (a - 1) by abel, hx]
    · right
      refine ⟨-x.re, -x.im, ?_⟩
      rw [show a = -1 + (a + 1) by abel, hx]
      have hxcoord : x = (⟨x.re, x.im⟩ : EIntege) := by
        ext <;> rfl
      rw [hxcoord]
      ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]; ring_nf
  · rintro (⟨m, n, rfl⟩ | ⟨m, n, rfl⟩)
    · left
      refine ⟨(⟨m, n⟩ : EIntege), ?_⟩
      ring
    · right
      refine ⟨-(⟨m, n⟩ : EIntege), ?_⟩
      ring

/-- Multiplication by `pi` in integral coordinates. -/
theorem pi_mul_coordinates (a b : ℤ) :
    pi * (⟨a, b⟩ : EIntege) = ⟨a - b, a + 2 * b⟩ := by
  ext <;> simp [pi, EInts.omega,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring

/-- The elementary divisibility test at the unique prime above three. -/
theorem pi_dvd_iff (x : EIntege) :
    pi ∣ x ↔ (3 : ℤ) ∣ x.im - x.re := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y.im, ?_⟩
    simp [pi, EInts.omega,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    ring
  · rintro ⟨d, hd⟩
    refine ⟨(⟨x.re + d, d⟩ : EIntege), ?_⟩
    rw [pi_mul_coordinates]
    apply QuadraticAlgebra.ext <;> simp
    omega

/-- If the imaginary coordinate is a multiple of three and the real
coordinate is not, the element is primary. -/
private theorem primary_im_re
    (x : EIntege) (him : (3 : ℤ) ∣ x.im)
    (hre : ¬ (3 : ℤ) ∣ x.re) : IsPrimary x := by
  obtain ⟨n, hn⟩ := him
  have hmod0 : x.re % 3 = 0 ↔ (3 : ℤ) ∣ x.re :=
    Int.dvd_iff_emod_eq_zero.symm
  have hnonzero : x.re % 3 ≠ 0 := by simpa [hmod0] using hre
  have hnonneg := Int.emod_nonneg x.re (by norm_num : (3 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos x.re (by norm_num : (0 : ℤ) < 3)
  have hcases : x.re % 3 = 1 ∨ x.re % 3 = 2 := by omega
  rw [primary_coordinates]
  rcases hcases with hrem | hrem
  · left
    refine ⟨x.re / 3, n, ?_⟩
    apply QuadraticAlgebra.ext
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat]
      omega
    · simp [QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat, hn]
  · right
    refine ⟨-(x.re / 3 + 1), -n, ?_⟩
    apply QuadraticAlgebra.ext
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat]
      omega
    · simp [QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat, hn]

/-- Multiplication by the three powers of `zeta` rotates the three possible
nonzero residue directions modulo `pi`. -/
theorem zeta_primary_dvd
    (x : EIntege) (hx : ¬ pi ∣ x) :
    ∃ i : Fin 3, IsPrimary (zeta ^ (i : ℕ) * x) := by
  have hdiff : ¬ (3 : ℤ) ∣ x.im - x.re := (pi_dvd_iff x).not.mp hx
  have hne : (x.re : ZMod 3) ≠ (x.im : ZMod 3) := by
    intro h
    apply hdiff
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (x.im - x.re) 3).mp
    simpa using sub_eq_zero.mpr h.symm
  have hfinite : ∀ a b : ZMod 3, a ≠ b →
      b = 0 ∨ a = 0 ∨ a + b = 0 := by decide
  have hz0re : (zeta ^ (0 : ℕ) * x).re = x.re := by simp
  have hz0im : (zeta ^ (0 : ℕ) * x).im = x.im := by simp
  have hz1re : (zeta ^ (1 : ℕ) * x).re = -x.re - x.im := by
    simp [zeta, EInts.omega,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    ring
  have hz1im : (zeta ^ (1 : ℕ) * x).im = x.re := by
    simp [zeta, EInts.omega,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hz2re : (zeta ^ (2 : ℕ) * x).re = x.im := by
    simp [zeta, EInts.omega, pow_two,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hz2im : (zeta ^ (2 : ℕ) * x).im = -x.re - x.im := by
    simp [zeta, EInts.omega, pow_two,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    ring
  rcases hfinite (x.re : ZMod 3) (x.im : ZMod 3) hne with hb | ha | hab
  · refine ⟨0, ?_⟩
    change IsPrimary (zeta ^ (0 : ℕ) * x)
    apply primary_im_re
    · rw [hz0im]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd x.im 3).mp hb
    · intro hre
      rw [hz0re] at hre
      apply hne
      have hra : (x.re : ZMod 3) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd x.re 3).2 hre
      rw [hra, hb]
  · refine ⟨1, ?_⟩
    change IsPrimary (zeta ^ (1 : ℕ) * x)
    apply primary_im_re
    · rw [hz1im]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd x.re 3).mp ha
    · intro hre
      rw [hz1re] at hre
      have hrz : ((-x.re - x.im : ℤ) : ZMod 3) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hre
      apply hne
      have hb0 : (x.im : ZMod 3) = 0 := by
        simpa [hz1re, ha] using hrz
      rw [ha, hb0]
  · refine ⟨2, ?_⟩
    change IsPrimary (zeta ^ (2 : ℕ) * x)
    apply primary_im_re
    · rw [hz2im]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (-x.re - x.im) 3).mp
      push_cast
      calc
        -(x.re : ZMod 3) - (x.im : ZMod 3) =
            -((x.re : ZMod 3) + (x.im : ZMod 3)) := by ring
        _ = 0 := by rw [hab]; simp
    · intro hre
      rw [hz2re] at hre
      have hrz : ((x.im : ℤ) : ZMod 3) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hre
      apply hne
      have hb0 : (x.im : ZMod 3) = 0 := by simpa [hz2re] using hrz
      have ha0 : (x.re : ZMod 3) = 0 := by simpa [hb0] using hab
      rw [ha0, hb0]

/-- Every nonzero Eisenstein integer has the source's normalization
`zeta^i * pi^j * a` with `a == ±1 (mod 3)`. -/
theorem zeta_pi_primary (x : EIntege)
    (hx : x ≠ 0) :
    ∃ (i : Fin 3) (j : ℕ) (a : EIntege),
      IsPrimary a ∧ x = zeta ^ (i : ℕ) * pi ^ j * a := by
  have hfinite : FiniteMultiplicity pi x :=
    FiniteMultiplicity.of_not_isUnit pi_not_unit hx
  obtain ⟨c, hxc, hc⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  obtain ⟨i, hi⟩ := zeta_primary_dvd c hc
  let k : Fin 3 := ⟨(3 - (i : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩
  have hzik : zeta ^ ((i : ℕ) + (k : ℕ)) = 1 := by
    fin_cases i <;> norm_num [k, zeta_pow_three]
  refine ⟨k, multiplicity pi x, zeta ^ (i : ℕ) * c, hi, ?_⟩
  calc
    x = pi ^ multiplicity pi x * c := hxc
    _ =
        zeta ^ ((i : ℕ) + (k : ℕ)) * (pi ^ multiplicity pi x * c) := by
          rw [hzik, one_mul]
    _ = zeta ^ (k : ℕ) * pi ^ multiplicity pi x *
        (zeta ^ (i : ℕ) * c) := by
          rw [pow_add]
          ac_rfl

/-- The note after Example 5.13: an ordinary integer prime to three is
automa congruent to `±1` modulo `3 Z[zeta]`. -/
theorem primary_cast_dvd (a : ℤ) (ha : ¬ (3 : ℤ) ∣ a) :
    IsPrimary (a : EIntege) := by
  apply primary_im_re
  · simp
  · simpa using ha

theorem zeta_ne_zero : zeta ≠ 0 := by
  intro h
  have hz := zeta_pow_three
  rw [h] at hz
  norm_num at hz

theorem pi_ne_zero : pi ≠ 0 := by
  intro h
  have hp := pi_norm
  rw [h] at hp
  norm_num [EInts.norm_formula] at hp

/-- The source's displayed normalization `a = ±(1 + 3(m+n zeta))`.
This deliberately uses the source basis `1, zeta`, rather than the native
coordinate basis `1, omega`. -/
def INormal (a : EIntege) (m n : ℤ) : Prop :=
  a = 1 + 3 * ((m : EIntege) + n * zeta) ∨
    a = -(1 + 3 * ((m : EIntege) + n * zeta))

theorem INormal.isPrimary {a : EIntege} {m n : ℤ}
    (h : INormal a m n) : IsPrimary a := by
  rw [primary_coordinates]
  rcases h with h | h
  · left
    have hcoord : (m : EIntege) + n * zeta =
        (⟨m - n, n⟩ : EIntege) := by
      ext <;> simp [zeta, EInts.omega,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; ring_nf
    exact ⟨m - n, n, h.trans (by rw [hcoord])⟩
  · right
    have hcoord : (m : EIntege) + n * zeta =
        (⟨m - n, n⟩ : EIntege) := by
      ext <;> simp [zeta, EInts.omega,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; ring_nf
    exact ⟨m - n, n, h.trans (by rw [hcoord])⟩

theorem INormal.ne_zero {a : EIntege} {m n : ℤ}
    (h : INormal a m n) : a ≠ 0 := by
  rintro rfl
  rcases h with h | h
  · have hre := congrArg QuadraticAlgebra.re h
    simp [QuadraticAlgebra.re_one, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, zeta, EInts.omega] at hre
    omega
  · have hre := congrArg QuadraticAlgebra.re h
    simp [QuadraticAlgebra.re_one, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, zeta, EInts.omega] at hre
    omega

end EIntege

abbrev EisensteinFraction := FractionRing EIntege

/-- A nonzero Eisenstein integer, viewed as a unit in its fraction field. -/
def eisensteinFractionUnit (a : EIntege) (ha : a ≠ 0) :
    EisensteinFractionˣ :=
  Units.mk0 (algebraMap EIntege EisensteinFraction a)
    (by
      intro hzero
      apply ha
      apply IsFractionRing.injective EIntege EisensteinFraction
      simpa using hzero)

variable {V μ : Type*} [CommGroup μ] [DecidableEq V]

/-- The power-reciprocity interface specialized to nonzero Eisenstein
integers.  The support fields only identify the evident global inputs to
Theorem 5.11: coprime numerators have disjoint non-distinguished support,
while `zeta` and `pi` are supported entirely above three.

No cubic-reciprocity conclusion or local Hilbert value is included here. -/
structure PRContex (V μ : Type*)
    [CommGroup μ] [DecidableEq V] where
  data : PRData EisensteinFractionˣ V μ
  cubicRoot : μ
  cubic_pow_three : cubicRoot ^ 3 = 1
  cubic_ne_one : cubicRoot ≠ 1
  disjoint_coprime : ∀ (a b : EIntege) (ha : a ≠ 0) (hb : b ≠ 0),
    IsCoprime a b →
      Disjoint
        (data.exceptionalSupport (eisensteinFractionUnit a ha))
        (data.exceptionalSupport (eisensteinFractionUnit b hb))
  exceptionalSupport_zeta :
    data.exceptionalSupport
      (eisensteinFractionUnit EIntege.zeta
        EIntege.zeta_ne_zero) = ∅
  exceptionalSupport_pi :
    data.exceptionalSupport
      (eisensteinFractionUnit EIntege.pi
        EIntege.pi_ne_zero) = ∅

namespace PRContex

variable (C : PRContex V μ)

/-- The cubic power-residue symbol `(a/b)` attached to the abstract global
reciprocity data. -/
def cubicResidue (a b : EIntege) (ha : a ≠ 0) (hb : b ≠ 0) : μ :=
  C.data.residueSymbol (eisensteinFractionUnit a ha)
    (eisensteinFractionUnit b hb)

/-- The only unavailable input: the explicit cyclotomic Hilbert-symbol
calculation at the prime above three.  These are precisely the three local
products used in Example 5.13, and contain no global reciprocity conclusion. -/
def CyclotomicHilbertComputation : Prop :=
  (∀ (a b : EIntege) (ha : a ≠ 0) (hb : b ≠ 0),
    EIntege.IsPrimary a → EIntege.IsPrimary b →
      (∏ v ∈ C.data.distinguishedPlaces,
        C.data.localHilbert v (eisensteinFractionUnit b hb)
          (eisensteinFractionUnit a ha)) = 1) ∧
  (∀ (a : EIntege) (m n : ℤ)
      (h : EIntege.INormal a m n),
    (∏ v ∈ C.data.distinguishedPlaces,
      C.data.localHilbert v
        (eisensteinFractionUnit a h.ne_zero)
        (eisensteinFractionUnit EIntege.zeta
          EIntege.zeta_ne_zero)) =
      C.cubicRoot ^ (-m - n : ℤ)) ∧
  (∀ (a : EIntege) (m n : ℤ)
      (h : EIntege.INormal a m n),
    (∏ v ∈ C.data.distinguishedPlaces,
      C.data.localHilbert v
        (eisensteinFractionUnit a h.ne_zero)
        (eisensteinFractionUnit EIntege.pi
          EIntege.pi_ne_zero)) =
      C.cubicRoot ^ m)

/-- **Example VIII.5.13 (cubic reciprocity law; Eisenstein), literal source
statement.** It includes cubic reciprocity for relatively prime primary
elements and the two displayed supplementary laws. -/
def CubicReciprocityLaw : Prop :=
  (∀ (a b : EIntege) (ha : a ≠ 0) (hb : b ≠ 0),
    IsCoprime a b →
    EIntege.IsPrimary a → EIntege.IsPrimary b →
      C.cubicResidue a b ha hb = C.cubicResidue b a hb ha) ∧
  (∀ (a : EIntege) (m n : ℤ)
      (h : EIntege.INormal a m n),
    C.cubicResidue EIntege.zeta a
        EIntege.zeta_ne_zero h.ne_zero =
      C.cubicRoot ^ (-m - n : ℤ) ∧
    C.cubicResidue EIntege.pi a
        EIntege.pi_ne_zero h.ne_zero =
      C.cubicRoot ^ m)

/-- Example 5.13 follows from Theorem 5.11 once the explicit Hilbert-symbol
values at the unique ramified prime are supplied. -/
theorem reciprocity_law_hilbert
    (hlocal : C.CyclotomicHilbertComputation) : C.CubicReciprocityLaw := by
  rcases hlocal with ⟨hprimary, hzeta, hpi⟩
  constructor
  · intro a b ha hb hab haPrimary hbPrimary
    have hreciprocity := C.data.powerReciprocity
      (eisensteinFractionUnit a ha) (eisensteinFractionUnit b hb)
      (C.disjoint_coprime a b ha hb hab)
    rw [hprimary a b ha hb haPrimary hbPrimary] at hreciprocity
    exact mul_inv_eq_one.mp hreciprocity
  · intro a m n hnormalized
    constructor
    · have h := C.data.moreover
          (b := eisensteinFractionUnit a hnormalized.ne_zero)
          (c := eisensteinFractionUnit EIntege.zeta
            EIntege.zeta_ne_zero)
          C.exceptionalSupport_zeta
      exact h.trans (hzeta a m n hnormalized)
    · have h := C.data.moreover
          (b := eisensteinFractionUnit a hnormalized.ne_zero)
          (c := eisensteinFractionUnit EIntege.pi
            EIntege.pi_ne_zero)
          C.exceptionalSupport_pi
      exact h.trans (hpi a m n hnormalized)

end PRContex

end

end Towers.CField.HRecip
