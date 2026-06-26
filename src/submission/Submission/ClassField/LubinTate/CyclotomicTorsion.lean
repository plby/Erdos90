import Mathlib.RingTheory.RootsOfUnity.Basic
import Submission.ClassField.LubinTate.TorsionSeries

/-!
# Class Field Theory, Chapter I, Example 3.2

For the cyclotomic Lubin--Tate series `(1 + T)^p - 1`, translation by one
identifies the zeros of the `n`-fold iterate with the `p^n`-th roots of
unity.  Under this identification the multiplicative formal-group law
`X + Y + XY` becomes ordinary multiplication.
-/

namespace Submission.CField.LTate

open Submission.CField.FGroups

noncomputable section

/-- Evaluation of the `n`-fold cyclotomic Lubin--Tate iterate is the
elementary function `(1 + x)^(m^n) - 1`. -/
theorem eval₂_substitutionIterate_cyclotomic
    {R : Type*} [CommRing R] [UniformSpace R] (m n : ℕ) (x : R) :
    PowerSeries.eval₂ (RingHom.id R) x
        (substitutionIterate (cyclotomicPowerSeries (R := R) m) n) =
      multiplicativePowerEndomorphism (m ^ n) x := by
  rw [substitutionIterate_cyclotomic]
  rw [show cyclotomicPowerSeries (R := R) (m ^ n) =
      (((1 + Polynomial.X) ^ (m ^ n) - 1 : Polynomial R) : PowerSeries R) by
        simp [cyclotomicPowerSeries]]
  rw [PowerSeries.eval₂_coe]
  simp [multiplicativePowerEndomorphism]

/-- The zero set of the cyclotomic Lubin--Tate endomorphism
`(1 + T)^N - 1`. -/
abbrev CTorsio (R : Type*) [CommRing R] (N : ℕ) :=
  {x : R // multiplicativePowerEndomorphism N x = 0}

/-- The zeros of the evaluated `n`-fold cyclotomic iterate are exactly the
elements of `CTorsio R (m^n)`. -/
def eval₂SubstitutionIterateEquivTorsion
    {R : Type*} [CommRing R] [UniformSpace R] (m n : ℕ) :
    {x : R // PowerSeries.eval₂ (RingHom.id R) x
        (substitutionIterate (cyclotomicPowerSeries (R := R) m) n) = 0} ≃
      CTorsio R (m ^ n) where
  toFun x := ⟨x, by
    simpa only [eval₂_substitutionIterate_cyclotomic] using x.2⟩
  invFun x := ⟨x, by
    simpa only [eval₂_substitutionIterate_cyclotomic] using x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace CTorsio

variable {R : Type*} [CommRing R] {N : ℕ}

/-- The multiplicative formal-group law preserves cyclotomic torsion. -/
def law (x y : CTorsio R N) : CTorsio R N :=
  ⟨multiplicativeLaw x y, by
    rw [multiplicative_endomorphism_law, x.2, y.2]
    simp [multiplicativeLaw]⟩

@[simp]
theorem coe_law (x y : CTorsio R N) :
    (law x y : R) = multiplicativeLaw (x : R) y :=
  rfl

/-- The natural-number scalar `[a](x) = (1+x)^a-1` preserves cyclotomic
torsion. -/
def natScalar (a : ℕ) (x : CTorsio R N) :
    CTorsio R N :=
  ⟨multiplicativePowerEndomorphism a (x : R), by
    apply sub_eq_zero.mpr
    have hx : (1 + (x : R)) ^ N = 1 := sub_eq_zero.mp x.2
    rw [multiplicativePowerEndomorphism]
    rw [show 1 + ((1 + (x : R)) ^ a - 1) = (1 + x) ^ a by ring]
    rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]⟩

@[simp]
theorem coe_natScalar (a : ℕ) (x : CTorsio R N) :
    (natScalar a x : R) = multiplicativePowerEndomorphism a (x : R) :=
  rfl

/-- Translation by one identifies the zeros of `(1 + T)^N - 1` with the
`N`-th roots of unity. -/
def equivRootsUnity [NeZero N] :
    CTorsio R N ≃ rootsOfUnity N R where
  toFun x := rootsOfUnity.mkOfPowEq (1 + (x : R)) (sub_eq_zero.mp x.2)
  invFun z := ⟨((z : Rˣ) : R) - 1, by
    rw [multiplicativePowerEndomorphism]
    have hz : (((z : Rˣ) : R) ^ N) = 1 :=
      (mem_rootsOfUnity' N (z : Rˣ)).mp z.2
    simpa using sub_eq_zero.mpr hz⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply rootsOfUnity.coe_injective
    simp

@[simp]
theorem equiv_roots_unity [NeZero N] (x : CTorsio R N) :
    ((((equivRootsUnity x : rootsOfUnity N R) : Rˣ) : R)) = 1 + x :=
  rfl

@[simp]
theorem roots_unity_symm [NeZero N] (z : rootsOfUnity N R) :
    ((equivRootsUnity (R := R) (N := N)).symm z : R) =
      ((z : Rˣ) : R) - 1 :=
  rfl

/-- Example 3.2's compatibility: `alpha ↦ 1 + alpha` carries formal-group
addition to multiplication of roots of unity. -/
theorem roots_unity_law [NeZero N]
    (x y : CTorsio R N) :
    equivRootsUnity (law x y) = equivRootsUnity x * equivRootsUnity y := by
  apply rootsOfUnity.coe_injective
  simp only [equiv_roots_unity, coe_law, Subgroup.coe_mul,
    Units.val_mul]
  exact add_multiplicative_law (x : R) y

/-- The natural scalar action corresponds to powering roots of unity. -/
theorem roots_unity_scalar [NeZero N]
    (a : ℕ) (x : CTorsio R N) :
    equivRootsUnity (natScalar a x) = equivRootsUnity x ^ a := by
  apply rootsOfUnity.coe_injective
  change 1 + ((1 + (x : R)) ^ a - 1) = (1 + (x : R)) ^ a
  ring

/-- The set equivalence with roots of unity, with the multiplicative target
regarded as an additive group. -/
private def additiveRootsUnity [NeZero N] :
    CTorsio R N ≃ Additive (rootsOfUnity N R) :=
  equivRootsUnity.trans Additive.ofMul

/-- The commutative group structure on cyclotomic torsion transported from
the group of roots of unity. -/
noncomputable instance [NeZero N] : AddCommGroup (CTorsio R N) :=
  additiveRootsUnity.addCommGroup

/-- The transported addition is precisely the multiplicative formal-group
law `x + y + xy`. -/
theorem add_eq_law [NeZero N] (x y : CTorsio R N) :
    x + y = law x y := by
  let e := additiveRootsUnity (R := R) (N := N)
  apply e.injective
  change (Equiv.addEquiv e) (x + y) = e (law x y)
  rw [map_add]
  change Additive.ofMul (equivRootsUnity x) +
      Additive.ofMul (equivRootsUnity y) =
    Additive.ofMul (equivRootsUnity (law x y))
  rw [roots_unity_law]
  rfl

/-- Example 3.2 as a bundled group isomorphism: formal addition on the
torsion set corresponds to multiplication of roots of unity. -/
def addRootsUnity [NeZero N] :
    CTorsio R N ≃+ Additive (rootsOfUnity N R) :=
  Equiv.addEquiv additiveRootsUnity

end CTorsio

/-- Example 3.2's literal bijection from roots of the `n`-fold cyclotomic
Lubin--Tate iterate to the `(m^n)`-th roots of unity. -/
def eval₂SubstitutionIterateEquivRootsOfUnity
    {R : Type*} [CommRing R] [UniformSpace R]
    (m : ℕ) [NeZero m] (n : ℕ) :
    {x : R // PowerSeries.eval₂ (RingHom.id R) x
        (substitutionIterate (cyclotomicPowerSeries (R := R) m) n) = 0} ≃
      rootsOfUnity (m ^ n) R :=
  (eval₂SubstitutionIterateEquivTorsion m n).trans
    CTorsio.equivRootsUnity

/-- The explicit set equivalence in Example 3.2 for the `n`-fold iterate of
the cyclotomic Lubin--Tate series. -/
def padicRootsUnity
    (p : ℕ) [Fact p.Prime] (n : ℕ) {R : Type*} [CommRing R] :
    CTorsio R (p ^ n) ≃ rootsOfUnity (p ^ n) R := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact CTorsio.equivRootsUnity

@[simp]
theorem coe_roots_unity
    (p : ℕ) [Fact p.Prime] (n : ℕ) {R : Type*} [CommRing R]
    (x : CTorsio R (p ^ n)) :
    (((padicRootsUnity p n x : rootsOfUnity (p ^ n) R) : Rˣ) : R) =
      1 + x := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact CTorsio.equiv_roots_unity x

end

end Submission.CField.LTate
