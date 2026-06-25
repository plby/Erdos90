import Mathlib.GroupTheory.OrderOfElement

/-!
# Chapter VII, Section 6: the coprime-exponent reduction

In Lemma 6.1 the norm quotient is killed by the prime `p`, while the
cyclotomic auxiliary degree `m` divides `p - 1`.  Hence `m` is coprime to
`p`, and multiplication by `m` is an automorphism of the quotient.  The
result below records that group-theoretic step for an arbitrary commutative
group of exponent dividing `p`.
-/

namespace Towers.CField.KNIndex

variable {A : Type*} [CommGroup A]

/-- Raising to a power coprime to the exponent is surjective. -/
theorem surjective_coprime_exponent
    {m p : ℕ} (hmp : m.Coprime p) (hp : ∀ x : A, x ^ p = 1) :
    Function.Surjective (powMonoidHom m : A →* A) := by
  intro x
  have horder : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hp x)
  have hcop : m.Coprime (orderOf x) := hmp.coprime_dvd_right horder
  obtain ⟨q, hq⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨x ^ q, ?_⟩
  calc
    (x ^ q) ^ m = x ^ (q * m) := (pow_mul x q m).symm
    _ = x ^ (m * q) := by rw [Nat.mul_comm q m]
    _ = (x ^ m) ^ q := pow_mul x m q
    _ = x := hq

/-- Raising to a power coprime to the exponent is injective. -/
theorem injective_coprime_exponent
    {m p : ℕ} (hmp : m.Coprime p) (hp : ∀ x : A, x ^ p = 1) :
    Function.Injective (powMonoidHom m : A →* A) := by
  intro x y hxy
  change x ^ m = y ^ m at hxy
  let z := x * y⁻¹
  have hzm : z ^ m = 1 := by
    change (x * y⁻¹) ^ m = 1
    rw [mul_pow, inv_pow, hxy, mul_inv_cancel]
  have horderM : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hzm
  have horderP : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one (hp z)
  have horder : orderOf z = 1 :=
    Nat.eq_one_of_dvd_coprimes hmp horderM horderP
  have hz : z = 1 := orderOf_eq_one_iff.mp horder
  exact mul_inv_eq_one.mp hz

/-- **Lemma VII.6.1, algebraic core.** On a commutative group killed by `p`,
the `m`th-power map is bijective whenever `m` and `p` are coprime. -/
theorem bijective_coprime_exponent
    {m p : ℕ} (hmp : m.Coprime p) (hp : ∀ x : A, x ^ p = 1) :
    Function.Bijective (powMonoidHom m : A →* A) :=
  ⟨injective_coprime_exponent hmp hp,
    surjective_coprime_exponent hmp hp⟩

end Towers.CField.KNIndex
