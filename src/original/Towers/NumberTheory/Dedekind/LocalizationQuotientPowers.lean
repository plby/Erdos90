import Mathlib

/-!
# Milne, Algebraic Number Theory, Lemma 3.10

Localization at a maximal ideal does not change the quotients by powers of that ideal.
-/

namespace Towers.NumberTheory.Milne

open scoped nonZeroDivisors

variable (A : Type*) [CommRing A] [IsDomain A]

/-- Lemma 3.10: if `p` is maximal and `q = p A_p`, then the canonical map
`A / p^m → A_p / q^m` is an isomorphism. -/
noncomputable def quotientLocalizationPrime
    (p : Ideal A) [p.IsMaximal] (m : ℕ) :
    A ⧸ p ^ m ≃+*
      Localization.AtPrime p ⧸
        (p.map (algebraMap A (Localization.AtPrime p))) ^ m := by
  letI : p.IsPrime := Ideal.IsMaximal.isPrime (inferInstance : p.IsMaximal)
  let S := Localization.AtPrime p
  let q : Ideal S := p.map (algebraMap A S)
  have hpow : p ^ m ≤ (q ^ m).comap (algebraMap A S) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  let f : A ⧸ p ^ m →+* S ⧸ q ^ m :=
    Ideal.quotientMap (q ^ m) (algebraMap A S) hpow
  apply RingEquiv.ofBijective f
  constructor
  · apply Ideal.quotientMap_injective'
    intro a ha
    rw [Ideal.mem_comap, ← Ideal.map_pow] at ha
    obtain ⟨s, hs, hsa⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S (p ^ m) a).mp ha
    exact (Ideal.IsMaximal.mul_mem_pow p hsa).resolve_left hs
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
    obtain ⟨b, i, hi, hbi⟩ := Ideal.IsMaximal.exists_inv_pow p s.2 m
    refine ⟨Ideal.Quotient.mk (p ^ m) (b * a), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    rw [← Ideal.map_pow]
    rw [← IsLocalization.mk'_one (S := S) (M := p.primeCompl)]
    rw [← IsLocalization.mk'_sub]
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    refine ⟨1, p.primeCompl.one_mem, ?_⟩
    simp only [Submonoid.coe_one, one_mul, mul_one]
    rw [show (b * a) * (s : A) - a = (b * (s : A) - 1) * a by ring]
    have hdiff : b * (s : A) - 1 = -i := by
      rw [← hbi]
      ring
    rw [hdiff]
    exact (p ^ m).mul_mem_right a ((p ^ m).neg_mem hi)

omit [IsDomain A] in
@[simp]
theorem localization_prime_mk
    (p : Ideal A) [p.IsMaximal] (m : ℕ) (a : A) :
    quotientLocalizationPrime A p m (Ideal.Quotient.mk (p ^ m) a) =
      Ideal.Quotient.mk
        ((p.map (algebraMap A (Localization.AtPrime p))) ^ m)
        (algebraMap A (Localization.AtPrime p) a) := by
  letI : p.IsPrime := Ideal.IsMaximal.isPrime (inferInstance : p.IsMaximal)
  rfl

end Towers.NumberTheory.Milne
