import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Intersections of cyclotomic fields with coprime conductors

This file formalizes Milne's Remark 6.3(b), in the stronger form for arbitrary
coprime conductors.
-/

namespace Towers.NumberTheory.Milne

open NumberField

/-- Cyclotomic subfields of a common number field with coprime conductors are
linearly disjoint over `ℚ`. -/
theorem disjoint_coprime_conductors
    {E : Type*} [Field E] [NumberField E]
    {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (F₁ F₂ : IntermediateField ℚ E)
    [IsCyclotomicExtension {n₁} ℚ F₁]
    [IsCyclotomicExtension {n₂} ℚ F₂]
    (h : n₁.Coprime n₂) :
    F₁.LinearDisjoint F₂ := by
  have h_coprime_discr :
      IsCoprime (NumberField.discr F₁) (NumberField.discr F₂) := by
    rw [Int.isCoprime_iff_nat_coprime,
      IsCyclotomicExtension.Rat.natAbs_discr n₁ F₁,
      IsCyclotomicExtension.Rat.natAbs_discr n₂ F₂]
    refine Nat.Coprime.coprime_div_left ?_
      (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos n₁))
    refine Nat.Coprime.coprime_div_right ?_
      (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos n₂))
    exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ h)
  letI : IsGalois ℚ F₁ := IsCyclotomicExtension.isGalois {n₁} ℚ F₁
  exact NumberField.linearDisjoint_of_isGalois_isCoprime_discr E F₁ F₂ h_coprime_discr

/-- Cyclotomic subfields with coprime conductors intersect only in `ℚ`. -/
theorem inf_coprime_conductors
    {E : Type*} [Field E] [NumberField E]
    {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (F₁ F₂ : IntermediateField ℚ E)
    [IsCyclotomicExtension {n₁} ℚ F₁]
    [IsCyclotomicExtension {n₂} ℚ F₂]
    (h : n₁.Coprime n₂) :
    F₁ ⊓ F₂ = ⊥ :=
  (disjoint_coprime_conductors F₁ F₂ h).inf_eq_bot

/-- Milne, Remark 6.3(b): cyclotomic fields of distinct prime-power
conductors have intersection `ℚ`. -/
theorem distinct_inf_bot
    {E : Type*} [Field E] [NumberField E]
    {p q r s : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (F₁ F₂ : IntermediateField ℚ E)
    [IsCyclotomicExtension {p ^ (r + 1)} ℚ F₁]
    [IsCyclotomicExtension {q ^ (s + 1)} ℚ F₂]
    (hpq : p ≠ q) :
    F₁ ⊓ F₂ = ⊥ := by
  letI : NeZero (p ^ (r + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  letI : NeZero (q ^ (s + 1)) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  exact inf_coprime_conductors F₁ F₂
    (Nat.coprime_pow_primes (r + 1) (s + 1) hp.out hq.out hpq)

end Towers.NumberTheory.Milne
