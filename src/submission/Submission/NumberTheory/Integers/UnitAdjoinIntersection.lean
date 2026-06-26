import Mathlib

/-!
# Milne, Algebraic Number Theory, Exercise 2-5

An element lying in both `A[u]` and `A[u⁻¹]`, for a unit `u`, is integral over `A`.
The proof uses the finite `A`-module spanned by a bounded interval of Laurent powers of `u`.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

private def laurentPowers (u : Bˣ) (m n : ℕ) : Set B :=
  (fun k : ℤ => ((u ^ k : Bˣ) : B)) '' Set.Icc (-(m : ℤ)) (n : ℤ)

private lemma laurentPowers_finite (u : Bˣ) (m n : ℕ) :
    (laurentPowers u m n).Finite :=
  (Set.finite_Icc (-(m : ℤ)) (n : ℤ)).image _

private lemma zpow_laurent_span (u : Bˣ) (m n : ℕ) (k : ℤ)
    (hk : k ∈ Set.Icc (-(m : ℤ)) (n : ℤ)) :
    ((u ^ k : Bˣ) : B) ∈ Submodule.span A (laurentPowers u m n) :=
  Submodule.subset_span ⟨k, hk, rfl⟩

private lemma one_laurent_span (u : Bˣ) (m n : ℕ) :
    (1 : B) ∈ Submodule.span A (laurentPowers u m n) := by
  simpa using zpow_laurent_span u m n 0 (by simp)

private lemma coe_pow_zpow (u : Bˣ) (i : ℕ) (k : ℤ) :
    (u : B) ^ i * ((u ^ k : Bˣ) : B) = ((u ^ ((i : ℤ) + k) : Bˣ) : B) := by
  change (((u ^ i) * (u ^ k) : Bˣ) : B) = ((u ^ ((i : ℤ) + k) : Bˣ) : B)
  congr 1
  rw [← zpow_natCast, ← zpow_add]

private lemma coe_inv_zpow (u : Bˣ) (i : ℕ) (k : ℤ) :
    (↑u⁻¹ : B) ^ i * ((u ^ k : Bˣ) : B) = ((u ^ (k - (i : ℤ)) : Bˣ) : B) := by
  change ((((u⁻¹) ^ i) * (u ^ k) : Bˣ) : B) = ((u ^ (k - (i : ℤ)) : Bˣ) : B)
  congr 1
  simp [zpow_sub, zpow_natCast, mul_comm]

private lemma integral_stable_submodule
    (M : Submodule A B) (hMfg : M.FG) (hone : (1 : B) ∈ M)
    (x : B) (hx : ∀ y ∈ M, x * y ∈ M) : IsIntegral A x := by
  letI : Module.Finite A M := Module.Finite.of_fg hMfg
  let f : Module.End A M :=
    { toFun := fun y => ⟨x * y, hx y y.property⟩
      map_add' := fun y z => by ext; simp [mul_add]
      map_smul' := fun a y => by ext; simp [Algebra.smul_def, mul_left_comm] }
  obtain ⟨p, hpmonic, hpzero⟩ := LinearMap.exists_monic_and_aeval_eq_zero A f
  refine ⟨p, hpmonic, ?_⟩
  let oneM : M := ⟨1, hone⟩
  have happly : Polynomial.aeval f p oneM = 0 := by rw [hpzero]; rfl
  have fpow (n : ℕ) (y : M) : (((f ^ n) y : M) : B) = x ^ n * y := by
    induction n generalizing y with
    | zero => simp
    | succ n hn =>
        rw [pow_succ, Module.End.mul_apply, hn]
        change x ^ n * (x * (y : B)) = x ^ (n + 1) * y
        ring
  have heval (r : A[X]) :
      ((Polynomial.aeval f r oneM : M) : B) = Polynomial.aeval x r := by
    induction r using Polynomial.induction_on' with
    | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
    | monomial n a =>
        simp [Polynomial.aeval_monomial, Module.End.mul_apply, fpow, oneM, Algebra.smul_def]
  change Polynomial.aeval x p = 0
  rw [← heval]
  exact congrArg Subtype.val happly

/-- Exercise 2-5: the intersection `A[u] ∩ A[u⁻¹]` consists of elements integral over `A`. -/
theorem integral_adjoin_inv (u : Bˣ) (x : B)
    (hpos : x ∈ Algebra.adjoin A ({(u : B)} : Set B))
    (hneg : x ∈ Algebra.adjoin A ({(↑u⁻¹ : B)} : Set B)) :
    IsIntegral A x := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hpos hneg
  obtain ⟨p, hp⟩ := hpos
  obtain ⟨q, hq⟩ := hneg
  let M : Submodule A B := Submodule.span A (laurentPowers u q.natDegree p.natDegree)
  have hMfg : M.FG := Submodule.fg_span (laurentPowers_finite u q.natDegree p.natDegree)
  have hone : (1 : B) ∈ M := one_laurent_span u q.natDegree p.natDegree
  apply integral_stable_submodule M hMfg hone x
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      rcases hz with ⟨k, hk, rfl⟩
      rcases hk with ⟨hk_lower, hk_upper⟩
      rcases le_total k 0 with hk_nonpos | hk_nonneg
      · rw [← hp]
        change Polynomial.aeval (u : B) p * ((u ^ k : Bˣ) : B) ∈ M
        rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
        apply Submodule.sum_mem
        intro i hi
        rw [Finset.mem_range] at hi
        have hki : (i : ℤ) + k ∈
            Set.Icc (-(q.natDegree : ℤ)) (p.natDegree : ℤ) := by
          constructor <;> omega
        have hpow := zpow_laurent_span (A := A) u q.natDegree p.natDegree
          ((i : ℤ) + k) hki
        convert M.smul_mem (p.coeff i) hpow using 1
        simp only [Algebra.smul_def]
        rw [mul_assoc, coe_pow_zpow]
      · rw [← hq]
        change Polynomial.aeval (↑u⁻¹ : B) q * ((u ^ k : Bˣ) : B) ∈ M
        rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
        apply Submodule.sum_mem
        intro i hi
        rw [Finset.mem_range] at hi
        have hki : k - (i : ℤ) ∈
            Set.Icc (-(q.natDegree : ℤ)) (p.natDegree : ℤ) := by
          constructor <;> omega
        have hpow := zpow_laurent_span (A := A) u q.natDegree p.natDegree
          (k - (i : ℤ)) hki
        convert M.smul_mem (q.coeff i) hpow using 1
        simp only [Algebra.smul_def]
        rw [mul_assoc, coe_inv_zpow]
  | zero => simp [M]
  | add y z _ _ hy hz => simpa [mul_add] using M.add_mem hy hz
  | smul a y _ hy =>
      simpa [Algebra.smul_def, mul_assoc, mul_left_comm] using M.smul_mem a hy

end Submission.NumberTheory.Milne
