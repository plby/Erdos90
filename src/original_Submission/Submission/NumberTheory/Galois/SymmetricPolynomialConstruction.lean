import Submission.NumberTheory.Galois.TransitiveCycleSwap
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.ReduceModChar


/-!
# Milne, Chapter 8, Example 8.27

Milne combines three prescribed monic integer polynomials by
`-15 f₁ + 10 f₂ + 6 f₃`.  The resulting polynomial reduces to `f₁`, `f₂`,
and `f₃` modulo `2`, `3`, and `5`, respectively.  The corresponding
Frobenius cycle types give a transitive Galois group, an `(n - 1)`-cycle,
and a transposition, so Lemma 8.26 identifies the group with `Sₙ`.
-/

namespace Submission.NumberTheory.Milne

open Equiv Finset MulAction Polynomial Subgroup

/-- The Chinese-remainder combination used in Example 8.27. -/
noncomputable def symmetricGroupConstruction (f₁ f₂ f₃ : ℤ[X]) : ℤ[X] :=
  C (-15) * f₁ + C 10 * f₂ + C 6 * f₃

/-- The coefficients in the Chinese-remainder combination add to one, so
three monic polynomials of the same degree again give a monic polynomial of
that degree. -/
theorem polynomial_monic_degree {n : ℕ} {f₁ f₂ f₃ : ℤ[X]}
    (hf₁ : IsMonicOfDegree f₁ n) (hf₂ : IsMonicOfDegree f₂ n)
    (hf₃ : IsMonicOfDegree f₃ n) :
    IsMonicOfDegree (symmetricGroupConstruction f₁ f₂ f₃) n := by
  rw [isMonicOfDegree_iff]
  constructor
  · exact natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        ((natDegree_C_mul_le (-15) f₁).trans hf₁.natDegree_eq.le)
        ((natDegree_C_mul_le 10 f₂).trans hf₂.natDegree_eq.le))
      ((natDegree_C_mul_le 6 f₃).trans hf₃.natDegree_eq.le)
  · have h₁ := (isMonicOfDegree_iff f₁ n).mp hf₁ |>.2
    have h₂ := (isMonicOfDegree_iff f₂ n).mp hf₂ |>.2
    have h₃ := (isMonicOfDegree_iff f₃ n).mp hf₃ |>.2
    simp [symmetricGroupConstruction, h₁, h₂, h₃]

/-- The Example 8.27 combination reduces to `f₁` modulo `2`. -/
theorem Polynomial_map_two (f₁ f₂ f₃ : ℤ[X]) :
    (symmetricGroupConstruction f₁ f₂ f₃).map (Int.castRingHom (ZMod 2)) =
      f₁.map (Int.castRingHom (ZMod 2)) := by
  simp only [symmetricGroupConstruction, Int.reduceNeg, eq_intCast, Int.cast_neg, Int.cast_ofNat,
    neg_mul,
    Polynomial.map_add, Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_ofNat]
  reduce_mod_char

/-- The Example 8.27 combination reduces to `f₂` modulo `3`. -/
theorem Polynomial_map_three (f₁ f₂ f₃ : ℤ[X]) :
    (symmetricGroupConstruction f₁ f₂ f₃).map (Int.castRingHom (ZMod 3)) =
      f₂.map (Int.castRingHom (ZMod 3)) := by
  simp only [symmetricGroupConstruction, Int.reduceNeg, eq_intCast, Int.cast_neg, Int.cast_ofNat,
    neg_mul,
    Polynomial.map_add, Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_ofNat]
  reduce_mod_char

/-- The Example 8.27 combination reduces to `f₃` modulo `5`. -/
theorem Polynomial_map_five (f₁ f₂ f₃ : ℤ[X]) :
    (symmetricGroupConstruction f₁ f₂ f₃).map (Int.castRingHom (ZMod 5)) =
      f₃.map (Int.castRingHom (ZMod 5)) := by
  simp only [symmetricGroupConstruction, Int.reduceNeg, eq_intCast, Int.cast_neg, Int.cast_ofNat,
    neg_mul,
    Polynomial.map_add, Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_ofNat]
  reduce_mod_char

/-- A commuting product of a transposition and an odd-order permutation has
an odd power equal to that transposition.  This is the group-theoretic step
in part (c') of Example 8.27. -/
theorem swap_odd_pow
    {alpha : Type*} [DecidableEq alpha] [Finite alpha]
    {swap oddPart : Equiv.Perm alpha} (hswap : swap.IsSwap)
    (hodd : Odd (orderOf oddPart)) (hcomm : Commute swap oddPart) :
    (swap * oddPart) ^ orderOf oddPart = swap := by
  rw [hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
  rw [← pow_mod_orderOf swap, hswap.orderOf, Nat.odd_iff.mp hodd, pow_one]

/-- The group-theoretic conclusion of Example 8.27.  The mod-`2` cycle makes
the action transitive, the mod-`3` cycle moves all but one root, and an odd
power of the mod-`5` Frobenius element is a transposition. -/
theorem symmetric_constructionperm_top
    {alpha : Type*} [DecidableEq alpha] [Fintype alpha]
    (H : Subgroup (Equiv.Perm alpha)) [MulAction.IsPretransitive H alpha]
    {longCycle rho swap oddPart : Equiv.Perm alpha}
    (hlongCycle : longCycle.IsCycle)
    (hlongCycleCard : longCycle.support.card + 1 = Fintype.card alpha)
    (hswap : swap.IsSwap) (hodd : Odd (orderOf oddPart))
    (hcomm : Commute swap oddPart) (hrho : rho = swap * oddPart)
    (hlongCycleMem : longCycle ∈ H) (hrhoMem : rho ∈ H) :
    H = ⊤ := by
  have hswapMem : swap ∈ H := by
    rw [← swap_odd_pow hswap hodd hcomm, ← hrho]
    exact H.pow_mem hrhoMem (orderOf oddPart)
  exact perm_pretransitive_cycle
    H hlongCycle hlongCycleCard hswap hlongCycleMem hswapMem

end Submission.NumberTheory.Milne
