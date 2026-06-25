import Towers.NumberTheory.Quadratic.QuadraticUnitExamples
import Towers.NumberTheory.Quadratic.ContinuedFractionExpansion

/-!
# Milne, Algebraic Number Theory, real quadratic numerical examples

We verify the Pell identities used for Milne's `ℚ(√94)` example and for Exercise 5-2.
The continued-fraction minimality assertions identifying these as fundamental units require
additional continued-fraction infrastructure.
-/

namespace Towers.NumberTheory.Milne

unseal Nat.sqrt.iter in
/-- The canonical continued fraction of `√94` has integer part `9`. -/
theorem sqrt_94_head :
    (GenContFract.of (Real.sqrt ((94 : ℕ) : ℝ))).h = 9 := by
  rw [GenContFract.of_h_eq_floor, Real.floor_real_sqrt_eq_nat_sqrt]
  have hsqrt : Nat.sqrt 94 = 9 := by decide
  rw [hsqrt]
  norm_num

/-- The finite continued fraction `[9; 1, 2, 3, 1, 1, 5, 1, 8, 1, 5, 1, 1, 3, 2, 1]`
whose value is Milne's fifteenth convergent for `√94`. -/
def sqrtFifteenthConvergent : GenContFract ℚ :=
  ⟨9, Stream'.Seq.ofList
    ([1, 2, 3, 1, 1, 5, 1, 8, 1, 5, 1, 1, 3, 2, 1].map fun b : ℚ =>
      (GenContFract.Pair.mk 1 b))⟩

/-- Milne's displayed fifteenth convergent of the continued fraction for `√94`. -/
theorem sqrt_94_fifteenth :
    sqrtFifteenthConvergent.convs 15 = (2143295 : ℚ) / 221064 := by
  norm_num [sqrtFifteenthConvergent, GenContFract.convs, GenContFract.nums,
    GenContFract.dens, GenContFract.conts, GenContFract.contsAux,
    GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen,
    Stream'.Seq.ofList, Stream'.map, Stream'.tail, Stream'.get]

theorem sqrt_94_identity :
    (2143295 : ℤ) ^ 2 - 94 * (221064 : ℤ) ^ 2 = 1 := by
  norm_num

theorem sqrt_94_large :
    IsUnit (⟨2143295, 221064⟩ : ℤ√94) := by
  rw [zsqrtd_pell_equation]
  exact Or.inl sqrt_94_identity

theorem sqrt_67_identity :
    (48842 : ℤ) ^ 2 - 67 * (5967 : ℤ) ^ 2 = 1 := by
  norm_num

theorem sqrt_67_exercise :
    IsUnit (⟨48842, 5967⟩ : ℤ√67) := by
  rw [zsqrtd_pell_equation]
  exact Or.inl sqrt_67_identity

end Towers.NumberTheory.Milne
