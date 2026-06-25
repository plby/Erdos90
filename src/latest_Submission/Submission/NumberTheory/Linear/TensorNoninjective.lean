import Mathlib

/-!
# Milne, Algebraic Number Theory, tensor products after Lemma 1.17

Tensoring an injective map need not produce an injective map. Milne's example tensors
multiplication by two on `ℤ` with `ℤ / 2ℤ`.
-/

namespace Submission.NumberTheory.Milne

/-- Multiplication by two on `ℤ` ceases to be injective after tensoring with `ZMod 2`.
This is Milne's counterexample following Lemma 1.17. -/
theorem tensor_not_injective :
    ¬Function.Injective ((LinearMap.mulLeft ℤ (2 : ℤ)).rTensor (ZMod 2)) := by
  intro h
  have hx : ((1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2)) = 0 := h (by
    simp only [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, mul_one, map_zero]
    rw [show (2 : ℤ) = (2 : ℤ) • (1 : ℤ) by norm_num, TensorProduct.smul_tmul]
    have htwo : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
    rw [htwo, TensorProduct.tmul_zero])
  have hzero : (1 : ZMod 2) = 0 := by
    simpa only [TensorProduct.lid_tmul, one_smul, map_zero] using
      congrArg (TensorProduct.lid ℤ (ZMod 2)) hx
  exact one_ne_zero hzero

end Submission.NumberTheory.Milne
