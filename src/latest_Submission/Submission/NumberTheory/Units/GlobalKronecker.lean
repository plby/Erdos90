import Submission.NumberTheory.Units.BoundedAlgebraicIntegers
import Submission.NumberTheory.Units.BoundedConjugates

/-!
# Milne, Algebraic Number Theory, Corollary 5.6 (global form)

Kronecker's theorem for a complex algebraic integer, without first fixing an ambient number
field.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

/-- **Milne, Corollary 5.6.** A complex algebraic integer all of whose rational conjugates
have absolute value one is a root of unity. -/
theorem complex_conjugates_norm {x : ℂ}
    (hxi : IsIntegral ℤ x) (hx : ∀ y : ℂ, IsConjRoot ℚ x y → ‖y‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {x}
  let xK : K :=
    ⟨x, IntermediateField.subset_adjoin ℚ {x} (Set.mem_singleton x)⟩
  letI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hxi.tower_top
  letI : NumberField K := {}
  have hxKi : IsIntegral ℤ xK := by
    let valZ : K →ₐ[ℤ] ℂ := (IntermediateField.val K).restrictScalars ℤ
    apply (isIntegral_algHom_iff valZ Subtype.val_injective).mp
    simpa only [valZ, xK] using hxi
  have hxKconj : ∀ φ : K →+* ℂ, ‖φ xK‖ = 1 := by
    intro φ
    apply hx
    apply (isConjRoot_iff_aeval_eq_zero hxi.tower_top).2
    have hmin : minpoly ℚ xK = minpoly ℚ x := by
      simpa only [xK] using
        (minpoly.algHom_eq (IntermediateField.val K) Subtype.val_injective xK).symm
    rw [← hmin]
    exact minpoly.aeval_algHom ℚ φ.toRatAlgHom xK
  obtain ⟨n, hn, hpow⟩ :=
    integral_all_conjugates K hxKi hxKconj
  exact ⟨n, hn, congrArg Subtype.val hpow⟩

end Submission.NumberTheory.Milne
