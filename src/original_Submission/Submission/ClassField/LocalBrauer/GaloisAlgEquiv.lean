import Submission.ClassField.LocalBrauer.LinearlyDisjointChange

/-!
# Transporting carry classes through a coefficient-field equivalence
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {F E C : Type u} [Field F] [Field E] [Field C]
  [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
  [Algebra F C] [FiniteDimensional F C] [IsGalois F C]

private theorem brauer_change_self (x : BrauerGroup F) :
    brauerBaseChange F F x = x := by
  induction x using Quotient.inductionOn with
  | _ A =>
      apply Quotient.sound
      exact brauer_equivalent_alg F _ _
        ((Algebra.TensorProduct.commRight F F A).symm.trans
          (Algebra.TensorProduct.lid F A))

variable {n : ℕ} [NeZero n]

/-- An equivalence of Galois coefficient fields carries the corresponding
carry crossed-product Brauer class to the transported carry class. -/
theorem brauer_carry_alg
    (e : E ≃ₐ[F] C)
    (eE : Multiplicative (ZMod n) ≃* Gal(E/F)) (a : Fˣ) :
    CProduc.brauerClass F E (galoisCarryCocycle F eE a) =
      CProduc.brauerClass F C
        (galoisCarryCocycle F (eE.trans e.autCongr) a) := by
  let coeffEquiv : E ⊗[F] F ≃ₐ[F] C :=
    ((Algebra.TensorProduct.commRight F F E).symm.trans
      (Algebra.TensorProduct.lid F E)).trans e
  have hi : ∀ sigma : Gal(E/F), ∀ x : E,
      e (sigma x) = e.autCongr sigma (e x) := by
    intro sigma x
    simp [AlgEquiv.autCongr_apply]
  have hbase : ∀ x : F,
      e (algebraMap F E x) = algebraMap F C (algebraMap F F x) := by
    intro x
    simp
  have hcoeff : ∀ (x : E) (y : F),
      coeffEquiv (x ⊗ₜ[F] y) = e x * algebraMap F C y := by
    intro x y
    simp [coeffEquiv, Algebra.smul_def, mul_comm]
  have h := brauer_base_carry e.toRingHom e.autCongr hi
    hbase coeffEquiv hcoeff eE (eE.trans e.autCongr) (fun _ ↦ rfl) a
  rw [brauer_change_self] at h
  simpa using h

end

end Submission.CField.LBrauer
