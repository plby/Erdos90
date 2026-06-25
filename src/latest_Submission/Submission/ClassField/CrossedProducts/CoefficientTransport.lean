import Submission.ClassField.CrossedProducts.ProductBaseChange

/-!
# Transporting crossed products along a coefficient-field equivalence

Changing the chosen Galois splitting field by an equivalence over the base
does not change the represented Brauer class.
-/

namespace Submission.CField.CProduca

noncomputable section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

/-- Scalar extension from a field to itself is the identity on its Brauer
group. -/
theorem brauer_change_self
    (k : Type u) [Field k] (x : BrauerGroup k) :
    BGroups.brauerBaseChange k k x = x := by
  induction x using Quotient.inductionOn with
  | _ A =>
      apply Quotient.sound
      apply BGroups.brauer_equivalent_alg k
      exact (Algebra.TensorProduct.commRight k k A).symm.trans
        (Algebra.TensorProduct.lid k A)

/-- Transporting the Galois group, coefficient field, and cocycle through a
base-field equivalence preserves the absolute crossed-product Brauer class. -/
theorem brauer_transported_cocycle
    (k L E : Type u)
    [Field k] [Field L] [Field E]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
    (e : L ≃ₐ[k] E)
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)) :
    CProduc.brauerClass k L c =
      CProduc.brauerClass k E
        (transportedGaloisCocycle e.toRingEquiv.toRingHom e.autCongr
          (fun sigma a => by simp [AlgEquiv.autCongr_apply]) c) := by
  let coeffEquiv : L ⊗[k] k ≃ₐ[k] E :=
    (Algebra.TensorProduct.commRight k k L).symm |>.trans
      (Algebra.TensorProduct.lid k L) |>.trans e
  have hcoeff : ∀ (a : L) (b : k),
      coeffEquiv (a ⊗ₜ[k] b) =
        e a * algebraMap k E b := by
    intro a b
    calc
      coeffEquiv (a ⊗ₜ[k] b) = algebraMap k E b * e a := by
        simp only [AlgEquiv.trans_apply,
          Algebra.TensorProduct.commRight_symm_tmul,
          Algebra.TensorProduct.lid_tmul, Algebra.smul_def, map_mul,
          e.commutes, coeffEquiv]
      _ = e a * algebraMap k E b := mul_comm _ _
  have h := brauer_base_crossed
    e.toRingEquiv.toRingHom e.autCongr
      (fun sigma a => by simp [AlgEquiv.autCongr_apply])
      (fun a => e.commutes a) c coeffEquiv hcoeff
  rw [brauer_change_self] at h
  exact h

end

end Submission.CField.CProduca
