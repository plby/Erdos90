import Submission.ClassField.BrauerGroups.BaseChangeBrauer
import Submission.ClassField.BrauerGroups.BaseChangeTower
import Submission.ClassField.BrauerGroups.CentralDivisionCSA

/-!
# Chapter IV, Section 2: the trivial Brauer class

A central simple algebra represents the identity Brauer class exactly when it
is a full matrix algebra over the base field.
-/

namespace Submission.CField.BGroups

open scoped TensorProduct

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- A central simple algebra represents the trivial Brauer class exactly when
it is a full matrix algebra over the base field. -/
theorem brauer_alg_matrix
    (A : CSA.{u, u} k) :
    brauerClass k A = 1 ↔
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) k) := by
  constructor
  · intro hA
    obtain ⟨n, hn, D, hDdiv, hDalg, hDcentral, hDfin, ⟨eA⟩⟩ :=
      matrix_division_algebra k A
    letI : NeZero n := hn
    letI : DivisionRing D := hDdiv
    letI : Algebra k D := hDalg
    letI : Algebra.IsCentral k D := hDcentral
    letI : Module.Finite k D := hDfin
    have hAD : IsBrauerEquivalent A (centralDivisionCSA k D) := by
      refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
      exact ⟨(matrixFinAlg k A).trans eA⟩
    have hAbase : IsBrauerEquivalent A (baseFieldCSA k) := by
      rw [← brauer_class]
      exact hA
    have hDbase : IsBrauerEquivalent (centralDivisionCSA k D)
        (centralDivisionCSA k k) := by
      simpa only [centralDivisionCSA, baseFieldCSA] using hAD.symm.trans hAbase
    obtain ⟨eD⟩ :=
      (division_brauer_equivalent k D k).1 hDbase
    exact ⟨n, NeZero.ne n, ⟨eA.trans eD.mapMatrix⟩⟩
  · rintro ⟨n, hn, ⟨e⟩⟩
    change brauerClass k A = brauerClass k (baseFieldCSA k)
    rw [brauer_class]
    exact brauer_equivalent_matrix k A n hn e

attribute [local instance low] Algebra.TensorProduct.rightAlgebra

/-- An algebra equivalence of extension fields transports the assertion that
a Brauer class becomes trivial. -/
theorem brauer_change_alg
    (K L E : Type u) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E]
    (e : L ≃ₐ[K] E) (beta : BrauerGroup.{u, u} K)
    (hL : brauerBaseChange K L beta = 1) :
    brauerBaseChange K E beta = 1 := by
  induction beta using Quotient.inductionOn with
  | _ A =>
      change brauerBaseChange K L (brauerClass K A) = 1 at hL
      change brauerBaseChange K E (brauerClass K A) = 1
      rw [brauer_change_class] at hL ⊢
      obtain ⟨n, hn, ⟨hA⟩⟩ :=
        (brauer_alg_matrix L
          (scalarExtensionCSA K L A)).1 hL
      apply (brauer_alg_matrix E
        (scalarExtensionCSA K E A)).2
      refine ⟨n, hn, ?_⟩
      change (A ⊗[K] L) ≃ₐ[L] Matrix (Fin n) (Fin n) L at hA
      let fRing : (A ⊗[K] E) ≃+* Matrix (Fin n) (Fin n) E :=
        (Algebra.TensorProduct.congr
            (AlgEquiv.refl : A ≃ₐ[K] A) e.symm).toRingEquiv |>.trans
          (hA.toRingEquiv.trans e.toRingEquiv.mapMatrix)
      let fE : (A ⊗[K] E) ≃ₐ[E] Matrix (Fin n) (Fin n) E :=
        { fRing with
          commutes' := by
            intro x
            change (hA (1 ⊗ₜ[K] e.symm x)).map e =
              algebraMap E (Matrix (Fin n) (Fin n) E) x
            calc
              (hA (1 ⊗ₜ[K] e.symm x)).map e =
                  (hA (algebraMap L (A ⊗[K] L) (e.symm x))).map e := by
                    rw [Algebra.TensorProduct.right_algebraMap_apply]
              _ = (algebraMap L (Matrix (Fin n) (Fin n) L)
                    (e.symm x)).map e := by rw [hA.commutes]
              _ = algebraMap E (Matrix (Fin n) (Fin n) E) x := by
                ext i j
                by_cases hij : i = j <;>
                  simp [Matrix.algebraMap_matrix_apply, hij] }
      exact ⟨fE⟩

end

end Submission.CField.BGroups
