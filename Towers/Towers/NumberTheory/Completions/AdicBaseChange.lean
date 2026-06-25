import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Adic completion after extending an ideal

For an `R`-algebra `S`, the `I`-adic filtration on the `R`-module `S`
agrees with the filtration by powers of the extended ideal `I S`.  This file
develops the quotient and completion equivalences needed to compare finite
module completion with ring completion in Milne's proof of Theorem 8.42.
-/

namespace Towers.NumberTheory.Milne

open scoped TensorProduct

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The module filtration by `I ^ n` is the restriction of scalars of the
ring filtration by the `n`-th power of the extended ideal. -/
theorem smul_restrict_scalars (I : Ideal R) (n : ℕ) :
    (I ^ n • (⊤ : Submodule R S)) =
      ((I.map (algebraMap R S)) ^ n : Ideal S).restrictScalars R := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow]

/-- Quotienting the `R`-module `S` by `I ^ n` agrees with quotienting the
ring `S` by the corresponding power of the extended ideal. -/
def adicChangeEquiv (I : Ideal R) (n : ℕ) :
    (S ⧸ (I ^ n • (⊤ : Submodule R S))) ≃ₗ[R]
      S ⧸ ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S S)) :=
  (Submodule.quotEquivOfEq _ _
    (smul_restrict_scalars I n)).trans
      ((Submodule.Quotient.restrictScalarsEquiv R
        ((I.map (algebraMap R S)) ^ n : Ideal S)).trans
          ((Submodule.quotEquivOfEq _ _ (by simp)).restrictScalars R))

@[simp]
theorem adic_base_change (I : Ideal R) (n : ℕ) (x : S) :
    adicChangeEquiv I n
        (Submodule.mkQ (I ^ n • (⊤ : Submodule R S)) x) =
      Submodule.mkQ
        ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S S)) x :=
  rfl

@[simp]
theorem adic_change_mk
    (I : Ideal R) (n : ℕ) (x : S) :
    adicChangeEquiv I n
        (Submodule.Quotient.mk
          (p := I ^ n • (⊤ : Submodule R S)) x) =
      Submodule.Quotient.mk
        (p := (I.map (algebraMap R S)) ^ n •
          (⊤ : Submodule S S)) x :=
  rfl

@[simp]
theorem base_change_mk
    (I : Ideal R) (n : ℕ) (x : S) :
    (adicChangeEquiv I n).symm
        (Submodule.mkQ
          ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S S)) x) =
      Submodule.mkQ (I ^ n • (⊤ : Submodule R S)) x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Reducing both quotient transition maps unfolds two scalar restrictions.
/-- The quotient equivalences commute with the transition maps in the two
adic inverse systems. -/
theorem base_change_transition
    (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : S ⧸ (I ^ n • (⊤ : Submodule R S))) :
    AdicCompletion.transitionMap (I.map (algebraMap R S)) S hmn
        (adicChangeEquiv (R := R) (S := S) I n x) =
      adicChangeEquiv (R := R) (S := S) I m
        (AdicCompletion.transitionMap I S hmn x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change AdicCompletion.transitionMap
          (I.map (algebraMap R S)) S hmn
            (adicChangeEquiv (R := R) (S := S) I n
              (Submodule.mkQ (I ^ n • (⊤ : Submodule R S)) x)) =
        adicChangeEquiv (R := R) (S := S) I m
          (AdicCompletion.transitionMap I S hmn
            (Submodule.mkQ (I ^ n • (⊤ : Submodule R S)) x))
      rw [adic_base_change]
      change Submodule.factor _ (Submodule.mkQ _ x) =
        adicChangeEquiv (R := R) (S := S) I m
          (Submodule.factor _ (Submodule.mkQ _ x))
      rw [Submodule.factor_mk]
      rw [Submodule.factor_mk]
      rw [adic_base_change]

/-- The inverse quotient equivalences also commute with transition maps. -/
theorem adic_change_transition
    (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : S ⧸ ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S S))) :
    AdicCompletion.transitionMap I S hmn
        ((adicChangeEquiv (R := R) (S := S) I n).symm x) =
      (adicChangeEquiv (R := R) (S := S) I m).symm
        (AdicCompletion.transitionMap (I.map (algebraMap R S)) S hmn x) := by
  apply (adicChangeEquiv (R := R) (S := S) I m).injective
  rw [LinearEquiv.apply_symm_apply]
  rw [← base_change_transition]
  rw [LinearEquiv.apply_symm_apply]

/-- Coordinatewise extension of the quotient comparison from the module
completion of `S` to the ring completion at the extended ideal. -/
def adicChangeLinear (I : Ideal R) :
    AdicCompletion I S →ₗ[R]
      AdicCompletion (I.map (algebraMap R S)) S where
  toFun x := ⟨fun n => adicChangeEquiv I n (x.val n),
    fun hmn => by
      rw [base_change_transition, x.property hmn]⟩
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact (adicChangeEquiv I n).map_add _ _
  map_smul' r x := by
    apply AdicCompletion.ext
    intro n
    exact (adicChangeEquiv I n).map_smul r _

/-- The inverse coordinatewise map from ring completion to module
completion. -/
def adicChangeInv (I : Ideal R) :
    AdicCompletion (I.map (algebraMap R S)) S →ₗ[R]
      AdicCompletion I S where
  toFun x := ⟨fun n => (adicChangeEquiv I n).symm (x.val n),
    fun hmn => by
      rw [adic_change_transition, x.property hmn]⟩
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact (adicChangeEquiv I n).symm.map_add _ _
  map_smul' r x := by
    apply AdicCompletion.ext
    intro n
    exact (adicChangeEquiv I n).symm.map_smul r _

/-- Completion of the `R`-module `S` at `I` is linearly equivalent to ring
completion of `S` at the extended ideal `I S`. -/
def adicBaseChange (I : Ideal R) :
    AdicCompletion I S ≃ₗ[R]
      AdicCompletion (I.map (algebraMap R S)) S where
  toFun := adicChangeLinear I
  invFun := adicChangeInv I
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (adicChangeEquiv I n).symm_apply_apply (x.val n)
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (adicChangeEquiv I n).apply_symm_apply (x.val n)
  map_add' := (adicChangeLinear I).map_add
  map_smul' := (adicChangeLinear I).map_smul

/-- For a finite algebra over a Noetherian ring, scalar extension to the
completed base is the completion at the extended ideal, as an `R`-module. -/
def adicCompletionRing
    (I : Ideal R) [IsNoetherianRing R] [Module.Finite R S] :
    AdicCompletion I R ⊗[R] S ≃ₗ[R]
      AdicCompletion (I.map (algebraMap R S)) S :=
  ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I S).restrictScalars R).trans
    (adicBaseChange I)

/-- The linear base-change equivalence evaluated in a quotient coordinate. -/
@[simp]
theorem adic_change_val
    (I : Ideal R) (x : AdicCompletion I S) (n : ℕ) :
    (adicBaseChange I x).val n =
      adicChangeEquiv I n (x.val n) :=
  rfl

/-- Scalar multiplication in a quotient coordinate, on representatives. -/
@[simp]
theorem adic_mk_smul
    (I : Ideal R) (n : ℕ) (r : R) (s : S) :
    Ideal.Quotient.mk (I ^ n • (⊤ : Ideal R)) r •
        Submodule.Quotient.mk
          (p := (I ^ n • (⊤ : Submodule R S))) s =
      r • Submodule.Quotient.mk
        (p := (I ^ n • (⊤ : Submodule R S))) s :=
  rfl

set_option linter.flexible false in
/-- The canonical comparison from scalar extension to completion is an
equivalence of `R`-algebras. -/
def adicTensorRing
    (I : Ideal R) [IsNoetherianRing R] [Module.Finite R S] :
    AdicCompletion I R ⊗[R] S ≃ₐ[R]
      AdicCompletion (I.map (algebraMap R S)) S :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (adicCompletionRing I)
    (by
      intro a₁ a₂ s₁ s₂
      apply AdicCompletion.ext
      intro n
      simp [adicCompletionRing,
        AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
        AdicCompletion.ofTensorProduct_tmul]
      induction a₁.val n using Submodule.Quotient.induction_on with
      | _ r₁ =>
          induction a₂.val n using Submodule.Quotient.induction_on with
          | _ r₂ =>
              change adicChangeEquiv I n
                  (Ideal.Quotient.mk (I ^ n • (⊤ : Ideal R)) (r₁ * r₂) •
                    Submodule.Quotient.mk (s₁ * s₂)) =
                adicChangeEquiv I n
                    (Ideal.Quotient.mk (I ^ n • (⊤ : Ideal R)) r₁ •
                      Submodule.Quotient.mk s₁) *
                  adicChangeEquiv I n
                    (Ideal.Quotient.mk (I ^ n • (⊤ : Ideal R)) r₂ •
                      Submodule.Quotient.mk s₂)
              rw [adic_mk_smul,
                adic_mk_smul, adic_mk_smul]
              rw [← Submodule.Quotient.mk_smul,
                ← Submodule.Quotient.mk_smul,
                ← Submodule.Quotient.mk_smul]
              rw [adic_change_mk,
                adic_change_mk,
                adic_change_mk]
              simp [Algebra.smul_def, mul_assoc, mul_left_comm])
    (by
      apply AdicCompletion.ext
      intro n
      simp [adicCompletionRing,
        AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
        AdicCompletion.ofTensorProduct_tmul]
      exact adic_base_change I n (1 : S))

/-- On a pure tensor, the algebra comparison is the coordinatewise
base-change of the usual completed-module comparison. -/
@[simp]
theorem adic_alg_tmul
    (I : Ideal R) [IsNoetherianRing R] [Module.Finite R S]
    (a : AdicCompletion I R) (s : S) :
    adicTensorRing I (a ⊗ₜ[R] s) =
      adicBaseChange I
        (a • AdicCompletion.of I S s) := by
  rfl

/-- In particular, the canonical copy of `S` is sent to its canonical
image in the completion at the extended ideal. -/
@[simp]
theorem adic_tensor_tmul
    (I : Ideal R) [IsNoetherianRing R] [Module.Finite R S] (s : S) :
    adicTensorRing I
        ((1 : AdicCompletion I R) ⊗ₜ[R] s) =
      AdicCompletion.of (I.map (algebraMap R S)) S s := by
  rw [adic_alg_tmul, one_smul]
  apply AdicCompletion.ext
  intro n
  exact adic_base_change I n s

end

end Towers.NumberTheory.Milne
