import Towers.ClassField.LocalReciprocity.CocycleNaturality
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The norm from a subgroup fixed field

For `F = Lᴴ`, the field norm `Fˣ → Kˣ` is the product over left
cosets of `H` in `Gal(L/K)`.  This is the field-theoretic input in the
corestriction square of Lemma III.3.2.
-/

namespace Towers.CField.LRecip

noncomputable section

open scoped BigOperators

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private abbrev F (H : Subgroup Gal(L/K)) :=
  IntermediateField.fixedField H

private theorem fixed_finrank_index (H : Subgroup Gal(L/K)) :
    Module.finrank K (F K L H) = H.index := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
  calc
    Module.finrank K (F K L H) * Nat.card H =
        Module.finrank K (F K L H) * Module.finrank (F K L H) L := by
      rw [IntermediateField.finrank_fixedField_eq_card]
    _ = Module.finrank K L := Module.finrank_mul_finrank K (F K L H) L
    _ = Nat.card Gal(L/K) :=
      (IsGalois.card_aut_eq_finrank K L).symm
    _ = Nat.card H * H.index := H.card_mul_index.symm
    _ = H.index * Nat.card H := Nat.mul_comm _ _

set_option maxHeartbeats 2000000 in
-- Expanding the fixed-field norm as a coset-indexed product requires extended normalization.
/-- The field norm from `Lᴴ` is the product of the conjugates indexed by
the left cosets of `H`. -/
theorem algebra_fixed_prod
    (H : Subgroup Gal(L/K)) (x : F K L H) :
    algebraMap K L (Algebra.norm K x) =
      ∏ q : Gal(L/K) ⧸ H, q.out (x : L) := by
  classical
  let G := Gal(L/K)
  let E := F K L H
  let A := AlgebraicClosure L
  let f : (G ⧸ H) → (E →ₐ[K] A) := fun q ↦
    (IsScalarTower.toAlgHom K L A).comp (q.out.toAlgHom.comp E.val)
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    have hrel : QuotientGroup.leftRel H q₁.out q₂.out := by
      apply QuotientGroup.leftRel_apply.mpr
      have hmem : q₁.out⁻¹ * q₂.out ∈ E.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hyE
        let yE : E := ⟨y, hyE⟩
        have hyA := DFunLike.congr_fun hq yE
        change algebraMap L A (q₁.out (y : L)) =
          algebraMap L A (q₂.out (y : L)) at hyA
        have hy : q₁.out (y : L) = q₂.out (y : L) :=
          (algebraMap L A).injective hyA
        change (q₁.out⁻¹ * q₂.out) (y : L) = (y : L)
        calc
          (q₁.out⁻¹ * q₂.out) (y : L) =
              q₁.out⁻¹ (q₂.out (y : L)) := rfl
          _ = q₁.out⁻¹ (q₁.out (y : L)) := by rw [hy]
          _ = (y : L) := q₁.out.symm_apply_apply (y : L)
      exact (le_of_eq (IntermediateField.fixingSubgroup_fixedField H)) hmem
    exact (Quotient.out_eq q₁).symm.trans
      ((Quotient.sound hrel).trans (Quotient.out_eq q₂))
  have hcard : Fintype.card (G ⧸ H) = Fintype.card (E →ₐ[K] A) := by
    calc
      Fintype.card (G ⧸ H) = Nat.card (G ⧸ H) :=
        Nat.card_eq_fintype_card.symm
      _ = H.index := H.index_eq_card.symm
      _ = Module.finrank K E := (fixed_finrank_index K L H).symm
      _ = Fintype.card (E →ₐ[K] A) :=
        (AlgHom.card K E A).symm
  let e : (G ⧸ H) ≃ (E →ₐ[K] A) :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩)
  apply (algebraMap L A).injective
  calc
    algebraMap L A (algebraMap K L (Algebra.norm K x)) =
        algebraMap K A (Algebra.norm K x) :=
      IsScalarTower.algebraMap_apply K L A (Algebra.norm K x)
    _ = ∏ σ : E →ₐ[K] A, σ x :=
      Algebra.norm_eq_prod_embeddings K A x
    _ = ∏ q : G ⧸ H, e q x := by
      exact (Fintype.prod_equiv e _ _ (fun _ ↦ rfl)).symm
    _ = ∏ q : G ⧸ H, algebraMap L A (q.out (x : L)) := by
      rfl
    _ = algebraMap L A (∏ q : G ⧸ H, q.out (x : L)) := by
      exact (map_prod (algebraMap L A) _ _).symm

end

end Towers.CField.LRecip
