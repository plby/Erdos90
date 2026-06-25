import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Bounding the degree of a completed factor

When scalar extension decomposes as a finite product of field extensions,
the degree of every factor is at most the degree before scalar extension.
Passing between a finite extension of domains and its fraction fields then
gives the corresponding bound for the integral valuation rings.
-/

namespace Submission.NumberTheory.Milne

open scoped TensorProduct

noncomputable section

universe u

section Product

variable {K L F ι : Type u}
  [Field K] [Field L] [Field F]
  [Algebra K L] [Algebra K F]
  [Finite ι]
variable (E : ι → Type u)
  [∀ i, Field (E i)] [∀ i, Algebra F (E i)]
  [∀ i, FiniteDimensional F (E i)]

/-- Every coordinate of a finite product decomposition of a scalar
extension has degree at most the original field extension. -/
theorem finrank_tensor_pi
    (e : F ⊗[K] L ≃ₐ[F] (∀ i, E i)) (i : ι) :
    Module.finrank F (E i) ≤ Module.finrank K L := by
  classical
  letI := Fintype.ofFinite ι
  calc
    Module.finrank F (E i) ≤ ∑ j : ι, Module.finrank F (E j) :=
      Finset.single_le_sum
        (s := Finset.univ) (f := fun j => Module.finrank F (E j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = Module.finrank F (∀ j, E j) :=
      (Module.finrank_pi_fintype (R := F) (M := E)).symm
    _ = Module.finrank F (F ⊗[K] L) :=
      e.toLinearEquiv.finrank_eq.symm
    _ = Module.finrank K L := Module.finrank_baseChange

/-- If a scalar extension decomposes into exactly as many nonzero field
coordinates as its degree, every coordinate has degree one. -/
theorem finrank_factor_card
    (e : F ⊗[K] L ≃ₐ[F] (∀ i, E i))
    (hcard : Nat.card ι = Module.finrank K L) (i : ι) :
    Module.finrank F (E i) = 1 := by
  classical
  letI := Fintype.ofFinite ι
  have hsum : ∑ j : ι, Module.finrank F (E j) = Fintype.card ι := by
    calc
      ∑ j : ι, Module.finrank F (E j) = Module.finrank F (∀ j, E j) :=
        (Module.finrank_pi_fintype (R := F) (M := E)).symm
      _ = Module.finrank F (F ⊗[K] L) := e.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K L := Module.finrank_baseChange
      _ = Fintype.card ι := by
        rw [← Nat.card_eq_fintype_card, hcard]
  let s : Finset ι := Finset.univ.erase i
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hsplit :
      ∑ j : ι, Module.finrank F (E j) =
        Module.finrank F (E i) + ∑ j ∈ s, Module.finrank F (E j) := by
    rw [← Finset.sum_erase_add _ _ hi, add_comm]
  have hcardSplit : Fintype.card ι = s.card + 1 := by
    rw [← Finset.card_univ, ← Finset.card_erase_add_one hi]
  have hrest : s.card ≤ ∑ j ∈ s, Module.finrank F (E j) := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun j _ => Module.finrank_pos
  have hpositive : 0 < Module.finrank F (E i) := Module.finrank_pos
  omega

end Product

section FractionFields

variable {C B F E : Type u}
  [CommRing C] [CommRing B] [IsDomain B]
  [Field F] [Field E]
  [Algebra C B] [FaithfulSMul C B]
  [Algebra.IsAlgebraic C B]
  [Algebra C F] [IsFractionRing C F]
  [Algebra B E] [IsFractionRing B E]
  [Algebra F E] [Algebra C E]
  [IsScalarTower C B E] [IsScalarTower C F E]

/-- A degree bound for the fraction fields is the same degree bound for
the underlying finite domain extension. -/
theorem finrank_fraction_fields (N : ℕ)
    (h : Module.finrank F E ≤ N) :
    Module.finrank C B ≤ N := by
  calc
    Module.finrank C B = Module.finrank F E :=
      (Algebra.IsAlgebraic.finrank_of_isFractionRing C F B E).symm
    _ ≤ N := h

end FractionFields

end

end Submission.NumberTheory.Milne
