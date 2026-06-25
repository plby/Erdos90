import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.Torsion
import Submission.ClassField.CrossedProducts.TensorRightCongr
import Submission.ClassField.CrossedProducts.Cohomology

/-!
# Chapter IV, Section 3, Corollary 3.17

The cohomological input to Milne's Corollary 3.17 is that cohomology of a
finite group is killed by the group order.  In degree two this has a short
explicit proof: for a multiplicative cocycle `f`, multiply its cocycle
identity over the final variable.

The theorem below formalizes the complete degree-two cocycle calculation used
by Milne.  The group isomorphism of Theorem 3.14 transports it to relative
Brauer groups, and Corollary 3.10 then proves that the full Brauer group is
torsion.
-/

namespace Submission.CField.CProduca

open scoped BigOperators
open groupCohomology

universe u

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M]
  [MulDistribMulAction G M]

/-- A multiplicative `2`-cocycle of a finite group, raised pointwise to the
order of the group, is a multiplicative `2`-coboundary.  This is the
degree-two cohomological assertion used in Corollary IV.3.17. -/
theorem isMulCoboundary₂_pow_card (f : G × G → M) (hf : IsMulCocycle₂ f) :
    IsMulCoboundary₂ (fun p ↦ f p ^ Fintype.card G) := by
  refine ⟨fun g ↦ ∏ j : G, f (g, j), ?_⟩
  intro g h
  have hcocycle :
      (∏ j : G, f (g * h, j) * f (g, h)) =
        ∏ j : G, g • f (h, j) * f (g, h * j) := by
    exact Fintype.prod_congr _ _ fun j ↦ hf g h j
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hcocycle
  rw [← Finset.smul_prod'] at hcocycle
  have hperm : (∏ j : G, f (g, h * j)) = ∏ j : G, f (g, j) := by
    exact Fintype.prod_bijective (h * ·) (Group.mulLeft_bijective h)
      (fun j ↦ f (g, h * j)) (fun j ↦ f (g, j)) (fun _ ↦ rfl)
  rw [hperm] at hcocycle
  change
    (g • ∏ j : G, f (h, j)) / (∏ j : G, f (g * h, j)) *
        (∏ j : G, f (g, j)) = f (g, h) ^ Fintype.card G
  rw [div_eq_mul_inv]
  calc
    (g • ∏ j : G, f (h, j)) * (∏ j : G, f (g * h, j))⁻¹ *
          (∏ j : G, f (g, j)) =
        ((g • ∏ j : G, f (h, j)) * (∏ j : G, f (g, j))) *
          (∏ j : G, f (g * h, j))⁻¹ := by ac_rfl
    _ = ((∏ j : G, f (g * h, j)) * f (g, h) ^ Fintype.card G) *
          (∏ j : G, f (g * h, j))⁻¹ := by rw [hcocycle]
    _ = f (g, h) ^ Fintype.card G := by
      simp [mul_assoc, mul_comm]

/-- Normalized cocycles satisfy the same exponent bound. -/
theorem NMCocycl₂.isMulCoboundary₂_pow_card
    (f : NMCocycl₂ (G := G) (M := M)) :
    IsMulCoboundary₂ (fun p ↦ f p ^ Fintype.card G) :=
  Submission.CField.CProduca.isMulCoboundary₂_pow_card
    (fun p ↦ f p) f.isMulCocycle₂

/-- Every class in multiplicative `H²(G,M)` is killed by the order of the
finite group `G`. -/
theorem MHTwo.card_pow_one
    (x : MHTwo G M) : x ^ Fintype.card G = 1 := by
  induction x using Quotient.inductionOn with
  | _ c =>
      change MHTwo.mk c ^ Fintype.card G = 1
      rw [← MHTwo.mk_pow]
      change MHTwo.mk (c ^ Fintype.card G) = MHTwo.mk 1
      apply Quotient.sound
      change MHTwo.IsCohomologous (c ^ Fintype.card G) 1
      simpa [MHTwo.IsCohomologous] using
        NMCocycl₂.isMulCoboundary₂_pow_card c

/-- Assuming the tensor-product calculation of Lemma IV.3.15, the relative
Brauer group of a finite Galois extension is killed by the extension degree.
This is the Galois case of Corollary IV.3.17. -/
theorem relative_tensor_compatibility
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (hcompat : ∀ c d : NMCocycl₂
      (G := Gal(L/k)) (M := Lˣ),
        CProduc.TensorCompatibility k L c d)
    (x : BGroups.relativeBrauerGroup k L) :
    x ^ Module.finrank k L = 1 := by
  obtain ⟨y, rfl⟩ := CProduc.h_brauer_surjective k L x
  let e := CProduc.hTensorCompatibility
    k L hcompat
  have hy := MHTwo.card_pow_one y
  have hcard : Fintype.card (Gal(L/k)) = Module.finrank k L :=
    Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank k L)
  change e y ^ Module.finrank k L = 1
  rw [← hcard, ← map_pow]
  simpa using congrArg e hy

/-- The relative Brauer group of a finite Galois extension is killed by the
extension degree. -/
theorem relative_brauer_one
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (x : BGroups.relativeBrauerGroup k L) :
    x ^ Module.finrank k L = 1 :=
  relative_tensor_compatibility k L
    (fun c d ↦ CProduc.tensorCompatibility k L c d) x

/-- **Corollary IV.3.17, first assertion.** The Brauer group of every field
is a torsion group. -/
theorem brauer_group_torsion (k : Type u) [Field k] :
    Monoid.IsTorsion (BrauerGroup.{u, u} k) := by
  intro x
  rw [isOfFinOrder_iff_pow_eq_one]
  have hx : x ∈ (Set.univ : Set (BrauerGroup.{u, u} k)) := Set.mem_univ x
  rw [brauer_i_classes] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨L, hxL⟩ := hx
  let y : BGroups.relativeBrauerGroup k L := ⟨x, hxL⟩
  refine ⟨Module.finrank k L, Module.finrank_pos, ?_⟩
  have hy := relative_brauer_one k L y
  exact congrArg Subtype.val hy

end Submission.CField.CProduca
